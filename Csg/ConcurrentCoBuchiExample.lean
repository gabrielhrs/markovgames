/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.CoBuchiOp
import Csg.ReachCertificate
import Csg.SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

/-!
# Worked instance: de Alfaro and Majumdar's Example 3 / Fig. 1

**Status: confirmed by a clean `lake build`.** Five rounds of fixes against real `lake build`
output, briefly: missing imports and a broken pair of fully-general `MatrixGame` lemmas replaced
by concrete `RowMove`/`ColMove`-specific ones (round 1); `cbR_zero` restated against `cbCSG.r`
plus assorted tactic-level fixes -- `ring`→`abel`, `norm_num`→`simp` on custom-inductive
`if`-conditions, `← mul_add`/`← add_mul` factoring, explicit `mul_le_mul_of_nonneg_left/right`
hints in place of bare `nlinarith` (round 2); a stray `ℝ≥0∞` that failed to parse (`ENNReal`
instead), and `coBuchiInnerOpFun`'s `Set.Icc`-subtype packaging defeating `rw`'s motive-checking
on `if_pos`/`if_neg`, fixed by adding `CSG.coBuchiInnerOpFun_coe` (`CoBuchiOp.lean`) as a
subtype-free `ℝ`-valued `if`-`then`-`else` (round 3); a `rw [lemma (by tac)]`/`exact lemma (by
tac)` pattern in `cbCoin_apply_left`/`_right`/`_other` leaving the embedded tactic block's target
as a genuinely separate unsolved goal, fixed by naming the side condition with an explicit `have`
first, plus a missing `.t5` case in `cbExpect_t3d`'s `rw` chain and several `cbInnerGfp_eq` spots
needing an explicit trailing `rfl` where `rw`'s own reflexivity check didn't unfold
`cbGClosed`/`cbGClosedVal` as aggressively as a standalone `rfl` (round 4); round 4's `have`
extraction for `cbCoin_apply_left`/`_right`/`_other` still filled the wrong argument slot --
`PMF.uniformOfFinset_apply_of_mem`/`_of_notMem` take `hs : s.Nonempty` as an *explicit* argument
*before* the membership proof -- fixed by supplying the witness explicitly,
`PMF.uniformOfFinset_apply_of_mem ⟨x, by simp⟩ hx` (round 5). **Cosmetic pass**: the 25 `show ...`
tactic calls that actually changed the goal (Lean's `show`-linter flags this) were all rewritten
to `change`; term-mode `show ... from rfl`/`show ... by decide` used as plain arguments inside
`rw [...]` are a different, unaffected construct and were left alone. The worked instance
`BuchiOp.lean`'s and `CoBuchiOp.lean`'s
docstrings both flagged as the natural next step: de Alfaro and Majumdar, "Quantitative Solution of
Omega-Regular Games," JCSS 68 (2004) 374-397, Example 3 / Fig. 1 (p. 395), the paper's own
demonstration that the MDP shortcut -- reducing a Büchi/co-Büchi condition to plain reachability of
the almost-surely-winning set -- fails for concurrent games. Five states `t1,...,t5`,
`U = {t1, t2, t4}`, co-Büchi objective `◇□U`. The paper states `⟨1⟩◇□U(t2) = 2/3` and
`⟨1⟩◇□U(t3) = 1/3` exactly (Section 7); this file proves
`(cbCSG.coBuchiOp cbU cbR_zero).lfp = cbVStar` with `cbVStar` matching those two values (and `1` at
`t1`, `0` at `t4`/`t5`) on the nose, via `OrderHom.lfp_eq_of_certificate`/`gfp_eq_of_certificate`.

Board (row player picks first coordinate of each action label, column picks second, per the
paper's own Fig. 1 caption): `t1` self-loops with probability `1`. At `t2`, only the row player
(`RowMove`) has a real choice: `b` self-loops to `t2`, `d` splits `1/2`/`1/2` to `t1`/`t3`. At `t3`,
only the column player (`ColMove`) has a real choice: `c` self-loops to `t3`, `d` splits `1/2`/`1/2`
to `t2`/`t4`. `t4` and `t5` alternate deterministically, `t4 → t5 → t4`. Row is this project's
minimizer and column its maximizer (`MatrixGame`'s own convention), and the paper's "player 1"
(the ◇□U achiever, maximizing) is column, "player 2" (the avoider, minimizing) is row -- read off
directly from which player is active where: player 1 (achiever) moves at `t3`, and reaching `t1`
(a certain win for the achiever) is exactly what the avoider at `t2` is trying to steer away from.

**The one substantial proof idea.** `(C.coBuchiOp U hr).lfp` is a fixed point of a fixed point:
`(cbCSG.coBuchiInnerOp cbU hr b).gfp`, the *inner* level, still has to be pinned down for an
*arbitrary* outer parameter `b`, not just at the final answer `cbVStar` -- that arbitrary-`b` fact
is exactly what `OrderHom.lfp_eq_of_certificate`'s `hlb` hypothesis (`vStar` below every
pre-fixed-point of the whole `coBuchiOp`) needs to unfold into. `cbInnerGfp_eq` supplies it: a
closed form for the inner `gfp` as an explicit function of `b`, proved via `coBuchiInnerOp`'s own
`OrderHom.gfp_eq_of_certificate` (`b`'s `¬U` states, `t3`/`t5`, resolve directly off `b` with no
self-reference; `t4` chains off the now-resolved `t5`; `t1` is unconstrained by its own trivial
self-loop equation and pinned only by every candidate's own `≤ 1` bound; `t2` chains off the
now-resolved `t1`/`t3`). Both `hfixed` (the outer level's own fixed-point check, specialising
`b := cbVStar`) and `hlb` (the outer level's least-fixed-point check, for arbitrary `b`) then
reduce to this one closed form plus `linarith`-level algebra -- no second, independent argument.
-/

namespace Csg

/-! ## The game itself -/

/-- The five states of Fig. 1. -/
inductive CBState
  | t1
  | t2
  | t3
  | t4
  | t5
  deriving DecidableEq, Inhabited

/-- Same `deriving Fintype` toolchain workaround as `IntrusionDetection.lean`'s `IDSState`. -/
instance : Fintype CBState where
  elems := {CBState.t1, .t2, .t3, .t4, .t5}
  complete := by intro s; cases s <;> decide

/-- Expand a sum over all of `CBState` into its five terms. -/
theorem cbState_sum {β : Type*} [AddCommMonoid β] (f : CBState → β) :
    ∑ s : CBState, f s = f .t1 + f .t2 + f .t3 + f .t4 + f .t5 := by
  have huniv : (Finset.univ : Finset CBState) = {CBState.t1, .t2, .t3, .t4, .t5} := by decide
  rw [huniv]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-- The row player's two moves at `t2` (irrelevant everywhere else, since every action is
    available in every state). -/
inductive RowMove
  | b
  | d
  deriving DecidableEq, Inhabited

instance : Fintype RowMove where
  elems := {RowMove.b, .d}
  complete := by intro a; cases a <;> decide

/-- Expand a sum over all of `RowMove` into its two terms, matching `IntrusionDetection.lean`'s
    `policyAction_sum` idiom. -/
theorem rowMove_sum {β : Type*} [AddCommMonoid β] (f : RowMove → β) :
    ∑ a : RowMove, f a = f .b + f .d := by
  have huniv : (Finset.univ : Finset RowMove) = {RowMove.b, .d} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The column player's two moves at `t3` (irrelevant outside `t3`, same convention as
    `RowMove`). -/
inductive ColMove
  | c
  | d
  deriving DecidableEq, Inhabited

instance : Fintype ColMove where
  elems := {ColMove.c, .d}
  complete := by intro a; cases a <;> decide

/-- Expand a sum over all of `ColMove` into its two terms. -/
theorem colMove_sum {β : Type*} [AddCommMonoid β] (f : ColMove → β) :
    ∑ a : ColMove, f a = f .c + f .d := by
  have huniv : (Finset.univ : Finset ColMove) = {ColMove.c, .d} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- A fair coin between two distinct states, via `PMF.uniformOfFinset` on the two-element
    `Finset` `{x, y}` -- each gets probability `1 / #{x, y} = 1/2`. -/
noncomputable def cbCoin (x y : CBState) (hxy : x ≠ y) : PMF CBState :=
  PMF.uniformOfFinset {x, y} ⟨x, by simp⟩

theorem cbCoin_apply_left (x y : CBState) (hxy : x ≠ y) :
    cbCoin x y hxy x = (2 : ENNReal)⁻¹ := by
  unfold cbCoin
  have hx : x ∈ ({x, y} : Finset CBState) := by simp
  rw [PMF.uniformOfFinset_apply_of_mem ⟨x, by simp⟩ hx, Finset.card_pair hxy]
  norm_num

theorem cbCoin_apply_right (x y : CBState) (hxy : x ≠ y) :
    cbCoin x y hxy y = (2 : ENNReal)⁻¹ := by
  unfold cbCoin
  have hy : y ∈ ({x, y} : Finset CBState) := by simp
  rw [PMF.uniformOfFinset_apply_of_mem ⟨x, by simp⟩ hy, Finset.card_pair hxy]
  norm_num

theorem cbCoin_apply_other (x y z : CBState) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    cbCoin x y hxy z = 0 := by
  unfold cbCoin
  have hz : z ∉ ({x, y} : Finset CBState) := by simp [hzx, hzy]
  exact PMF.uniformOfFinset_apply_of_notMem ⟨x, by simp⟩ hz

/-- The transition kernel, read directly off Fig. 1: `t1` a deterministic self-loop; `t2`'s row
    move `b` self-loops, `d` splits evenly to `t1`/`t3`; `t3`'s column move `c` self-loops, `d`
    splits evenly to `t2`/`t4`; `t4 → t5` and `t5 → t4` deterministically. -/
noncomputable def cbK : CBState → RowMove → ColMove → PMF CBState
  | .t1, _, _ => PMF.pure .t1
  | .t2, .b, _ => PMF.pure .t2
  | .t2, .d, _ => cbCoin .t1 .t3 (by decide)
  | .t3, _, .c => PMF.pure .t3
  | .t3, _, .d => cbCoin .t2 .t4 (by decide)
  | .t4, _, _ => PMF.pure .t5
  | .t5, _, _ => PMF.pure .t4

/-- Reward-free, as `coBuchiOp`/`buchiOp` both require. -/
noncomputable def cbR : CBState → RowMove → ColMove → ℝ := fun _ _ _ => 0

/-- Fig. 1, as a `CSG`. -/
noncomputable def cbCSG : CSG CBState RowMove ColMove where
  K := cbK
  r := cbR

theorem cbCSG_r (s : CBState) (a1 : RowMove) (a2 : ColMove) : cbCSG.r s a1 a2 = 0 := rfl

/-- Stated in terms of `cbCSG.r`, not the raw `cbR`, since that is the form `coBuchiOp`/
    `coBuchiInnerOp`'s `hr` parameter actually expects (`C.r`, specialised to `C := cbCSG`) --
    the two are definitionally equal, but the earlier `cbR`-headed statement failed to unify
    against that expected type and cascaded into a long list of downstream elaboration failures. -/
theorem cbR_zero : ∀ s a1 a2, cbCSG.r s a1 a2 = 0 := cbCSG_r

/-- `U = {t1, t2, t4}`, exactly Example 3's own choice. -/
def cbU : CBState → Prop := fun s => s = .t1 ∨ s = .t2 ∨ s = .t4

instance : DecidablePred cbU := fun s => by unfold cbU; infer_instance

/-! ## `expect`, computed at every reachable `(state, action)` pair -/

theorem cbExpect_pure (v : CBState → ℝ) (s t : CBState) (a1 : RowMove) (a2 : ColMove)
    (h : cbK s a1 a2 = PMF.pure t) : cbCSG.expect s a1 a2 v = v t := by
  change ∑ s', (cbCSG.K s a1 a2 s').toReal * v s' = v t
  rw [show cbCSG.K = cbK from rfl, h, cbState_sum]
  rcases t with _ | _ | _ | _ | _ <;> simp [PMF.pure_apply]

theorem cbExpect_t1 (a1 : RowMove) (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t1 a1 a2 v = v .t1 := cbExpect_pure v .t1 .t1 a1 a2 rfl

theorem cbExpect_t2b (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t2 .b a2 v = v .t2 := cbExpect_pure v .t2 .t2 .b a2 rfl

theorem cbExpect_t3c (a1 : RowMove) (v : CBState → ℝ) :
    cbCSG.expect .t3 a1 .c v = v .t3 := cbExpect_pure v .t3 .t3 a1 .c rfl

theorem cbExpect_t4 (a1 : RowMove) (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t4 a1 a2 v = v .t5 := cbExpect_pure v .t4 .t5 a1 a2 rfl

theorem cbExpect_t5 (a1 : RowMove) (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t5 a1 a2 v = v .t4 := cbExpect_pure v .t5 .t4 a1 a2 rfl

theorem cbExpect_t2d (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t2 .d a2 v = (v .t1 + v .t3) / 2 := by
  change ∑ s', (cbCSG.K .t2 .d a2 s').toReal * v s' = (v .t1 + v .t3) / 2
  rw [show cbCSG.K = cbK from rfl, show cbK .t2 .d a2 = cbCoin .t1 .t3 (by decide) from rfl,
    cbState_sum]
  rw [cbCoin_apply_left .t1 .t3 (by decide),
    cbCoin_apply_other .t1 .t3 .t2 (by decide) (by decide) (by decide),
    cbCoin_apply_right .t1 .t3 (by decide),
    cbCoin_apply_other .t1 .t3 .t4 (by decide) (by decide) (by decide),
    cbCoin_apply_other .t1 .t3 .t5 (by decide) (by decide) (by decide)]
  simp [ENNReal.toReal_inv]
  ring

theorem cbExpect_t3d (a1 : RowMove) (v : CBState → ℝ) :
    cbCSG.expect .t3 a1 .d v = (v .t2 + v .t4) / 2 := by
  change ∑ s', (cbCSG.K .t3 a1 .d s').toReal * v s' = (v .t2 + v .t4) / 2
  rw [show cbCSG.K = cbK from rfl, show cbK .t3 a1 .d = cbCoin .t2 .t4 (by decide) from rfl,
    cbState_sum]
  rw [cbCoin_apply_other .t2 .t4 .t1 (by decide) (by decide) (by decide),
    cbCoin_apply_left .t2 .t4 (by decide),
    cbCoin_apply_other .t2 .t4 .t3 (by decide) (by decide) (by decide),
    cbCoin_apply_right .t2 .t4 (by decide),
    cbCoin_apply_other .t2 .t4 .t5 (by decide) (by decide) (by decide)]
  simp [ENNReal.toReal_inv]
  ring

/-! ## Point strategies -/

/-- The pure row strategy playing `m` with certainty. -/
def pointRow (m : RowMove) : RowMove → ℝ := fun m' => if m' = m then 1 else 0

/-- The pure column strategy playing `m` with certainty. -/
def pointCol (m : ColMove) : ColMove → ℝ := fun m' => if m' = m then 1 else 0

theorem pointRow_mem (m : RowMove) : pointRow m ∈ stdSimplex ℝ RowMove := by
  refine ⟨fun i => by unfold pointRow; split_ifs <;> norm_num, ?_⟩
  unfold pointRow; rw [rowMove_sum]; cases m <;> simp

theorem pointCol_mem (m : ColMove) : pointCol m ∈ stdSimplex ℝ ColMove := by
  refine ⟨fun j => by unfold pointCol; split_ifs <;> norm_num, ?_⟩
  unfold pointCol; rw [colMove_sum]; cases m <;> simp

/-! ## `stageValue`, computed at every state -/

/-- At a state where every joint action gives the same payoff `c`, the stage value is `c` --
    every strategy pair is trivially a saddle point. -/
theorem cbStageValue_const (v : CBState → ℝ) (s : CBState) (c : ℝ)
    (hc : ∀ (i : RowMove) (j : ColMove), (cbCSG.stageGame s v).A i j = c) :
    cbCSG.stageValue s v = c := by
  change (cbCSG.stageGame s v).value = c
  have hp0 := pointRow_mem .b
  have hq0 := pointCol_mem .c
  have hpay : ∀ (p : RowMove → ℝ) (q : ColMove → ℝ), p ∈ stdSimplex ℝ RowMove →
      q ∈ stdSimplex ℝ ColMove → (cbCSG.stageGame s v).payoff p q = c := by
    intro p q hp hq
    rw [MatrixGame.payoff_eq_sum_mul, rowMove_sum]
    have h1 : ∑ j, (cbCSG.stageGame s v).A .b j * q j = c := by
      have : ∀ j, (cbCSG.stageGame s v).A .b j * q j = c * q j := fun j => by
        rw [hc .b j]
      rw [colMove_sum, this .c, this .d, ← mul_add, ← colMove_sum q, hq.2, mul_one]
    have h2 : ∑ j, (cbCSG.stageGame s v).A .d j * q j = c := by
      have : ∀ j, (cbCSG.stageGame s v).A .d j * q j = c * q j := fun j => by
        rw [hc .d j]
      rw [colMove_sum, this .c, this .d, ← mul_add, ← colMove_sum q, hq.2, mul_one]
    have hsum : p .b + p .d = 1 := by have := hp.2; rwa [rowMove_sum] at this
    rw [h1, h2, ← add_mul, hsum, one_mul]
  have huu := hpay _ _ hp0 hq0
  have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
      (cbCSG.stageGame s v).payoff (pointRow .b) (pointCol .c) ≤
        (cbCSG.stageGame s v).payoff p' (pointCol .c) := fun p' hp' =>
    le_of_eq (huu.trans (hpay p' _ hp' hq0).symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
      (cbCSG.stageGame s v).payoff (pointRow .b) q' ≤
        (cbCSG.stageGame s v).payoff (pointRow .b) (pointCol .c) := fun q' hq' =>
    le_of_eq ((hpay _ q' hp0 hq').trans huu.symm)
  have hval := (cbCSG.stageGame s v).value_unique hp0 hq0 hrow hcol
  rw [← hval]; exact huu

theorem cbStageValue_t1 (v : CBState → ℝ) : cbCSG.stageValue .t1 v = v .t1 := by
  apply cbStageValue_const
  intro i j
  change cbCSG.r .t1 i j + cbCSG.expect .t1 i j v = v .t1
  rw [cbCSG_r, cbExpect_t1]; ring

theorem cbStageValue_t4 (v : CBState → ℝ) : cbCSG.stageValue .t4 v = v .t5 := by
  apply cbStageValue_const
  intro i j
  change cbCSG.r .t4 i j + cbCSG.expect .t4 i j v = v .t5
  rw [cbCSG_r, cbExpect_t4]; ring

theorem cbStageValue_t5 (v : CBState → ℝ) : cbCSG.stageValue .t5 v = v .t4 := by
  apply cbStageValue_const
  intro i j
  change cbCSG.r .t5 i j + cbCSG.expect .t5 i j v = v .t4
  rw [cbCSG_r, cbExpect_t5]; ring

/-- The row player's own certain payoff at `t2`, playing `i` against *any* column action -- `v .t2`
    for `b`, the average `(v .t1 + v .t3) / 2` for `d`. -/
theorem cbT2A (i : RowMove) (j : ColMove) (v : CBState → ℝ) :
    (cbCSG.stageGame .t2 v).A i j = if i = .b then v .t2 else (v .t1 + v .t3) / 2 := by
  change cbCSG.r .t2 i j + cbCSG.expect .t2 i j v = if i = .b then v .t2 else (v .t1 + v .t3) / 2
  rw [cbCSG_r]
  rcases i with _ | _
  · rw [cbExpect_t2b]; simp
  · rw [cbExpect_t2d]; simp

/-- The payoff at `t2`, for an arbitrary row strategy `p` and any column strategy `q` in the
    simplex -- the column player has no influence at all. -/
theorem cbT2_payoff (v : CBState → ℝ) (p : RowMove → ℝ) (q : ColMove → ℝ)
    (hq : q ∈ stdSimplex ℝ ColMove) :
    (cbCSG.stageGame .t2 v).payoff p q = p .b * v .t2 + p .d * ((v .t1 + v .t3) / 2) := by
  rw [MatrixGame.payoff_eq_sum_mul, rowMove_sum]
  have hb : ∑ j, (cbCSG.stageGame .t2 v).A .b j * q j = v .t2 := by
    have : ∀ j, (cbCSG.stageGame .t2 v).A .b j * q j = v .t2 * q j := fun j => by
      rw [cbT2A]; simp
    rw [colMove_sum, this .c, this .d, ← mul_add, ← colMove_sum q, hq.2, mul_one]
  have hd : ∑ j, (cbCSG.stageGame .t2 v).A .d j * q j = (v .t1 + v .t3) / 2 := by
    have : ∀ j, (cbCSG.stageGame .t2 v).A .d j * q j = (v .t1 + v .t3) / 2 * q j := fun j => by
      rw [cbT2A]; simp
    rw [colMove_sum, this .c, this .d, ← mul_add, ← colMove_sum q, hq.2, mul_one]
  rw [hb, hd]

theorem cbStageValue_t2 (v : CBState → ℝ) :
    cbCSG.stageValue .t2 v = min (v .t2) ((v .t1 + v .t3) / 2) := by
  change (cbCSG.stageGame .t2 v).value = min (v .t2) ((v .t1 + v .t3) / 2)
  have hp0 := pointRow_mem .b
  have hp0' := pointRow_mem .d
  have hq0 := pointCol_mem .c
  rcases le_total (v .t2) ((v .t1 + v .t3) / 2) with h | h
  · rw [min_eq_left h]
    have huu : (cbCSG.stageGame .t2 v).payoff (pointRow .b) (pointCol .c) = v .t2 := by
      rw [cbT2_payoff _ _ _ hq0]; simp [pointRow]
    have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
        (cbCSG.stageGame .t2 v).payoff (pointRow .b) (pointCol .c) ≤
          (cbCSG.stageGame .t2 v).payoff p' (pointCol .c) := by
      intro p' hp'
      rw [huu, cbT2_payoff _ _ _ hq0]
      have hsum : p' .b + p' .d = 1 := by have := hp'.2; rwa [rowMove_sum] at this
      have hb_eq : p' .b = 1 - p' .d := by linarith
      have key : p' .d * v .t2 ≤ p' .d * ((v .t1 + v .t3) / 2) :=
        mul_le_mul_of_nonneg_left h (hp'.1 .d)
      rw [hb_eq]
      nlinarith [key]
    have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
        (cbCSG.stageGame .t2 v).payoff (pointRow .b) q' ≤
          (cbCSG.stageGame .t2 v).payoff (pointRow .b) (pointCol .c) := by
      intro q' hq'
      rw [huu, cbT2_payoff _ _ _ hq']; simp [pointRow]
    have hval := (cbCSG.stageGame .t2 v).value_unique hp0 hq0 hrow hcol
    rw [← hval]; exact huu
  · rw [min_eq_right h]
    have huu : (cbCSG.stageGame .t2 v).payoff (pointRow .d) (pointCol .c) =
        (v .t1 + v .t3) / 2 := by
      rw [cbT2_payoff _ _ _ hq0]; simp [pointRow]
    have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
        (cbCSG.stageGame .t2 v).payoff (pointRow .d) (pointCol .c) ≤
          (cbCSG.stageGame .t2 v).payoff p' (pointCol .c) := by
      intro p' hp'
      rw [huu, cbT2_payoff _ _ _ hq0]
      have hsum : p' .b + p' .d = 1 := by have := hp'.2; rwa [rowMove_sum] at this
      have hd_eq : p' .d = 1 - p' .b := by linarith
      have key : p' .b * ((v .t1 + v .t3) / 2) ≤ p' .b * v .t2 :=
        mul_le_mul_of_nonneg_left h (hp'.1 .b)
      rw [hd_eq]
      nlinarith [key]
    have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
        (cbCSG.stageGame .t2 v).payoff (pointRow .d) q' ≤
          (cbCSG.stageGame .t2 v).payoff (pointRow .d) (pointCol .c) := by
      intro q' hq'
      rw [huu, cbT2_payoff _ _ _ hq']; simp [pointRow]
    have hval := (cbCSG.stageGame .t2 v).value_unique hp0' hq0 hrow hcol
    rw [← hval]; exact huu

/-- The column player's own certain payoff at `t3`, playing `j` against *any* row action -- `v .t3`
    for `c`, the average `(v .t2 + v .t4) / 2` for `d`. -/
theorem cbT3A (i : RowMove) (j : ColMove) (v : CBState → ℝ) :
    (cbCSG.stageGame .t3 v).A i j = if j = .c then v .t3 else (v .t2 + v .t4) / 2 := by
  change cbCSG.r .t3 i j + cbCSG.expect .t3 i j v = if j = .c then v .t3 else (v .t2 + v .t4) / 2
  rw [cbCSG_r]
  rcases j with _ | _
  · rw [cbExpect_t3c]; simp
  · rw [cbExpect_t3d]; simp

/-- The payoff at `t3`, for an arbitrary column strategy `q` and any row strategy `p` in the
    simplex -- the row player has no influence at all. -/
theorem cbT3_payoff (v : CBState → ℝ) (p : RowMove → ℝ) (q : ColMove → ℝ)
    (hp : p ∈ stdSimplex ℝ RowMove) :
    (cbCSG.stageGame .t3 v).payoff p q = q .c * v .t3 + q .d * ((v .t2 + v .t4) / 2) := by
  rw [MatrixGame.payoff_eq_sum_mul', colMove_sum]
  have hc : ∑ i, p i * (cbCSG.stageGame .t3 v).A i .c = v .t3 := by
    have : ∀ i, p i * (cbCSG.stageGame .t3 v).A i .c = p i * v .t3 := fun i => by
      rw [cbT3A]; simp
    rw [rowMove_sum, this .b, this .d, ← add_mul, ← rowMove_sum p, hp.2, one_mul]
  have hd : ∑ i, p i * (cbCSG.stageGame .t3 v).A i .d = (v .t2 + v .t4) / 2 := by
    have : ∀ i, p i * (cbCSG.stageGame .t3 v).A i .d = p i * ((v .t2 + v .t4) / 2) := fun i => by
      rw [cbT3A]; simp
    rw [rowMove_sum, this .b, this .d, ← add_mul, ← rowMove_sum p, hp.2, one_mul]
  rw [hc, hd]; ring

theorem cbStageValue_t3 (v : CBState → ℝ) :
    cbCSG.stageValue .t3 v = max (v .t3) ((v .t2 + v .t4) / 2) := by
  change (cbCSG.stageGame .t3 v).value = max (v .t3) ((v .t2 + v .t4) / 2)
  have hp0 := pointRow_mem .b
  have hq0 := pointCol_mem .c
  have hq0' := pointCol_mem .d
  rcases le_total (v .t3) ((v .t2 + v .t4) / 2) with h | h
  · rw [max_eq_right h]
    have huu : (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .d) =
        (v .t2 + v .t4) / 2 := by
      rw [cbT3_payoff _ _ _ hp0]; simp [pointCol]
    have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
        (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .d) ≤
          (cbCSG.stageGame .t3 v).payoff p' (pointCol .d) := by
      intro p' hp'
      rw [huu, cbT3_payoff _ _ _ hp']; simp [pointCol]
    have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
        (cbCSG.stageGame .t3 v).payoff (pointRow .b) q' ≤
          (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .d) := by
      intro q' hq'
      rw [huu, cbT3_payoff _ _ _ hp0]
      have hsum : q' .c + q' .d = 1 := by have := hq'.2; rwa [colMove_sum] at this
      have hd_eq : q' .d = 1 - q' .c := by linarith
      have key : q' .c * v .t3 ≤ q' .c * ((v .t2 + v .t4) / 2) :=
        mul_le_mul_of_nonneg_left h (hq'.1 .c)
      rw [hd_eq]
      nlinarith [key]
    have hval := (cbCSG.stageGame .t3 v).value_unique hp0 hq0' hrow hcol
    rw [← hval]; exact huu
  · rw [max_eq_left h]
    have huu : (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .c) = v .t3 := by
      rw [cbT3_payoff _ _ _ hp0]; simp [pointCol]
    have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
        (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .c) ≤
          (cbCSG.stageGame .t3 v).payoff p' (pointCol .c) := by
      intro p' hp'
      rw [huu, cbT3_payoff _ _ _ hp']; simp [pointCol]
    have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
        (cbCSG.stageGame .t3 v).payoff (pointRow .b) q' ≤
          (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .c) := by
      intro q' hq'
      rw [huu, cbT3_payoff _ _ _ hp0]
      have hsum : q' .c + q' .d = 1 := by have := hq'.2; rwa [colMove_sum] at this
      have hc_eq : q' .c = 1 - q' .d := by linarith
      have key : q' .d * ((v .t2 + v .t4) / 2) ≤ q' .d * v .t3 :=
        mul_le_mul_of_nonneg_left h (hq'.1 .d)
      rw [hc_eq]
      nlinarith [key]
    have hval := (cbCSG.stageGame .t3 v).value_unique hp0 hq0 hrow hcol
    rw [← hval]; exact huu

/-! ## The candidate value, and the inner `gfp`'s closed form -/

/-- The claimed value of `⟨1⟩◇□U` at every state, matching the paper's Example 3 exactly: `1` at
    `t1` (a certain, permanent win), `2/3` at `t2`, `1/3` at `t3`, `0` at `t4`/`t5` (`R_2` in the
    paper's own notation, a certain, permanent loss). -/
noncomputable def cbVStarVal : CBState → ℝ
  | .t1 => 1
  | .t2 => 2 / 3
  | .t3 => 1 / 3
  | .t4 => 0
  | .t5 => 0

theorem cbVStarVal_mem (s : CBState) : cbVStarVal s ∈ Set.Icc (0 : ℝ) 1 := by
  cases s <;> constructor <;> norm_num [cbVStarVal]

/-- `cbVStarVal`, bundled into `CBState → Set.Icc (0 : ℝ) 1`. -/
noncomputable def cbVStar : CBState → Set.Icc (0 : ℝ) 1 := fun s =>
  ⟨cbVStarVal s, cbVStarVal_mem s⟩

/-- The closed form of `(cbCSG.coBuchiInnerOp cbU cbR_zero b).gfp`, for an *arbitrary* outer
    parameter `b` (not just `b = cbVStar`) -- the one general fact both `hfixed` and `hlb` below
    reduce to. `t3`/`t5` (outside `U`) read off `b` directly, with no self-reference; `t4` chains
    off the now-resolved `t5`; `t1`'s own equation (`U`, self-loop) is `g .t1 = g .t1`, entirely
    unconstrained, so the greatest solution puts it at the top of `[0, 1]`; `t2` chains off the
    now-resolved `t1`/`t3`. -/
noncomputable def cbGClosedVal (b : CBState → ℝ) : CBState → ℝ
  | .t1 => 1
  | .t2 => (1 + max (b .t3) ((b .t2 + b .t4) / 2)) / 2
  | .t3 => max (b .t3) ((b .t2 + b .t4) / 2)
  | .t4 => b .t4
  | .t5 => b .t4

theorem cbGClosedVal_mem (b : CBState → Set.Icc (0 : ℝ) 1) (s : CBState) :
    cbGClosedVal (fun s' => (b s' : ℝ)) s ∈ Set.Icc (0 : ℝ) 1 := by
  have h2 := (b .t2).2; have h3 := (b .t3).2; have h4 := (b .t4).2
  simp only [Set.mem_Icc] at h2 h3 h4
  have hmax_nonneg : (0 : ℝ) ≤ max ((b .t3 : ℝ)) (((b .t2 : ℝ) + b .t4) / 2) :=
    le_trans h3.1 (le_max_left _ _)
  have hmax_le_one : max ((b .t3 : ℝ)) (((b .t2 : ℝ) + b .t4) / 2) ≤ 1 :=
    max_le h3.2 (by linarith [h2.2, h4.2])
  cases s with
  | t1 => unfold cbGClosedVal; constructor <;> norm_num
  | t2 =>
      unfold cbGClosedVal
      constructor
      · linarith [hmax_nonneg]
      · linarith [hmax_le_one]
  | t3 => unfold cbGClosedVal; exact ⟨hmax_nonneg, hmax_le_one⟩
  | t4 => unfold cbGClosedVal; exact h4
  | t5 => unfold cbGClosedVal; exact h4

/-- `cbGClosedVal`, bundled into `CBState → Set.Icc (0 : ℝ) 1`. -/
noncomputable def cbGClosed (b : CBState → Set.Icc (0 : ℝ) 1) : CBState → Set.Icc (0 : ℝ) 1 :=
  fun s => ⟨cbGClosedVal (fun s' => (b s' : ℝ)) s, cbGClosedVal_mem b s⟩

theorem cbInnerGfp_eq (b : CBState → Set.Icc (0 : ℝ) 1) :
    (cbCSG.coBuchiInnerOp cbU cbR_zero b).gfp = cbGClosed b := by
  refine OrderHom.gfp_eq_of_certificate _ _ ?_ ?_
  · funext s
    apply Subtype.ext
    change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b (cbGClosed b) s : ℝ) =
      cbGClosedVal (fun s' => (b s' : ℝ)) s
    rw [CSG.coBuchiInnerOpFun_coe]
    cases s with
    | t1 =>
      have hU : cbU .t1 := Or.inl rfl
      rw [if_pos hU, cbStageValue_t1]
      rfl
    | t2 =>
      have hU : cbU .t2 := Or.inr (Or.inl rfl)
      rw [if_pos hU, cbStageValue_t2]
      change min (cbGClosedVal (fun s' => (b s' : ℝ)) .t2)
          ((cbGClosedVal (fun s' => (b s' : ℝ)) .t1 +
            cbGClosedVal (fun s' => (b s' : ℝ)) .t3) / 2) =
        cbGClosedVal (fun s' => (b s' : ℝ)) .t2
      unfold cbGClosedVal
      rw [min_eq_left (le_refl _)]
    | t3 =>
      have hU : ¬ cbU .t3 := by unfold cbU; simp
      rw [if_neg hU, cbStageValue_t3]
      rfl
    | t4 =>
      have hU : cbU .t4 := Or.inr (Or.inr rfl)
      rw [if_pos hU, cbStageValue_t4]
      rfl
    | t5 =>
      have hU : ¬ cbU .t5 := by unfold cbU; simp
      rw [if_neg hU, cbStageValue_t5]
      rfl
  · intro w hw
    have hw3 : (w .t3 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t3 := by
      have hU : ¬ cbU .t3 := by unfold cbU; simp
      calc (w .t3 : ℝ) ≤ (cbCSG.coBuchiInnerOp cbU cbR_zero b w .t3 : ℝ) := hw .t3
        _ = cbCSG.stageValue .t3 (fun s' => (b s' : ℝ)) := by
              change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b w .t3 : ℝ) =
                cbCSG.stageValue .t3 (fun s' => (b s' : ℝ))
              rw [CSG.coBuchiInnerOpFun_coe, if_neg hU]
        _ = cbGClosedVal (fun s' => (b s' : ℝ)) .t3 := by rw [cbStageValue_t3]; rfl
    have hw5 : (w .t5 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t5 := by
      have hU : ¬ cbU .t5 := by unfold cbU; simp
      calc (w .t5 : ℝ) ≤ (cbCSG.coBuchiInnerOp cbU cbR_zero b w .t5 : ℝ) := hw .t5
        _ = cbCSG.stageValue .t5 (fun s' => (b s' : ℝ)) := by
              change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b w .t5 : ℝ) =
                cbCSG.stageValue .t5 (fun s' => (b s' : ℝ))
              rw [CSG.coBuchiInnerOpFun_coe, if_neg hU]
        _ = cbGClosedVal (fun s' => (b s' : ℝ)) .t5 := by rw [cbStageValue_t5]; rfl
    have hw4 : (w .t4 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t4 := by
      have hU : cbU .t4 := Or.inr (Or.inr rfl)
      calc (w .t4 : ℝ) ≤ (cbCSG.coBuchiInnerOp cbU cbR_zero b w .t4 : ℝ) := hw .t4
        _ = cbCSG.stageValue .t4 (fun s' => (w s' : ℝ)) := by
              change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b w .t4 : ℝ) =
                cbCSG.stageValue .t4 (fun s' => (w s' : ℝ))
              rw [CSG.coBuchiInnerOpFun_coe, if_pos hU]
        _ = (w .t5 : ℝ) := by rw [cbStageValue_t4]
        _ ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t5 := hw5
        _ = cbGClosedVal (fun s' => (b s' : ℝ)) .t4 := rfl
    have hw1 : (w .t1 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t1 := by
      change (w .t1 : ℝ) ≤ 1
      exact (w .t1).2.2
    have hw2 : (w .t2 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t2 := by
      have hU : cbU .t2 := Or.inr (Or.inl rfl)
      calc (w .t2 : ℝ) ≤ (cbCSG.coBuchiInnerOp cbU cbR_zero b w .t2 : ℝ) := hw .t2
        _ = min (w .t2 : ℝ) (((w .t1 : ℝ) + (w .t3 : ℝ)) / 2) := by
              change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b w .t2 : ℝ) =
                min (w .t2 : ℝ) (((w .t1 : ℝ) + (w .t3 : ℝ)) / 2)
              rw [CSG.coBuchiInnerOpFun_coe, if_pos hU, cbStageValue_t2]
        _ ≤ ((w .t1 : ℝ) + (w .t3 : ℝ)) / 2 := min_le_right _ _
        _ ≤ (cbGClosedVal (fun s' => (b s' : ℝ)) .t1 +
              cbGClosedVal (fun s' => (b s' : ℝ)) .t3) / 2 := by
              gcongr
        _ = cbGClosedVal (fun s' => (b s' : ℝ)) .t2 := rfl
    intro s
    cases s with
    | t1 => exact hw1
    | t2 => exact hw2
    | t3 => exact hw3
    | t4 => exact hw4
    | t5 => exact hw5

/-! ## The final theorem -/

theorem cbGClosed_cbVStar : cbGClosed cbVStar = cbVStar := by
  funext s
  apply Subtype.ext
  change cbGClosedVal (fun s' => (cbVStar s' : ℝ)) s = cbVStarVal s
  cases s <;> unfold cbGClosedVal cbVStarVal cbVStar cbVStarVal <;> norm_num

/-- **The payoff.** `⟨1⟩◇□U`, computed on Fig. 1, matches the paper's Example 3 exactly: `1` at
    `t1`, `2/3` at `t2`, `1/3` at `t3`, `0` at `t4`/`t5`. -/
theorem cbCSG_coBuchiOp_lfp_eq : (cbCSG.coBuchiOp cbU cbR_zero).lfp = cbVStar := by
  refine OrderHom.lfp_eq_of_certificate _ _ ?_ ?_
  · change (cbCSG.coBuchiInnerOp cbU cbR_zero cbVStar).gfp = cbVStar
    rw [cbInnerGfp_eq, cbGClosed_cbVStar]
  · intro b hb
    have hb' : cbGClosed b ≤ b := by
      rw [← cbInnerGfp_eq]; exact hb
    have h1 : (1 : ℝ) ≤ (b .t1 : ℝ) := hb' .t1
    have h3 : max ((b .t3 : ℝ)) (((b .t2 : ℝ) + (b .t4 : ℝ)) / 2) ≤ (b .t3 : ℝ) := hb' .t3
    have h3' : ((b .t2 : ℝ) + (b .t4 : ℝ)) / 2 ≤ (b .t3 : ℝ) := le_trans (le_max_right _ _) h3
    have h4nn : (0 : ℝ) ≤ (b .t4 : ℝ) := (b .t4).2.1
    have h2 : (1 + max ((b .t3 : ℝ)) (((b .t2 : ℝ) + (b .t4 : ℝ)) / 2)) / 2 ≤ (b .t2 : ℝ) := hb' .t2
    have h2' : (1 + (b .t3 : ℝ)) / 2 ≤ (b .t2 : ℝ) :=
      le_trans (by gcongr; exact le_max_left _ _) h2
    have ht3 : (1 : ℝ) / 3 ≤ (b .t3 : ℝ) := by linarith
    have ht2 : (2 : ℝ) / 3 ≤ (b .t2 : ℝ) := by linarith
    intro s
    cases s with
    | t1 => change cbVStarVal .t1 ≤ (b .t1 : ℝ); rw [cbVStarVal]; linarith
    | t2 => change cbVStarVal .t2 ≤ (b .t2 : ℝ); rw [cbVStarVal]; linarith
    | t3 => change cbVStarVal .t3 ≤ (b .t3 : ℝ); rw [cbVStarVal]; linarith
    | t4 => change cbVStarVal .t4 ≤ (b .t4 : ℝ); rw [cbVStarVal]; exact h4nn
    | t5 => change cbVStarVal .t5 ≤ (b .t5 : ℝ); rw [cbVStarVal]; exact (b .t5).2.1

end Csg
