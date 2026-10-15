/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Shapley
import Csg.ReachOp
import Csg.IntervalCertificate

/-!
# Certified lower bounds on a reachability value, from a computed iterate

**Status: confirmed by a clean `lake build`.**

The undiscounted counterpart of `Comp/Iterate.lean`. There is no contraction here and so no `ε`,
but there is something cheaper that is often all one wants: every iterate from `0` is a *sound*
lower bound on the reachability value, and this file lets a rationally-computed iterate carry that
guarantee.

**Why the lower bound is nearly free, and the upper one is not.** For a least fixed point the two
sides are not symmetric, which is easy to get backwards.
`Csg/IntervalCertificate.lean`'s `OrderHom.lfp_mem_Icc_of_certificate` asks `f hi ≤ hi` for the
upper candidate -- a single inequality, decidable per state -- but `∀ b, f b ≤ b → lo ≤ b` for the
lower one, a lower bound over *every* pre-fixed point. That second hypothesis is the
hand-written minimality argument (`Csg/RockPaperScissorsLfp.lean`'s `rpsVStar_le_of_prefixed`), and
it is not a checkable property of a vector.

So a lower bound does not come from certifying the vector. It comes from the vector *being an
iterate*: `a ≤ lfp` implies `f a ≤ f lfp = lfp` by monotonicity and `OrderHom.map_lfp`, so one step
preserves the property. That is `OrderHom.le_lfp_of_step` below, three lines, and chaining it from
`⊥` gives a lower bound after any number of steps. (`Csg/ReachConverge.lean`'s
`reachOp_lfp_eq_sSup_iterate` gives the same conclusion for `f^[n] ⊥` via Kleene; the one-step form
is used here because it composes with the per-step certificates without an induction on `n`.)

**Where positivity enters, and where it does not.** Soundness of the bound needs no positivity at
all -- only monotonicity and a starting point below the fixed point. What positivity decides is
whether `0` *is* such a starting point. For probabilistic reachability it is the bottom of
`S → Set.Icc (0:ℝ) 1` outright, so the base case is `bot_le`. For an expected-reward objective it
would need the rewards to be nonnegative, since otherwise `0` can already exceed the value; that is
the one place the hypothesis earns its keep, and it is why this file is about reachability rather
than rewards.

**What a run looks like.** `#eval` the search once per state to get the next iterate, as in
`Comp/TwoStateQ.lean`; certify each state's stage game with a `ValueCert`; feed the collected
per-state equalities to `le_lfp_of_step`; repeat. Each step's output is a vector with a proof that
it is `≤` the true reachability value. No contraction, no `ε`, no appeal to the solver, and -- the
point your own practice makes -- cheap, because the expensive half of an interval was never needed.

**The subtype friction, recorded as a standing rule.** `reachOp` acts on `S → Set.Icc (0:ℝ) 1`, not
on `S → ℝ` as `shapley` does, so a rational vector has to be packaged with its two bounds
(`castIcc`) and every pointwise equality has to be lifted through `Subtype.ext`. That is the only
structural difference from `Comp/Shapley.lean`, and it is confined to `castIcc` and
`reachOp_castIcc_eq`; everything above them is stated about the real *coercion* and so never
mentions the subtype.

**Upper bounds are here too, and equally free.** `OrderHom.lfp_le_of_step` is the mirror image,
and its starting point costs nothing (`le_top`), so iterating downward from `⊤` gives sound upper
bounds with no certificate and no end-component analysis. A run therefore yields the whole interval
`[f^[n] ⊥, f^[n] ⊤]`.

What is *not* here is any guarantee that the interval shrinks. The upper iteration stalls above the
value wherever the players can keep the play off the target forever -- end-component territory,
whose game-theoretic analogue is `Csg/QualitativeAlmostSure.lean`'s `AFG` on the target's
complement. That analysis is what would make the gap close; it is not needed for either bound to be
valid. **Also not here:** rewards, where the sign of `r` decides which end `0` sits at, and the
discounted case, whose two-sided bound is already `Csg/DiscountedValueIteration.lean`'s
`shapley_apriori_bound` and whose constant brackets `r_min/(1-l)`, `r_max/(1-l)` are immediate.
-/

/-- One step preserves being below the least fixed point: a monotone map sends anything `≤ f.lfp`
    to something `≤ f.lfp`, because `f.lfp` is a fixed point (`OrderHom.map_lfp`). Stated with the
    step as an equation `b = f a` so that it composes directly with a certified computation, which
    produces `b` and a proof that it is what `f` returned.

    Declared at top level in the `OrderHom` namespace, following
    `Csg/IntervalCertificate.lean`'s own lattice-level lemmas. -/
theorem OrderHom.le_lfp_of_step {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : a ≤ f.lfp) (hb : b = f a) : b ≤ f.lfp := by
  subst hb
  calc f a ≤ f f.lfp := f.monotone ha
    _ = f.lfp := f.map_lfp

/-- The dual: one step preserves being *above* the least fixed point, so iterating downward from
    anything above it gives sound upper bounds. For reachability the starting point costs nothing --
    `f.lfp ≤ ⊤` is `le_top` -- and with nonpositive rewards the constant `0` serves instead, being
    pre-fixed there.

    Soundness of an upper bound therefore needs no end-component analysis. What such analysis buys
    is *convergence*: iterating from `⊤` stalls above the value wherever the players can keep the
    play off the target forever, so the bound stays valid but stops improving. -/
theorem OrderHom.lfp_le_of_step {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : f.lfp ≤ a) (hb : b = f a) : f.lfp ≤ b := by
  subst hb
  calc f.lfp = f f.lfp := f.map_lfp.symm
    _ ≤ f a := f.monotone ha

namespace Comp

open Csg

namespace CsgQ

/-! ## Packaging a rational vector into the operator's carrier

In their own section with only `{S : Type*}`: none of these needs finiteness or any instance on the
action types, and declaring them under the wider block below would carry unused arguments that the
`unusedSectionVars` and `unusedFintypeInType` linters correctly flag. -/

section Cast

variable {S : Type*}

/-- A rational vector with both bounds, as an element of `reachOp`'s carrier. The two side
    conditions are decidable over `ℚ`, so at a concrete instance they are `norm_num`. -/
noncomputable def castIcc (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) :
    S → Set.Icc (0 : ℝ) 1 :=
  fun s => ⟨((v s : ℚ) : ℝ), by exact_mod_cast h0 s, by exact_mod_cast h1 s⟩

@[simp]
theorem castIcc_coe (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (s : S) :
    ((castIcc v h0 h1 s : ℝ)) = ((v s : ℚ) : ℝ) := rfl

/-- The all-zero rational vector packages to the bottom of the carrier, which is the base case of
    any chain of steps. -/
theorem castIcc_zero (h0 : ∀ s, (0 : ℚ) ≤ (fun _ : S => (0 : ℚ)) s)
    (h1 : ∀ s, (fun _ : S => (0 : ℚ)) s ≤ 1) :
    castIcc (fun _ : S => (0 : ℚ)) h0 h1 = ⊥ := by
  funext s
  exact Subtype.ext (by simp)

/-- The all-one rational vector packages to the top of the carrier, the starting point for a
    downward chain. -/
theorem castIcc_one (h0 : ∀ s, (0 : ℚ) ≤ (fun _ : S => (1 : ℚ)) s)
    (h1 : ∀ s, (fun _ : S => (1 : ℚ)) s ≤ 1) :
    castIcc (fun _ : S => (1 : ℚ)) h0 h1 = ⊤ := by
  funext s
  exact Subtype.ext (by simp)

end Cast

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

/-! ## The reachability stage game, rationally -/

/-- The stage game a non-goal state plays for reachability: no reward, so the payoff is exactly the
    rational one-step expectation. The reward-free convention is the same one every existing
    reachability instance uses. -/
def reachGameQ (G : CsgQ S A1 A2) (s : S) (v : S → ℚ) : MatrixGameQ A1 A2 where
  A a1 a2 := G.expectQ s a1 a2 v

/-- A reward-free rational game casts to a reward-free real one: the hypothesis `reachOp` wants. -/
theorem toCSG_r_zero (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) :
    ∀ s a1 a2, (G.toCSG h).r s a1 a2 = 0 := by
  intro s a1 a2
  change ((G.r s a1 a2 : ℚ) : ℝ) = 0
  rw [hr0 s a1 a2, Rat.cast_zero]

/-- The two stage games agree entrywise: the reward term vanishes by `hr0`, and the expectation is
    `CsgQ.expect_toCSG`. -/
theorem reachGameQ_A_cast (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (s : S) (v : S → ℚ)
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (a1 : A1) (a2 : A2) :
    ((G.toCSG h).stageGame s (fun s' => ((castIcc v h0 h1 s' : ℝ)))).A a1 a2
      = ((G.reachGameQ s v).toMatrixGame).A a1 a2 := by
  change (G.toCSG h).r s a1 a2
      + (G.toCSG h).expect s a1 a2 (fun s' => ((v s' : ℚ) : ℝ))
    = ((G.expectQ s a1 a2 v : ℚ) : ℝ)
  rw [toCSG_r_zero G h hr0 s a1 a2, CsgQ.expect_toCSG, zero_add]

/-- Hence the two have the same value. Entrywise equality into
    `MatrixGame.abs_value_sub_le` at `ε = 0`, exactly as in `Comp/Shapley.lean` and for the same
    reason: `MatrixGame` has no `@[ext]` lemma, so an already-proved Lipschitz bound is the robust
    way to get an equality. -/
theorem reachGameQ_stageValue (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (s : S) (v : S → ℚ)
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) :
    (G.toCSG h).stageValue s (fun s' => ((castIcc v h0 h1 s' : ℝ)))
      = (G.reachGameQ s v).toMatrixGame.value := by
  change ((G.toCSG h).stageGame s (fun s' => ((castIcc v h0 h1 s' : ℝ)))).value = _
  have hb : |((G.toCSG h).stageGame s (fun s' => ((castIcc v h0 h1 s' : ℝ)))).value
      - (G.reachGameQ s v).toMatrixGame.value| ≤ 0 :=
    MatrixGame.abs_value_sub_le (ε := 0) fun a1 a2 => by
      rw [reachGameQ_A_cast G h hr0 s v h0 h1 a1 a2]
      simp
  have hz := abs_nonpos_iff.mp hb
  linarith

/-! ## One certified step -/

/-- `reachOp`'s coercion as a subtype-free, `ℝ`-valued `if`-`then`-`else`. Without this, `change`
    cannot reach past the `Set.Icc` packaging: the `ite` sits on an abstract `DecidablePred goal`
    instance and so will not reduce definitionally, whatever the ambient hypothesis says about
    `goal s`. The fix is `Csg/CoBuchiOp.lean`'s own `coBuchiInnerOpFun_coe`, verbatim --
    `unfold`, then `split_ifs <;> rfl` -- and with it in hand `ite_eq_left`/`ite_eq_right` work as
    ordinary rewrite lemmas, which is how `Csg/CoalitionComplementReach.lean` handles the same
    branch.

    This is a fact about `CSG`, not about `CsgQ`, and would sit more naturally beside the operator
    in `Csg/ReachOp.lean`; it is stated here to keep the change confined to one file. -/
theorem reachOp_coe (C : CSG S A1 A2) (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (((C.reachOp goal hr) v s : ℝ))
      = if goal s then 1 else C.stageValue s (fun s' => ((v s' : ℝ))) := by
  change ((C.reachOpFun goal hr v s : ℝ))
    = if goal s then 1 else C.stageValue s (fun s' => ((v s' : ℝ)))
  unfold CSG.reachOpFun
  split_ifs <;> rfl

/-- At a non-goal state, a value certificate on the rational stage game pins the operator's value
    there. Stated about the real coercion, so the subtype never appears. -/
theorem reachOp_coe_of_valueCert (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) {s : S} {t : ℚ}
    {p : A1 → ℚ} {q : A2 → ℚ} (hs : ¬ goal s)
    (hc : (G.reachGameQ s v).ValueCert t p q) :
    ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((t : ℚ) : ℝ) := by
  rw [reachOp_coe, ite_eq_right hs, reachGameQ_stageValue G h hr0 s v h0 h1]
  exact MatrixGameQ.value_eq_of_valueCert hc

/-- At a goal state the operator is pinned to `1`, with no game to solve. -/
theorem reachOp_coe_of_goal (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) {s : S} (hs : goal s) :
    ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ)) = 1 := by
  rw [reachOp_coe, ite_eq_left hs]

/-- Collected per-state equalities lift to an equality of carrier vectors. This is the only place
    `Subtype.ext` is needed, and it is why everything above is stated about the coercion. -/
theorem reachOp_castIcc_eq (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v w : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1)
    (k0 : ∀ s, 0 ≤ w s) (k1 : ∀ s, w s ≤ 1)
    (hstep : ∀ s, ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((w s : ℚ) : ℝ)) :
    ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) = castIcc w k0 k1 := by
  funext s
  exact Subtype.ext (hstep s)

/-- **The payoff.** A certified step from a vector already known to be a lower bound yields another
    lower bound on the reachability value. Chaining this from `⊥` -- whose base case is `bot_le`
    together with `castIcc_zero` -- gives a sound lower bound after any number of computed steps,
    with no contraction and no `ε`. -/
theorem le_lfp_of_step (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v w : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1)
    (k0 : ∀ s, 0 ≤ w s) (k1 : ∀ s, w s ≤ 1)
    (hv : castIcc v h0 h1 ≤ ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp)
    (hstep : ∀ s, ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((w s : ℚ) : ℝ)) :
    castIcc w k0 k1 ≤ ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp :=
  OrderHom.le_lfp_of_step _ hv
    (reachOp_castIcc_eq G h hr0 goal v w h0 h1 k0 k1 hstep).symm

/-- **The dual payoff.** A certified step from a vector already known to be an upper bound yields
    another upper bound. Chaining from `⊤` -- base case `le_top` with `castIcc_one` -- gives a sound
    upper bound after any number of computed steps, so a run produces the whole interval
    `[lower, upper]` rather than one side of it.

    The interval is sound at every step but not guaranteed to shrink: see `OrderHom.lfp_le_of_step`
    on why that is a convergence question rather than a soundness one. -/
theorem lfp_le_of_step (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v w : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1)
    (k0 : ∀ s, 0 ≤ w s) (k1 : ∀ s, w s ≤ 1)
    (hv : ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp ≤ castIcc v h0 h1)
    (hstep : ∀ s, ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((w s : ℚ) : ℝ)) :
    ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp ≤ castIcc w k0 k1 :=
  OrderHom.lfp_le_of_step _ hv
    (reachOp_castIcc_eq G h hr0 goal v w h0 h1 k0 k1 hstep).symm

end CsgQ

end Comp
