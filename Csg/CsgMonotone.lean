/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Basic

/-!
# Monotonicity and boundedness of `CSG.stageValue`

**Status: done, confirmed by a clean `lake build` -- both the original monotonicity/boundedness
family (`expect_mono` through `stageValue_le_one`) and the later addition (`expect_lipschitz`
through `stageValue_lipschitz`, Lipschitz continuity of `stageValue` in the continuation), the
latter after two genuinely separate fix rounds -- see `PHASE0-NOTES.md`'s "reachability iterate"
section, Stage 2.**
Stage 2 of the infinite-horizon build order (`PHASE0-NOTES.md`): lifts `MatrixGameMonotone.lean`'s
facts about `MatrixGame.value` (monotone in the payoff matrix; sandwiched between constant bounds
on the matrix; Lipschitz in the matrix) up through `CSG.expect` and `CSG.stageGame` to
`CSG.stageValue` itself. Monotonicity and boundedness are exactly the ingredient the reachability
Bellman operator (next artifact) needs to be a genuine `OrderHom` on `S → Set.Icc (0:ℝ) 1`;
Lipschitz continuity is the ingredient Stage 3 needs to show that operator is `ωScottContinuous`,
hence that its `.lfp` equals the limit of the naive iterate sequence
(`OrderHom.lfp_eq_sSup_iterate`).

Boundedness needs one extra hypothesis monotonicity and the Lipschitz bound don't: a reward-free
`CSG` (`C.r ≡ 0` everywhere). This is not a real restriction for reachability -- every reachability
property built on `reachBounded`/the coming reachability operator uses a `CSG` exactly like
`rpsCSG` (`RockPaperScissors.lean`), whose reward is `≡ 0` by construction, since reachability
cares only about which state is reached, never about accumulated reward. Without `C.r ≡ 0`,
`stageValue` could of course leave `[0, 1]` (a stage game paying `100` regardless of the
continuation has value `100`), so the hypothesis is carried explicitly on every boundedness lemma
below rather than assumed as a standing fact about `CSG` itself -- monotonicity and the Lipschitz
bound need no such hypothesis (a reward term that doesn't depend on `v` cancels out of any
*difference* of stage values, whether or not it's zero) and don't get one.

Four layers, `expect` → `stageGame.A` → `stageValue`, each following the same shape
`MatrixGameMonotone.lean`'s own families already used: a monotonicity fact free of any side
condition, two boundedness facts (`nonneg`/`le_one`) that do need one, and a Lipschitz fact
(needs `0 ≤ ε` explicitly, since `S` isn't assumed `Nonempty` here, so `ε`'s sign can't be
recovered from a pointwise bound the way it could if some `s'` were guaranteed to exist) that,
like monotonicity, doesn't.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- `expect` is monotone in the continuation `v`: it's a weighted average with nonnegative
    weights (transition probabilities), so raising `v` pointwise can only raise the average. -/
theorem expect_mono {s : S} {a1 : A1} {a2 : A2} {v w : S → ℝ} (hle : ∀ s', v s' ≤ w s') :
    C.expect s a1 a2 v ≤ C.expect s a1 a2 w := by
  unfold expect
  exact Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hle s') ENNReal.toReal_nonneg

/-- `expect` stays nonnegative whenever the continuation does -- same nonnegative-weights fact,
    the degenerate case of monotonicity against the constant continuation `0`. -/
theorem expect_nonneg {s : S} {a1 : A1} {a2 : A2} {v : S → ℝ} (hv : ∀ s', 0 ≤ v s') :
    0 ≤ C.expect s a1 a2 v := by
  unfold expect
  exact Finset.sum_nonneg fun s' _ => mul_nonneg ENNReal.toReal_nonneg (hv s')

/-- `expect` stays `≤ 1` whenever the continuation does: bound each term by the weight itself
    (since `v s' ≤ 1`), then the weights themselves sum to at most `1` -- a transition kernel is
    a genuine `PMF`, `Finset.univ`'s mass can't exceed the total mass `PMF.tsum_coe` fixes at
    `1`. -/
theorem expect_le_one {s : S} {a1 : A1} {a2 : A2} {v : S → ℝ} (hv : ∀ s', v s' ≤ 1) :
    C.expect s a1 a2 v ≤ 1 := by
  unfold expect
  have hmass : (∑ s' : S, C.K s a1 a2 s').toReal ≤ 1 := by
    have hle : (∑ s' : S, C.K s a1 a2 s') ≤ 1 := by
      calc ∑ s' : S, C.K s a1 a2 s' ≤ ∑' s', C.K s a1 a2 s' := ENNReal.sum_le_tsum Finset.univ
        _ = 1 := (C.K s a1 a2).tsum_coe
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle
  calc ∑ s' : S, (C.K s a1 a2 s').toReal * v s'
      ≤ ∑ s' : S, (C.K s a1 a2 s').toReal * 1 :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hv s') ENNReal.toReal_nonneg
    _ = ∑ s' : S, (C.K s a1 a2 s').toReal := by simp
    _ = (∑ s' : S, C.K s a1 a2 s').toReal :=
        (ENNReal.toReal_sum fun s' _ => (C.K s a1 a2).apply_ne_top s').symm
    _ ≤ 1 := hmass

/-- The stage game's payoff matrix is monotone in the continuation `v`, entrywise -- the reward
    term doesn't move, and `expect` is monotone (`expect_mono`). -/
theorem stageGame_A_mono {s : S} {v w : S → ℝ} (hle : ∀ s', v s' ≤ w s') (a1 : A1) (a2 : A2) :
    (C.stageGame s v).A a1 a2 ≤ (C.stageGame s w).A a1 a2 := by
  change C.r s a1 a2 + C.expect s a1 a2 v ≤ C.r s a1 a2 + C.expect s a1 a2 w
  have h : C.expect s a1 a2 v ≤ C.expect s a1 a2 w := C.expect_mono hle
  linarith

/-- With `C.r ≡ 0`, the stage game's payoff matrix stays nonnegative whenever the continuation
    does -- immediate from `expect_nonneg` once the (zero) reward term is dropped. -/
theorem stageGame_A_nonneg (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', 0 ≤ v s') (a1 : A1) (a2 : A2) : 0 ≤ (C.stageGame s v).A a1 a2 := by
  change 0 ≤ C.r s a1 a2 + C.expect s a1 a2 v
  rw [hr s a1 a2, zero_add]
  exact C.expect_nonneg hv

/-- With `C.r ≡ 0`, the stage game's payoff matrix stays `≤ 1` whenever the continuation does --
    immediate from `expect_le_one` once the (zero) reward term is dropped. -/
theorem stageGame_A_le_one (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', v s' ≤ 1) (a1 : A1) (a2 : A2) : (C.stageGame s v).A a1 a2 ≤ 1 := by
  change C.r s a1 a2 + C.expect s a1 a2 v ≤ 1
  rw [hr s a1 a2, zero_add]
  exact C.expect_le_one hv

/-- **The payoff.** `stageValue` is monotone in the continuation `v`: `MatrixGame.value_mono`
    applied to `stageGame_A_mono`. This is exactly what makes the reachability Bellman operator
    (next artifact) an `OrderHom`, not just a function. -/
theorem stageValue_mono {s : S} {v w : S → ℝ} (hle : ∀ s', v s' ≤ w s') :
    C.stageValue s v ≤ C.stageValue s w := by
  change (C.stageGame s v).value ≤ (C.stageGame s w).value
  exact MatrixGame.value_mono fun a1 a2 => C.stageGame_A_mono hle a1 a2

/-- With `C.r ≡ 0`, `stageValue` stays nonnegative whenever the continuation does --
    `MatrixGame.le_value_of_forall_le` applied to `stageGame_A_nonneg`. -/
theorem stageValue_nonneg (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', 0 ≤ v s') : 0 ≤ C.stageValue s v := by
  change (0:ℝ) ≤ (C.stageGame s v).value
  exact (C.stageGame s v).le_value_of_forall_le fun a1 a2 => C.stageGame_A_nonneg hr hv a1 a2

/-- With `C.r ≡ 0`, `stageValue` stays `≤ 1` whenever the continuation does --
    `MatrixGame.value_le_of_forall_le` applied to `stageGame_A_le_one`. Together with
    `stageValue_nonneg`, this is exactly the boundedness half the reachability Bellman operator
    needs to land in `S → Set.Icc (0:ℝ) 1`, not just `S → ℝ`. -/
theorem stageValue_le_one (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', v s' ≤ 1) : C.stageValue s v ≤ 1 := by
  change (C.stageGame s v).value ≤ (1:ℝ)
  exact (C.stageGame s v).value_le_of_forall_le fun a1 a2 => C.stageGame_A_le_one hr hv a1 a2

/-- One-directional half of `expect_lipschitz`, in the `value_le_add_of_forall_le`/
    `payoff_add_const` style already used in `MatrixGameMonotone.lean`: shifting every state's
    continuation value up by at most `ε` shifts the expectation up by at most `ε`, since the
    transition weights are nonnegative and sum to at most `1` (`expect_le_one`'s own `hmass`
    argument, reused verbatim). Needs `0 ≤ ε` explicitly for the final `mul_le_mul_of_nonneg_right`
    step: without it, `(Σ weights) * ε ≤ 1 * ε` could point the wrong way. -/
theorem expect_le_add_of_forall_le {s : S} {a1 : A1} {a2 : A2} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', v s' ≤ w s' + ε) : C.expect s a1 a2 v ≤ C.expect s a1 a2 w + ε := by
  unfold expect
  have hmass : (∑ s' : S, (C.K s a1 a2 s').toReal) ≤ 1 := by
    have hle : (∑ s' : S, C.K s a1 a2 s') ≤ 1 := by
      calc ∑ s' : S, C.K s a1 a2 s' ≤ ∑' s', C.K s a1 a2 s' := ENNReal.sum_le_tsum Finset.univ
        _ = 1 := (C.K s a1 a2).tsum_coe
    have h1 : (∑ s' : S, C.K s a1 a2 s').toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle
    rwa [ENNReal.toReal_sum fun s' _ => (C.K s a1 a2).apply_ne_top s'] at h1
  calc ∑ s' : S, (C.K s a1 a2 s').toReal * v s'
      ≤ ∑ s' : S, (C.K s a1 a2 s').toReal * (w s' + ε) :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h s') ENNReal.toReal_nonneg
    _ = ∑ s' : S, ((C.K s a1 a2 s').toReal * w s' + (C.K s a1 a2 s').toReal * ε) :=
        Finset.sum_congr rfl fun s' _ => by ring
    _ = (∑ s' : S, (C.K s a1 a2 s').toReal * w s') + ∑ s' : S, (C.K s a1 a2 s').toReal * ε :=
        Finset.sum_add_distrib
    _ = (∑ s' : S, (C.K s a1 a2 s').toReal * w s') + (∑ s' : S, (C.K s a1 a2 s').toReal) * ε := by
        rw [← Finset.sum_mul]
    _ ≤ (∑ s' : S, (C.K s a1 a2 s').toReal * w s') + 1 * ε := by
        linarith [mul_le_mul_of_nonneg_right hmass hε]
    _ = (∑ s' : S, (C.K s a1 a2 s').toReal * w s') + ε := by rw [one_mul]

/-- **Stage 2's key lemma.** `expect` moves by at most `ε` when the continuation does, in either
    direction -- the one-step version of the Lipschitz bound this project already has for
    `MatrixGame.value` (`MatrixGameMonotone.lean`'s `abs_value_sub_le`), needed to lift that bound
    up through `stageGame`/`stageValue` in turn. Same `abs_le`-splitting shape as
    `abs_value_sub_le` itself. -/
theorem expect_lipschitz {s : S} {a1 : A1} {a2 : A2} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) : |C.expect s a1 a2 v - C.expect s a1 a2 w| ≤ ε := by
  have hub : ∀ s', v s' ≤ w s' + ε := fun s' => by linarith [(abs_le.mp (h s')).2]
  have hlb : ∀ s', w s' ≤ v s' + ε := fun s' => by linarith [(abs_le.mp (h s')).1]
  have h1 : C.expect s a1 a2 v ≤ C.expect s a1 a2 w + ε := C.expect_le_add_of_forall_le hε hub
  have h2 : C.expect s a1 a2 w ≤ C.expect s a1 a2 v + ε := C.expect_le_add_of_forall_le hε hlb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The stage game's payoff matrix moves by at most `ε` when the continuation does, entrywise --
    the reward term doesn't depend on `v` at all, so it cancels exactly out of the difference,
    leaving `expect_lipschitz`. -/
theorem stageGame_A_lipschitz {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) (a1 : A1) (a2 : A2) :
    |(C.stageGame s v).A a1 a2 - (C.stageGame s w).A a1 a2| ≤ ε := by
  have heq : (C.stageGame s v).A a1 a2 - (C.stageGame s w).A a1 a2 =
      C.expect s a1 a2 v - C.expect s a1 a2 w := by
    change (C.r s a1 a2 + C.expect s a1 a2 v) - (C.r s a1 a2 + C.expect s a1 a2 w) = _
    ring
  rw [heq]
  exact C.expect_lipschitz hε h

/-- **The payoff.** `stageValue` moves by at most `ε` when the continuation does, in the sup-norm
    sense (`h`): `MatrixGame.abs_value_sub_le` applied to `stageGame_A_lipschitz`. This is exactly
    the ingredient Stage 3 needs for `ωScottContinuous`: a monotone chain converging pointwise
    forces its `stageValue` images to converge to the same limit's `stageValue`, since Lipschitz
    continuity (in particular, plain continuity) commutes with limits of monotone real sequences
    the same way it does with any convergent sequence. -/
theorem stageValue_lipschitz {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) : |C.stageValue s v - C.stageValue s w| ≤ ε := by
  change |(C.stageGame s v).value - (C.stageGame s w).value| ≤ ε
  exact MatrixGame.abs_value_sub_le fun a1 a2 => C.stageGame_A_lipschitz hε h a1 a2

end CSG
end Csg
