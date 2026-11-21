/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.CsgMonotone

/-!
# The reachability Bellman operator, bundled as an `OrderHom`

**Status: confirmed by a clean `lake build`.** The per-state reachability step -- `reachBounded`'s
recursive case (`BoundedReachability.lean`), goal states pinned to `1`, everywhere else the
stage-game value against the continuation -- bundled as an `OrderHom (S → Set.Icc (0 : ℝ) 1)
(S → Set.Icc (0 : ℝ) 1)` rather than a bare function on `S → ℝ`. `CsgMonotone.lean` supplies what
this needs: `stageValue_mono` for the monotonicity proof `OrderHom` bundling demands, and
`stageValue_nonneg`/`_le_one` (both needing the same `C.r ≡ 0` hypothesis carried through here) to
show the operator lands back in `[0, 1]`, not just `ℝ`.

Why bundle at all, rather than work with plain functions the way `reachBounded` does:
`S → Set.Icc (0 : ℝ) 1` is a `CompleteLattice` (`Set.Icc.completeLattice` plus
`Pi.instCompleteLattice`), so Mathlib's Knaster-Tarski (`OrderHom.lfp`, in
`Mathlib/Order/FixedPoints.lean`) applies to any bundled monotone self-map of it *for free*: no
extra existence proof to write, `(reachOp goal hr).lfp` is a term the moment `reachOp` below
typechecks. An `OrderHom` is a structure with a monotonicity proof attached, and Mathlib's
fixed-point machinery is stated for exactly that bundle, not for a bare function plus a side
lemma.

This file stops at the operator and its monotonicity -- it does not state or prove anything
connecting `(reachOp goal hr).lfp` to `reachBounded`'s own sequence (e.g. via
`OrderHom.lfp_eq_sSup_iterate`), or compute it for the concrete rock-paper-scissors instance.
`ReachConverge.lean` and `RockPaperScissorsLfp.lean` do those.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The reachability Bellman step, on `S → Set.Icc (0 : ℝ) 1` rather than bare `S → ℝ`: a `goal`
    state is worth `1` regardless of the continuation (absorption, same as `reachBounded`'s own
    `if goal s then 1 else ...`); any other state plays its stage game against the continuation,
    packaged back into `[0, 1]` by `stageValueIcc` (needing `C.r ≡ 0`, see
    `CsgMonotone.lean`). Named `reachOpFun` rather than `reachOp` itself so the monotonicity proof
    below (`reachOpFun_mono`) can refer to it by name before it's bundled into an `OrderHom`. -/
noncomputable def reachOpFun (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) : Set.Icc (0 : ℝ) 1 :=
  if goal s then ⟨1, by norm_num, by norm_num⟩
  else C.stageValueIcc hr v s

/-- **The payoff.** `reachOpFun` is monotone in the continuation `v` -- `goal` states are pinned
    to the same constant `1` regardless of `v` (so trivially monotone there), and every other
    state's value is `stageValueIcc_mono`. -/
theorem reachOpFun_mono (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    Monotone (C.reachOpFun goal hr) := by
  intro v w hvw s
  by_cases h : goal s
  · have heq : C.reachOpFun goal hr v s = C.reachOpFun goal hr w s := by
      simp only [reachOpFun, ite_eq_left h]
    exact heq.le
  · simp only [reachOpFun, ite_eq_right h]
    exact C.stageValueIcc_mono hr hvw s

/-- **The payoff.** The reachability Bellman operator, bundled as an `OrderHom` on the complete
    lattice `S → Set.Icc (0 : ℝ) 1` -- `reachOpFun` plus its own monotonicity proof. Existence of a
    least (and greatest) fixed point is now free, no further work needed: `(C.reachOp goal hr).lfp`
    (Knaster-Tarski, `Mathlib/Order/FixedPoints.lean`) already typechecks the moment this
    definition does, since `OrderHom.lfp` is defined for *any* monotone self-map of *any*
    `CompleteLattice`. `ReachConverge.lean` relates it to the iterate sequence, and
    `RockPaperScissorsLfp.lean` computes it for the concrete rock-paper-scissors instance. -/
noncomputable def reachOp (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.reachOpFun goal hr
  monotone' := C.reachOpFun_mono goal hr

end CSG
end Csg
