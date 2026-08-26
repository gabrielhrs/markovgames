/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.CsgMonotone

/-!
# The reachability Bellman operator, bundled as an `OrderHom`

**Status: drafted, not yet run through `lake build`.** Stage 3 of the infinite-horizon build
order: the per-state reachability step -- `reachBounded`'s recursive case
(`BoundedReachability.lean`), goal states pinned to `1`, everywhere else the stage-game value
against the continuation -- bundled as a genuine `OrderHom (S → Set.Icc (0 : ℝ) 1)
(S → Set.Icc (0 : ℝ) 1)` rather than a bare function on `S → ℝ`. `CsgMonotone.lean` supplied exactly
what this needs: `stageValue_mono` for the monotonicity proof `OrderHom` bundling demands,
`stageValue_nonneg`/`_le_one` (both needing the same `C.r ≡ 0` hypothesis carried through here) to
show the operator actually lands back in `[0, 1]`, not just `ℝ`.

Why bundle at all, rather than keep working with plain functions the way `reachBounded` does:
`S → Set.Icc (0 : ℝ) 1` is a genuine `CompleteLattice` (confirmed against the cached Mathlib source
in `MatrixGameMonotone.lean`'s own docstring -- `Set.Icc.completeLattice` plus
`Pi.instCompleteLattice`), so Mathlib's own Knaster-Tarski (`OrderHom.lfp`, in
`Mathlib/Order/FixedPoints.lean`) applies to any bundled monotone self-map of it *for free*: no
extra existence proof to write, `(reachOp goal hr).lfp` is already a term the moment `reachOp`
below typechecks. That's the entire payoff of doing the monotonicity/boundedness work in
`CsgMonotone.lean` first -- an `OrderHom` is a structure with a monotonicity proof attached, and
Mathlib's fixed-point machinery is stated for exactly that bundle, not for a bare function plus a
side lemma.

This file stops at the operator and its monotonicity -- it does not yet state or prove anything
connecting `(reachOp goal hr).lfp` to `reachBounded`'s own sequence (e.g. via
`OrderHom.lfp_eq_sSup_iterate`), or compute it for the concrete rock-paper-scissors instance. That
connection is the next artifact, once this one is confirmed.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The reachability Bellman step, on `S → Set.Icc (0 : ℝ) 1` rather than bare `S → ℝ`: a `goal`
    state is worth `1` regardless of the continuation (absorption, same as `reachBounded`'s own
    `if goal s then 1 else ...`); any other state plays its stage game against the continuation,
    packaged back into `[0, 1]` via `stageValue_nonneg`/`_le_one` (needing `C.r ≡ 0`, see
    `CsgMonotone.lean`). Named `reachOpFun` rather than `reachOp` itself so the monotonicity proof
    below (`reachOpFun_mono`) can refer to it by name before it's bundled into an `OrderHom`. -/
noncomputable def reachOpFun (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) : Set.Icc (0 : ℝ) 1 :=
  if goal s then ⟨1, by norm_num, by norm_num⟩
  else ⟨C.stageValue s (fun s' => (v s' : ℝ)),
    C.stageValue_nonneg hr (fun s' => (v s').2.1), C.stageValue_le_one hr (fun s' => (v s').2.2)⟩

/-- **The payoff.** `reachOpFun` is monotone in the continuation `v` -- `goal` states are pinned
    to the same constant `1` regardless of `v` (so trivially monotone there), and every other
    state's value is `stageValue_mono` applied to the pointwise hypothesis, unwrapped from
    `Set.Icc (0 : ℝ) 1`'s order back to `≤` on `ℝ` by definitional unfolding (`exact`'s defeq
    check, not a named simp lemma -- this Lean toolchain has picked up a fresh core
    `Subtype.instLE` alongside Mathlib's own `Preorder`-derived one, so a lemma like
    `Subtype.mk_le_mk` compiled against one may not syntactically match a goal stated against the
    other, even though both compute to exactly the same underlying comparison and `exact`'s
    defeq check sees through either). -/
theorem reachOpFun_mono (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    Monotone (C.reachOpFun goal hr) := by
  intro v w hvw s
  by_cases h : goal s
  · have heq : C.reachOpFun goal hr v s = C.reachOpFun goal hr w s := by
      simp only [reachOpFun, if_pos h]
    exact heq.le
  · simp only [reachOpFun, if_neg h]
    exact C.stageValue_mono fun s' => hvw s'

/-- **The payoff.** The reachability Bellman operator, bundled as an `OrderHom` on the complete
    lattice `S → Set.Icc (0 : ℝ) 1` -- `reachOpFun` plus its own monotonicity proof. Existence of a
    least (and greatest) fixed point is now free, no further work needed: `(C.reachOp goal hr).lfp`
    (Knaster-Tarski, `Mathlib/Order/FixedPoints.lean`) already typechecks the moment this
    definition does, since `OrderHom.lfp` is defined for *any* monotone self-map of *any*
    `CompleteLattice`. Relating it to `reachBounded`'s own sequence, and computing it for the
    concrete rock-paper-scissors instance, is the next artifact. -/
noncomputable def reachOp (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.reachOpFun goal hr
  monotone' := C.reachOpFun_mono goal hr

end CSG
end Csg
