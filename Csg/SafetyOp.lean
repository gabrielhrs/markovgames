/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.CsgMonotone

/-!
# The safety Bellman operator, bundled as an `OrderHom`

**Status: drafted, not yet run through `lake build`.** The dual of `ReachOp.lean`: `G safe`
("always safe") rather than `F goal` ("eventually goal"). Reachability is a **least** fixed point
because reaching `goal` is a one-off event that a candidate value can be pinned down from below;
safety is a **greatest** fixed point because staying `safe` forever can only be falsified by an
actual violation, so `⊤` (never falsified, i.e. never leaving `safe`) is the right thing to
converge to from above. Per `VERIFICATION-FRAMEWORK.md`'s own taxonomy (Axis A, the temporal-shape
row for "Safety/always"), this is exactly the "short, near-mechanical mirror" anticipated there --
`safetyOpFun` is `reachOpFun` with the two branches' outcomes swapped (`0` on violation instead of
`1` on absorption) and the case condition negated (`¬ safe s` instead of `goal s`), and
`OrderHom.gfp` supplies the same free existence `OrderHom.lfp` did, off Mathlib's own
`le_gfp`/`gfp_le` pinning lemmas (`Mathlib/Order/FixedPoints.lean`, checked directly rather than
guessed -- both are already stated in terms of `f.gfp` itself, with no need to route through
`f.dual` explicitly the way the file's own internal proofs do).

Why the branches are the way they are, stated explicitly since it is easy to get backwards: `safe`
holding at `s` is *not* itself a reason to stop and declare victory (unlike `reachOp`'s `goal`
branch, which absorbs at `1` because reaching `goal` once is enough) -- staying safe is an ongoing
obligation, so a `safe` state still has to keep playing its stage game against the continuation.
Only *leaving* `safe` is absorbing, and it absorbs at `0` (immediate, irrecoverable failure of the
property), the mirror image of `reachOp`'s `goal`-absorbs-at-`1`.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The safety Bellman step, on `S → Set.Icc (0 : ℝ) 1` rather than bare `S → ℝ`: leaving `safe`
    is absorbing at `0` (an irrecoverable violation, regardless of the continuation); any `safe`
    state still plays its stage game against the continuation, packaged back into `[0, 1]` via
    `stageValue_nonneg`/`_le_one` exactly as `reachOpFun` does. Named `safetyOpFun` rather than
    `safetyOp` itself so the monotonicity proof below (`safetyOpFun_mono`) can refer to it by name
    before it's bundled into an `OrderHom`, mirroring `reachOpFun`/`reachOpFun_mono`. -/
noncomputable def safetyOpFun (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) : Set.Icc (0 : ℝ) 1 :=
  if safe s then
    ⟨C.stageValue s (fun s' => (v s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (v s').2.1), C.stageValue_le_one hr (fun s' => (v s').2.2)⟩
  else ⟨0, by norm_num, by norm_num⟩

/-- **The payoff.** `safetyOpFun` is monotone in the continuation `v` -- a `safe` state's value is
    `stageValue_mono` applied to the pointwise hypothesis, unwrapped from `Set.Icc (0 : ℝ) 1`'s
    order back to `≤` on `ℝ` exactly as `reachOpFun_mono` does; a violating state is pinned to the
    same constant `0` regardless of `v`, trivially monotone there. -/
theorem safetyOpFun_mono (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    Monotone (C.safetyOpFun safe hr) := by
  intro v w hvw s
  by_cases h : safe s
  · simp only [safetyOpFun, if_pos h]
    exact C.stageValue_mono fun s' => hvw s'
  · have heq : C.safetyOpFun safe hr v s = C.safetyOpFun safe hr w s := by
      simp only [safetyOpFun, if_neg h]
    exact heq.le

/-- **The payoff.** The safety Bellman operator, bundled as an `OrderHom` on the complete lattice
    `S → Set.Icc (0 : ℝ) 1` -- `safetyOpFun` plus its own monotonicity proof. `(C.safetyOp safe
    hr).gfp` (Knaster-Tarski's greatest-fixed-point half) is a term the moment this definition
    typechecks, the same free existence `reachOp`'s `.lfp` gets. -/
noncomputable def safetyOp (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.safetyOpFun safe hr
  monotone' := C.safetyOpFun_mono safe hr

end CSG
end Csg
