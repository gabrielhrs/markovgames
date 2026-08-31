/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.ReachOp

/-!
# A reusable reachability-value certificate

**Status: done, confirmed by a clean `lake build` on the first attempt (one cosmetic
unused-variable warning at the call site, fixed by naming an unused lambda binder `_`).** Pulls
the assembly step of
`RockPaperScissorsLfp.lean`'s headline theorem -- `le_antisymm` applied to Knaster-Tarski's two
pinning lemmas, `OrderHom.lfp_le_fixed`/`OrderHom.le_lfp` -- out of that one instance and into a
combinator any `CSG`/goal/candidate can call directly. This is the first concrete artifact
proposed in `VERIFICATION-FRAMEWORK.md`'s routing taxonomy: the "exact closed form" branch of that
document's candidate-form axis, generalised from its one worked example.

What this combinator automates is exactly the assembly, and nothing more: given a candidate `v`
that the caller has *already* shown to be an exact fixed point of `reachOp`, and to lower-bound
every pre-fixed point, it hands back the fact that `v` is the least fixed point on the nose. It
does not, and cannot, discharge those two hypotheses itself -- that is the actual mathematical
content of any correctness proof for a specific model, and stays exactly as hard as that model
makes it (a handful of case splits closed by `linarith` for something rock-paper-scissors-sized
and symmetric; realistically an external numeric solver plus a widened interval version of this
same combinator for anything larger, per `VERIFICATION-FRAMEWORK.md`'s own scope note).

**Update: the assembly step itself has nothing to do with `CSG`s.** `le_antisymm` applied to
`OrderHom.lfp_le_fixed`/`OrderHom.le_lfp` never touches `reachOp`, `stageValue`, or any `CSG` field
-- it is a fact about an arbitrary monotone self-map `f` of an arbitrary `CompleteLattice`.
`OrderHom.lfp_eq_of_certificate` below states it at that level of generality; `CSG`'s own
`reachOp_lfp_eq_of_certificate` is now a one-line wrapper specialising `f` to `C.reachOp goal hr`.
This is a pure refactor -- the statement `CSG.reachOp_lfp_eq_of_certificate` proves is unchanged,
and `RockPaperScissorsLfp.lean`'s call site needs no edit. -/

/-- **The payoff, fully generalised.** A candidate `v` in any `CompleteLattice` that is an exact
    fixed point of a monotone self-map `f`, and that lower-bounds every pre-fixed point of `f`,
    *is* `f`'s least fixed point -- Knaster-Tarski's two pinning lemmas assembled via
    `le_antisymm`, with no reference to `CSG`s, `reachOp`, or `[0, 1]`-valued functions anywhere in
    the statement or proof. Checked against the cached Mathlib source
    (`Mathlib/Order/FixedPoints.lean`) for a naming collision before adding this: none found. -/
theorem OrderHom.lfp_eq_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α) (v : α)
    (hfixed : f v = v) (hlb : ∀ b, f b ≤ b → v ≤ b) : f.lfp = v :=
  le_antisymm (f.lfp_le_fixed hfixed) (f.le_lfp hlb)

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- **The payoff.** A candidate `v` that is an exact fixed point of `reachOp`, and that
    lower-bounds every pre-fixed point of `reachOp`, *is* the least fixed point -- the
    Knaster-Tarski pinning argument, generalised from `RockPaperScissorsLfp.lean`'s
    `rpsVStar`-specific proof to an arbitrary `CSG`, goal, and candidate. Callers still have to
    supply `hfixed`/`hlb` themselves: this combinator automates the assembly of the two pinning
    lemmas via `le_antisymm`, not the two mathematical facts underneath it. Now a one-line wrapper
    around the fully generic `OrderHom.lfp_eq_of_certificate` above, specialising its `f` to
    `C.reachOp goal hr` -- the statement is exactly what it was before this refactor. -/
theorem reachOp_lfp_eq_of_certificate (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1)
    (hfixed : C.reachOp goal hr v = v)
    (hlb : ∀ b, C.reachOp goal hr b ≤ b → v ≤ b) :
    (C.reachOp goal hr).lfp = v :=
  OrderHom.lfp_eq_of_certificate (C.reachOp goal hr) v hfixed hlb

end CSG
end Csg
