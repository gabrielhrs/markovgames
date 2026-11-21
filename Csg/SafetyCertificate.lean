/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.SafetyOp
import Csg.FixedPoints

/-!
# A reusable safety-value certificate, dual to `ReachCertificate.lean`

**Status: confirmed by a clean `lake build`.** Mirrors `ReachCertificate.lean` on the `gfp` side
of Knaster-Tarski rather than the `lfp` side. With it the zero-sum temporal shapes each have a
certificate: step-bounded (`bwInd`), unbounded reachability/until (`reachOp`/`untilOp`),
reward-until-absorption (`RewardUntilCertificate.lean`), and safety/always.
`RockPaperScissorsSafety.lean` is a worked instance.

As anticipated there, this came out close to a mechanical mirror. `OrderHom.gfp_eq_of_certificate`
is `OrderHom.lfp_eq_of_certificate` with `le_gfp`/`gfp_le` in place of `le_lfp`/`lfp_le_fixed`
(`Mathlib/Order/FixedPoints.lean`, checked directly) and the two hypotheses' inequalities flipped
to match -- an upper-bound hypothesis over every *post*-fixed point (`b ≤ f b`) rather than a
lower-bound hypothesis over every *pre*-fixed point (`f b ≤ b`), since `gfp` is the greatest such
`b`, the dual notion to `lfp` being the least. `CSG.safetyOp_gfp_eq_of_certificate` is then the
same one-line wrapper `CSG.reachOp_lfp_eq_of_certificate` is, specialising `f` to `C.safetyOp safe
hr` in place of `C.reachOp goal hr`.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- **The payoff.** A candidate `v` that is an exact fixed point of `safetyOp`, and that
    upper-bounds every post-fixed point of `safetyOp`, *is* the greatest fixed point -- the dual of
    `reachOp_lfp_eq_of_certificate`, specialising the fully generic `OrderHom.gfp_eq_of_certificate`
    above to `f := C.safetyOp safe hr`. Callers still have to supply `hfixed`/`hub` themselves:
    this combinator automates the assembly of the two pinning lemmas via `le_antisymm`, not the two
    mathematical facts underneath it. -/
theorem safetyOp_gfp_eq_of_certificate (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1)
    (hfixed : C.safetyOp safe hr v = v)
    (hub : ∀ b, b ≤ C.safetyOp safe hr b → b ≤ v) :
    (C.safetyOp safe hr).gfp = v :=
  OrderHom.gfp_eq_of_certificate (C.safetyOp safe hr) v hfixed hub

end CSG
end Csg
