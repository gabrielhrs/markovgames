/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.ReachOp
import Csg.SafetyOp

/-!
# A reusable interval certificate: bounding a fixed point rather than pinning it exactly

**Status: done, confirmed by a clean `lake build` (via `RockPaperScissorsInterval.lean`, its first
concrete consumer).** The last open row of
`VERIFICATION-FRAMEWORK.md`'s Axis C (candidate form): every certificate built so far
(`ReachCertificate.lean`, `SafetyCertificate.lean`) pins `f.lfp`/`f.gfp` down to a single guessed
candidate *exactly*, via Knaster-Tarski's two-sided lemmas. That approach's one real limitation,
flagged in both those files' own docstrings, is that solving for an exact closed form by hand only
works for small, highly symmetric games like rock-paper-scissors -- anything larger or less
symmetric has no reason to admit one at all. This file builds the weaker, realistic fallback:
sandwiching `f.lfp`/`f.gfp` between two one-sided candidates, `lo ≤ f.lfp ≤ hi` (respectively
`lo ≤ f.gfp ≤ hi`), rather than pinning it to a single point.

**The key fact making this cheap, confirmed directly against
`Mathlib/Order/FixedPoints.lean`.** The exact-pinning certificates used
`OrderHom.lfp_le_fixed {a} (h : f a = a) : f.lfp ≤ a` -- an *exact* fixed point upper-bounds
`f.lfp`. What that file actually proves first, and `lfp_le_fixed` merely specialises, is strictly
more general: `OrderHom.lfp_le {a} (h : f a ≤ a) : f.lfp ≤ a` -- *any* pre-fixed point (`f a ≤ a`,
one inequality, not two) already upper-bounds `f.lfp`, since `f.lfp` is defined as the infimum of
exactly that set. So an upper-bound candidate `hi` for this file needs a strictly *weaker*
hypothesis than the exact certificates' `hi`, not a different one -- `f hi ≤ hi` rather than
`f hi = hi`. The lower-bound half is unchanged from the exact certificates: `OrderHom.le_lfp
{a} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ f.lfp` was already exactly this shape (a candidate lower-
bounding every pre-fixed point), reused here verbatim as `hlb`. The dual (`gfp`) side mirrors this
precisely, confirmed against the same source file: `OrderHom.le_gfp {a} (h : a ≤ f a) : a ≤ f.gfp`
(a post-fixed point lower-bounds `f.gfp`, the exact dual of `lfp_le`) and `OrderHom.gfp_le
{a} (h : ∀ b, b ≤ f b → b ≤ a) : f.gfp ≤ a` (an upper bound over every post-fixed point, dual to
`le_lfp`, reused verbatim as `hub`).

**What this buys over the exact certificates, concretely.** Proving `f hi = hi` demands solving a
system of equations exactly; proving `f hi ≤ hi` only demands checking that a *guessed* candidate
does not need to grow under one more Bellman step -- a strictly easier, one-directional numeric
check, and the natural shape of a "safe overestimate" argument for a game too large or asymmetric
to solve by hand. `hlb` is unchanged in difficulty from the exact certificates (it was already the
harder, case-split-heavy half of `RockPaperScissorsLfp.lean`'s own proof), so this file's real
payoff is specifically on the upper-bound side.

**What this file automates, and does not.** Exactly as with `ReachCertificate.lean`/
`SafetyCertificate.lean`: the assembly of `hlb`/`hpre` (respectively `hpost`/`hub`) into the
`Icc` membership conclusion, via `OrderHom.le_lfp`/`OrderHom.lfp_le` (dually `le_gfp`/`gfp_le`).
Discharging those hypotheses for a specific model is exactly as hard as that model makes it, and
this file changes nothing about that -- it only widens the target from an equality to an interval,
which is what makes discharging tractable at all for anything past RPS-sized and symmetric.
-/

/-- **The payoff, `lfp` side.** A lower bound `lo` over every pre-fixed point, together with an
    upper candidate `hi` that is itself a pre-fixed point (`f hi ≤ hi`, not the exact-certificate's
    stronger `f hi = hi`), sandwiches `f.lfp` between them. `OrderHom.le_lfp`/`OrderHom.lfp_le`
    assembled directly, no `le_antisymm` needed since the two conclusions are independent
    inequalities rather than two sides of one equality. -/
theorem OrderHom.lfp_mem_Icc_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α)
    (lo hi : α) (hlb : ∀ b, f b ≤ b → lo ≤ b) (hpre : f hi ≤ hi) :
    lo ≤ f.lfp ∧ f.lfp ≤ hi :=
  ⟨f.le_lfp hlb, f.lfp_le hpre⟩

/-- **The payoff, `gfp` side, dual.** A post-fixed-point lower candidate `lo` (`lo ≤ f lo`) together
    with an upper bound `hi` over every post-fixed point sandwiches `f.gfp` between them --
    `OrderHom.le_gfp`/`OrderHom.gfp_le`, the exact mirror of the `lfp` case above with the roles of
    `lo`/`hi` swapped to match which side gets the easier one-directional hypothesis. -/
theorem OrderHom.gfp_mem_Icc_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α)
    (lo hi : α) (hpost : lo ≤ f lo) (hub : ∀ b, b ≤ f b → b ≤ hi) :
    lo ≤ f.gfp ∧ f.gfp ≤ hi :=
  ⟨f.le_gfp hpost, f.gfp_le hub⟩

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The reachability specialisation of `OrderHom.lfp_mem_Icc_of_certificate`, exactly the way
    `CSG.reachOp_lfp_eq_of_certificate` specialises the exact-pinning version. -/
theorem reachOp_lfp_mem_Icc_of_certificate (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (lo hi : S → Set.Icc (0 : ℝ) 1)
    (hlb : ∀ b, C.reachOp goal hr b ≤ b → lo ≤ b) (hpre : C.reachOp goal hr hi ≤ hi) :
    lo ≤ (C.reachOp goal hr).lfp ∧ (C.reachOp goal hr).lfp ≤ hi :=
  OrderHom.lfp_mem_Icc_of_certificate (C.reachOp goal hr) lo hi hlb hpre

/-- The safety specialisation of `OrderHom.gfp_mem_Icc_of_certificate`, dual to
    `reachOp_lfp_mem_Icc_of_certificate` above exactly as `CSG.safetyOp_gfp_eq_of_certificate` is
    dual to `CSG.reachOp_lfp_eq_of_certificate`. -/
theorem safetyOp_gfp_mem_Icc_of_certificate (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (lo hi : S → Set.Icc (0 : ℝ) 1)
    (hpost : lo ≤ C.safetyOp safe hr lo) (hub : ∀ b, b ≤ C.safetyOp safe hr b → b ≤ hi) :
    lo ≤ (C.safetyOp safe hr).gfp ∧ (C.safetyOp safe hr).gfp ≤ hi :=
  OrderHom.gfp_mem_Icc_of_certificate (C.safetyOp safe hr) lo hi hpost hub

end CSG
end Csg
