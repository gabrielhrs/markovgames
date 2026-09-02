/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.CsgMonotone

/-!
# The Büchi Bellman operator, bundled as a genuine nested fixed point

**Status: done, confirmed by a clean `lake build` and clean in VS Code, first attempt, no fix round
needed.** The first genuinely new architectural piece in the `Csg/` line since
`ReachOp.lean`/`SafetyOp.lean`/`UntilOp.lean` were first built: every operator so far has been a
*single-level* `OrderHom.lfp` or `.gfp`. This file's `buchiOp` is a *fixed point of a fixed point*
-- `νy.μx.(...)` -- following de Alfaro and Majumdar, "Quantitative Solution of Omega-Regular
Games," JCSS 68 (2004) 374-397, eq. (4):

`⟨1⟩□◇U = νy·μx·((¬U ∧ Ppre₁(x)) ∨ (U ∧ Ppre₁(y)))`

where `Ppre₁` is exactly this project's `CSG.stageValue` (their own Section 2.3 defines it as the
value of the one-step matrix game against the continuation, the same construction
`CsgMonotone.lean` already works with). At a state `s`: if `s ∈ U`, the `∧`/`∨` (min/max) collapse
the formula to `Ppre₁(y)(s)` (`¬U`'s branch is forced to `0`); if `s ∉ U`, it collapses to
`Ppre₁(x)(s)`. Neither branch is a bare absorbing constant, unlike `reachOpFun`'s `goal`-branch or
`untilOpFun`'s dead-end branch -- Büchi's "visit `U` infinitely often" condition never lets a single
visit end the game, it only resets which continuation (`x`, the still-searching-for-`U` value, or
`y`, the just-reset value) gets one more step of `Ppre₁` applied to it.

This is also the *general* form of the LTL-shaped recurrence claim
`IntrusionDetectionRecurrence.lean` proves for one specific instance via a from-scratch probability
argument (Borel-Cantelli, an oblivious attacker only): `buchiOp` instead characterises `⟨1⟩□◇U` as
a fixed point, for *any* reward-free `CSG` and *any* opponent (not just oblivious ones), the way
`reachOp`/`safetyOp` already do for reachability and safety. The two are complementary, not
competing -- `IntrusionDetectionRecurrence.lean`'s result is a genuine probability-1 recurrence fact
reached by a shortcut specific to IDS's
uniform-strategy structure; `buchiOp` is the reusable machinery for the general case, still needing
a `BuchiCertificate.lean`-style pinning combinator and a worked instance (a natural candidate: the
paper's own Example 3/Fig. 1, a small co-Büchi game demonstrating that the MDP trick of reducing
Büchi conditions to plain reachability of the almost-surely-winning set fails for concurrent games)
before it says anything about a concrete model. This file stops at the operator and its
well-definedness, mirroring `ReachOp.lean`'s own stated scope.

**The one genuinely new ingredient**, beyond everything `CsgMonotone.lean` already supplies:
bundling the outer (`νy`) level as an `OrderHom` needs knowing that `y ↦ (buchiInnerOp U hr y).lfp`
is itself monotone in `y` -- that is, that `OrderHom.lfp` is monotone *in the operator itself*, not
just in the lattice element the operator is applied to. This isn't a named lemma in
`Mathlib/Order/FixedPoints.lean` (checked directly), but follows in three lines from two lemmas
that already are: `OrderHom.map_lfp` (`f a = a` becomes `g (g.lfp) = g.lfp`) and `OrderHom.lfp_le`
(already relied on by `IntervalCertificate.lean`) -- `f ≤ g` pointwise gives
`f (g.lfp) ≤ g (g.lfp) = g.lfp`,
i.e. `g.lfp` is a pre-fixed point of `f`, so `f.lfp ≤ g.lfp` by `lfp_le`. `OrderHom.lfp_mono_of_le`
below states this once, generally, the same "pull the CSG-independent lattice fact out of the
CSG-specific file that first needed it" move `ReachCertificate.lean` made for
`OrderHom.lfp_eq_of_certificate`.
-/

/-- **CSG-independent.** `OrderHom.lfp` is monotone in the operator itself: if `f ≤ g` pointwise,
    then `f.lfp ≤ g.lfp`. Not a named lemma in `Mathlib/Order/FixedPoints.lean` (checked directly),
    but a three-line consequence of two that are: `g.lfp` is a fixed point of `g`
    (`OrderHom.map_lfp`), so `f ≤ g` pointwise makes it a *pre*-fixed point of `f` too, and
    `OrderHom.lfp_le` then gives
    `f.lfp ≤ g.lfp` directly, no further argument needed. -/
theorem OrderHom.lfp_mono_of_le {α : Type*} [CompleteLattice α] {f g : α →o α}
    (h : ∀ a, f a ≤ g a) : f.lfp ≤ g.lfp :=
  f.lfp_le ((h g.lfp).trans (le_of_eq g.map_lfp))

/-- **CSG-independent, dual.** `OrderHom.gfp` is monotone in the operator itself: if `f ≤ g`
    pointwise, then `f.gfp ≤ g.gfp` -- the exact mirror of `lfp_mono_of_le` via `OrderHom.map_gfp`/
    `OrderHom.le_gfp`. Not needed by `buchiOp` below (only the `lfp` direction is), but stated
    alongside it since `co-Büchi`'s solution formula (eq. (5) of the same paper, `μx·νy·(...)`) will
    need exactly this dual fact for its own outer level, the same way `reachOp`/`safetyOp` are
    proved as a matched pair. -/
theorem OrderHom.gfp_mono_of_le {α : Type*} [CompleteLattice α] {f g : α →o α}
    (h : ∀ a, f a ≤ g a) : f.gfp ≤ g.gfp :=
  g.le_gfp ((le_of_eq f.map_gfp.symm).trans (h f.gfp))

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The Büchi Bellman step's **inner** (`μx`) level, for a fixed outer candidate `y`: a `U`-state
    plays its stage game against `y` (having just reached `U`, one more step is still owed before
    the condition can be satisfied *again* -- `y` is "the value from here, having just reset");
    a state outside `U` plays its stage game against the inner continuation `x`, exactly as
    `reachOpFun`'s non-`goal` branch does. Named `buchiInnerOpFun` rather than `buchiInnerOp` itself
    so the monotonicity proofs below can refer to it by name before bundling, mirroring
    `reachOpFun`/`reachOpFun_mono`. -/
noncomputable def buchiInnerOpFun (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (y x : S → Set.Icc (0 : ℝ) 1) (s : S) :
    Set.Icc (0 : ℝ) 1 :=
  if U s then
    ⟨C.stageValue s (fun s' => (y s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (y s').2.1), C.stageValue_le_one hr (fun s' => (y s').2.2)⟩
  else
    ⟨C.stageValue s (fun s' => (x s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (x s').2.1), C.stageValue_le_one hr (fun s' => (x s').2.2)⟩

/-- **The payoff.** `buchiInnerOpFun` is monotone in the inner continuation `x` -- a `U`-state's
    value doesn't mention `x` at all (trivially monotone there), and every other state's value is
    `stageValue_mono` applied to the pointwise hypothesis, the same unwrapping `reachOpFun_mono`
    already does. -/
theorem buchiInnerOpFun_mono (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (y : S → Set.Icc (0 : ℝ) 1) :
    Monotone (C.buchiInnerOpFun U hr y) := by
  intro x1 x2 hx s
  by_cases h : U s
  · have heq : C.buchiInnerOpFun U hr y x1 s = C.buchiInnerOpFun U hr y x2 s := by
      simp only [buchiInnerOpFun, if_pos h]
    exact heq.le
  · simp only [buchiInnerOpFun, if_neg h]
    exact C.stageValue_mono fun s' => hx s'

/-- The inner Bellman step, bundled as an `OrderHom` for a fixed outer candidate `y` --
    `buchiInnerOpFun` plus its own monotonicity, exactly the `reachOp`/`safetyOp` pattern. Its
    `.lfp` is `μx.(...)`, the object `buchiOp` below takes as its own per-`y` value. -/
noncomputable def buchiInnerOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (y : S → Set.Icc (0 : ℝ) 1) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.buchiInnerOpFun U hr y
  monotone' := C.buchiInnerOpFun_mono U hr y

/-- **The payoff.** `buchiInnerOpFun` is *also* monotone in the outer candidate `y`, for any fixed
    inner continuation `x` -- a `U`-state's value is `stageValue_mono` applied to `y`'s inequality;
    a non-`U` state's value doesn't mention `y` at all, so both sides are the literal same term.
    This is exactly the pointwise operator inequality `OrderHom.lfp_mono_of_le` needs to bundle the
    outer (`νy`) level as a genuine `OrderHom` in turn. -/
theorem buchiInnerOpFun_mono_y (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {y1 y2 : S → Set.Icc (0 : ℝ) 1} (hy : y1 ≤ y2)
    (x : S → Set.Icc (0 : ℝ) 1) :
    C.buchiInnerOpFun U hr y1 x ≤ C.buchiInnerOpFun U hr y2 x := by
  intro s
  by_cases h : U s
  · simp only [buchiInnerOpFun, if_pos h]
    exact C.stageValue_mono fun s' => hy s'
  · have heq : C.buchiInnerOpFun U hr y1 x s = C.buchiInnerOpFun U hr y2 x s := by
      simp only [buchiInnerOpFun, if_neg h]
    exact heq.le

/-- **The payoff.** The Büchi Bellman operator, `y ↦ μx.buchiInnerOpFun U y x`, bundled as an
    `OrderHom` on `S → Set.Icc (0 : ℝ) 1` via `OrderHom.lfp_mono_of_le` applied to
    `buchiInnerOpFun_mono_y` -- the one genuinely new architectural step this file needed beyond
    `CsgMonotone.lean`. `(C.buchiOp U hr).gfp` is `⟨1⟩□◇U`, de Alfaro and Majumdar's eq. (4): the
    maximal probability of visiting `U` infinitely often. -/
noncomputable def buchiOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun y := (C.buchiInnerOp U hr y).lfp
  monotone' := fun y1 y2 hy =>
    OrderHom.lfp_mono_of_le (fun x => C.buchiInnerOpFun_mono_y U hr hy x)

end CSG
end Csg
