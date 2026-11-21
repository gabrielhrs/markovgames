/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.CsgMonotone
import Csg.FixedPoints

/-!
# The Büchi Bellman operator, bundled as a genuine nested fixed point

**Status: confirmed by a clean `lake build`.** Every operator in `ReachOp.lean`, `SafetyOp.lean`
and `UntilOp.lean` is a *single-level* `OrderHom.lfp` or `.gfp`. This file's `buchiOp` is a
*fixed point of a fixed point* -- `νy.μx.(...)` -- following de Alfaro and Majumdar,
"Quantitative Solution of Omega-Regular Games," JCSS 68 (2004) 374-397, eq. (4):

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
`IntrusionDetectionRecurrence.lean` proves for one specific instance via a probability argument
(Borel-Cantelli, an oblivious attacker only): `buchiOp` instead characterises `⟨1⟩□◇U` as a fixed
point, for *any* reward-free `CSG` and *any* opponent, the way `reachOp`/`safetyOp` do for
reachability and safety. The two are complementary: `IntrusionDetectionRecurrence.lean`'s result
is a probability-1 recurrence fact reached by a shortcut specific to that game's uniform-strategy
structure; `buchiOp` is the reusable machinery for the general case. This file stops at the
operator and its well-definedness, as `ReachOp.lean` does; no instance of `buchiOp` itself is
worked here, and `ConcurrentCoBuchiExample.lean` works one for the dual, `coBuchiOp`.

**The one ingredient beyond `CsgMonotone.lean`:** bundling the outer (`νy`) level as an
`OrderHom` needs `y ↦ (buchiInnerOp U hr y).lfp` to be monotone in `y`, that is, `OrderHom.lfp` to
be monotone *in the operator*, not just in the lattice element the operator is applied to. Mathlib
bundles `OrderHom.lfp` as a monotone map `(α →o α) →o α`, which is this fact;
`OrderHom.lfp_mono_of_le` (`FixedPoints.lean`) restates it with the hypothesis in the pointwise
form `∀ a, f a ≤ g a` that `buchiBody_mono_y` supplies.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The shared body of the Büchi and co-Büchi Bellman steps, de Alfaro and Majumdar's
    `(¬U ∧ Ppre₁(x)) ∨ (U ∧ Ppre₁(y))`: a `U`-state plays its stage game against `y`, a state
    outside `U` plays its stage game against `x`. Eq. (4) (Büchi, `νy·μx`) and eq. (5) (co-Büchi,
    `μx·νy`) have this same body and differ only in which variable is the inner one and which
    fixed point binds it: `buchiInnerOp` below fixes `y` and iterates `x`, and `CoBuchiOp.lean`'s
    `coBuchiInnerOp` fixes `x` and iterates `y`. -/
noncomputable def buchiBody (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x y : S → Set.Icc (0 : ℝ) 1) (s : S) :
    Set.Icc (0 : ℝ) 1 :=
  if U s then C.stageValueIcc hr y s else C.stageValueIcc hr x s

/-- **The payoff.** The coercion of `buchiBody` to `ℝ`, as a plain `if`-`then`-`else` with no
    subtype packaging. Consumers that reason about the *value* of `buchiBody`, rather than its
    monotonicity, should rewrite with this first: each branch is a `stageValueIcc`, an element
    of `Set.Icc (0 : ℝ) 1` (value plus a two-part membership proof), and `rw [ite_eq_left h]`/
    `rw [ite_eq_right h]` applied directly to an unfolded `buchiBody` goal can report "motive is
    not type correct" or a pattern-matching failure, even though the two sides are definitionally
    equal. With this `ℝ`-valued equation the packaging is gone: `split_ifs` produces two goals,
    each closed by `rfl` (`stageValueIcc_coe`). -/
theorem buchiBody_coe (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x y : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (C.buchiBody U hr x y s : ℝ) = if U s then C.stageValue s (fun s' => (y s' : ℝ))
      else C.stageValue s (fun s' => (x s' : ℝ)) := by
  unfold buchiBody
  split_ifs <;> rfl

/-- **The payoff.** `buchiBody` is monotone in `x`, for any fixed `y`: a state outside `U` is
    `stageValueIcc_mono` applied to `x`'s inequality, and a `U`-state does not mention `x` at all.
    This is the monotonicity of Büchi's inner step, and the pointwise operator inequality
    `OrderHom.gfp_mono_of_le` needs for co-Büchi's outer level. -/
theorem buchiBody_mono_x (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {x1 x2 : S → Set.Icc (0 : ℝ) 1} (hx : x1 ≤ x2)
    (y : S → Set.Icc (0 : ℝ) 1) :
    C.buchiBody U hr x1 y ≤ C.buchiBody U hr x2 y := by
  intro s
  by_cases h : U s
  · have heq : C.buchiBody U hr x1 y s = C.buchiBody U hr x2 y s := by
      simp only [buchiBody, ite_eq_left h]
    exact heq.le
  · simp only [buchiBody, ite_eq_right h]
    exact C.stageValueIcc_mono hr hx s

/-- **The payoff.** `buchiBody` is monotone in `y`, for any fixed `x`: a `U`-state is
    `stageValueIcc_mono` applied to `y`'s inequality, and a state outside `U` does not mention
    `y` at all. This is the monotonicity of co-Büchi's inner step, and the pointwise operator
    inequality `OrderHom.lfp_mono_of_le` needs for Büchi's outer level. -/
theorem buchiBody_mono_y (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x : S → Set.Icc (0 : ℝ) 1)
    {y1 y2 : S → Set.Icc (0 : ℝ) 1} (hy : y1 ≤ y2) :
    C.buchiBody U hr x y1 ≤ C.buchiBody U hr x y2 := by
  intro s
  by_cases h : U s
  · simp only [buchiBody, ite_eq_left h]
    exact C.stageValueIcc_mono hr hy s
  · have heq : C.buchiBody U hr x y1 s = C.buchiBody U hr x y2 s := by
      simp only [buchiBody, ite_eq_right h]
    exact heq.le

/-- The Büchi Bellman step's **inner** (`μx`) level, for a fixed outer candidate `y`, bundled as
    an `OrderHom`: `x ↦ buchiBody U hr x y`. A `U`-state plays against `y` (having just reached
    `U`, one more step is owed before the condition can be satisfied *again*, so `y` is "the value
    from here, having just reset"); a state outside `U` plays against the inner continuation `x`,
    as `reachOpFun`'s non-`goal` branch does. Its `.lfp` is `μx.(...)`, the object `buchiOp` below
    takes as its own per-`y` value. -/
noncomputable def buchiInnerOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (y : S → Set.Icc (0 : ℝ) 1) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun x := C.buchiBody U hr x y
  monotone' := fun _x1 _x2 hx => C.buchiBody_mono_x U hr hx y

/-- **The payoff.** The Büchi Bellman operator, `y ↦ μx.buchiBody U x y`, bundled as an
    `OrderHom` on `S → Set.Icc (0 : ℝ) 1` via `OrderHom.lfp_mono_of_le` applied to
    `buchiBody_mono_y`. `(C.buchiOp U hr).gfp` is `⟨1⟩□◇U`, de Alfaro and Majumdar's eq. (4): the
    maximal probability of visiting `U` infinitely often. -/
noncomputable def buchiOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun y := (C.buchiInnerOp U hr y).lfp
  monotone' := fun _y1 _y2 hy =>
    OrderHom.lfp_mono_of_le (fun x => C.buchiBody_mono_y U hr x hy)

end CSG
end Csg
