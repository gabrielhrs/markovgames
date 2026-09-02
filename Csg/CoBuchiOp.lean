/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.BuchiOp

/-!
# The co-Büchi Bellman operator, the dual nested fixed point

**Status: confirmed by a clean `lake build` (only cosmetic deprecation/unused-variable warnings --
deprecated `if_pos`/`if_neg` at a few call sites, unused lambda binder names -- no errors).**
`BuchiOp.lean`'s exact dual, following de
Alfaro and Majumdar, "Quantitative Solution of Omega-Regular Games," JCSS 68 (2004) 374-397, eq.
(5):

`⟨1⟩◇□U = μx·νy·((¬U ∧ Ppre₁(x)) ∨ (U ∧ Ppre₁(y)))`

The paper writes eq. (4) (Büchi, `BuchiOp.lean`) and eq. (5) (co-Büchi, here) with the *same* body
formula -- the `¬U` branch always reads off `x`, the `U` branch always reads off `y` -- and lets
only the quantifier prefix differ: `νy·μx` for Büchi, `μx·νy` for co-Büchi. So `x`/`y` swap roles
wholesale: in `BuchiOp.lean`, `y` is the outer (`ν`/`gfp`) parameter and `x` is the inner (`μ`/
`lfp`) iterating variable; here, `x` is the outer (`μ`/`lfp`) parameter and `y` is the inner (`ν`/
`gfp`) iterating variable. The branch/variable pairing itself (`¬U`→`x`, `U`→`y`) does not move,
only which quantifier binds which name, and at which nesting level. Concretely: `coBuchiInnerOpFun`
below is `buchiInnerOpFun` with its two continuation arguments in the opposite order and its
monotonicity lemmas paired with `.gfp` (inner) and `.lfp` (outer) rather than the reverse.

**The one ingredient this file needs that `BuchiOp.lean` didn't**: `OrderHom.gfp_mono_of_le`, to
bundle the outer (`μx`) level as a genuine `OrderHom` -- `x ↦ (coBuchiInnerOp U hr x).gfp` needs to
be monotone in `x`, which is exactly "`.gfp` is monotone in the operator itself," the dual fact
`BuchiOp.lean` already proved (unused there) anticipating precisely this. Imported via
`Csg.BuchiOp` rather than restated.

Same scope as `BuchiOp.lean`: the operator and its well-definedness, nothing about a pinning
combinator or a worked instance. `ConcurrentCoBuchiExample.lean` supplies both: the paper's own
Example 3/Fig. 1, a small co-Büchi game demonstrating that the MDP trick of reducing Büchi/co-Büchi
conditions to plain reachability of the almost-surely-winning set fails for concurrent games (the
motivating claim `BuchiOp.lean`'s docstring flagged as the natural next worked instance), pinned
via `OrderHom.lfp_eq_of_certificate`/`OrderHom.gfp_eq_of_certificate` exactly as `ReachCertificate`/
`SafetyCertificate` do for the single-level operators.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The co-Büchi Bellman step's **inner** (`νy`) level, for a fixed outer candidate `x`: a `U`-state
    plays its stage game against the inner continuation `y` (the level currently being iterated to
    a greatest fixed point); a state outside `U` plays its stage game against the outer `x` (held
    fixed throughout that iteration) -- `buchiInnerOpFun U hr` with its two continuation arguments
    in the opposite order, matching eq. (5)'s `μx·νy` swapping which name is outer relative to eq.
    (4)'s `νy·μx` while leaving the `¬U`→`x`/`U`→`y` branch pairing itself untouched. Named
    `coBuchiInnerOpFun` rather than `coBuchiInnerOp` itself so the monotonicity proofs below can
    refer to it by name before bundling, mirroring `buchiInnerOpFun`/`buchiInnerOpFun_mono`. -/
noncomputable def coBuchiInnerOpFun (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x y : S → Set.Icc (0 : ℝ) 1) (s : S) :
    Set.Icc (0 : ℝ) 1 :=
  if U s then
    ⟨C.stageValue s (fun s' => (y s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (y s').2.1), C.stageValue_le_one hr (fun s' => (y s').2.2)⟩
  else
    ⟨C.stageValue s (fun s' => (x s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (x s').2.1), C.stageValue_le_one hr (fun s' => (x s').2.2)⟩

/-- **The payoff.** The coercion of `coBuchiInnerOpFun` to `ℝ`, as a plain `if`-`then`-`else` with
    no subtype packaging left to get in the way. Consumers that need to reason about the *value* of
    `coBuchiInnerOpFun` -- rather than just its monotonicity -- should rewrite with this first:
    `coBuchiInnerOpFun`'s own definition packages each branch as an anonymous-constructor element
    of `Set.Icc (0 : ℝ) 1` (value plus a two-part membership proof), and Mathlib's `rw`/`show`
    machinery can fail to see through that packaging at the transparency level those tactics check
    against -- concretely, `rw [if_pos h]`/`rw [if_neg h]` applied directly to an unfolded
    `coBuchiInnerOpFun` goal can report a spurious "motive is not type correct" or pattern-matching
    failure, even though the two sides are definitionally equal. Working with this `ℝ`-valued
    equation instead avoids the packaging entirely: `split_ifs` produces two goals, each closed by
    `rfl` since `(⟨v, _⟩ : Set.Icc _ _)`'s coercion to `ℝ` is its first component by definition. -/
theorem coBuchiInnerOpFun_coe (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x y : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (C.coBuchiInnerOpFun U hr x y s : ℝ) = if U s then C.stageValue s (fun s' => (y s' : ℝ))
      else C.stageValue s (fun s' => (x s' : ℝ)) := by
  unfold coBuchiInnerOpFun
  split_ifs <;> rfl

/-- **The payoff.** `coBuchiInnerOpFun` is monotone in the inner continuation `y` -- a `U`-state's
    value is `stageValue_mono` applied to the pointwise hypothesis, a non-`U` state's value doesn't
    mention `y` at all. Exactly `buchiInnerOpFun_mono_y` with `x`/`y` swapped (there the outer
    argument varies and is named `y`; here the inner argument varies and is named `y` too, since
    `y` is always eq. (5)'s `U`-branch name, regardless of which level it binds at). -/
theorem coBuchiInnerOpFun_mono (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x : S → Set.Icc (0 : ℝ) 1) :
    Monotone (C.coBuchiInnerOpFun U hr x) := by
  intro y1 y2 hy s
  by_cases h : U s
  · simp only [coBuchiInnerOpFun, if_pos h]
    exact C.stageValue_mono fun s' => hy s'
  · have heq : C.coBuchiInnerOpFun U hr x y1 s = C.coBuchiInnerOpFun U hr x y2 s := by
      simp only [coBuchiInnerOpFun, if_neg h]
    exact heq.le

/-- The inner Bellman step, bundled as an `OrderHom` for a fixed outer candidate `x` --
    `coBuchiInnerOpFun` plus its own monotonicity. Its `.gfp` is `νy.(...)`, the object `coBuchiOp`
    below takes as its own per-`x` value -- the `gfp` counterpart of `buchiInnerOp`'s `lfp`. -/
noncomputable def coBuchiInnerOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x : S → Set.Icc (0 : ℝ) 1) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.coBuchiInnerOpFun U hr x
  monotone' := C.coBuchiInnerOpFun_mono U hr x

/-- **The payoff.** `coBuchiInnerOpFun` is *also* monotone in the outer candidate `x`, for any
    fixed inner continuation `y` -- a non-`U` state's value is `stageValue_mono` applied to `x`'s
    inequality; a `U`-state's value doesn't mention `x` at all, so both sides are the literal same
    term. This is exactly the pointwise operator inequality `OrderHom.gfp_mono_of_le` needs to
    bundle the outer (`μx`) level as a genuine `OrderHom` in turn -- the mirror of
    `buchiInnerOpFun_mono_y`, with the roles of the two branches exchanged to match. -/
theorem coBuchiInnerOpFun_mono_x (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {x1 x2 : S → Set.Icc (0 : ℝ) 1} (hx : x1 ≤ x2)
    (y : S → Set.Icc (0 : ℝ) 1) :
    C.coBuchiInnerOpFun U hr x1 y ≤ C.coBuchiInnerOpFun U hr x2 y := by
  intro s
  by_cases h : U s
  · have heq : C.coBuchiInnerOpFun U hr x1 y s = C.coBuchiInnerOpFun U hr x2 y s := by
      simp only [coBuchiInnerOpFun, if_pos h]
    exact heq.le
  · simp only [coBuchiInnerOpFun, if_neg h]
    exact C.stageValue_mono fun s' => hx s'

/-- **The payoff.** The co-Büchi Bellman operator, `x ↦ νy.coBuchiInnerOpFun U x y`, bundled as an
    `OrderHom` on `S → Set.Icc (0 : ℝ) 1` via `OrderHom.gfp_mono_of_le` applied to
    `coBuchiInnerOpFun_mono_x` -- the one genuinely new architectural step this file needed beyond
    `BuchiOp.lean`. `(C.coBuchiOp U hr).lfp` is `⟨1⟩◇□U`, de Alfaro and Majumdar's eq. (5): the
    maximal probability of eventually visiting `U` forever. -/
noncomputable def coBuchiOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun x := (C.coBuchiInnerOp U hr x).gfp
  monotone' := fun x1 x2 hx =>
    OrderHom.gfp_mono_of_le (fun y => C.coBuchiInnerOpFun_mono_x U hr hx y)

end CSG
end Csg
