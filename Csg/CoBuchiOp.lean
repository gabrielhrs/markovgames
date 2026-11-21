/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.BuchiOp

/-!
# The co-Büchi Bellman operator, the dual nested fixed point

**Status: confirmed by a clean `lake build`.** `BuchiOp.lean`'s exact dual, following de
Alfaro and Majumdar, "Quantitative Solution of Omega-Regular Games," JCSS 68 (2004) 374-397, eq.
(5):

`⟨1⟩◇□U = μx·νy·((¬U ∧ Ppre₁(x)) ∨ (U ∧ Ppre₁(y)))`

The paper writes eq. (4) (Büchi, `BuchiOp.lean`) and eq. (5) (co-Büchi, here) with the *same* body
formula -- the `¬U` branch always reads off `x`, the `U` branch always reads off `y` -- and lets
only the quantifier prefix differ: `νy·μx` for Büchi, `μx·νy` for co-Büchi. So `x`/`y` swap roles
wholesale: in `BuchiOp.lean`, `y` is the outer (`ν`/`gfp`) parameter and `x` is the inner (`μ`/
`lfp`) iterating variable; here, `x` is the outer (`μ`/`lfp`) parameter and `y` is the inner (`ν`/
`gfp`) iterating variable. The branch/variable pairing itself (`¬U`→`x`, `U`→`y`) does not move,
only which quantifier binds which name, and at which nesting level. Concretely: both files use the
one body `buchiBody` (`BuchiOp.lean`). `buchiInnerOp` fixes its `y` argument and iterates `x`;
`coBuchiInnerOp` here fixes `x` and iterates `y`, and the fixed points are `.gfp` (inner) and
`.lfp` (outer) rather than the reverse.

**The one ingredient this file needs that `BuchiOp.lean` didn't**: `OrderHom.gfp_mono_of_le`, to
bundle the outer (`μx`) level as a genuine `OrderHom` -- `x ↦ (coBuchiInnerOp U hr x).gfp` needs to
be monotone in `x`, which is exactly "`.gfp` is monotone in the operator itself" -- the dual
of the fact `BuchiOp.lean` uses, stated beside it in `FixedPoints.lean`.

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

/-- The co-Büchi Bellman step's **inner** (`νy`) level, for a fixed outer candidate `x`, bundled
    as an `OrderHom`: `y ↦ buchiBody U hr x y`. A `U`-state plays its stage game against the inner
    continuation `y` (the level being iterated to a greatest fixed point); a state outside `U`
    plays against the outer `x`, held fixed throughout that iteration. Its `.gfp` is `νy.(...)`,
    the object `coBuchiOp` below takes as its own per-`x` value. -/
noncomputable def coBuchiInnerOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x : S → Set.Icc (0 : ℝ) 1) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.buchiBody U hr x
  monotone' := fun _y1 _y2 hy => C.buchiBody_mono_y U hr x hy

/-- **The payoff.** The co-Büchi Bellman operator, `x ↦ νy.buchiBody U x y`, bundled as an
    `OrderHom` on `S → Set.Icc (0 : ℝ) 1` via `OrderHom.gfp_mono_of_le` applied to
    `buchiBody_mono_x`. `(C.coBuchiOp U hr).lfp` is `⟨1⟩◇□U`, de Alfaro and Majumdar's eq. (5):
    the maximal probability of eventually visiting `U` forever. -/
noncomputable def coBuchiOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun x := (C.coBuchiInnerOp U hr x).gfp
  monotone' := fun _x1 _x2 hx =>
    OrderHom.gfp_mono_of_le (fun y => C.buchiBody_mono_x U hr hx y)

end CSG
end Csg
