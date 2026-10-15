/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Search

/-!
# The rational Shapley step, and its agreement with the real-valued operator

**Status: confirmed by a clean `lake build`.**

One state's worth of executable value iteration. `shapleyGameQ` is the discounted stage game with
rational entries, and `shapley_eq_of_find` says that when the search of `Comp/Search.lean` succeeds
on it, the number it returns *is* `Csg/Discounted.lean`'s `shapley` at that state -- exactly, with
no error term. That is the join between the computation and the specification, and everything the
iteration needs.

**Why this is stated pointwise rather than as a `shapleyQ : (S → ℚ) → (S → ℚ)`.** Returning a whole
vector would mean folding over the states, which needs a computable `List S`, and
`Comp/Search.lean`'s module docstring records why there is none: every route out of `Fintype S` goes
through `Multiset.toList`, which is `noncomputable`. A pointwise statement needs no enumeration of
`S` at all, composes however the caller wants, and at a concrete instance is applied once per state
by name. The same reasoning is why the action lists stay parameters.

**Why the value agreement avoids structure equality.** The obvious route is to show the two stage
games are *equal* as `MatrixGame`s and rewrite. But `MatrixGame` carries no `@[ext]` lemma -- the
same obstacle `Csg/CoalitionComplement.lean` hit -- so that means `funext` plus `congrArg
MatrixGame.mk` and a reliance on structure eta firing at the right moment. Instead
`shapleyGameQ_value` feeds entrywise equality to `MatrixGame.abs_value_sub_le` at `ε = 0`: the
hypothesis becomes `|x - x| ≤ 0` and the conclusion `|v' - v| ≤ 0`, which pins the values with no
new machinery and no structure-level reasoning. Using an already-proved Lipschitz bound to get an
equality is cheap and avoids the fragile step entirely.

**What this does not say.** Nothing here claims the search succeeds -- `shapley_eq_of_find` is
conditional on it having returned something, which is the honest shape, since completeness of
support enumeration is not proved anywhere in `Comp/`. And nothing here iterates; the fixed point of
`shapley` is irrational in general (see `Csg/DiscountedValueIteration.lean`), so an iteration's
guarantee is `valueIteration_error`'s `ε` bound and not an equality, whatever this file proves about
single steps.
-/

namespace Comp

open Csg

namespace DiscountedCsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

/-- The discounted stage game at `s` against continuation `v`, with rational entries: the immediate
    reward plus `l` times the rational one-step expectation. The computable counterpart of
    `Csg.DiscountedCSG.shapleyGame`, and a `MatrixGameQ`, so `Comp/Search.lean`'s machinery applies
    to it directly. -/
def shapleyGameQ (G : DiscountedCsgQ S A1 A2) (s : S) (v : S → ℚ) : MatrixGameQ A1 A2 where
  A a1 a2 := G.toCsgQ.r s a1 a2 + G.l * G.toCsgQ.expectQ s a1 a2 v

/-- The entries of the two stage games agree under the cast: the real operator's payoff at a joint
    action is the cast of the rational one's. The reward term casts directly, and the expectation
    term is `CsgQ.expect_toCSG`; `push_cast` then moves the cast across the sum and product.

    Written with `change` to put both sides in their unfolded form first -- the projections through
    `extends` (`toDiscountedCSG`'s `toCSG`, and that structure's `r`) all reduce definitionally, but
    `rw` will not fire against them until they do. -/
theorem shapleyGameQ_A_cast (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) (s : S) (v : S → ℚ)
    (a1 : A1) (a2 : A2) :
    ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).A a1 a2
      = ((G.shapleyGameQ s v).toMatrixGame).A a1 a2 := by
  change ((G.toCsgQ.r s a1 a2 : ℚ) : ℝ)
      + ((G.l : ℚ) : ℝ)
        * (G.toCsgQ.toCSG h.1).expect s a1 a2 (fun s' => ((v s' : ℚ) : ℝ))
      = ((G.toCsgQ.r s a1 a2 + G.l * G.toCsgQ.expectQ s a1 a2 v : ℚ) : ℝ)
  rw [CsgQ.expect_toCSG]
  push_cast
  ring

/-- The two stage games have the same value. Entrywise equality fed to
    `MatrixGame.abs_value_sub_le` at `ε = 0`, as the module docstring explains -- no `MatrixGame`
    equality and no `ext`. -/
theorem shapleyGameQ_value (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) (s : S) (v : S → ℚ) :
    ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).value
      = (G.shapleyGameQ s v).toMatrixGame.value := by
  have hb : |((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).value
      - (G.shapleyGameQ s v).toMatrixGame.value| ≤ 0 :=
    MatrixGame.abs_value_sub_le (ε := 0) fun a1 a2 => by
      rw [shapleyGameQ_A_cast G h s v a1 a2]
      simp
  have hz := abs_nonpos_iff.mp hb
  linarith

/-- **The payoff.** When the search succeeds on the rational stage game at `s`, the value `t` it
    returns is exactly the real Shapley operator's value there. Composition of
    `shapleyGameQ_value` with `Comp/Search.lean`'s `value_eq_of_find`, so the solver is still never
    trusted -- only its checked output is.

    This is the statement an executable iteration rests on: run the search per state with `#eval`,
    read off the numbers, and each one is pinned to the specification by this theorem. -/
theorem shapley_eq_of_find (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {As1 : List A1} {As2 : List A2} {v : S → ℚ} {s : S}
    {t : ℚ} {p : A1 → ℚ} {q : A2 → ℚ}
    (hf : (G.shapleyGameQ s v).findValueCert As1 As2 = some (t, p, q)) :
    (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s = ((t : ℚ) : ℝ) := by
  change ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).value = ((t : ℚ) : ℝ)
  rw [shapleyGameQ_value G h s v]
  exact MatrixGameQ.value_eq_of_find hf

end DiscountedCsgQ

end Comp
