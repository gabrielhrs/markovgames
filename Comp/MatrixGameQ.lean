/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Basic

/-!
# Rational matrix and bimatrix games, and decidable certificates for their solutions

**Status: confirmed by a clean `lake build`.**

The certification half of `Comp/`. Nothing here searches for anything; this file says what it means
for a supplied rational witness to be *correct*, decidably, and proves that a correct witness pins
the real-valued `MatrixGame.value` exactly. The search that produces witnesses is the next
checkpoint, and it needs no correctness proof of its own precisely because of what is proved here:
a wrong witness fails `decide` and is rejected.

**What actually certifies a zero-sum value, and what does not.** `ValueCert` below asks for a
candidate value `t` and a pair of rational mixed strategies, subject to two families of linear
inequalities: `p` holds the row player's loss down to `t` against every *pure* column, and `q`
holds the column player's gain up to `t` against every *pure* row. That is all. `MatrixGame.lean`'s
`value_isLeast_rowLPFeasible` and `value_isGreatest_colLPFeasible` then sandwich the value from both
sides and `le_antisymm` closes it. No complementary-slackness condition appears, and none is needed:
the inequalities alone are necessary and sufficient, because LP duality has already been done once
and for all in those two theorems.

**So why is the bimatrix layer here at all?** Two reasons, neither of them about the zero-sum value.
First, complementarity is what makes the *search* tractable: it characterises equilibria as
*equalities* over a chosen support, which is what turns an optimisation problem into finitely many
exactly-solvable linear systems. That is why `CSGNashLCPZ3.java` encodes it as
`mkOr(mkEq(x[i], zero), mkEq(u, ay))` -- an SMT solver uses the disjunctions to search, not to
check. Second, and more importantly, for *nonzero-sum* games there is no value to sandwich, and
certifying that a pair of strategies is an equilibrium genuinely does require complementarity: one
must witness that each player's realised payoff equals its best response, not merely that it is
bounded by something. So `NashCert` is the shape the equilibria line will need, and `ValueCert` is
recovered from it as the `R = -C` special case (`valueCert_of_nashCert`).

**A remark on redundancy, not proved here.** `NashCert`'s two complementarity clauses are in fact
*implied* by its inequality clauses together with `p`, `q` being distributions: if every
`(R q)ᵢ ≤ u` and `u = ∑ᵢ pᵢ (R q)ᵢ`, then `∑ᵢ pᵢ (u - (R q)ᵢ) = 0` is a sum of nonnegative terms, so
each vanishes. They are kept anyway -- they cost nothing to check, they match the encoding PRISM
uses, and a redundant conjunct can only make a certificate stricter, never wrong.

**Exactness, and its limits.** `value_eq_of_valueCert`'s conclusion is an *equality* --
`G.toMatrixGame.value = (t : ℝ)`, no error term -- which is available because a matrix game with
rational entries has a rational value, LP duality putting it at a vertex of a rational polytope.
This is a fact about one stage game and must not be read as one about an iteration's limit: the
fixed point of the Shapley operator is algebraic and generally irrational, for the reason recorded
in `Csg/DiscountedValueIteration.lean`'s docstring.

**Not here:** any search procedure, any iteration, and anything about `CsgQ`'s stage games. Those
come next.
-/

namespace Comp

open Csg

/-! ## Rational mixed strategies

Deliberately in their own section with only `[Fintype I]`: neither `IsStratQ` nor its cast into
`stdSimplex` needs `Nonempty` or `DecidableEq` on the index type, and declaring them under the
wider `variable` block below would carry unused instance arguments that the
`linter.unusedDecidableInType` check correctly flags. -/

section Strategies

variable {I : Type*} [Fintype I]

/-- A rational mixed strategy: nonnegative weights summing to one. The computable counterpart of
    membership in `stdSimplex ℝ I`, and decidable, so it can sit inside a certificate. -/
def IsStratQ (p : I → ℚ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

instance (p : I → ℚ) : Decidable (IsStratQ p) := by
  unfold IsStratQ
  infer_instance

/-- A rational mixed strategy casts to a point of the real standard simplex. The bridge every
    statement below uses to hand a rational witness to a theorem stated over `ℝ`.

    Both branches open with `change` to force the beta-reduced form: membership in `stdSimplex ℝ I`
    unfolds with the witness still applied as `(fun i => ↑(p i)) i`, and `norm_cast` does not see
    through an unreduced application, so `exact_mod_cast` fails against it. Beta is definitional,
    so `change` is free. -/
theorem mem_stdSimplex_of_isStratQ {p : I → ℚ} (h : IsStratQ p) :
    (fun i => ((p i : ℚ) : ℝ)) ∈ stdSimplex ℝ I := by
  refine ⟨fun i => ?_, ?_⟩
  · change (0 : ℝ) ≤ ((p i : ℚ) : ℝ)
    exact_mod_cast h.1 i
  · change ∑ i, ((p i : ℚ) : ℝ) = 1
    have hq : ((∑ i, p i : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by rw [h.2]
    push_cast at hq
    exact hq

end Strategies

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

/-- A two-player zero-sum game with rational payoffs, in `MatrixGame`'s own convention: `A i j` is
    paid by the row player (who minimises) to the column player (who maximises). -/
structure MatrixGameQ (I J : Type*) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] where
  /-- The rational payoff matrix. -/
  A : I → J → ℚ

namespace MatrixGameQ

/-- The real-valued `MatrixGame` a rational one denotes -- the object `value` and all of
    `MatrixGame.lean`'s theory are about. -/
noncomputable def toMatrixGame (G : MatrixGameQ I J) : MatrixGame I J where
  A i j := ((G.A i j : ℚ) : ℝ)

@[simp]
theorem toMatrixGame_A (G : MatrixGameQ I J) (i : I) (j : J) :
    G.toMatrixGame.A i j = ((G.A i j : ℚ) : ℝ) := rfl

/-- **A value certificate.** `t` is the candidate value, `p` and `q` the candidate optimal mixed
    strategies, and the two inequality families say that `p` caps the row player's loss at `t`
    against every pure column and `q` guarantees the column player `t` against every pure row.
    Purely a finite conjunction of rational linear inequalities -- no reference to a continuum of
    strategies and no complementarity, for the reason set out in the module docstring. -/
def ValueCert (G : MatrixGameQ I J) (t : ℚ) (p : I → ℚ) (q : J → ℚ) : Prop :=
  IsStratQ p ∧ IsStratQ q ∧ (∀ j, ∑ i, p i * G.A i j ≤ t) ∧ (∀ i, t ≤ ∑ j, G.A i j * q j)

/-- A value certificate is decidable: finitely many rational comparisons. This is what lets a
    search procedure stay entirely unverified -- whatever it returns is checked here, and a wrong
    answer is rejected rather than believed. -/
instance (G : MatrixGameQ I J) (t : ℚ) (p : I → ℚ) (q : J → ℚ) : Decidable (G.ValueCert t p q) := by
  unfold ValueCert
  infer_instance

/-- **The payoff of this file.** A value certificate pins the real-valued game value exactly: no
    approximation, no error term. The row inequalities put `t` in `rowLPFeasible`, so
    `value ≤ t` by `value_isLeast_rowLPFeasible`; the column inequalities put `t` in
    `colLPFeasible`, so `t ≤ value` by `value_isGreatest_colLPFeasible`; `le_antisymm` finishes.

    All the mathematics is in those two theorems, which is why this proof is bookkeeping: cast the
    rational witnesses into `ℝ`, and cast the rational inequalities across the finite sums. -/
theorem value_eq_of_valueCert {G : MatrixGameQ I J} {t : ℚ} {p : I → ℚ} {q : J → ℚ}
    (h : G.ValueCert t p q) : G.toMatrixGame.value = ((t : ℚ) : ℝ) := by
  obtain ⟨hp, hq, hrow, hcol⟩ := h
  refine le_antisymm ?_ ?_
  · refine G.toMatrixGame.value_isLeast_rowLPFeasible.2 ?_
    refine ⟨fun i => ((p i : ℚ) : ℝ), mem_stdSimplex_of_isStratQ hp, fun j => ?_⟩
    have hc : ((∑ i, p i * G.A i j : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ) := by exact_mod_cast hrow j
    push_cast at hc
    simpa using hc
  · refine G.toMatrixGame.value_isGreatest_colLPFeasible.2 ?_
    refine ⟨fun j => ((q j : ℚ) : ℝ), mem_stdSimplex_of_isStratQ hq, fun i => ?_⟩
    have hc : ((t : ℚ) : ℝ) ≤ ((∑ j, G.A i j * q j : ℚ) : ℝ) := by exact_mod_cast hcol i
    push_cast at hc
    simpa using hc

end MatrixGameQ

/-- A two-player general-sum game with rational payoffs: each player has its own matrix and
    *maximises* it. Unlike `MatrixGameQ`, there is no single value to speak of -- the solution
    notion is an equilibrium, certified by `NashCert`.

    This is the shape the nonzero-sum line needs. `MatrixGameQ.toBimatrixQ` below embeds the
    zero-sum case as `R = -C`. -/
structure BimatrixQ (I J : Type*) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] where
  /-- The row player's own payoff, which it maximises. -/
  R : I → J → ℚ
  /-- The column player's own payoff, which it maximises. -/
  C : I → J → ℚ

namespace BimatrixQ

/-- The row player's expected payoff under a mixed profile. -/
def rowPayoff (G : BimatrixQ I J) (p : I → ℚ) (q : J → ℚ) : ℚ := ∑ i, ∑ j, p i * G.R i j * q j

/-- The column player's expected payoff under a mixed profile. -/
def colPayoff (G : BimatrixQ I J) (p : I → ℚ) (q : J → ℚ) : ℚ := ∑ i, ∑ j, p i * G.C i j * q j

/-- **A Nash equilibrium certificate**, in the complementary-slackness form PRISM's
    `CSGNashLCPZ3.java` encodes: both profiles are distributions, neither player's pure deviation
    beats its realised payoff, and every pure action carrying positive weight achieves that payoff
    exactly. The last two clauses are the conjunction of disjunctions -- each is
    `pᵢ = 0 ∨ (R q)ᵢ = rowPayoff`, a disjunction of rational linear equations. -/
def NashCert (G : BimatrixQ I J) (p : I → ℚ) (q : J → ℚ) : Prop :=
  IsStratQ p ∧ IsStratQ q
    ∧ (∀ i, (∑ j, G.R i j * q j) ≤ G.rowPayoff p q)
    ∧ (∀ j, (∑ i, p i * G.C i j) ≤ G.colPayoff p q)
    ∧ (∀ i, p i = 0 ∨ (∑ j, G.R i j * q j) = G.rowPayoff p q)
    ∧ (∀ j, q j = 0 ∨ (∑ i, p i * G.C i j) = G.colPayoff p q)

/-- A Nash certificate is decidable -- a finite boolean combination of rational comparisons,
    disjunctions included. This is what makes the complementarity formulation usable as a check
    rather than only as an SMT query. -/
instance (G : BimatrixQ I J) (p : I → ℚ) (q : J → ℚ) : Decidable (G.NashCert p q) := by
  unfold NashCert
  infer_instance

end BimatrixQ

namespace MatrixGameQ

/-- The zero-sum game as a bimatrix game. The row player minimises what it pays, so it maximises
    the negation; the column player maximises the payment directly. Hence `R = -A` and `C = A`,
    which is exactly the zero-sum condition `R = -C`. -/
def toBimatrixQ (G : MatrixGameQ I J) : BimatrixQ I J where
  R i j := -G.A i j
  C i j := G.A i j

/-- A pure row's payoff in the zero-sum bimatrix game is the negation of its payment. The two
    `simp` calls here and in the next lemma are deliberately left without an explicit
    sum-of-negations lemma name: the fact is in `simp`'s default set, and naming it wrongly would
    be an unknown-constant error rather than an unsolved goal. -/
theorem toBimatrixQ_sum_row (G : MatrixGameQ I J) (q : J → ℚ) (i : I) :
    ∑ j, G.toBimatrixQ.R i j * q j = -(∑ j, G.A i j * q j) := by
  simp [toBimatrixQ, neg_mul]

/-- The row player's payoff in the zero-sum bimatrix game is the negation of the column player's --
    the zero-sum property at the level of mixed profiles. -/
theorem toBimatrixQ_rowPayoff (G : MatrixGameQ I J) (p : I → ℚ) (q : J → ℚ) :
    G.toBimatrixQ.rowPayoff p q = -(G.toBimatrixQ.colPayoff p q) := by
  simp [BimatrixQ.rowPayoff, BimatrixQ.colPayoff, toBimatrixQ, neg_mul, mul_neg]

/-- A pure column's payment is unchanged by the embedding, since `C = A`. -/
theorem toBimatrixQ_sum_col (G : MatrixGameQ I J) (p : I → ℚ) (j : J) :
    ∑ i, p i * G.toBimatrixQ.C i j = ∑ i, p i * G.A i j := rfl

/-- **The zero-sum corollary.** A Nash certificate for the zero-sum bimatrix game is a value
    certificate for the original matrix game, with the equilibrium payoff as the value. Note which
    clauses are used: only the two *inequality* families, never the complementarity ones -- the
    sandwich needs no more, as the module docstring explains. -/
theorem valueCert_of_nashCert {G : MatrixGameQ I J} {p : I → ℚ} {q : J → ℚ}
    (h : G.toBimatrixQ.NashCert p q) :
    G.ValueCert (G.toBimatrixQ.colPayoff p q) p q := by
  obtain ⟨hp, hq, hrow, hcol, -, -⟩ := h
  refine ⟨hp, hq, fun j => ?_, fun i => ?_⟩
  · have := hcol j
    rwa [toBimatrixQ_sum_col] at this
  · have hr := hrow i
    rw [toBimatrixQ_sum_row, toBimatrixQ_rowPayoff] at hr
    linarith

/-- The matrix game's value, read off a Nash certificate for its bimatrix form. The composition of
    `valueCert_of_nashCert` with `value_eq_of_valueCert`, recorded so the equilibria line can use
    one name. -/
theorem value_eq_of_nashCert {G : MatrixGameQ I J} {p : I → ℚ} {q : J → ℚ}
    (h : G.toBimatrixQ.NashCert p q) :
    G.toMatrixGame.value = ((G.toBimatrixQ.colPayoff p q : ℚ) : ℝ) :=
  value_eq_of_valueCert (valueCert_of_nashCert h)

end MatrixGameQ

end Comp
