/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Finite two-player zero-sum matrix games

**Status: done, confirmed by a clean `lake build`.** This is the first artifact for Goal 02
(concurrent stochastic games), and plays the same role for the CSG line of work that
`RecyclingRobot.lean` played for the discounted-MDP line: a small, self-contained, hands-on
exercise that checks a genuinely nontrivial piece of Mathlib before any downstream theory gets
built on top of it. Here the load-bearing dependency is `Mathlib.Topology.Sion`
(`Sion.exists_isSaddlePointOn`), a 2025 formalisation of Sion's minimax theorem, which that file's
own docstring notes specialises to von Neumann's minimax theorem in the finite bilinear case —
exactly the finite zero-sum matrix game below.

Why this matters for the project as a whole (see `PHASE0-NOTES.md`, "Heavy debrief" section): the
per-state value computation of a *concurrent* stochastic game, at every stage of a
`Backward_Induction.thy`-style bounded computation, is not a plain `Finset.sup'` over actions the
way it is for MDPs (`DiscountedMDP.bellman` in `Basic.lean`) — it's the value of a one-shot finite
zero-sum matrix game between the two players, since both choose actions simultaneously at a
state. Existence of that value (as a mixed-strategy saddle point) was, before this file, the
single biggest unconfirmed dependency in the CSG roadmap. `exists_optimal_strategies` below closes
it: it exists in Mathlib, and it is usable directly, without reproving von Neumann from scratch the
way the rest of this project avoids reproving Banach from scratch for the MDP case.

Scope, deliberately small: existence of a saddle point (a pair of optimal mixed strategies) for a
single one-shot matrix game. This file does not yet package the result as a `Finset.sup'`-style
per-state value *function* the way `DiscountedMDP.bellman` does for MDPs — that packaging (turning
`exists_optimal_strategies` into a `noncomputable def value : ℝ` via `Classical.choose`, the
`CSG`/backward-induction structure itself, and the reachcert-derived infinite-horizon value
certificates) is follow-up work, not this file's job.

Convention: the row player picks `i : I` and *minimizes* the payoff `A i j`; the column player
picks `j : J` and *maximizes* it. This matches `Sion.exists_isSaddlePointOn`'s own `X`/`Y`
convention exactly (`X` is the minimizing side, `Y` the maximizing side), so no sign flip is
needed anywhere below — a deliberate choice, not the more common "row player maximizes" textbook
convention.
-/

namespace Csg

/-- A finite two-player zero-sum matrix game: row player picks `i : I` (minimizing), column
    player picks `j : J` (maximizing), `A i j` is the payoff from row to column. `DecidableEq` on
    both index types is needed downstream only to exhibit a nonempty mixed strategy
    (`single_mem_stdSimplex`) -- a mild hypothesis, true of every concrete finite action set this
    project actually uses (`Fin n`, hand-rolled enums with `deriving DecidableEq`, as in
    `RecyclingRobot.lean`). -/
structure MatrixGame (I J : Type*) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] where
  /-- The payoff matrix: `A i j` is paid by the row player to the column player. -/
  A : I → J → ℝ

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

namespace MatrixGame

variable (G : MatrixGame I J)

/-- Expected payoff of a pair of mixed strategies `x : I → ℝ`, `y : J → ℝ` -- the bilinear
    extension of `A` to the mixed extension of the game. No claim that `x`/`y` are themselves
    mixed strategies (i.e. lie in `stdSimplex ℝ I`/`stdSimplex ℝ J`) is baked in here; that's
    imposed where needed by the theorems below, matching how `DiscountedMDP.expect` in
    `Basic.lean` is stated for a bare `v : S → ℝ` with no side conditions. -/
noncomputable def payoff (x : I → ℝ) (y : J → ℝ) : ℝ := ∑ i, ∑ j, x i * G.A i j * y j

/-- `payoff`, regrouped so the row player's mixed strategy is pulled out as an outer sum of
    single factors -- the shape linearity-in-`x` and continuity-in-`x` arguments below actually
    want. -/
theorem payoff_eq_sum_mul (x : I → ℝ) (y : J → ℝ) :
    G.payoff x y = ∑ i, x i * ∑ j, G.A i j * y j := by
  unfold payoff
  congr 1
  funext i
  rw [Finset.mul_sum]
  congr 1
  funext j
  ring

/-- `payoff`, regrouped the other way: the column player's mixed strategy pulled out as an outer
    sum -- the shape linearity-in-`y` and continuity-in-`y` want. -/
theorem payoff_eq_sum_mul' (x : I → ℝ) (y : J → ℝ) :
    G.payoff x y = ∑ j, (∑ i, x i * G.A i j) * y j := by
  unfold payoff
  rw [Finset.sum_comm]
  congr 1
  funext j
  rw [Finset.sum_mul]

/-- `payoff` is linear (not just convex/concave) in its row argument, for fixed column strategy --
    the bilinear extension of a matrix is exactly linear in each argument separately. This is the
    one fact `convexOn_payoff_left` and `continuous_payoff_left` both reduce to. -/
theorem payoff_smul_add_smul_left (p₁ p₂ : I → ℝ) (q : J → ℝ) (a b : ℝ) :
    G.payoff (a • p₁ + b • p₂) q = a * G.payoff p₁ q + b * G.payoff p₂ q := by
  simp only [payoff_eq_sum_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  funext i
  ring

/-- `payoff` is linear in its column argument, for fixed row strategy. Symmetric counterpart of
    `payoff_smul_add_smul_left`. -/
theorem payoff_smul_add_smul_right (p : I → ℝ) (q₁ q₂ : J → ℝ) (a b : ℝ) :
    G.payoff p (a • q₁ + b • q₂) = a * G.payoff p q₁ + b * G.payoff p q₂ := by
  simp only [payoff_eq_sum_mul', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  funext j
  ring

/-- `payoff` is continuous in the row player's strategy, for a fixed column strategy: a finite sum
    of `x ↦ x i * (constant)` terms, each continuous since coordinate projection is. -/
theorem continuous_payoff_left (y : J → ℝ) :
    Continuous (fun x : I → ℝ => G.payoff x y) := by
  simp only [payoff_eq_sum_mul]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

/-- `payoff` is continuous in the column player's strategy, for a fixed row strategy. Symmetric
    counterpart of `continuous_payoff_left`. -/
theorem continuous_payoff_right (x : I → ℝ) :
    Continuous (fun y : J → ℝ => G.payoff x y) := by
  simp only [payoff_eq_sum_mul']
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

/-- `payoff`, as a function of the row player's mixed strategy on the simplex, is convex --
    trivially, since (`payoff_smul_add_smul_left`) it is exactly linear, and linear functions are
    convex with equality rather than strict inequality. This is the hypothesis
    `Sion.exists_isSaddlePointOn` calls `hfy'`. -/
theorem convexOn_payoff_left (y : J → ℝ) :
    ConvexOn ℝ (stdSimplex ℝ I) (fun x => G.payoff x y) := by
  refine ⟨convex_stdSimplex ℝ I, ?_⟩
  intro p _ p' _ a b _ _ _
  simp only [smul_eq_mul]
  exact (G.payoff_smul_add_smul_left p p' y a b).le

/-- `payoff`, as a function of the column player's mixed strategy on the simplex, is concave --
    symmetric counterpart of `convexOn_payoff_left`, using `payoff_smul_add_smul_right`. This is
    the hypothesis `Sion.exists_isSaddlePointOn` calls `hfx'`. -/
theorem concaveOn_payoff_right (x : I → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ J) (fun y => G.payoff x y) := by
  refine ⟨convex_stdSimplex ℝ J, ?_⟩
  intro q _ q' _ a b _ _ _
  simp only [smul_eq_mul]
  exact (G.payoff_smul_add_smul_right x q q' a b).ge

/-- **The payoff.** The matrix game has a pair of optimal mixed strategies: a row strategy `p`
    that minimizes the payoff against the worst-case response, and a column strategy `q` that
    maximizes it against the worst-case response, with neither player able to improve by
    unilaterally deviating while the other holds still. This is von Neumann's minimax theorem for
    finite two-player zero-sum games, obtained here as a direct instance of Mathlib's
    `Sion.exists_isSaddlePointOn` -- every hypothesis it asks for (nonemptiness, convexity,
    compactness of the two simplices; continuity and quasiconvexity/quasiconcavity of the
    bilinear payoff in each argument) is supplied by the lemmas above, with no extra work beyond
    bilinearity of `payoff`. The one thing this proof leans on that hasn't been exercised
    elsewhere in this project yet: that Mathlib's ambient
    `IsTopologicalAddGroup`/`ContinuousSMul ℝ`-style instances for the Pi type `I → ℝ` (a
    finite-dimensional real vector space) resolve automatically -- expected to be routine, but
    genuinely unconfirmed until `lake build` says so. -/
theorem exists_optimal_strategies :
    ∃ p ∈ stdSimplex ℝ I, ∃ q ∈ stdSimplex ℝ J,
      (∀ p' ∈ stdSimplex ℝ I, G.payoff p q ≤ G.payoff p' q) ∧
      (∀ q' ∈ stdSimplex ℝ J, G.payoff p q' ≤ G.payoff p q) := by
  obtain ⟨p, hp, q, hq, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn
      (X := stdSimplex ℝ I) (Y := stdSimplex ℝ J) (f := G.payoff)
      (ne_X := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary I)⟩)
      (cX := convex_stdSimplex ℝ I) (kX := isCompact_stdSimplex ℝ I)
      (hfy := fun y _ => (G.continuous_payoff_left y).continuousOn.lowerSemicontinuousOn)
      (hfy' := fun y _ => G.convexOn_payoff_left y |>.quasiconvexOn)
      (cY := convex_stdSimplex ℝ J)
      (ne_Y := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary J)⟩)
      (kY := isCompact_stdSimplex ℝ J)
      (hfx := fun x _ => (G.continuous_payoff_right x).continuousOn.upperSemicontinuousOn)
      (hfx' := fun x _ => G.concaveOn_payoff_right x |>.quasiconcaveOn)
  exact ⟨p, hp, q, hq, fun p' hp' => hsaddle p' hp' q hq, fun q' hq' => hsaddle p hp q' hq'⟩

end MatrixGame

end Csg
