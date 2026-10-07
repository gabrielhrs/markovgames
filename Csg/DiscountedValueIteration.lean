/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Discounted

/-!
# Value iteration for discounted concurrent stochastic games

**Status: confirmed by a clean `lake build`.**

Everything `Csg/Discounted.lean`'s contraction makes free, plus the stopping rule. Combines what
the MDP line splits across two files, minus the policy half: `Mdp/ValueIteration.lean`'s
`vOpt`/convergence/error-bound block, and `Mdp/ValueIterationAlgorithm.lean` in full. No proof here
contains an idea that isn't already in those two files with `bellman` where this has `shapley` --
the mathematical content is entirely in `shapley_contracting`, and this file is the harvest.

Maps to the MDP line:

* `vOpt`, `vOpt_fixedPoint`, `exists_unique_fixedPoint_choose_eq_vOpt`, `shapley_iterate_tendsto`,
  `shapley_apriori_bound`, `shapley_aposteriori_bound` -- the identically-named facts in
  `Mdp/ValueIteration.lean` (with `bellman_` for `shapley_`).
* `stopCond`, `exists_stopCond`, `numIters`, `numIters_spec`, `valueIteration`,
  `valueIteration_error` -- `Mdp/ValueIterationAlgorithm.lean`, which in turn follows
  `Value_Iteration.thy`. `valueIteration` is defined in closed form via `Nat.find` rather than as
  a structural recursion with a separate termination proof, for the reason recorded there.

**`vOpt` goes through `ContractingWith.fixedPoint`, not through `exists_unique_fixedPoint`.** Same
reason as in `Mdp/ValueIteration.lean`: Mathlib's convergence and error-bound lemmas
(`tendsto_iterate_fixedPoint`, `apriori_`/`aposteriori_dist_iterate_fixedPoint_le`) are stated for
its own canonical `fixedPoint` construction and not for an arbitrary fixed point, so taking the
other entry point would mean transporting every one of them across a uniqueness argument.
`exists_unique_fixedPoint_choose_eq_vOpt` records that the two agree.

**Why the terminal theorem is an error bound and not an exactness result.** For an MDP this
distinction is a convenience: `bellman` is a `max` of affine functions, so for each of the finitely
many stationary policies the fixed-point equation is a rational linear system, and `vOpt` is
rational whenever the data is. For a concurrent game it is not. `MatrixGame.value` is not affine in
the payoff matrix -- for a 2x2 game with a mixed equilibrium it is the ratio
`(ad - bc) / (a + d - b - c)` -- and the stage payoffs are affine in the continuation, so
`v = shapley v` is a *polynomial* system. Its solutions are algebraic and in general irrational,
which is the standard state of affairs for concurrent games. So no rational iterate can ever equal
`vOpt`, there is no exactness result to aim for, and `valueIteration_error` is the strongest
statement available rather than a weaker stand-in for one. This is what makes the discount worth
having: the undiscounted operators converge (`ReachConverge.lean`) but with no rate, so they cannot
even bound the gap after finitely many steps.

**Not here:** anything executable. `shapley` is `noncomputable` -- it is a `MatrixGame.value`,
hence `Classical.choose` on Sion's theorem -- and so is everything below it, including
`valueIteration` itself, whose `Nat.find` additionally needs `Classical.decPred` because the
stopping predicate is an inequality on reals. Running this means recomputing the whole chain over
`ℚ` and relating it back, which belongs in the `Comp/` library per the project's split: `Mdp/` and
`Csg/` prove algorithms correct, `Comp/` runs them. Also not here: the policy side
(`Mdp/ValueIteration.lean`'s `Lpolicy` family and the `findPolicy`/`vi_policy` extraction its own
docstring flags as unported) -- for concurrent games the analogue is a pair of mixed stage
strategies rather than a deterministic action, and nothing downstream needs it yet.
-/

namespace Csg

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

namespace DiscountedCSG

variable (D : DiscountedCSG S A1 A2)

/-- The value vector of the discounted concurrent game: `shapley`'s unique fixed point, built via
    Mathlib's canonical `ContractingWith.fixedPoint` so that the convergence and error-bound lemmas
    below apply to it directly. Mirrors `DiscountedMDP.vOpt`.

    This is the object Shapley (1953) identifies as the game's value. What is proved here is that
    it exists and is unique; that it coincides with what the two coalitions can guarantee under
    optimal play over an infinite horizon is a separate statement, and not one this file makes. -/
noncomputable def vOpt : S → ℝ :=
  ContractingWith.fixedPoint D.shapley D.contractingWith_shapley

/-- `vOpt` really is a fixed point of `shapley` -- the Shapley equations hold at it. -/
theorem vOpt_fixedPoint : D.shapley D.vOpt = D.vOpt :=
  D.contractingWith_shapley.fixedPoint_isFixedPt

/-- `vOpt` and `Csg/Discounted.lean`'s `exists_unique_fixedPoint` witness are the same function:
    both are *the* unique fixed point of `shapley`, reached through different Mathlib entry
    points. -/
theorem exists_unique_fixedPoint_choose_eq_vOpt :
    D.exists_unique_fixedPoint.choose = D.vOpt :=
  D.contractingWith_shapley.fixedPoint_unique D.exists_unique_fixedPoint.choose_spec.1

/-- Iterating `shapley` from *any* starting vector converges to `vOpt` -- value iteration's
    correctness, straight out of `ContractingWith.tendsto_iterate_fixedPoint`. Note what the
    discount buys over `ReachConverge.lean`'s undiscounted analogue: there, convergence of the
    naive iterates needs `ωScottContinuous` and monotonicity and holds only from below, from a
    specific starting point; here it is unconditional in the starting point and comes with the two
    quantitative bounds below. -/
theorem shapley_iterate_tendsto (v : S → ℝ) :
    Filter.Tendsto (fun n => D.shapley^[n] v) Filter.atTop (nhds D.vOpt) :=
  D.contractingWith_shapley.tendsto_iterate_fixedPoint v

/-- A priori error bound: after `n` iterations from `v`, the distance to `vOpt` is bounded by the
    first step's movement, shrinking geometrically in `n`. Mirrors `bellman_apriori_bound`. -/
theorem shapley_apriori_bound (v : S → ℝ) (n : ℕ) :
    dist (D.shapley^[n] v) D.vOpt ≤ dist v (D.shapley v) * (D.lNN : ℝ) ^ n / (1 - D.lNN) :=
  D.contractingWith_shapley.apriori_dist_iterate_fixedPoint_le v n

/-- A posteriori error bound: the distance to `vOpt` after `n` iterations, bounded purely by how
    much the last step moved. This is the "stop once consecutive iterates are close" criterion, and
    the fact `stopCond` below is built to exploit. Mirrors `bellman_aposteriori_bound`. -/
theorem shapley_aposteriori_bound (v : S → ℝ) (n : ℕ) :
    dist (D.shapley^[n] v) D.vOpt ≤ dist (D.shapley^[n] v) (D.shapley^[n + 1] v) / (1 - D.lNN) :=
  D.contractingWith_shapley.aposteriori_dist_iterate_fixedPoint_le v n

/-- The per-`n` stopping predicate: consecutive iterates, `l`-scaled, are within `eps * (1 - l)`.
    Mirrors `DiscountedMDP.stopCond`, itself the inner predicate of `term_measure` in
    `Value_Iteration.thy`. -/
def stopCond (eps : ℝ) (v : S → ℝ) (n : ℕ) : Prop :=
  2 * D.l * dist (D.shapley^[n + 1] v) (D.shapley^[n] v) < eps * (1 - D.l)

/-- For `eps > 0`, some `n` satisfies `stopCond`: consecutive iterates both converge to `vOpt`
    (`shapley_iterate_tendsto`), so their distance tends to `0`, so the `l`-scaled distance
    eventually drops below the positive threshold `eps * (1 - l)`. Mirrors
    `DiscountedMDP.exists_stopCond`. -/
theorem exists_stopCond {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    ∃ n, D.stopCond eps v n := by
  have h1 : Filter.Tendsto (fun n => D.shapley^[n + 1] v) Filter.atTop (nhds D.vOpt) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr (D.shapley_iterate_tendsto v)
  have h2 : Filter.Tendsto (fun n => D.shapley^[n] v) Filter.atTop (nhds D.vOpt) :=
    D.shapley_iterate_tendsto v
  have hdist : Filter.Tendsto (fun n => dist (D.shapley^[n + 1] v) (D.shapley^[n] v))
      Filter.atTop (nhds 0) := by
    have := h1.dist h2
    rwa [dist_self] at this
  have hscaled : Filter.Tendsto
      (fun n => 2 * D.l * dist (D.shapley^[n + 1] v) (D.shapley^[n] v)) Filter.atTop (nhds 0) := by
    have := hdist.const_mul (2 * D.l)
    simpa using this
  have hpos : (0 : ℝ) < eps * (1 - D.l) := mul_pos heps (by linarith [D.l_lt_one])
  exact (hscaled.eventually_lt_const hpos).exists

/-- The least number of iterations after which `stopCond` holds, for `eps > 0`. The explicit
    `@Nat.find _ (Classical.decPred _)` idiom is needed for the same reason as in
    `Mdp/ValueIterationAlgorithm.lean`: instance search does not unfold the `stopCond` `def` far
    enough to find the `<` on reals underneath, so `DecidablePred (D.stopCond eps v)` has to be
    supplied classically rather than resolved. -/
noncomputable def numIters {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) : ℕ :=
  @Nat.find _ (Classical.decPred _) (D.exists_stopCond heps v)

theorem numIters_spec {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    D.stopCond eps v (D.numIters heps v) :=
  @Nat.find_spec _ (Classical.decPred _) (D.exists_stopCond heps v)

/-- Value iteration for a discounted concurrent game: apply `shapley` `numIters + 1` times. The
    `eps ≤ 0` branch mirrors the degenerate case in `Value_Iteration.thy` as ported in
    `Mdp/ValueIterationAlgorithm.lean` -- a single step, with no guarantee attached. -/
noncomputable def valueIteration (eps : ℝ) (v : S → ℝ) : S → ℝ :=
  if h : 0 < eps then D.shapley^[D.numIters h v + 1] v else D.shapley v

/-- **The payoff.** Once value iteration stops (`eps > 0`), its output is within `eps / 2` of the
    game's value. Mirrors `DiscountedMDP.valueIteration_error` and, through it,
    `value_iteration_error` in `Value_Iteration.thy`; the proof below is that one with `shapley`
    for `bellman`.

    This is the statement the whole discounted line exists to reach, and the one the undiscounted
    operators cannot state at all: `ReachConverge.lean` has convergence without a rate, so it can
    say the iterates approach the value but never that a particular iterate is within a given
    distance of it. See the module docstring on why an exactness result is not available here even
    in principle. -/
theorem valueIteration_error {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    2 * dist (D.valueIteration eps v) D.vOpt < eps := by
  have hval : D.valueIteration eps v = D.shapley^[D.numIters heps v + 1] v := by
    simp only [valueIteration, dite_eq_left heps]
  have hstop : 2 * D.l * dist (D.shapley^[D.numIters heps v + 1] v)
      (D.shapley^[D.numIters heps v] v) < eps * (1 - D.l) :=
    D.numIters_spec heps v
  set N := D.numIters heps v
  set w := D.shapley^[N] v with hw
  have hbw : D.shapley^[N + 1] v = D.shapley w := by
    rw [hw]; exact Function.iterate_succ_apply' D.shapley N v
  rw [hbw] at hval hstop
  rw [dist_comm (D.shapley w) w] at hstop
  rw [hval]
  have hlcast : (D.lNN : ℝ) = D.l := rfl
  have hbound : dist w D.vOpt ≤ dist w (D.shapley w) / (1 - D.l) := by
    have h0 := D.shapley_aposteriori_bound w 0
    simp only [Function.iterate_zero_apply, zero_add, Function.iterate_one] at h0
    rwa [hlcast] at h0
  have hopt_move : dist w D.vOpt * (1 - D.l) ≤ dist w (D.shapley w) := by
    rw [le_div_iff₀ (by linarith [D.l_lt_one] : (0 : ℝ) < 1 - D.l)] at hbound
    exact hbound
  have hcontract : dist (D.shapley w) D.vOpt ≤ D.l * dist w D.vOpt := by
    have h1 := D.shapley_contracting w D.vOpt
    rwa [D.vOpt_fixedPoint] at h1
  have step1 : (2 * D.l * dist w D.vOpt) * (1 - D.l) ≤ 2 * D.l * dist w (D.shapley w) := by
    nlinarith [hopt_move, D.l_nonneg]
  have step2 : (2 * D.l * dist w D.vOpt) * (1 - D.l) < eps * (1 - D.l) := by
    nlinarith [step1, hstop]
  have step3 : 2 * D.l * dist w D.vOpt < eps :=
    lt_of_mul_lt_mul_right step2 (by linarith [D.l_lt_one] : (0 : ℝ) ≤ 1 - D.l)
  linarith [hcontract, step3]

end DiscountedCSG

end Csg
