/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mdp.ValueIteration

/-!
# The value iteration algorithm — Phase 2b

**Status: drafted, not yet run through `lake build`.** Ports `value_iteration` itself from
`Value_Iteration.thy` — the piece Phase 2a deliberately left out because its termination argument
in Isabelle (a `LEAST n` measure, shown to strictly decrease) isn't a corollary of anything already
proved.

Rather than reproduce that as a Lean well-founded recursion (`termination_by`/`decreasing_by`,
mirroring `Least_Suc_less`), this file sidesteps it. Isabelle's `value_iteration eps v` unwinds, by
induction on the number of recursive calls, to exactly `bellman^[N+1] v` where `N` is the *least*
number of iterations after which consecutive iterates are within the stopping threshold — so it's
defined here directly in that closed form via `Nat.find`, rather than as a structurally-recursive
function whose termination has to be proved separately. Same mathematical object, reached without
wrestling Lean's well-founded recursion machinery. Existence of `N` — the fact `Nat.find` needs to
fire at all — comes from `bellman_iterate_tendsto` (Phase 2a): consecutive iterates converge to
the same limit `vOpt`, so their distance tends to `0`, so it eventually drops below any positive
threshold.

Maps to `Value_Iteration.thy`:

* `stopCond`, `exists_stopCond`, `numIters` — `term_measure`'s inner predicate and the `LEAST n`
  itself, restated as an existence proof plus a direct `Nat.find`.
* `valueIteration` — `value_iteration`.
* `valueIteration_error` — `value_iteration_error`, via the same route as
  `dist_\<L>\<^sub>b_opt_eps` there: combine the stopping condition with `dist_fixedPoint_le`
  (`contraction_\<L>_dist`, reused here as `bellman_aposteriori_bound _ 0`) and the contraction
  property applied at the fixed point (`contraction_\<L>[of v \<nu>\<^sub>b_opt]`).

Not yet ported: `find_policy`/`vi_policy`/`vi_policy_opt` (extracting an ε-optimal *policy* from
`valueIteration`'s output). Phase 2a's `findPolicy`/`bellman_eq_Lpolicy_findPolicy` already give the
pieces this needs; wiring them together is a short follow-up once this file builds clean.

**Status: `lake build` clean, zero `sorry`s.** Two build rounds got there:

* **Round 1**: `Real.decidableLT` does *not* auto-resolve `DecidablePred (M.stopCond eps v)` for
  `Nat.find` — instance search doesn't unfold the `stopCond` `def` far enough to see the `<`
  underneath, unlike a bare `dite (0 < eps)` (no wrapping `def`), which resolved fine on its own.
  Fixed with the explicit `@Nat.find _ (Classical.decPred _) h` idiom from
  `Mathlib/GroupTheory/Rank.lean`. Every other guessed Mathlib name in the file —
  `Filter.tendsto_add_atTop_iff_nat`, `Filter.Tendsto.dist`, `Filter.Tendsto.const_mul`,
  `Filter.Tendsto.eventually_lt_const`, `Function.iterate_succ_apply'`, `le_div_iff₀`,
  `lt_of_mul_lt_mul_right` — compiled as written.
* **Round 2**: `hlcast` (`(M.lNN : ℝ) = M.l`) really is `rfl`, confirmed by the build's own
  unreachable-tactic warnings on the `norm_cast`/`simp` fallbacks that had been hedging against
  round 1's `simp [DiscountedMDP.lNN, NNReal.coe_mk]` not closing the goal — narrowed to plain
  `rfl` once that was known. -/

namespace Mdp

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

namespace DiscountedMDP

variable (M : DiscountedMDP S A)

/-- The per-`n` stopping predicate value iteration checks for: consecutive iterates, `l`-scaled,
    are within `eps * (1 - l)`. Matches the inner predicate of `term_measure` in
    `Value_Iteration.thy`. -/
def stopCond (eps : ℝ) (v : S → ℝ) (n : ℕ) : Prop :=
  2 * M.l * dist (M.bellman^[n + 1] v) (M.bellman^[n] v) < eps * (1 - M.l)

/-- For `eps > 0`, some `n` satisfies `stopCond`: consecutive iterates `bellman^[n+1] v` and
    `bellman^[n] v` both converge to `vOpt` (Phase 2a's `bellman_iterate_tendsto`), so their
    distance tends to `0`, so `2 * l * dist(...)` (also tending to `0`) eventually drops below the
    positive threshold `eps * (1 - l)`. -/
theorem exists_stopCond {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    ∃ n, M.stopCond eps v n := by
  have h1 : Filter.Tendsto (fun n => M.bellman^[n + 1] v) Filter.atTop (nhds M.vOpt) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr (M.bellman_iterate_tendsto v)
  have h2 : Filter.Tendsto (fun n => M.bellman^[n] v) Filter.atTop (nhds M.vOpt) :=
    M.bellman_iterate_tendsto v
  have hdist : Filter.Tendsto (fun n => dist (M.bellman^[n + 1] v) (M.bellman^[n] v))
      Filter.atTop (nhds 0) := by
    have := h1.dist h2
    rwa [dist_self] at this
  have hscaled : Filter.Tendsto (fun n => 2 * M.l * dist (M.bellman^[n + 1] v) (M.bellman^[n] v))
      Filter.atTop (nhds 0) := by
    have := hdist.const_mul (2 * M.l)
    simpa using this
  have hpos : (0 : ℝ) < eps * (1 - M.l) := mul_pos heps (by linarith [M.l_lt_one])
  exact (hscaled.eventually_lt_const hpos).exists

/-- The least number of iterations after which `stopCond` holds, for `eps > 0`. Corresponds to
    `term_measure (eps, v)` in `Value_Iteration.thy`. -/
noncomputable def numIters {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) : ℕ :=
  @Nat.find _ (Classical.decPred _) (M.exists_stopCond heps v)

theorem numIters_spec {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    M.stopCond eps v (M.numIters heps v) :=
  @Nat.find_spec _ (Classical.decPred _) (M.exists_stopCond heps v)

/-- Value iteration: apply `bellman` `numIters + 1` times. For `eps ≤ 0`, matches Isabelle's
    degenerate case (the `∨ eps ≤ 0` disjunct fires immediately): a single `bellman`
    application, no convergence guarantee. Corresponds to `value_iteration` in
    `Value_Iteration.thy` — see the module docstring for why this is a direct definition rather
    than a structural recursion. -/
noncomputable def valueIteration (eps : ℝ) (v : S → ℝ) : S → ℝ :=
  if h : 0 < eps then M.bellman^[M.numIters h v + 1] v else M.bellman v

/-- **The payoff.** Once `value_iteration` terminates (`eps > 0`), its output is within `eps / 2`
    of optimal. Corresponds to `value_iteration_error` in `Value_Iteration.thy`. -/
theorem valueIteration_error {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    2 * dist (M.valueIteration eps v) M.vOpt < eps := by
  have hval : M.valueIteration eps v = M.bellman^[M.numIters heps v + 1] v := by
    simp only [valueIteration, dif_pos heps]
  have hstop : 2 * M.l * dist (M.bellman^[M.numIters heps v + 1] v)
      (M.bellman^[M.numIters heps v] v) < eps * (1 - M.l) :=
    M.numIters_spec heps v
  set N := M.numIters heps v
  set w := M.bellman^[N] v with hw
  have hbw : M.bellman^[N + 1] v = M.bellman w := by
    rw [hw]; exact Function.iterate_succ_apply' M.bellman N v
  rw [hbw] at hval hstop
  rw [dist_comm (M.bellman w) w] at hstop
  rw [hval]
  have hlcast : (M.lNN : ℝ) = M.l := rfl
  have hbound : dist w M.vOpt ≤ dist w (M.bellman w) / (1 - M.l) := by
    have h0 := M.bellman_aposteriori_bound w 0
    simp only [Function.iterate_zero_apply, zero_add, Function.iterate_one] at h0
    rwa [hlcast] at h0
  have hopt_move : dist w M.vOpt * (1 - M.l) ≤ dist w (M.bellman w) := by
    rw [le_div_iff₀ (by linarith [M.l_lt_one] : (0 : ℝ) < 1 - M.l)] at hbound
    exact hbound
  have hcontract : dist (M.bellman w) M.vOpt ≤ M.l * dist w M.vOpt := by
    have h1 := M.bellman_contracting w M.vOpt
    rwa [M.vOpt_fixedPoint] at h1
  have step1 : (2 * M.l * dist w M.vOpt) * (1 - M.l) ≤ 2 * M.l * dist w (M.bellman w) := by
    nlinarith [hopt_move, M.l_nonneg]
  have step2 : (2 * M.l * dist w M.vOpt) * (1 - M.l) < eps * (1 - M.l) := by
    nlinarith [step1, hstop]
  have step3 : 2 * M.l * dist w M.vOpt < eps :=
    lt_of_mul_lt_mul_right step2 (by linarith [M.l_lt_one] : (0 : ℝ) ≤ 1 - M.l)
  linarith [hcontract, step3]

end DiscountedMDP

end Mdp
