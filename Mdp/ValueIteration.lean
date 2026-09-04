/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mdp.Basic
import Mathlib.Data.Finset.Max

/-!
# Value iteration for discounted MDPs — Phase 2a

**Status: confirmed by a clean `lake build`, zero `sorry`s (Phase 2a) — see `PHASE0-NOTES.md`.**
This status line had gone stale (it said "drafted, not yet run through `lake build`" long after
the build had actually gone clean); corrected in place rather than treated as still-open work.
Ports the parts of `Value_Iteration.thy` that come essentially for free once `Basic.lean`'s
`bellman_contracting` / `contractingWith_bellman` are in hand, plus stationary policy evaluation
(needed to state what "value iteration converges to an ε-optimal *policy*", not just an
ε-optimal *value*, means).

What this file does **not** yet do: translate `value_iteration` itself, the recursive function in
`Value_Iteration.thy` that repeatedly applies `\<L>\<^sub>b` until
`2 * l * dist v (\<L>\<^sub>b v) < eps * (1 - l)`. Its Isabelle termination proof is a genuinely
new argument (a `LEAST n` measure, shown to strictly decrease via `Least_Suc_less`), not a
corollary of anything already proved — it's its own increment, next after this one builds clean.

Maps to `Value_Iteration.thy` as follows:

* `vOpt`, `vOpt_fixedPoint` — the value function used implicitly throughout the Isabelle file as
  `\<nu>\<^sub>b_opt`.
* `bellman_iterate_tendsto` — `dist_\<L>\<^sub>b_tendsto`, the convergence fact the termination
  proof and `value_iteration_error` both lean on.
* `bellman_apriori_bound` / `bellman_aposteriori_bound` — the quantitative content behind
  `contraction_\<L>_dist` / `dist_\<L>\<^sub>b_opt_eps` / `value_iteration_error`, though stated
  per-iteration-count `n` rather than via the `eps`-driven stopping rule; reconciling the two is
  part of translating `value_iteration` itself.
* `Lpolicy`, `Lpolicy_contracting`, `value` — the policy evaluation operator `L d` from
  `MDP_reward.thy` and its fixed point `\<nu>\<^sub>b d` (`mk_stationary_det d` +
  `\<nu>\<^sub>b`), specialised to deterministic stationary policies `d : S → A`.
* `findPolicy`, `findPolicy_spec`, `bellman_eq_Lpolicy_findPolicy` — `find_policy` and
  `is_arg_max_find_policy` / `\<L>\<^sub>b_eq_argmax_L\<^sub>a`: extracting a policy that
  realises the `sup` in `bellman` at a given value function.

**Least-certain call in this file, confirmed correct by the clean build**:
`ContractingWith.fixedPoint f hf` takes `f` as an *explicit* argument alongside
`hf : ContractingWith K f` (confirmed by reading `Mathlib/Topology/MetricSpace/Contracting.lean`
directly rather than guessed at — see the `variable (f) in` annotation right before its `def`),
so it's applied here as `ContractingWith.fixedPoint M.bellman M.contractingWith_bellman` rather
than via dot notation, to sidestep any dot-notation argument-order surprise. -/

namespace Mdp

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

namespace DiscountedMDP

variable (M : DiscountedMDP S A)

/-- The optimal value function, built via Mathlib's canonical `ContractingWith.fixedPoint` rather
    than the basepoint-`exists_fixedPoint` construction `Basic.lean`'s `exists_unique_fixedPoint`
    uses. Needed in this form because the convergence/error-bound lemmas below are only stated for
    `ContractingWith.fixedPoint`, not for an arbitrary fixed point. -/
noncomputable def vOpt : S → ℝ :=
  ContractingWith.fixedPoint M.bellman M.contractingWith_bellman

/-- `vOpt` really is a fixed point of `bellman`. -/
theorem vOpt_fixedPoint : M.bellman M.vOpt = M.vOpt :=
  M.contractingWith_bellman.fixedPoint_isFixedPt

/-- `vOpt` and `Basic.lean`'s `exists_unique_fixedPoint` witness are the same value function: both
    are *the* (unique) fixed point of `bellman`, just reached via different Mathlib entry
    points. -/
theorem exists_unique_fixedPoint_choose_eq_vOpt :
    M.exists_unique_fixedPoint.choose = M.vOpt :=
  M.contractingWith_bellman.fixedPoint_unique M.exists_unique_fixedPoint.choose_spec.1

/-- Iterating `bellman` from *any* starting value function converges to `vOpt`. This is the
    mathematical content behind value iteration's correctness — the Isabelle side proves the same
    fact as `dist_\<L>\<^sub>b_tendsto` and leans on it directly in `Value_Iteration.thy`'s
    termination argument. Here it falls straight out of `ContractingWith.tendsto_iterate_fixedPoint`
    applied to `contractingWith_bellman`; no new proof content. -/
theorem bellman_iterate_tendsto (v : S → ℝ) :
    Filter.Tendsto (fun n => M.bellman^[n] v) Filter.atTop (nhds M.vOpt) :=
  M.contractingWith_bellman.tendsto_iterate_fixedPoint v

/-- A priori error bound: after `n` iterations from `v`, distance to `vOpt` is bounded by the
    *first* step's movement, shrinking geometrically in `n`. Quantitative cousin of
    `contraction_\<L>_dist` in `Value_Iteration.thy`. -/
theorem bellman_apriori_bound (v : S → ℝ) (n : ℕ) :
    dist (M.bellman^[n] v) M.vOpt ≤ dist v (M.bellman v) * (M.lNN : ℝ) ^ n / (1 - M.lNN) :=
  M.contractingWith_bellman.apriori_dist_iterate_fixedPoint_le v n

/-- A posteriori error bound: distance to `vOpt` after `n` iterations, bounded purely by how much
    the *last* step moved — the "stop once consecutive iterates are close" criterion real
    implementations use, and the shape `Value_Iteration.thy`'s `term_measure` is built from. -/
theorem bellman_aposteriori_bound (v : S → ℝ) (n : ℕ) :
    dist (M.bellman^[n] v) M.vOpt ≤ dist (M.bellman^[n] v) (M.bellman^[n + 1] v) / (1 - M.lNN) :=
  M.contractingWith_bellman.aposteriori_dist_iterate_fixedPoint_le v n

/-- The Bellman operator for a *fixed* deterministic stationary policy `d : S → A`: no `sup`
    over actions, just `d`'s own choice at each state. Corresponds to `L d v s` specialised to
    `d = mk_dec_det d'` in `MDP_reward.thy` (`L\<^sub>a (d s) v s`, unfolded). -/
noncomputable def Lpolicy (d : S → A) (v : S → ℝ) (s : S) : ℝ :=
  M.r s (d s) + M.l * M.expect s (d s) v

/-- `Lpolicy d` is an `l`-Lipschitz contraction, same proof shape as `bellman_contracting` but
    simpler: no `sup`, so no need for `abs_sup'_sub_sup'_le` — the per-state bound from
    `abs_expect_sub_le` transfers directly. -/
theorem Lpolicy_contracting (d : S → A) (v u : S → ℝ) :
    dist (M.Lpolicy d v) (M.Lpolicy d u) ≤ M.l * dist v u := by
  rw [dist_pi_le_iff (mul_nonneg M.l_nonneg dist_nonneg)]
  intro s
  rw [Real.dist_eq]
  have hbound : |M.expect s (d s) v - M.expect s (d s) u| ≤ dist v u :=
    M.abs_expect_sub_le s (d s) v u
  calc |M.Lpolicy d v s - M.Lpolicy d u s|
      = M.l * |M.expect s (d s) v - M.expect s (d s) u| := by
        rw [show M.Lpolicy d v s - M.Lpolicy d u s
              = M.l * (M.expect s (d s) v - M.expect s (d s) u) from by
              simp only [Lpolicy]; ring,
            abs_mul, abs_of_nonneg M.l_nonneg]
    _ ≤ M.l * dist v u := mul_le_mul_of_nonneg_left hbound M.l_nonneg

theorem lipschitzWith_Lpolicy (d : S → A) : LipschitzWith M.lNN (M.Lpolicy d) :=
  LipschitzWith.of_dist_le_mul fun v u => M.Lpolicy_contracting d v u

theorem contractingWith_Lpolicy (d : S → A) : ContractingWith M.lNN (M.Lpolicy d) :=
  ⟨by exact_mod_cast M.l_lt_one, M.lipschitzWith_Lpolicy d⟩

/-- The value of following the stationary deterministic policy `d` forever: `Lpolicy d`'s unique
    fixed point. Corresponds to `\<nu>\<^sub>b (mk_stationary_det d)` in `MDP_reward.thy`. -/
noncomputable def value (d : S → A) : S → ℝ :=
  ContractingWith.fixedPoint (M.Lpolicy d) (M.contractingWith_Lpolicy d)

theorem value_fixedPoint (d : S → A) : M.Lpolicy d (M.value d) = M.value d :=
  (M.contractingWith_Lpolicy d).fixedPoint_isFixedPt

/-- Every state has a best action for value function `v`: `A` is a nonempty `Fintype`, so the
    per-action value `M.r s a + M.l * M.expect s a v` attains a maximum over `Finset.univ`. -/
theorem exists_argmax (v : S → ℝ) (s : S) :
    ∃ a ∈ (Finset.univ : Finset A), ∀ a' ∈ (Finset.univ : Finset A),
      M.r s a' + M.l * M.expect s a' v ≤ M.r s a + M.l * M.expect s a v :=
  Finset.exists_max_image Finset.univ (fun a => M.r s a + M.l * M.expect s a v) Finset.univ_nonempty

/-- A policy that's greedy w.r.t. `v`: at each state, an action realising the `sup` in
    `bellman v s`. Corresponds to `find_policy` in `Value_Iteration.thy`
    (`arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s)`), specialised to the finite, per-state-total
    action set used throughout this port. -/
noncomputable def findPolicy (v : S → ℝ) (s : S) : A :=
  (M.exists_argmax v s).choose

theorem findPolicy_spec (v : S → ℝ) (s : S) (a' : A) :
    M.r s a' + M.l * M.expect s a' v
      ≤ M.r s (M.findPolicy v s) + M.l * M.expect s (M.findPolicy v s) v :=
  (M.exists_argmax v s).choose_spec.2 a' (Finset.mem_univ a')

/-- `findPolicy v` really does realise the `sup` in `bellman v` at every state: applying `Lpolicy`
    with the greedy policy gives back exactly `bellman`. Corresponds to
    `is_arg_max_find_policy` / `\<L>\<^sub>b_eq_argmax_L\<^sub>a` in `Value_Iteration.thy`, and is
    the bridge that will let `vi_policy_opt`-style theorems (value iteration's extracted policy is
    ε-optimal) transfer once `value_iteration` itself is ported. -/
theorem bellman_eq_Lpolicy_findPolicy (v : S → ℝ) (s : S) :
    M.bellman v s = M.Lpolicy (M.findPolicy v) v s := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    exact M.findPolicy_spec v s a
  · exact Finset.le_sup' (fun a => M.r s a + M.l * M.expect s a v)
      (Finset.mem_univ (M.findPolicy v s))

end DiscountedMDP

end Mdp
