/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Discounted Markov Decision Processes

**Status: `bellman_contracting` and `exists_unique_fixedPoint` both compile clean, zero
`sorry`s** — confirmed by `lake build`. Together these are Phase 1's core for the finite-state
case: the Bellman contraction (`contraction_ℒ` from `MDP_reward.thy`) and, via Mathlib's
`ContractingWith`, existence/uniqueness of the optimal value function (`ν_opt`) — the payoff for
using that machinery instead of reproving Banach by hand the way `MDP_reward.thy` has to (see
`is_contraction`/`banach'` there). Every Mathlib name involved (`PMF.tsum_coe`, `tsum_fintype`,
`dist_pi_le_iff`, `LipschitzWith.of_dist_le_mul`, `ContractingWith`, `edist_ne_top`, …) turned out
correct as guessed; every bug across three build rounds was homegrown proof-shape mismatches, not
wrong Mathlib API.

This is the Lean counterpart of the Isabelle/HOL AFP entries this project ports:

* `MDP-Rewards/MDP_disc.thy`      — the `discrete_MDP` locale (state/action spaces, kernel `K`)
* `MDP-Rewards/MDP_reward.thy`    — the `MDP_reward` locale (reward `r`, discount `l`, the
                                     Bellman operator `L`/`ℒ`, its contraction property)
* `MDP-Rewards/Bounded_Functions.thy` — the `bfun` type (`'a ⇒⇩b 'b`, bounded functions,
                                     a Banach space for any domain, no topology required)

Scope for this first file: **finite** state and action spaces only, matching the
`MDP_finite_type` / `MDP_PI_finite` layer in the Isabelle development (the layer the code-export
and the two evaluated examples actually run on). This sidesteps the general `bfun`/
`BoundedContinuousFunction` question for now, since on a `Fintype` every real-valued function is
automatically bounded and `Π i, ℝ` already gets a complete sup-norm space for free from Mathlib
(`Pi.normedAddCommGroup`, `Pi.completeSpace`) — no extra boundedness proof obligation, unlike the
Isabelle development which has to carry `bfun` because it *doesn't* restrict to finite state
spaces at this layer. Worth revisiting once Phase 2 needs the general case.
-/

namespace Mdp

/-- If two functions on a nonempty `Finset` are pointwise within `c` of each other, so are their
    `sup'`s. The general "`sup'` is 1-Lipschitz" fact the contraction proof below needs — proved
    from scratch (`Finset.le_sup'` / `Finset.sup'_le` only) rather than guessed at from a possibly
    wrong Mathlib name. Goes via the two one-sided bounds `sup' f ≤ sup' g + c` and
    `sup' g ≤ sup' f + c` rather than attacking `|sup' f - sup' g| ≤ c` directly, since
    `Finset.sup'_le`'s conclusion is a plain `≤`, not a subtraction. Corresponds to the role
    `le_SUP_diff'` plays in `contraction_ℒ` in `MDP_reward.thy`. -/
theorem abs_sup'_sub_sup'_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) (c : ℝ)
    (h : ∀ a ∈ s, |f a - g a| ≤ c) :
    |s.sup' hs f - s.sup' hs g| ≤ c := by
  have hfg : s.sup' hs f ≤ s.sup' hs g + c := by
    apply Finset.sup'_le
    intro a ha
    have hc := (abs_sub_le_iff.mp (h a ha)).1
    have hle := Finset.le_sup' g ha
    linarith
  have hgf : s.sup' hs g ≤ s.sup' hs f + c := by
    apply Finset.sup'_le
    intro a ha
    have hc := (abs_sub_le_iff.mp (h a ha)).2
    have hle := Finset.le_sup' f ha
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- A finite-state, finite-action discounted MDP.

Corresponds to `MDP_reward` (reward `r`, discount `l`) built on top of `discrete_MDP`
(state/action spaces, kernel `K`) in `MDP_reward.thy`. Unlike the Isabelle locale, action sets
are not yet restricted per-state (`A :: 's ⇒ 'a set` there) — every action is available in every
state here. Isabelle's per-state restriction is a separate locale layer (`MDP_act`); adding it is
a TODO once this base case compiles. -/
structure DiscountedMDP (S A : Type*) [Fintype S] [Fintype A] [Nonempty A] where
  /-- Transition kernel: `K s a` is the distribution over next states after taking action `a`
      in state `s`. Corresponds to `K :: 's × 'a ⇒ 's pmf`, curried here. -/
  K : S → A → PMF S
  /-- Reward for taking action `a` in state `s`. Corresponds to `r :: 's × 'a ⇒ real`; no
      explicit boundedness hypothesis needed here since `S × A` is finite. -/
  r : S → A → ℝ
  /-- Discount factor. Corresponds to `l :: real`. -/
  l : ℝ
  l_nonneg : 0 ≤ l
  l_lt_one : l < 1

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

namespace DiscountedMDP

variable (M : DiscountedMDP S A)

/-- Expected value of `v` one step after taking action `a` in state `s`.

Corresponds to the transition operator `\<P>\<^sub>1` in `MDP_reward.thy` (there defined for a whole
decision rule via `push_exp (K_st d)`; here specialised to a single state-action pair, which is
the more primitive notion the Isabelle development builds `\<P>\<^sub>1` out of via `K_st d s = d s
\<bind> (\<lambda>a. K (s,a))`).

This turned out to type-check as a direct `∑ s', (M.K s a s').toReal * v s'` — `PMF S` coerces to
`S → ℝ≥0∞` and `ENNReal.toReal` gets us back to `ℝ`. Confirmed by `lake build`, not just hoped
for; still worth a `simp`/`norm_num` sanity check that this sum actually equals 1 when `v = 1`
before trusting it in a real proof. -/
noncomputable def expect (s : S) (a : A) (v : S → ℝ) : ℝ :=
  ∑ s', (M.K s a s').toReal * v s'

/-- The Bellman optimality operator: for each state, the best expected immediate reward plus
    discounted continuation value, maximised over actions.

    Corresponds to `\<L> v s = (\<Squnion>d \<in> D\<^sub>R. L d v s)` in `MDP_reward.thy`
    (there a supremum over *randomised* decision rules; here, since `A` is finite and this is the
    single-step deterministic-action version, a `Finset.max'`/`Finset.sup'` over actions directly
    — matching the *equivalent* characterisation
    `\<L>\<^sub>b v s = (\<Squnion>a \<in> A s. L\<^sub>a a v s)` proved in
    `MDP_ord`/`MDP_PI_finite` for the finite case, which is the one this file
    should actually start from). -/
noncomputable def bellman (v : S → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => M.r s a + M.l * M.expect s a v)

/-- The kernel really is a probability distribution once you convert its `ℝ≥0∞` masses to `ℝ`:
    they still sum to `1`. Isolated as its own lemma because it's the one step in the contraction
    proof that has to reach into `PMF`'s own API (`tsum_coe`) rather than pure `Finset`/`abs`
    manipulation. `PMF.tsum_coe`, `tsum_fintype`, and `PMF.apply_ne_top` all confirmed by
    `lake build`, as-named. -/
theorem expect_kernel_sum_one (s : S) (a : A) :
    ∑ s' : S, (M.K s a s').toReal = 1 := by
  have h1 : ∑' s' : S, M.K s a s' = 1 := (M.K s a).tsum_coe
  have h2 : ∑' s' : S, M.K s a s' = ∑ s' : S, M.K s a s' := tsum_fintype _
  have h3 : (∑ s' : S, M.K s a s').toReal = ∑ s' : S, (M.K s a s').toReal :=
    ENNReal.toReal_sum fun s' _ => PMF.apply_ne_top (M.K s a) s'
  rw [← h3, ← h2, h1, ENNReal.toReal_one]

/-- One step of `expect` moves `l`-scaled by at most `dist v u`: the PMF-weighted average of two
    functions is within `dist v u` of each other, since the weights are nonnegative and sum to
    `1` (`expect_kernel_sum_one`). Corresponds to non-expansiveness of `\<P>\<^sub>1 d` in the
    Isabelle proof of `contraction_ℒ`. -/
theorem abs_expect_sub_le (s : S) (a : A) (v u : S → ℝ) :
    |M.expect s a v - M.expect s a u| ≤ dist v u := by
  have hrw : M.expect s a v - M.expect s a u
      = ∑ s' : S, (M.K s a s').toReal * (v s' - u s') := by
    simp only [expect, ← Finset.sum_sub_distrib]
    congr 1; ext s'; ring
  rw [hrw]
  calc |∑ s' : S, (M.K s a s').toReal * (v s' - u s')|
      ≤ ∑ s' : S, |(M.K s a s').toReal * (v s' - u s')| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s' : S, (M.K s a s').toReal * |v s' - u s'| := by
        simp [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ s' : S, (M.K s a s').toReal * dist v u := by
        apply Finset.sum_le_sum
        intro s' _
        have hv : |v s' - u s'| ≤ dist v u := by
          rw [← Real.dist_eq]
          exact dist_le_pi_dist v u s'
        exact mul_le_mul_of_nonneg_left hv ENNReal.toReal_nonneg
    _ = dist v u := by rw [← Finset.sum_mul, M.expect_kernel_sum_one s a, one_mul]

/-- **The theorem Phase 1 exists to port.** The Bellman operator is an `l`-Lipschitz contraction
    in sup distance. Corresponds to `contraction_ℒ` in `MDP_reward.thy`:

    `dist (\<L>\<^sub>b v) (\<L>\<^sub>b u) \<le> l * dist v u`

    Built from `abs_sup'_sub_sup'_le` (sup is 1-Lipschitz) applied at each state, plus
    `abs_expect_sub_le` (the transition step is `1`-Lipschitz, so scaling by `l` makes the whole
    per-action term `l`-Lipschitz in `v`), then glued across states via `dist_pi_le_iff`. -/
theorem bellman_contracting (v u : S → ℝ) :
    dist (M.bellman v) (M.bellman u) ≤ M.l * dist v u := by
  rw [dist_pi_le_iff (mul_nonneg M.l_nonneg dist_nonneg)]
  intro s
  rw [Real.dist_eq]
  apply abs_sup'_sub_sup'_le _ _ _ _ _
  intro a _
  have hbound : |M.expect s a v - M.expect s a u| ≤ dist v u := M.abs_expect_sub_le s a v u
  calc |(M.r s a + M.l * M.expect s a v) - (M.r s a + M.l * M.expect s a u)|
      = M.l * |M.expect s a v - M.expect s a u| := by
        rw [show (M.r s a + M.l * M.expect s a v) - (M.r s a + M.l * M.expect s a u)
              = M.l * (M.expect s a v - M.expect s a u) from by ring,
            abs_mul, abs_of_nonneg M.l_nonneg]
    _ ≤ M.l * dist v u := mul_le_mul_of_nonneg_left hbound M.l_nonneg

/-- `M.l` repackaged as an `NNReal`, the form `LipschitzWith`/`ContractingWith` want their
    constant in. `M.l_nonneg` is exactly the side condition `NNReal.mk`/`⟨_, _⟩` needs. -/
noncomputable def lNN (M : DiscountedMDP S A) : NNReal := ⟨M.l, M.l_nonneg⟩

/-- `bellman_contracting` restated in the `LipschitzWith` vocabulary (`edist`-based, not
    `dist`-based) that `ContractingWith` is built on. `LipschitzWith.of_dist_le_mul` is the
    bridging lemma from the plain-`dist` inequality we already have to the official definition —
    least certain name in this block, alongside `ContractingWith` itself. -/
theorem lipschitzWith_bellman : LipschitzWith M.lNN M.bellman :=
  LipschitzWith.of_dist_le_mul fun v u => M.bellman_contracting v u

/-- The Bellman operator is a genuine contraction: Lipschitz with constant `< 1`. -/
theorem contractingWith_bellman : ContractingWith M.lNN M.bellman :=
  ⟨by exact_mod_cast M.l_lt_one, M.lipschitzWith_bellman⟩

/-- **The payoff.** `M.bellman` has exactly one fixed point — corresponds to
    `\<L>\<^sub>b_conv`/`\<nu>\<^sub>b_opt` in `MDP_reward.thy`, but where Isabelle has to build
    its own Banach fixed point argument (`is_contraction`, `banach'`) from scratch, this falls out
    of `ContractingWith.exists_fixedPoint` (existence, from completeness of `S → ℝ` as a
    `Fintype`-indexed Pi type) plus a five-line direct argument for uniqueness (two fixed points
    would each be a contraction-factor away from the other, forcing distance `0`). `(0 : S → ℝ)`
    as the iteration basepoint is arbitrary — any starting point works. Every Mathlib name here
    (`LipschitzWith.of_dist_le_mul`, `ContractingWith`, `exists_fixedPoint`'s 4-way return,
    `edist_ne_top`) confirmed by `lake build` as written; the one bug was `∃!`'s uniqueness clause
    unfolding as `w = v`, not `v = w` — flipped which side `by_contra`'s hypothesis needed
    `.symm`ed. -/
theorem exists_unique_fixedPoint : ∃! v : S → ℝ, M.bellman v = v := by
  obtain ⟨v, hv_fix, -, -⟩ := M.contractingWith_bellman.exists_fixedPoint 0 (edist_ne_top _ _)
  refine ⟨v, hv_fix, fun w hw_fix => ?_⟩
  by_contra hne
  have hpos : 0 < dist v w := dist_pos.mpr (Ne.symm hne)
  have hshrink : dist v w ≤ M.l * dist v w := by
    have := M.bellman_contracting v w
    rwa [hv_fix, hw_fix] at this
  nlinarith [M.l_lt_one]

end DiscountedMDP

end Mdp
