/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mdp.ValueIteration

/-!
# Policy iteration — Phase 2c

**Status: drafted, not yet run through `lake build`.** Ports the whole of `Policy_Iteration.thy`
for the finite-state/finite-action case: policy improvement never hurts, no improvement possible
means already optimal, the algorithm reaches a fixed point in finitely many steps, and that fixed
point's value is exactly `vOpt`.

Isabelle proves the first, hardest piece (`policy_eval_mon`) via a
Neumann-series/`blinfun`-inverse argument (`lemma_6_1_2_b`, `inv_norm_le'`), because its Banach
fixed-point machinery at that layer doesn't hand it a monotone-convergence shortcut. This port
takes a different route, available precisely *because* Phase 1/2a went through Mathlib's
`ContractingWith` instead of reproving Banach by hand: `Lpolicy d'` is monotone (`Lpolicy_mono`,
a nonneg-weighted-sum argument, same shape as `abs_expect_sub_le`), a policy-improvement step only
ever raises the value at the start (`Lpolicy_policyStep_ge`, from the improvement bridge lemma
plus `bellman`'s `sup'` being `≥` any one term), and a monotone operator applied to a rising start
keeps rising under iteration, converging (Phase 2a machinery) to something `≥` the start
(`Monotone.ge_of_tendsto`). No Neumann series needed anywhere in this file.

The termination argument is handled the same way Phase 2b handled `value_iteration`'s: rather
than a native Lean `termination_by`/`decreasing_by` mirroring Isabelle's well-founded recursion
on a strict order over the finite decision-rule set, `policyIteration` is defined directly in
closed form via `Nat.find` on an existence proof (`exists_policyStep_fixedPoint`) built from
pigeonhole (`Finite.exists_ne_map_eq_of_infinite`, applicable because `S → A` is finite via
`Pi.finite` — no `DecidableEq` needed, resolving an earlier-flagged concern) plus the same
monotone-convergence machinery used for `value_policyStep_ge`.

Maps to `Policy_Iteration.thy`:

* `policyImprove` — `policy_improvement`: keep `d s` if it's already a maximiser, else switch to
  a genuine maximiser (`findPolicy`, Phase 2a). The "prefer to keep" behaviour is what lets
  `eval_eq_imp_policy_eq` conclude `d = policy_step d` from "no improvement possible", rather
  than just "some equally-good policy".
* `policyStep` — `policy_step`.
* `Lpolicy_policyImprove_eq_bellman` — `is_arg_max_find_policy` /
  `\<L>\<^sub>b_eq_argmax_L\<^sub>a`, specialised to the improved policy: applying `Lpolicy` with
  the improved policy reproduces `bellman` exactly, whichever branch fired.
* `value_policyStep_ge` — `policy_eval_mon`.
* `eval_eq_imp_policy_eq` — the converse direction: if a step leaves the value unchanged, the
  policy itself hadn't changed. Needed so the loop is *allowed* to stop exactly when it does.
* `exists_policyStep_fixedPoint`, `policyIterNum`, `policyIteration` — the termination argument
  and `policy_iteration` itself, reached via `Nat.find` rather than Isabelle's `termination`
  proof (`finite_D𝔻`/`finite_acyclic_wf`).
* `policyStep_fixedPoint_value_eq_vOpt`, `policy_iteration_correct` — a
  `policyStep`-fixed policy's value is a `bellman`-fixed point too, hence (Banach uniqueness,
  Phase 2a) exactly `vOpt`.

Modified Policy Iteration and the splitting methods remain optional stretch, not prerequisites
for Goal 02 (CSGs).

**Least certain parts of this file**, all confirmed against the actual Mathlib source rather than
guessed: `Ne.lt_or_gt (h : a ≠ b) : a < b ∨ b < a` (`Mathlib/Order/Basic.lean`, not the guessed
`Ne.lt_or_lt`); `Finite.exists_ne_map_eq_of_infinite {α β} [Infinite α] [Finite β]
(f : α → β) : ∃ x y, x ≠ y ∧ f x = f y` (`Mathlib/Data/Fintype/Pigeonhole.lean`); and that
`Pi.finite`
(`Mathlib/Data/Finite/Prod.lean`) needs only `[Finite α] [∀ a, Finite (β a)]`, no `DecidableEq`,
so `Finite (S → A)` resolves automatically from the ambient `[Fintype S] [Fintype A]` with no
extra work. The pigeonhole-to-fixed-point squeeze in `exists_policyStep_fixedPoint` (monotone
value sequence + two equal iterates forces every intermediate value equal) hasn't been exercised
elsewhere in the project and is the single riskiest proof shape in this file. -/

namespace Mdp

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

namespace DiscountedMDP

variable (M : DiscountedMDP S A)

/-- Improve `d` at value function `v`: keep `d s` if it already realises the `sup` in
    `bellman v s`, otherwise switch to a genuine maximiser. Corresponds to `policy_improvement`
    in `Policy_Iteration.thy`; the "prefer to keep" branch is what lets `eval_eq_imp_policy_eq`
    conclude `d = policy_step d` from "no improvement possible", rather than just "some
    equally-good policy". -/
noncomputable def policyImprove (d : S → A) (v : S → ℝ) (s : S) : A :=
  if M.r s (d s) + M.l * M.expect s (d s) v = M.bellman v s then d s else M.findPolicy v s

/-- Applying `Lpolicy` with the improved policy reproduces `bellman` exactly, whichever branch of
    `policyImprove` fired: if `d s` was kept, that's because its own value already equals the
    `sup`; if it was switched, `bellman_eq_Lpolicy_findPolicy` (Phase 2a) gives it directly.
    Corresponds to `is_arg_max_find_policy` / `\<L>\<^sub>b_eq_argmax_L\<^sub>a` in
    `Value_Iteration.thy`, specialised to the improved policy. -/
theorem Lpolicy_policyImprove_eq_bellman (d : S → A) (v : S → ℝ) :
    M.Lpolicy (M.policyImprove d v) v = M.bellman v := by
  funext s
  change M.r s (M.policyImprove d v s) + M.l * M.expect s (M.policyImprove d v s) v
      = M.bellman v s
  unfold policyImprove
  split_ifs with h
  · exact h
  · exact (M.bellman_eq_Lpolicy_findPolicy v s).symm

/-- One step of policy iteration: evaluate `d`, then improve it against its own value.
    Corresponds to `policy_step` in `Policy_Iteration.thy`. -/
noncomputable def policyStep (d : S → A) : S → A :=
  M.policyImprove d (M.value d)

/-- `Lpolicy d` is monotone: a nonneg-weighted average (`expect`) of a pointwise-larger function
    is pointwise larger, and scaling by `M.l ≥ 0` and adding the (unchanged) reward preserve that.
    Same shape as `abs_expect_sub_le`, with `≤` in place of `abs`. New in this file — not a
    corollary of anything in Phase 1/2a/2b. -/
theorem Lpolicy_mono (d : S → A) : Monotone (M.Lpolicy d) := by
  intro v w hvw
  have hexpect : ∀ s a, M.expect s a v ≤ M.expect s a w := by
    intro s a
    unfold expect
    apply Finset.sum_le_sum
    intro s' _
    exact mul_le_mul_of_nonneg_left (hvw s') ENNReal.toReal_nonneg
  intro s
  change M.Lpolicy d v s ≤ M.Lpolicy d w s
  unfold Lpolicy
  have hstep : M.l * M.expect s (d s) v ≤ M.l * M.expect s (d s) w :=
    mul_le_mul_of_nonneg_left (hexpect s (d s)) M.l_nonneg
  linarith [hstep]

/-- Iterating `Lpolicy d` from any starting value function converges to `d`'s own value function.
    Exact proof shape of Phase 2a's `bellman_iterate_tendsto`, specialised to a fixed policy
    instead of the `sup`-taking Bellman operator; new in this file since Phase 2a never needed it
    for a general policy. -/
theorem Lpolicy_iterate_tendsto (d : S → A) (v : S → ℝ) :
    Filter.Tendsto (fun n => (M.Lpolicy d)^[n] v) Filter.atTop (nhds (M.value d)) :=
  (M.contractingWith_Lpolicy d).tendsto_iterate_fixedPoint v

/-- If a monotone operator's first application from `v` doesn't decrease it, iterating from `v`
    stays monotone. Extracted from `value_policyStep_ge`'s proof (where it was inlined for the
    specific case `v := M.value d`) since `eval_eq_imp_policy_eq` needs the exact same induction
    again, for the same operator but a different purpose. -/
theorem Lpolicy_iterate_mono (d : S → A) {v : S → ℝ} (hv : v ≤ M.Lpolicy d v) :
    Monotone (fun n => (M.Lpolicy d)^[n] v) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa using hv
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact M.Lpolicy_mono d ih

/-- A policy-improvement step, applied once to `d`'s own value function, never decreases it
    pointwise: either `d s` was already a maximiser (so `Lpolicy d`'s value at `s` already
    equals the `sup`, by `value_fixedPoint`), or it was switched to one (so the `sup` at `s` is
    realised exactly, which is automatically `≥` `d`'s own value there since `bellman`'s `sup'`
    is `≥` any one term, in particular `d s`'s). Extracted from `value_policyStep_ge`'s proof
    since `eval_eq_imp_policy_eq` needs it again to rebuild the same monotone-convergence
    argument. -/
theorem Lpolicy_policyStep_ge (d : S → A) :
    M.value d ≤ M.Lpolicy (M.policyStep d) (M.value d) := by
  have heq : M.Lpolicy (M.policyStep d) (M.value d) = M.bellman (M.value d) :=
    M.Lpolicy_policyImprove_eq_bellman d (M.value d)
  rw [heq]
  intro s
  have hle : M.Lpolicy d (M.value d) s ≤ M.bellman (M.value d) s := by
    change M.r s (d s) + M.l * M.expect s (d s) (M.value d) ≤ M.bellman (M.value d) s
    exact Finset.le_sup' (fun a => M.r s a + M.l * M.expect s a (M.value d))
      (Finset.mem_univ (d s))
  rwa [M.value_fixedPoint d] at hle

/-- **The payoff.** Policy improvement never makes the value worse. Corresponds to
    `policy_eval_mon` in `Policy_Iteration.thy`, but reached via monotone convergence
    (`Lpolicy_mono` + `Monotone.ge_of_tendsto`) rather than Isabelle's Neumann-series argument —
    see the module docstring. -/
theorem value_policyStep_ge (d : S → A) : M.value d ≤ M.value (M.policyStep d) := by
  have hmono := M.Lpolicy_iterate_mono (M.policyStep d) (M.Lpolicy_policyStep_ge d)
  have htend := M.Lpolicy_iterate_tendsto (M.policyStep d) (M.value d)
  simpa using hmono.ge_of_tendsto htend 0

/-- The converse of `value_policyStep_ge`: if a policy-improvement step leaves the value
    unchanged, the policy itself was already unchanged. Corresponds to `eval_eq_imp_policy_eq` in
    `Policy_Iteration.thy`. Needed so the iteration is *allowed* to stop exactly when consecutive
    values agree, not just permitted to keep going.

    Proof: if `d ≠ policyStep d`, pick a witness state `s₀` where they differ. `policyStep` only
    ever differs from `d` at a state by *switching away* from `d`'s own action there (the "prefer
    to keep" branch of `policyImprove`), which only happens when `d s₀`'s own value is *strictly*
    below the `sup` realised by `bellman`. Feeding that strict inequality into the same
    monotone-convergence machinery as `value_policyStep_ge`, evaluated one step in instead of at
    the start, gives `M.value d s₀ < M.value (policyStep d) s₀` — contradicting the hypothesis
    that the two values agree everywhere. -/
theorem eval_eq_imp_policy_eq (d : S → A) (h : M.value d = M.value (M.policyStep d)) :
    d = M.policyStep d := by
  by_contra hne
  obtain ⟨s₀, hs₀⟩ := Function.ne_iff.mp hne
  have hnotkeep :
      M.r s₀ (d s₀) + M.l * M.expect s₀ (d s₀) (M.value d)
        ≠ M.bellman (M.value d) s₀ := by
    intro hkeep
    apply hs₀
    change d s₀ = M.policyImprove d (M.value d) s₀
    unfold policyImprove
    rw [if_pos hkeep]
  have hle :
      M.r s₀ (d s₀) + M.l * M.expect s₀ (d s₀) (M.value d) ≤ M.bellman (M.value d) s₀ :=
    Finset.le_sup' (fun a => M.r s₀ a + M.l * M.expect s₀ a (M.value d))
      (Finset.mem_univ (d s₀))
  have hlt :
      M.r s₀ (d s₀) + M.l * M.expect s₀ (d s₀) (M.value d) < M.bellman (M.value d) s₀ :=
    lt_of_le_of_ne hle hnotkeep
  have hval_eq : M.Lpolicy d (M.value d) s₀ = M.value d s₀ :=
    congrFun (M.value_fixedPoint d) s₀
  have hval : M.value d s₀ < M.bellman (M.value d) s₀ := by
    change M.r s₀ (d s₀) + M.l * M.expect s₀ (d s₀) (M.value d) = M.value d s₀ at hval_eq
    rwa [hval_eq] at hlt
  have hstep1 : M.Lpolicy (M.policyStep d) (M.value d) s₀ = M.bellman (M.value d) s₀ :=
    congrFun (M.Lpolicy_policyImprove_eq_bellman d (M.value d)) s₀
  rw [← hstep1] at hval
  have hmono := M.Lpolicy_iterate_mono (M.policyStep d) (M.Lpolicy_policyStep_ge d)
  have htend := M.Lpolicy_iterate_tendsto (M.policyStep d) (M.value d)
  have hge : M.Lpolicy (M.policyStep d) (M.value d) ≤ M.value (M.policyStep d) := by
    simpa using hmono.ge_of_tendsto htend 1
  have hfin : M.value d s₀ < M.value (M.policyStep d) s₀ := lt_of_lt_of_le hval (hge s₀)
  rw [h] at hfin
  exact lt_irrefl _ hfin

/-- The value sequence along repeated policy improvement is monotone: each `policyStep` only
    ever helps (`value_policyStep_ge`), applied along the iteration. -/
theorem value_policyStep_iterate_mono (d : S → A) :
    Monotone (fun n => M.value ((M.policyStep)^[n] d)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Function.iterate_succ_apply']
  exact M.value_policyStep_ge ((M.policyStep)^[n] d)

/-- Iterating `policyStep` from any starting policy reaches a fixed point after finitely many
    steps. Corresponds to the termination argument behind `policy_iteration` in
    `Policy_Iteration.thy` (there, well-founded recursion on a strict order over the finite
    decision-rule set); reached here via pigeonhole instead.

    `S → A` is finite (`Pi.finite`), so the sequence `n ↦ (policyStep)^[n] d` — infinitely
    many "pigeons" (`ℕ`) into finitely many "holes" — must repeat: some `p < q` has
    `(policyStep)^[p] d = (policyStep)^[q] d`. The value sequence is monotone
    (`value_policyStep_iterate_mono`) and agrees at `p` and `q`, so by squeeze it's constant from
    `p` to `p + 1` too; `eval_eq_imp_policy_eq` then promotes that value-equality to the policies
    at `p` and `p + 1` being equal, i.e. a `policyStep` fixed point at index `p`. -/
theorem exists_policyStep_fixedPoint (d : S → A) :
    ∃ n, M.policyStep ((M.policyStep)^[n] d) = (M.policyStep)^[n] d := by
  have hval := M.value_policyStep_iterate_mono d
  have key : ∀ p q : ℕ, p < q →
      (M.policyStep)^[p] d = (M.policyStep)^[q] d →
      ∃ n, M.policyStep ((M.policyStep)^[n] d) = (M.policyStep)^[n] d := by
    intro p q hpq heqpq
    have hvaleq : M.value ((M.policyStep)^[p] d) = M.value ((M.policyStep)^[q] d) :=
      congrArg M.value heqpq
    have h1 : M.value ((M.policyStep)^[p] d) ≤ M.value ((M.policyStep)^[p + 1] d) :=
      hval (by omega)
    have h2 : M.value ((M.policyStep)^[p + 1] d) ≤ M.value ((M.policyStep)^[q] d) :=
      hval (by omega)
    have h2' : M.value ((M.policyStep)^[p + 1] d) ≤ M.value ((M.policyStep)^[p] d) := by
      rw [hvaleq]; exact h2
    have heq2 : M.value ((M.policyStep)^[p] d) = M.value ((M.policyStep)^[p + 1] d) :=
      le_antisymm h1 h2'
    have hstep : M.policyStep ((M.policyStep)^[p] d) = (M.policyStep)^[p + 1] d :=
      (Function.iterate_succ_apply' M.policyStep p d).symm
    have heq2' :
        M.value ((M.policyStep)^[p] d) = M.value (M.policyStep ((M.policyStep)^[p] d)) := by
      rw [hstep]; exact heq2
    exact ⟨p, (M.eval_eq_imp_policy_eq _ heq2').symm⟩
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n => (M.policyStep)^[n] d)
  rcases hij.lt_or_gt with hlt | hgt
  · exact key i j hlt heq
  · exact key j i hgt heq.symm

/-- The least number of `policyStep` iterations from `d` after which a fixed point is reached.
    Corresponds to the measure `policy_iteration`'s Isabelle `termination` proof shows strictly
    decreases, restated here directly as a `Nat.find`, mirroring `numIters` in Phase 2b. -/
noncomputable def policyIterNum (d : S → A) : ℕ :=
  @Nat.find _ (Classical.decPred _) (M.exists_policyStep_fixedPoint d)

theorem policyIterNum_spec (d : S → A) :
    M.policyStep ((M.policyStep)^[M.policyIterNum d] d) = (M.policyStep)^[M.policyIterNum d] d :=
  @Nat.find_spec _ (Classical.decPred _) (M.exists_policyStep_fixedPoint d)

/-- Policy iteration: repeatedly apply `policyStep` until it stops changing anything. Corresponds
    to `policy_iteration` in `Policy_Iteration.thy` — see the module docstring for why this is a
    direct definition rather than a structural recursion. -/
noncomputable def policyIteration (d : S → A) : S → A :=
  (M.policyStep)^[M.policyIterNum d] d

/-- `policyIteration d` really is a fixed point of `policyStep`. -/
theorem policyIteration_isFixedPt (d : S → A) :
    M.policyStep (M.policyIteration d) = M.policyIteration d :=
  M.policyIterNum_spec d

/-- If `d` is already a fixed point of `policyStep`, its value function is already the global
    optimum. Corresponds to the heart of `policy_iteration_correct` in `Policy_Iteration.thy`: a
    policy admitting no further improvement has already-optimal value, because its value function
    is then a fixed point of `bellman` itself — which, by Banach (Phase 2a's `vOpt`), has only
    one. -/
theorem policyStep_fixedPoint_value_eq_vOpt (d : S → A) (hd : M.policyStep d = d) :
    M.value d = M.vOpt := by
  have h1 : M.Lpolicy (M.policyStep d) (M.value d) = M.bellman (M.value d) :=
    M.Lpolicy_policyImprove_eq_bellman d (M.value d)
  rw [hd] at h1
  have hbellman : M.bellman (M.value d) = M.value d := by
    rw [← h1]
    exact M.value_fixedPoint d
  exact M.contractingWith_bellman.fixedPoint_unique hbellman

/-- **The final payoff.** Policy iteration, run from any starting policy, produces a policy whose
    value is exactly optimal. Corresponds to `policy_iteration_correct` in
    `Policy_Iteration.thy`. -/
theorem policy_iteration_correct (d : S → A) : M.value (M.policyIteration d) = M.vOpt :=
  M.policyStep_fixedPoint_value_eq_vOpt (M.policyIteration d) (M.policyIteration_isFixedPt d)

end DiscountedMDP

end Mdp
