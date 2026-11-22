/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.ReachOp

/-!
# Capping a pre-fixed vector of the reachability operator

**Status: confirmed by a clean `lake build`.** A vector `u` with `C.reachOp goal hr u ≤ u` lies
above the reachability value, the least fixed point being below every pre-fixed point. This file
gives two ways of lowering such a vector that keep it pre-fixed, and so keep it an upper bound.

**Capping on a set.** Let `X` be a set of states with no goal state in it and `c ≥ 0` a number.
Suppose that at every state `s` of `X` the row player has a mixed action `p` such that each column
action `a2` is of one of two kinds: against every row action in the support of `p` it keeps the
play inside `X`, or it pays at most `c` against `p` under `u`. Let `w` be `u` capped at `c` on
`X`, that is `min (u s) c` at the states of `X` and `u s` elsewhere. Then `w` is pre-fixed
(`reachOp_cap_le`), and the reachability value lies below it (`reachOp_lfp_le_of_cap`).

Nothing else is asked of `X`. It need not be an end component, and `c` need not be the least
number with the property.

**The proof.** Where `w = u`, monotonicity is enough: the operator at `w` is below the operator at
`u`, which is below `u`. At a state of `X` where the cap bites, `p` is a certificate that the
stage value against `w` is at most `c` (`MatrixGame.value_le_of_col_le`). A column of the first
kind has all its successors under `p` in `X`, where `w ≤ c`, so its expectation is at most `c`
(`expect_le_of_support_le`). A column of the second kind pays at most `c` under `u`, and `w ≤ u`.

**Lowering between a step and the vector.** If `C.reachOp goal hr u ≤ w ≤ u` then `w` is
pre-fixed (`reachOp_le_of_between`). So the result of a step may be rounded up, as long as it
stays below the vector the step started from.

`Comp/ReachDeflate.lean` searches for upper vectors by alternating these two moves.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The expectation of a continuation that is at most `c ≥ 0` on the support of the transition
    is at most `c`: off the support the weight is zero, and the weights sum to at most `1`. -/
theorem expect_le_of_support_le {v : S → ℝ} {c : ℝ} (hc : 0 ≤ c) {s : S} {a1 : A1} {a2 : A2}
    (hv : ∀ s' ∈ (C.K s a1 a2).support, v s' ≤ c) : C.expect s a1 a2 v ≤ c := by
  unfold expect
  calc ∑ s' : S, (C.K s a1 a2 s').toReal * v s'
      ≤ ∑ s' : S, (C.K s a1 a2 s').toReal * c := by
        refine Finset.sum_le_sum fun s' _ => ?_
        by_cases hs' : s' ∈ (C.K s a1 a2).support
        · exact mul_le_mul_of_nonneg_left (hv s' hs') ENNReal.toReal_nonneg
        · have hK : C.K s a1 a2 s' = 0 := by
            by_contra hne
            exact hs' ((PMF.mem_support_iff _ _).mpr hne)
          rw [hK]
          simp
    _ = (∑ s' : S, (C.K s a1 a2 s').toReal) * c := by rw [Finset.sum_mul]
    _ ≤ 1 * c := mul_le_mul_of_nonneg_right (C.sum_toReal_K_le_one s a1 a2) hc
    _ = c := one_mul c

/-- **Lowering between a step and the vector keeps the vector pre-fixed.** If one step of the
    operator from `u` is below `w` and `w` is below `u`, then the operator maps `w` below itself:
    `F w ≤ F u ≤ w`. -/
theorem reachOp_le_of_between (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {u w : S → Set.Icc (0 : ℝ) 1}
    (hstep : C.reachOp goal hr u ≤ w) (hwu : w ≤ u) : C.reachOp goal hr w ≤ w :=
  ((C.reachOp goal hr).monotone hwu).trans hstep

/-- **Capping a pre-fixed vector on a set keeps it pre-fixed.** `u` is pre-fixed, `X` contains no
    goal state, and `w` is `u` capped at `c ≥ 0` on `X`. At every state of `X` there is a row
    strategy `p` against which each column either keeps the play inside `X`, whichever row action
    of the support of `p` is drawn, or pays at most `c` under `u`. Then the operator maps `w`
    below itself. -/
theorem reachOp_cap_le (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {X : Set S} (hgoal : ∀ s ∈ X, ¬ goal s)
    {c : ℝ} (hc : 0 ≤ c) (u w : S → Set.Icc (0 : ℝ) 1)
    (hu : C.reachOp goal hr u ≤ u)
    (hwX : ∀ s ∈ X, (w s : ℝ) = min (u s : ℝ) c) (hwnX : ∀ s, s ∉ X → w s = u s)
    (hexit : ∀ s ∈ X, ∃ p ∈ stdSimplex ℝ A1, ∀ a2,
      (∀ a1, p a1 ≠ 0 → (C.K s a1 a2).support ⊆ X) ∨
        ∑ a1, p a1 * C.expect s a1 a2 (fun s' => (u s' : ℝ)) ≤ c) :
    C.reachOp goal hr w ≤ w := by
  have hwu : w ≤ u := by
    intro s
    by_cases hs : s ∈ X
    · have h1 : (w s : ℝ) ≤ (u s : ℝ) := (hwX s hs).le.trans (min_le_left _ _)
      exact h1
    · exact (hwnX s hs).le
  have hwu' : ∀ s', (w s' : ℝ) ≤ (u s' : ℝ) := fun s' => hwu s'
  have hwc : ∀ s' ∈ X, (w s' : ℝ) ≤ c := fun s' hs' => (hwX s' hs').le.trans (min_le_right _ _)
  intro s
  have hmono : (C.reachOp goal hr) w s ≤ u s :=
    ((C.reachOp goal hr).monotone hwu s).trans (hu s)
  by_cases hs : s ∈ X
  · by_cases hcap : (u s : ℝ) ≤ c
    · -- the cap does not bite: `w s = u s`
      have hws : (w s : ℝ) = (u s : ℝ) := (hwX s hs).trans (min_eq_left hcap)
      have h1 : ((C.reachOp goal hr) w s : ℝ) ≤ (u s : ℝ) := hmono
      exact h1.trans_eq hws.symm
    · -- the cap bites: `w s = c`, and `p` certifies that the stage value is at most `c`
      have hws : (w s : ℝ) = c := (hwX s hs).trans (min_eq_right (not_le.mp hcap).le)
      have hval : ((C.reachOp goal hr) w s : ℝ) = C.stageValue s (fun s' => (w s' : ℝ)) := by
        rw [C.reachOp_coe goal hr w s, ite_eq_right (hgoal s hs)]
      obtain ⟨p, hp, hcols⟩ := hexit s hs
      have hA : ∀ a1 a2, (C.stageGame s (fun s' => (w s' : ℝ))).A a1 a2
          = C.expect s a1 a2 (fun s' => (w s' : ℝ)) := by
        intro a1 a2
        change C.r s a1 a2 + C.expect s a1 a2 (fun s' => (w s' : ℝ)) = _
        rw [hr s a1 a2, zero_add]
      have hle : C.stageValue s (fun s' => (w s' : ℝ)) ≤ c := by
        change (C.stageGame s (fun s' => (w s' : ℝ))).value ≤ c
        refine (C.stageGame s (fun s' => (w s' : ℝ))).value_le_of_col_le hp fun a2 => ?_
        rcases hcols a2 with hst | hlv
        · -- the column stays in `X` against the support of `p`
          calc ∑ a1, p a1 * (C.stageGame s (fun s' => (w s' : ℝ))).A a1 a2
              ≤ ∑ a1, p a1 * c := by
                refine Finset.sum_le_sum fun a1 _ => ?_
                by_cases hp0 : p a1 = 0
                · simp [hp0]
                · have hE : C.expect s a1 a2 (fun s' => (w s' : ℝ)) ≤ c :=
                    C.expect_le_of_support_le hc fun s' hs' => hwc s' (hst a1 hp0 hs')
                  exact mul_le_mul_of_nonneg_left ((hA a1 a2).trans_le hE) (hp.1 a1)
            _ = c := by rw [← Finset.sum_mul, hp.2, one_mul]
        · -- the column pays at most `c` under `u`, and `w ≤ u`
          calc ∑ a1, p a1 * (C.stageGame s (fun s' => (w s' : ℝ))).A a1 a2
              ≤ ∑ a1, p a1 * C.expect s a1 a2 (fun s' => (u s' : ℝ)) := by
                refine Finset.sum_le_sum fun a1 _ => ?_
                have hE : C.expect s a1 a2 (fun s' => (w s' : ℝ))
                    ≤ C.expect s a1 a2 (fun s' => (u s' : ℝ)) := C.expect_mono hwu'
                exact mul_le_mul_of_nonneg_left ((hA a1 a2).trans_le hE) (hp.1 a1)
            _ ≤ c := hlv
      have h2 : ((C.reachOp goal hr) w s : ℝ) ≤ c := hval.le.trans hle
      exact h2.trans_eq hws.symm
  · exact hmono.trans (hwnX s hs).ge

/-- **The reachability value lies below a capped pre-fixed vector.** `reachOp_cap_le` and
    `OrderHom.lfp_le`. -/
theorem reachOp_lfp_le_of_cap (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {X : Set S} (hgoal : ∀ s ∈ X, ¬ goal s)
    {c : ℝ} (hc : 0 ≤ c) (u w : S → Set.Icc (0 : ℝ) 1)
    (hu : C.reachOp goal hr u ≤ u)
    (hwX : ∀ s ∈ X, (w s : ℝ) = min (u s : ℝ) c) (hwnX : ∀ s, s ∉ X → w s = u s)
    (hexit : ∀ s ∈ X, ∃ p ∈ stdSimplex ℝ A1, ∀ a2,
      (∀ a1, p a1 ≠ 0 → (C.K s a1 a2).support ⊆ X) ∨
        ∑ a1, p a1 * C.expect s a1 a2 (fun s' => (u s' : ℝ)) ≤ c) :
    (C.reachOp goal hr).lfp ≤ w :=
  (C.reachOp goal hr).lfp_le (C.reachOp_cap_le goal hr hgoal hc u w hu hwX hwnX hexit)

end CSG
end Csg
