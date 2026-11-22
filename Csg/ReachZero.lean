/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.ReachOp
import Csg.QualitativeSure

/-!
# Where the reachability value is zero

**Status: confirmed by a clean `lake build`.** The reachability value `(C.reachOp goal hr).lfp` is
what the column player can force against a row player who minimises. This file identifies a set
of states on which it vanishes, in terms of the *row* player's sure one-step control `Pre1`
(`QualitativeSure.lean`).

**The statement.** Let `Z` be a set of states that contains no goal state and satisfies
`Z ⊆ C.Pre1 Z`: from every state of `Z` the row player has an action that keeps the play in `Z`
whatever the column player does. Then the reachability value is `0` on `Z`
(`reachOp_lfp_eq_zero_of_avoid`). The largest such `Z` is the row player's sure-safety region for
the complement of the goal, `C.G {t | ¬ goal t}`, so the value is `0` there
(`reachOp_lfp_eq_zero_of_mem_G`).

**The proof is one pre-fixed point.** Take any vector `u` that is `0` on `Z` and `1` off it. At a
state of `Z` the stage game against `u` has a row whose every entry is an expectation of `u` over
successors inside `Z`, so the row is zero and the stage value is at most `0`
(`stageValue_le_zero_of_mem_Pre1`, through `MatrixGame.value_le_of_col_le` at that pure row). Off
`Z` there is nothing to show, since `u` is `1` there. So the operator maps `u` below itself, and
the least fixed point lies below every such vector (`reachOp_lfp_le_of_avoid`).

**Why the general form is kept.** `reachOp_lfp_le_of_avoid` bounds the value by *any* vector that
is `0` on `Z` and `1` elsewhere, and asks only `Z ⊆ C.Pre1 Z`, not that `Z` be the largest such
set. That is the form a computation uses: a candidate `Z` is found by a sure-safety loop and then
only its closure under `Pre1` has to be checked, and the resulting vector is a starting point for
upper bounds on the value that is below the constant `1`.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The expectation of a continuation that vanishes on `Z`, over a transition supported inside
    `Z`, is `0`: every term has a zero weight or a zero value. -/
theorem expect_eq_zero_of_support_subset {Z : Set S} {v : S → ℝ} (hv : ∀ s' ∈ Z, v s' = 0)
    {s : S} {a1 : A1} {a2 : A2} (hsub : (C.K s a1 a2).support ⊆ Z) :
    C.expect s a1 a2 v = 0 := by
  unfold expect
  refine Finset.sum_eq_zero fun s' _ => ?_
  by_cases hs' : s' ∈ (C.K s a1 a2).support
  · rw [hv s' (hsub hs'), mul_zero]
  · have hK : C.K s a1 a2 s' = 0 := by
      by_contra hne
      exact hs' ((PMF.mem_support_iff _ _).mpr hne)
    rw [hK]
    simp

/-- At a state of `C.Pre1 Z`, the stage value against a continuation that vanishes on `Z` is at
    most `0`: the row action witnessing `Pre1` has a zero row, and playing it purely is a
    certificate (`MatrixGame.value_le_of_col_le`). -/
theorem stageValue_le_zero_of_mem_Pre1 (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {Z : Set S}
    {v : S → ℝ} (hv : ∀ s' ∈ Z, v s' = 0) {s : S} (hs : s ∈ C.Pre1 Z) :
    C.stageValue s v ≤ 0 := by
  obtain ⟨a1, ha1⟩ := hs
  have hA : ∀ a2, (C.stageGame s v).A a1 a2 = 0 := by
    intro a2
    change C.r s a1 a2 + C.expect s a1 a2 v = 0
    rw [hr s a1 a2, zero_add]
    exact C.expect_eq_zero_of_support_subset hv (ha1 a2)
  change (C.stageGame s v).value ≤ 0
  refine (C.stageGame s v).value_le_of_col_le (single_mem_stdSimplex ℝ a1) fun a2 => ?_
  have hsum : ∑ i, (Pi.single a1 (1 : ℝ) : A1 → ℝ) i * (C.stageGame s v).A i a2
      = (C.stageGame s v).A a1 a2 := by
    simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq', Finset.mem_univ]
  exact (hsum.trans (hA a2)).le

/-- **The bound.** If `Z` contains no goal state and `Z ⊆ C.Pre1 Z`, then the reachability value
    lies below every vector that is `0` on `Z` and `1` off it: such a vector is a pre-fixed point
    of `reachOp`. -/
theorem reachOp_lfp_le_of_avoid (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {Z : Set S} (hpre : Z ⊆ C.Pre1 Z)
    (hgoal : ∀ s ∈ Z, ¬ goal s) (u : S → Set.Icc (0 : ℝ) 1)
    (hZ : ∀ s ∈ Z, (u s : ℝ) = 0) (hnZ : ∀ s, s ∉ Z → (u s : ℝ) = 1) :
    (C.reachOp goal hr).lfp ≤ u := by
  apply (C.reachOp goal hr).lfp_le
  intro s
  by_cases hs : s ∈ Z
  · have h1 : (((C.reachOp goal hr) u s : ℝ)) = C.stageValue s (fun s' => (u s' : ℝ)) := by
      rw [C.reachOp_coe goal hr u s, ite_eq_right (hgoal s hs)]
    have h2 : C.stageValue s (fun s' => (u s' : ℝ)) ≤ 0 :=
      C.stageValue_le_zero_of_mem_Pre1 hr (fun s' hs' => hZ s' hs') (hpre hs)
    change (((C.reachOp goal hr) u s : ℝ)) ≤ (u s : ℝ)
    rw [h1, hZ s hs]
    exact h2
  · change (((C.reachOp goal hr) u s : ℝ)) ≤ (u s : ℝ)
    rw [hnZ s hs]
    exact ((C.reachOp goal hr) u s).2.2

/-- **The value is zero on a set the row player can stay in.** If `Z` contains no goal state and
    `Z ⊆ C.Pre1 Z`, the reachability value is `0` at every state of `Z`. -/
theorem reachOp_lfp_eq_zero_of_avoid (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {Z : Set S} (hpre : Z ⊆ C.Pre1 Z)
    (hgoal : ∀ s ∈ Z, ¬ goal s) {s : S} (hs : s ∈ Z) :
    ((C.reachOp goal hr).lfp s : ℝ) = 0 := by
  classical
  obtain ⟨u, hu0, hu1⟩ : ∃ u : S → Set.Icc (0 : ℝ) 1,
      (∀ t ∈ Z, (u t : ℝ) = 0) ∧ ∀ t, t ∉ Z → (u t : ℝ) = 1 := by
    refine ⟨fun t => if t ∈ Z then ⟨0, by norm_num, by norm_num⟩
      else ⟨1, by norm_num, by norm_num⟩, fun t ht => ?_, fun t ht => ?_⟩
    · simp [ht]
    · simp [ht]
  have hle : ((C.reachOp goal hr).lfp s : ℝ) ≤ (u s : ℝ) :=
    C.reachOp_lfp_le_of_avoid goal hr hpre hgoal u hu0 hu1 s
  exact le_antisymm (hle.trans_eq (hu0 s hs)) ((C.reachOp goal hr).lfp s).2.1

/-- **The value is zero on the row player's sure-safety region.** `C.G {t | ¬ goal t}` is the
    largest set that avoids the goal and is closed under `Pre1`, so the two hypotheses of
    `reachOp_lfp_eq_zero_of_avoid` are its fixed-point equation and `G_subset`. -/
theorem reachOp_lfp_eq_zero_of_mem_G (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} (hs : s ∈ C.G {t | ¬ goal t}) :
    ((C.reachOp goal hr).lfp s : ℝ) = 0 := by
  have hfix : C.GOrderHom {t | ¬ goal t} (C.G {t | ¬ goal t}) = C.G {t | ¬ goal t} :=
    (C.GOrderHom {t | ¬ goal t}).map_gfp
  refine C.reachOp_lfp_eq_zero_of_avoid goal hr (Z := C.G {t | ¬ goal t}) ?_ ?_ hs
  · intro t ht
    rw [← hfix] at ht
    exact ht.1
  · intro t ht
    exact C.G_subset _ ht

end CSG
end Csg
