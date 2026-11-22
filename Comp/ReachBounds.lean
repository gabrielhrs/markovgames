/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ReachTrace

/-!
# Reachability bounds from one-sided checks

**Status: confirmed by a clean `lake build`.** `Comp/ReachTrace.lean` checks a run by pinning every
step exactly: each state's next value comes with both players' strategies. A bound needs less.
This file checks a lower run with the column player's strategies alone and an upper vector with
the row player's alone, and both through inequalities.

**Below.** Write `F` for the reachability operator. If `v` is below the reachability value and
`w ≤ F v`, then `w` is below it too (`OrderHom.le_lfp_of_le_step`). `ReachLower` is the checkable
form of `w ≤ F v`: at each state off the target, a column strategy that secures at least `w s` in
the stage game against `v`. So a lower run may round each computed value down, and its vectors
need not be iterates.

**Above.** Any `u` with `F u ≤ u` is above the value, the least fixed point being below every
pre-fixed point (`OrderHom.lfp_le`). `ReachUpper` at `v = w = u` is the checkable form: `u` is `1`
on the target, and at each other state a row strategy holds every column to at most `u s` in the
stage game against `u`. That is one check of one vector. No run stands behind it, and it asks
nothing about where the vector came from.

**The answer.** `answers_reach_of_bounds` puts a lower run from `0` and a pre-fixed upper vector
together as an answer to `Objective.reach`.

**The bounds `0 ≤ w s ≤ 1`** are part of both predicates. A rounded value is not the operator's
output, so its membership in `[0, 1]` does not follow from the step and is checked with it.

**Finding a small pre-fixed point** is not this file's business. Iterating the operator from above
yields pre-fixed points, and they approach the value only where that iteration converges to it.
Elsewhere a smaller vector has to be proposed by other means, and whatever proposes it needs no
proof of its own: `ReachUpper` is what establishes the bound. `Comp/ReachDeflate.lean` is one such
proposer.
-/

namespace Comp

open Csg

namespace CsgQ

/-! ## One state, one side -/

section Stage

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

/-- At a non-goal state, an upper certificate on the rational stage game bounds the operator's
    value there from above. The one-sided form of `reachOp_coe_of_valueCert`. -/
theorem reachOp_coe_le_of_upperCert (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) {s : S} {t : ℚ}
    {p : A1 → ℚ} (hs : ¬ goal s) (hc : (G.reachGameQ s v).UpperCert t p) :
    ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      ≤ ((t : ℚ) : ℝ) := by
  rw [CSG.reachOp_coe, ite_eq_right hs, reachGameQ_stageValue G h hr0 s v h0 h1]
  exact MatrixGameQ.value_le_of_upperCert hc

/-- At a non-goal state, a lower certificate on the rational stage game bounds the operator's
    value there from below. -/
theorem le_reachOp_coe_of_lowerCert (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) {s : S} {t : ℚ}
    {q : A2 → ℚ} (hs : ¬ goal s) (hc : (G.reachGameQ s v).LowerCert t q) :
    ((t : ℚ) : ℝ)
      ≤ ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ)) := by
  rw [CSG.reachOp_coe, ite_eq_right hs, reachGameQ_stageValue G h hr0 s v h0 h1]
  exact MatrixGameQ.le_value_of_lowerCert hc

end Stage

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

/-! ## The two checks -/

/-- **A lower step.** `w` lies in `[0, 1]`, and at every state off the target the column strategy
    `q s` secures at least `w s` in the reachability stage game against `v`. Nothing is asked at a
    target state beyond the bounds, the operator being `1` there. -/
def ReachLower (G : CsgQ S A1 A2) (target : Finset S) (v w : S → ℚ) (q : S → A2 → ℚ) : Prop :=
  ∀ s, 0 ≤ w s ∧ w s ≤ 1 ∧ (s ∉ target → (G.reachGameQ s v).LowerCert (w s) (q s))

instance (G : CsgQ S A1 A2) (target : Finset S) (v w : S → ℚ) (q : S → A2 → ℚ) :
    Decidable (G.ReachLower target v w q) := by
  unfold ReachLower
  infer_instance

/-- **An upper step.** `w` lies in `[0, 1]` and is `1` on the target, and at every other state the
    row strategy `p s` holds every column to at most `w s` in the reachability stage game against
    `v`. With `v = w` this says that the vector is a pre-fixed point of the operator. -/
def ReachUpper (G : CsgQ S A1 A2) (target : Finset S) (v w : S → ℚ) (p : S → A1 → ℚ) : Prop :=
  ∀ s, 0 ≤ w s ∧ w s ≤ 1 ∧ (s ∈ target → w s = 1) ∧
    (s ∉ target → (G.reachGameQ s v).UpperCert (w s) (p s))

instance (G : CsgQ S A1 A2) (target : Finset S) (v w : S → ℚ) (p : S → A1 → ℚ) :
    Decidable (G.ReachUpper target v w p) := by
  unfold ReachUpper
  infer_instance

/-- A checked lower step lies below the operator's output, as vectors of the carrier. -/
theorem le_reachOp_of_reachLower (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S) {v w : S → ℚ} {q : S → A2 → ℚ}
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (k0 : ∀ s, 0 ≤ w s) (k1 : ∀ s, w s ≤ 1)
    (hstep : G.ReachLower target v w q) :
    castIcc w k0 k1
      ≤ ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)) (castIcc v h0 h1) := by
  intro s
  by_cases hs : s ∈ target
  · have hw : ((w s : ℚ) : ℝ) ≤ 1 := by exact_mod_cast k1 s
    exact hw.trans_eq (reachOp_coe_of_goal G h hrf (· ∈ target) v h0 h1 hs).symm
  · exact le_reachOp_coe_of_lowerCert G h hrf (· ∈ target) v h0 h1 hs ((hstep s).2.2 hs)

/-- A checked upper step lies above the operator's output, as vectors of the carrier. -/
theorem reachOp_le_of_reachUpper (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S) {v w : S → ℚ} {p : S → A1 → ℚ}
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (k0 : ∀ s, 0 ≤ w s) (k1 : ∀ s, w s ≤ 1)
    (hstep : G.ReachUpper target v w p) :
    ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)) (castIcc v h0 h1)
      ≤ castIcc w k0 k1 := by
  intro s
  by_cases hs : s ∈ target
  · have hw1 : (1 : ℚ) ≤ w s := ((hstep s).2.2.1 hs).ge
    have hw : (1 : ℝ) ≤ ((w s : ℚ) : ℝ) := by exact_mod_cast hw1
    exact (reachOp_coe_of_goal G h hrf (· ∈ target) v h0 h1 hs).trans_le hw
  · exact reachOp_coe_le_of_upperCert G h hrf (· ∈ target) v h0 h1 hs ((hstep s).2.2.2 hs)

/-! ## A lower run, and a pre-fixed upper vector -/

/-- **A lower run.** If `vs 0` is below the reachability value and each of the first `n` steps
    passes `ReachLower`, then `vs n` is below the reachability value. Induction on `n` with
    `OrderHom.le_lfp_of_le_step`; the bounds on each vector are read off its own step. -/
theorem le_lfp_of_lowers (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S) (vs : ℕ → S → ℚ) (qs : ℕ → S → A2 → ℚ) (n : ℕ)
    (h0 : ∀ s, 0 ≤ vs 0 s) (h1 : ∀ s, vs 0 s ≤ 1)
    (hstart : castIcc (vs 0) h0 h1
      ≤ ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp)
    (hsteps : ∀ k < n, G.ReachLower target (vs k) (vs (k + 1)) (qs k)) :
    ∃ (k0 : ∀ s, 0 ≤ vs n s) (k1 : ∀ s, vs n s ≤ 1),
      castIcc (vs n) k0 k1
        ≤ ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp := by
  induction n with
  | zero => exact ⟨h0, h1, hstart⟩
  | succ n ih =>
    obtain ⟨k0, k1, hle⟩ := ih fun k hk => hsteps k (Nat.lt_succ_of_lt hk)
    have hstep := hsteps n (Nat.lt_succ_self n)
    have m0 : ∀ s, 0 ≤ vs (n + 1) s := fun s => (hstep s).1
    have m1 : ∀ s, vs (n + 1) s ≤ 1 := fun s => (hstep s).2.1
    exact ⟨m0, m1, OrderHom.le_lfp_of_le_step _ hle
      (le_reachOp_of_reachLower G h hrf target k0 k1 m0 m1 hstep)⟩

/-- **A pre-fixed vector is above the reachability value.** `ReachUpper` from `u` to `u` says the
    operator maps `u` below itself, and `OrderHom.lfp_le` concludes. -/
theorem lfp_le_of_reachUpper (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S) {u : S → ℚ} {p : S → A1 → ℚ} (hu : G.ReachUpper target u u p) :
    ∃ (k0 : ∀ s, 0 ≤ u s) (k1 : ∀ s, u s ≤ 1),
      ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp ≤ castIcc u k0 k1 := by
  have k0 : ∀ s, 0 ≤ u s := fun s => (hu s).1
  have k1 : ∀ s, u s ≤ 1 := fun s => (hu s).2.1
  exact ⟨k0, k1, OrderHom.lfp_le _ (reachOp_le_of_reachUpper G h hrf target k0 k1 k0 k1 hu)⟩

/-! ## The answer -/

/-- **A lower run and a pre-fixed upper vector answer the reachability objective.** `lo` is a run
    of `n` checked lower steps from the constant `0`, and `hi` passes `ReachUpper` against itself.
    Then the interval `[lo n, hi]` answers `Objective.reach target`. The lower run carries column
    strategies only and the upper vector row strategies only. -/
theorem answers_reach_of_bounds (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S) (lo : ℕ → S → ℚ) (lq : ℕ → S → A2 → ℚ) (n : ℕ)
    (hi : S → ℚ) (up : S → A1 → ℚ)
    (hlo0 : ∀ s, lo 0 s = 0)
    (hlo : ∀ k < n, G.ReachLower target (lo k) (lo (k + 1)) (lq k))
    (hhi : G.ReachUpper target hi hi up) :
    G.Answers h (Objective.reach target) (Answer.interval (lo n) hi) := by
  have a0 : ∀ s, 0 ≤ lo 0 s := fun s => (hlo0 s).ge
  have a1 : ∀ s, lo 0 s ≤ 1 := fun s => (hlo0 s).le.trans zero_le_one
  obtain ⟨k0, k1, hL⟩ := le_lfp_of_lowers G h hrf target lo lq n a0 a1
    (castIcc_le_of_eq_zero (lo 0) a0 a1 hlo0 _) hlo
  obtain ⟨j0, j1, hU⟩ := lfp_le_of_reachUpper G h hrf target hhi
  exact .reach hrf k0 k1 j0 j1 hL hU

end CsgQ

end Comp
