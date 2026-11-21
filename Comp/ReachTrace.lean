/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Objective

/-!
# A checked trace for probabilistic reachability

**Status: confirmed by a clean `lake build`.** `Comp/Reach.lean` certifies one step of the
reachability operator from per-state equalities, and `Comp/Objective.lean` says what an answer to
`Objective.reach` is: two rational vectors enclosing the operator's least fixed point. This file
joins them for a whole run.

**The trace.** A run is a sequence of rational vectors `vs 0, vs 1, …, vs n`, and for each step
`k` a row strategy `ps k s` and a column strategy `qs k s` at every state. `ReachStep` is the
statement that one step is right: at a target state the next value is `1`, and at any other state
the next value, with the two strategies, is a `MatrixGameQ.ValueCert` for that state's stage game
against the current vector. It is a finite conjunction of rational equalities and inequalities,
and it is decidable. Nothing in it mentions how the values and strategies were found.

**What a trace proves.**

* `le_lfp_of_steps`: a trace that starts below the reachability value ends below it.
* `lfp_le_of_steps`: a trace that starts above the reachability value ends above it.
* `answers_reach_of_steps`: a trace from the constant `0` and a trace from the constant `1`
  together answer `Objective.reach target` with the interval `[lo n, hi m]`.

The bounds `0 ≤ vs k s ≤ 1` that packaging a vector into the operator's carrier needs are not
hypotheses beyond the starting vector: `reachStep_bounds` derives them for the next vector from
the step itself, because the operator's values lie in `[0, 1]`.

**What a trace does not prove.** That the interval is narrow. The lower chain converges to the
value; the upper chain stays above it but stalls wherever play can avoid the target forever. See
`Comp/Reach.lean` on why that is a convergence question and not a soundness one.

The vectors and strategies are indexed by `ℕ`, as functions. An instance supplies them however is
convenient, for example by reading literal tables with `List.getD`; the step count `n` says how
much of the sequence is used.
-/

namespace Comp

open Csg

namespace CsgQ

/-! ## The two starting points -/

section Start

variable {S : Type*}

/-- A rational vector that is `0` everywhere packages to something below every element of the
    carrier. The base case of a lower chain. -/
theorem castIcc_le_of_eq_zero (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1)
    (hv : ∀ s, v s = 0) (x : S → Set.Icc (0 : ℝ) 1) : castIcc v h0 h1 ≤ x := by
  intro s
  change ((v s : ℚ) : ℝ) ≤ (x s : ℝ)
  rw [hv s, Rat.cast_zero]
  exact (x s).2.1

/-- A rational vector that is `1` everywhere packages to something above every element of the
    carrier. The base case of an upper chain. -/
theorem le_castIcc_of_eq_one (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1)
    (hv : ∀ s, v s = 1) (x : S → Set.Icc (0 : ℝ) 1) : x ≤ castIcc v h0 h1 := by
  intro s
  change (x s : ℝ) ≤ ((v s : ℚ) : ℝ)
  rw [hv s, Rat.cast_one]
  exact (x s).2.2

end Start

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

/-! ## One checked step -/

/-- **One step of a trace.** From the vector `v`, the next vector `w` is `1` on the target, and
    elsewhere `w s` is the value of state `s`'s reachability stage game against `v`, certified by
    the strategies `p s` and `q s`. A finite conjunction of rational comparisons. -/
def ReachStep (G : CsgQ S A1 A2) (target : Finset S) (v w : S → ℚ)
    (p : S → A1 → ℚ) (q : S → A2 → ℚ) : Prop :=
  ∀ s, (s ∈ target → w s = 1) ∧
    (s ∉ target → (G.reachGameQ s v).ValueCert (w s) (p s) (q s))

instance (G : CsgQ S A1 A2) (target : Finset S) (v w : S → ℚ) (p : S → A1 → ℚ)
    (q : S → A2 → ℚ) : Decidable (G.ReachStep target v w p q) := by
  unfold ReachStep
  infer_instance

/-- A checked step computes the operator: at every state, the real reachability operator applied
    to `v` returns `w`. The two cases are `reachOp_coe_of_goal` and `reachOp_coe_of_valueCert`. -/
theorem reachOp_coe_of_reachStep (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S) {v w : S → ℚ} {p : S → A1 → ℚ} {q : S → A2 → ℚ}
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (hstep : G.ReachStep target v w p q) (s : S) :
    ((((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)) (castIcc v h0 h1) s : ℝ))
      = ((w s : ℚ) : ℝ) := by
  by_cases hs : s ∈ target
  · have hw : w s = 1 := (hstep s).1 hs
    rw [hw, Rat.cast_one]
    exact reachOp_coe_of_goal G h hrf (· ∈ target) v h0 h1 hs
  · exact reachOp_coe_of_valueCert G h hrf (· ∈ target) v h0 h1 hs ((hstep s).2 hs)

omit [DecidableEq S] in
/-- The vector a checked step produces lies in `[0, 1]`: it is the operator's output, and the
    operator's carrier is `S → Set.Icc 0 1`. So a trace needs the two bounds only of its starting
    vector. The statement mentions no decidability, so the proof takes it classically. -/
theorem reachStep_bounds (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S) {v w : S → ℚ} {p : S → A1 → ℚ} {q : S → A2 → ℚ}
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (hstep : G.ReachStep target v w p q) :
    (∀ s, 0 ≤ w s) ∧ ∀ s, w s ≤ 1 := by
  classical
  have key : ∀ (x : Set.Icc (0 : ℝ) 1) (r : ℝ), (x : ℝ) = r → 0 ≤ r ∧ r ≤ 1 := by
    intro x r hxr
    subst hxr
    exact x.2
  refine ⟨fun s => ?_, fun s => ?_⟩
  · have hI : (0 : ℝ) ≤ ((w s : ℚ) : ℝ) :=
      (key _ _ (reachOp_coe_of_reachStep G h hrf target h0 h1 hstep s)).1
    exact_mod_cast hI
  · have hI : ((w s : ℚ) : ℝ) ≤ 1 :=
      (key _ _ (reachOp_coe_of_reachStep G h hrf target h0 h1 hstep s)).2
    exact_mod_cast hI

/-! ## Chains of steps -/

/-- **A lower chain.** If `vs 0` is below the reachability value and each of the first `n` steps
    is checked, then `vs n` is below the reachability value. Induction on `n` with
    `le_lfp_of_step`; the bounds on `vs n` come out of the induction with it. -/
theorem le_lfp_of_steps (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S) (vs : ℕ → S → ℚ) (ps : ℕ → S → A1 → ℚ) (qs : ℕ → S → A2 → ℚ) (n : ℕ)
    (h0 : ∀ s, 0 ≤ vs 0 s) (h1 : ∀ s, vs 0 s ≤ 1)
    (hstart : castIcc (vs 0) h0 h1
      ≤ ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp)
    (hsteps : ∀ k < n, G.ReachStep target (vs k) (vs (k + 1)) (ps k) (qs k)) :
    ∃ (k0 : ∀ s, 0 ≤ vs n s) (k1 : ∀ s, vs n s ≤ 1),
      castIcc (vs n) k0 k1
        ≤ ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp := by
  induction n with
  | zero => exact ⟨h0, h1, hstart⟩
  | succ n ih =>
    obtain ⟨k0, k1, hle⟩ := ih fun k hk => hsteps k (Nat.lt_succ_of_lt hk)
    have hstep := hsteps n (Nat.lt_succ_self n)
    obtain ⟨m0, m1⟩ := reachStep_bounds G h hrf target k0 k1 hstep
    exact ⟨m0, m1, le_lfp_of_step G h hrf (· ∈ target) (vs n) (vs (n + 1)) k0 k1 m0 m1 hle
      fun s => reachOp_coe_of_reachStep G h hrf target k0 k1 hstep s⟩

/-- **An upper chain.** If `vs 0` is above the reachability value and each of the first `n` steps
    is checked, then `vs n` is above the reachability value. The mirror of `le_lfp_of_steps`, with
    `lfp_le_of_step`. -/
theorem lfp_le_of_steps (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S) (vs : ℕ → S → ℚ) (ps : ℕ → S → A1 → ℚ) (qs : ℕ → S → A2 → ℚ) (n : ℕ)
    (h0 : ∀ s, 0 ≤ vs 0 s) (h1 : ∀ s, vs 0 s ≤ 1)
    (hstart : ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp
      ≤ castIcc (vs 0) h0 h1)
    (hsteps : ∀ k < n, G.ReachStep target (vs k) (vs (k + 1)) (ps k) (qs k)) :
    ∃ (k0 : ∀ s, 0 ≤ vs n s) (k1 : ∀ s, vs n s ≤ 1),
      ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp
        ≤ castIcc (vs n) k0 k1 := by
  induction n with
  | zero => exact ⟨h0, h1, hstart⟩
  | succ n ih =>
    obtain ⟨k0, k1, hle⟩ := ih fun k hk => hsteps k (Nat.lt_succ_of_lt hk)
    have hstep := hsteps n (Nat.lt_succ_self n)
    obtain ⟨m0, m1⟩ := reachStep_bounds G h hrf target k0 k1 hstep
    exact ⟨m0, m1, lfp_le_of_step G h hrf (· ∈ target) (vs n) (vs (n + 1)) k0 k1 m0 m1 hle
      fun s => reachOp_coe_of_reachStep G h hrf target k0 k1 hstep s⟩

/-! ## The answer -/

/-- **A run answers the reachability objective.** `lo` is a trace of `n` checked steps from the
    constant `0` and `hi` a trace of `m` checked steps from the constant `1`. Then the interval
    `[lo n, hi m]` answers `Objective.reach target`: the real reachability value of the game `G`
    denotes lies between the two vectors at every state. The two step counts are independent. -/
theorem answers_reach_of_steps (G : CsgQ S A1 A2) (h : G.WellFormed) (hrf : G.RewardFree)
    (target : Finset S)
    (lo : ℕ → S → ℚ) (lp : ℕ → S → A1 → ℚ) (lq : ℕ → S → A2 → ℚ) (n : ℕ)
    (hi : ℕ → S → ℚ) (up : ℕ → S → A1 → ℚ) (uq : ℕ → S → A2 → ℚ) (m : ℕ)
    (hlo0 : ∀ s, lo 0 s = 0)
    (hlo : ∀ k < n, G.ReachStep target (lo k) (lo (k + 1)) (lp k) (lq k))
    (hhi0 : ∀ s, hi 0 s = 1)
    (hhi : ∀ k < m, G.ReachStep target (hi k) (hi (k + 1)) (up k) (uq k)) :
    G.Answers h (Objective.reach target) (Answer.interval (lo n) (hi m)) := by
  have a0 : ∀ s, 0 ≤ lo 0 s := fun s => (hlo0 s).ge
  have a1 : ∀ s, lo 0 s ≤ 1 := fun s => (hlo0 s).le.trans zero_le_one
  have b0 : ∀ s, 0 ≤ hi 0 s := fun s => le_trans zero_le_one (hhi0 s).ge
  have b1 : ∀ s, hi 0 s ≤ 1 := fun s => (hhi0 s).le
  obtain ⟨k0, k1, hL⟩ := le_lfp_of_steps G h hrf target lo lp lq n a0 a1
    (castIcc_le_of_eq_zero (lo 0) a0 a1 hlo0 _) hlo
  obtain ⟨j0, j1, hU⟩ := lfp_le_of_steps G h hrf target hi up uq m b0 b1
    (le_castIcc_of_eq_one (hi 0) b0 b1 hhi0 _) hhi
  exact .reach hrf k0 k1 j0 j1 hL hU

end CsgQ

end Comp
