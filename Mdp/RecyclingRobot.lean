/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mdp.PolicyIteration

/-!
# Worked example: the recycling robot

**Status: confirmed by a clean `lake build`; `robotMDP.vOpt` matches the hand-solved closed form
exactly — see `PHASE0-NOTES.md`.** This status line had gone stale (it said "drafted, not yet run
through `lake build`" long after the build had actually gone clean); corrected in place rather
than treated as still-open work. A concrete instantiation of `DiscountedMDP`, used to check the
abstract Phase 1/2 machinery against a hand-solved, closed-form ground truth rather than just
`lake build` accepting it. This is Sutton & Barto's "recycling robot" (the canonical minimal
example used to introduce discounted MDPs in the first place): a robot with battery level `high`
or `low`, choosing at each step to `search` for cans (risky when low on battery), `wait` (safe,
low reward), or `recharge` (only useful when low).

Numbers, picked for clean arithmetic rather than taken from a published source (the textbook
itself leaves them symbolic): `α = β = 1/2` (chance of staying in the current battery state while
searching), `r_search = 2`, `r_wait = 1`, a depletion penalty of `-3` if searching at low battery
fails, and discount `l = 1/2`. Since `DiscountedMDP.r : S → A → ℝ` depends only on the state
and action, not the outcome state, the "search at low" reward is the pre-computed expectation
`β · r_search + (1 - β) · (-3) = -1/2` — mathematically identical to an outcome-dependent
reward for Bellman-equation purposes, since only its expectation ever enters the equation.

`recharge` is not a natural action at `high` battery; it's given the same behaviour as `wait`
there (self-loop, reward `r_wait`) purely so `K`/`r` are total functions, and this convention is
harmless since `search` already strictly dominates `wait` at `high` regardless of what `recharge`
does there.

Hand-solved optimal value function, checked against *every* alternative action at both states —
not just the guessed-optimal policy. (The first guess, "always search," turned out not to be
optimal at `low`; only checking the full Bellman optimality condition against all three actions
caught it.)

  `v_high = 10/3`, `v_low = 2`, optimal policy: `search` at `high`, `wait` at `low`.

All six action/state Q-values checked strictly, so there's no tie-breaking ambiguity here.

`robotMDP_vOpt` proves `robotMDP.vOpt` equals this vector *exactly* — not "converges toward" —
by exhibiting it as a fixed point of `bellman` and invoking `ContractingWith.fixedPoint_unique`
(Phase 2a), the same route `policyStep_fixedPoint_value_eq_vOpt` uses. This is a genuinely
different kind of check than everything before it in this project: `ℝ` and `PMF` are both
noncomputable in Mathlib (confirmed against the source — `PMF`'s whole file is a `noncomputable
section`), so none of this can be `#eval`'d to watch numbers converge. The payoff here is a
symbolic equality proof against a hand-derived closed form, which is a strictly stronger claim
than a numerical approximation converging toward one would be. -/

open Mdp Mdp.DiscountedMDP

/-- Battery state: high or low. -/
inductive RobotState
  | high
  | low
  deriving DecidableEq, Inhabited

/-- `deriving Fintype` produces an ill-typed `Finset.univ` on this Lean/Mathlib toolchain
    combination (a `List.Nodup`/`Multiset.Nodup` coercion mismatch inside the deriving
    handler's generated instance, confirmed by the build error rather than guessed) — so this
    instance is built by hand instead, sidestepping the handler entirely. -/
instance : Fintype RobotState where
  elems := {RobotState.high, RobotState.low}
  complete := by intro x; cases x <;> decide

/-- Available actions. `recharge` at `high` battery is a harmless convention (see the module
    docstring), not a natural choice there. -/
inductive RobotAction
  | search
  | wait
  | recharge
  deriving DecidableEq, Inhabited

/-- Same `deriving Fintype` workaround as `RobotState` above. -/
instance : Fintype RobotAction where
  elems := {RobotAction.search, RobotAction.wait, RobotAction.recharge}
  complete := by intro x; cases x <;> decide

/-- Expand a sum over all of `RobotState` into its two terms. Generic in the codomain so it
    covers both the `ℝ`-valued sums in `expect` and the `ℝ≥0∞`-valued sum-to-one side
    condition below. -/
private theorem robotState_sum {β : Type*} [AddCommMonoid β] (f : RobotState → β) :
    ∑ s : RobotState, f s = f RobotState.high + f RobotState.low := by
  have huniv : (Finset.univ : Finset RobotState) = {RobotState.high, RobotState.low} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The `α = β = 1/2` transition: uniform over `{high, low}`. Used for `search` at *both* states,
    since our chosen `α` and `β` happen to coincide. -/
noncomputable def searchPMF : PMF RobotState :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [robotState_sum, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num [ENNReal.ofReal_one])

private theorem toReal_searchPMF (s' : RobotState) : (searchPMF s').toReal = 1 / 2 := by
  unfold searchPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (by norm_num)

private theorem toReal_pure_high_high :
    (PMF.pure RobotState.high RobotState.high).toReal = 1 := by
  simp [PMF.pure_apply]

private theorem toReal_pure_high_low :
    (PMF.pure RobotState.high RobotState.low).toReal = 0 := by
  simp [PMF.pure_apply]

private theorem toReal_pure_low_low :
    (PMF.pure RobotState.low RobotState.low).toReal = 1 := by
  simp [PMF.pure_apply]

private theorem toReal_pure_low_high :
    (PMF.pure RobotState.low RobotState.high).toReal = 0 := by
  simp [PMF.pure_apply]

/-- The transition kernel. `search` uses `searchPMF` at both states (since `α = β`); `wait`
    self-loops; `recharge` goes to `high` for real at `low` battery, and is a harmless copy of
    `wait` at `high` (see the module docstring). -/
noncomputable def robotK : RobotState → RobotAction → PMF RobotState
  | .high, .search => searchPMF
  | .high, .wait => PMF.pure .high
  | .high, .recharge => PMF.pure .high
  | .low, .search => searchPMF
  | .low, .wait => PMF.pure .low
  | .low, .recharge => PMF.pure .high

/-- The reward function. `low, search` is the pre-computed expectation
    `β · r_search + (1 - β) · (-3) = (1/2) · 2 + (1/2) · (-3) = -1/2` (see the module
    docstring for why this is exact, not an approximation, of the outcome-dependent reward). -/
noncomputable def robotR : RobotState → RobotAction → ℝ
  | .high, .search => 2
  | .high, .wait => 1
  | .high, .recharge => 1
  | .low, .search => -(1 / 2)
  | .low, .wait => 1
  | .low, .recharge => 0

/-- The recycling robot, as a `DiscountedMDP`. -/
noncomputable def robotMDP : DiscountedMDP RobotState RobotAction where
  K := robotK
  r := robotR
  l := 1 / 2
  l_nonneg := by norm_num
  l_lt_one := by norm_num

/-- The hand-solved optimal value function: `10/3` at `high`, `2` at `low`. -/
noncomputable def robotV0 : RobotState → ℝ
  | .high => 10 / 3
  | .low => 2

private theorem expect_high_search : robotMDP.expect .high .search robotV0 = 8 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.high RobotAction.search s').toReal * robotV0 s'
    = 8 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_searchPMF, robotV0]
  norm_num

private theorem expect_high_wait : robotMDP.expect .high .wait robotV0 = 10 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.high RobotAction.wait s').toReal * robotV0 s'
    = 10 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_pure_high_high, toReal_pure_high_low, robotV0]
  norm_num

private theorem expect_high_recharge : robotMDP.expect .high .recharge robotV0 = 10 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.high RobotAction.recharge s').toReal * robotV0 s'
    = 10 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_pure_high_high, toReal_pure_high_low, robotV0]
  norm_num

private theorem expect_low_search : robotMDP.expect .low .search robotV0 = 8 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.low RobotAction.search s').toReal * robotV0 s'
    = 8 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_searchPMF, robotV0]
  norm_num

private theorem expect_low_wait : robotMDP.expect .low .wait robotV0 = 2 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.low RobotAction.wait s').toReal * robotV0 s' = 2
  rw [robotState_sum]
  simp only [robotK, toReal_pure_low_low, toReal_pure_low_high, robotV0]
  norm_num

private theorem expect_low_recharge : robotMDP.expect .low .recharge robotV0 = 10 / 3 := by
  unfold DiscountedMDP.expect
  change ∑ s' : RobotState, (robotK RobotState.low RobotAction.recharge s').toReal * robotV0 s'
    = 10 / 3
  rw [robotState_sum]
  simp only [robotK, toReal_pure_high_high, toReal_pure_high_low, robotV0]
  norm_num

/-- **The payoff.** `robotMDP`'s optimal value function is *exactly* the hand-solved vector, not
    an approximation of it — checked by exhibiting it as a `bellman` fixed point and invoking
    Banach uniqueness (Phase 2a), the same route `policyStep_fixedPoint_value_eq_vOpt` uses. -/
theorem robotMDP_vOpt : robotMDP.vOpt = robotV0 := by
  refine (robotMDP.contractingWith_bellman.fixedPoint_unique ?_).symm
  funext s
  unfold DiscountedMDP.bellman
  cases s with
  | high =>
      apply le_antisymm
      · rw [Finset.sup'_le_iff]
        rintro a -
        cases a with
        | search =>
            rw [expect_high_search]
            simp only [robotR, robotMDP, robotV0]
            norm_num
        | wait =>
            rw [expect_high_wait]
            simp only [robotR, robotMDP, robotV0]
            norm_num
        | recharge =>
            rw [expect_high_recharge]
            simp only [robotR, robotMDP, robotV0]
            norm_num
      · have hle := Finset.le_sup'
          (fun a => robotR RobotState.high a
            + robotMDP.l * robotMDP.expect RobotState.high a robotV0)
          (Finset.mem_univ RobotAction.search)
        rw [expect_high_search] at hle
        simp only [robotR, robotMDP, robotV0] at hle ⊢
        linarith [hle]
  | low =>
      apply le_antisymm
      · rw [Finset.sup'_le_iff]
        rintro a -
        cases a with
        | search =>
            rw [expect_low_search]
            simp only [robotR, robotMDP, robotV0]
            norm_num
        | wait =>
            rw [expect_low_wait]
            simp only [robotR, robotMDP, robotV0]
            norm_num
        | recharge =>
            rw [expect_low_recharge]
            simp only [robotR, robotMDP, robotV0]
            norm_num
      · have hle := Finset.le_sup'
          (fun a => robotR RobotState.low a
            + robotMDP.l * robotMDP.expect RobotState.low a robotV0)
          (Finset.mem_univ RobotAction.wait)
        rw [expect_low_wait] at hle
        simp only [robotR, robotMDP, robotV0] at hle ⊢
        linarith [hle]

/-- Corollaries in the shape someone skimming the file would actually want to see. -/
theorem robotMDP_vOpt_high : robotMDP.vOpt RobotState.high = 10 / 3 := by
  rw [robotMDP_vOpt]; simp [robotV0]

theorem robotMDP_vOpt_low : robotMDP.vOpt RobotState.low = 2 := by
  rw [robotMDP_vOpt]; simp [robotV0]
