/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.GameData
import Comp.ModelDataReach

/-!
# Three players, one model, three coalitions

**Status: confirmed by a clean `lake build`.** A model with three players, given once as a
`GameData`, and the same question asked of it for three coalitions: with what probability can the
coalition get the runner home? The answers at the hiding place are `0`, between `12/25` and
`1/2`, and `1`. Each is obtained by building the two-sided game for that coalition with
`GameData.reduceMax` and answering `Objective.reach` on it.

**The players.** Player `0` is the runner, who runs (`0`) or hides (`1`). Player `1` is the
thrower, who throws (`0`) or waits (`1`). Player `2` is the keeper of a gate, who opens it (`0`)
or shuts it (`1`).

**The states.**

* State `0`, the hiding place. The runner and the thrower choose and the keeper idles. Running
  into a throw ends wet. Hiding from a throw reaches the gate. Running past a waiting thrower
  slips. Hiding from a waiting thrower stays.
* State `1`, the gate. Only the keeper chooses: open leads home, shut leads back to hiding.
* State `2`, slipping. Nobody chooses: home, wet, or back to hiding, a third each.
* State `3`, home, and state `4`, wet, are terminal.

**The three coalitions.**

* *The runner alone* (`gkR`). The thrower throws and the keeper shuts, and the runner never gets
  home: the value is exactly `0` at the hiding place and at the gate.
* *The runner and the keeper* (`gkRK`). The gate now opens, and the hiding place is the hiding
  place of `Comp/HideRunSlipQ.lean` with slipping as a state of its own: the value is `1/2`,
  certified between `12/25` and `1/2`.
* *All three* (`gkAll`). The thrower throws at a hiding runner, who reaches the gate, and the
  keeper opens it: the value is exactly `1`. The other side has no player and the single
  action `0`.

**Reading the tables.** A side's action is the code of its players' choices
(`Comp/GameData.lean`), with `0` for idling. For the thrower alone, `1` is throw and `2` is wait.
For the runner and the keeper together the code is the runner's digit plus three times the
keeper's: `1` is run, `2` is hide, `3` is open and `6` is shut. A strategy is a list of pairs of
such a code and its weight.
-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

namespace GateKeeper

/-! ## The model -/

/-- The runner, the thrower and the keeper, as data. -/
abbrev gk : GameData where
  nActs := [2, 2, 2]
  states :=
    [ -- state 0, the hiding place: the runner and the thrower choose, the keeper idles
      ⟨0, [⟨[some 0, some 0, none], [(4, 1)], 0⟩, ⟨[some 1, some 0, none], [(1, 1)], 0⟩,
           ⟨[some 0, some 1, none], [(2, 1)], 0⟩, ⟨[some 1, some 1, none], [(0, 1)], 0⟩]⟩,
      -- state 1, the gate: only the keeper chooses
      ⟨0, [⟨[none, none, some 0], [(3, 1)], 0⟩, ⟨[none, none, some 1], [(0, 1)], 0⟩]⟩,
      -- state 2, slipping: nobody chooses
      ⟨0, [⟨[none, none, none], [(3, 1/3), (4, 1/3), (0, 1/3)], 0⟩]⟩,
      -- state 3, home: terminal
      ⟨0, []⟩,
      -- state 4, wet: terminal
      ⟨0, []⟩ ]

theorem gk_shape : gk.Shape := by decide +kernel

/-! ## The runner and the keeper against the thrower -/

/-- The two-sided game in which the runner and the keeper maximise. -/
abbrev gkRK : ModelData := gk.reduceMax [0, 2]

instance : NeZero gkRK.nStates := ⟨by decide +kernel⟩

instance : NeZero gkRK.nAct1 := ⟨by decide +kernel⟩

instance : NeZero gkRK.nAct2 := ⟨by decide +kernel⟩

theorem gkRK_shape : gkRK.Shape := by decide +kernel

theorem gkRK_stochastic : gkRK.Stochastic := by decide +kernel

theorem gkRK_wf : gkRK.toCsgQ.WellFormed :=
  gkRK.wellFormed gkRK_shape gkRK_stochastic

theorem gkRK_rewardFree : gkRK.toCsgQ.RewardFree := by decide +kernel

/-- Getting home. -/
def gkRKHome : Finset (Fin gkRK.nStates) := {3}

#eval gkRK.enabled1 gkRK_shape 0
-- expect: {1, 2}    the thrower throws or waits

#eval gkRK.enabled2 gkRK_shape 1
-- expect: {3, 6}    at the gate the runner idles and the keeper opens or shuts

#eval gkRK.reachLowerRun gkRKHome 100 13
-- expect: the tables of `gkRKLo` below

/-- Thirteen lower steps from `0`, rounded down to hundredths. -/
def gkRKLo : ReachRun where
  vals := [[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 1, 33/100, 1, 0], [6/25, 1, 33/100, 1, 0],
           [3/10, 1, 41/100, 1, 0], [9/25, 1, 43/100, 1, 0], [2/5, 1, 9/20, 1, 0],
           [21/50, 1, 23/50, 1, 0], [11/25, 1, 47/100, 1, 0], [9/20, 1, 12/25, 1, 0],
           [23/50, 1, 12/25, 1, 0], [47/100, 1, 12/25, 1, 0], [47/100, 1, 49/100, 1, 0],
           [12/25, 1, 49/100, 1, 0]]
  rows := []
  cols := [[[(2, 1)], [(6, 1)], [(0, 1)], [], [(0, 1)]],
           [[(2, 1)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 100/133), (2, 33/133)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 76/109), (2, 33/109)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 70/111), (2, 41/111)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 64/107), (2, 43/107)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 4/7), (2, 3/7)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 29/52), (2, 23/52)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 56/103), (2, 47/103)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 55/103), (2, 48/103)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 9/17), (2, 8/17)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 53/101), (2, 48/101)], [(3, 1)], [(0, 1)], [], [(0, 1)]],
           [[(1, 53/102), (2, 49/102)], [(3, 1)], [(0, 1)], [], [(0, 1)]]]

#eval gkRK.reachUpperRun gkRKHome (fun s => ([1/2, 1, 1/2, 1, 0] : List ℚ).getD s.val 0)
-- expect: both vectors `[1/2, 1, 1/2, 1, 0]`

/-- The upper vector `(1/2, 1, 1/2, 1, 0)`, with the thrower's strategies: wait at the hiding
    place, idle elsewhere. -/
def gkRKHi : ReachRun where
  vals := [[1/2, 1, 1/2, 1, 0]]
  rows := [[[(2, 1)], [(0, 1)], [(0, 1)], [], [(0, 1)]]]
  cols := []

/-- **The runner and the keeper get home with probability between the two vectors**, at every
    state. -/
theorem gkRK_reach :
    gkRK.toCsgQ.Answers gkRK_wf (Objective.reach gkRKHome)
      (Answer.interval (gkRKLo.val 13) (gkRKHi.val 0)) :=
  gkRK.answers_reach_of_bounds gkRK_shape gkRK_stochastic gkRK_rewardFree gkRKHome gkRKLo
    gkRKHi 13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The runner alone -/

/-- The two-sided game in which the runner alone maximises. -/
abbrev gkR : ModelData := gk.reduceMax [0]

instance : NeZero gkR.nStates := ⟨by decide +kernel⟩

instance : NeZero gkR.nAct1 := ⟨by decide +kernel⟩

instance : NeZero gkR.nAct2 := ⟨by decide +kernel⟩

theorem gkR_shape : gkR.Shape := by decide +kernel

theorem gkR_stochastic : gkR.Stochastic := by decide +kernel

theorem gkR_wf : gkR.toCsgQ.WellFormed :=
  gkR.wellFormed gkR_shape gkR_stochastic

theorem gkR_rewardFree : gkR.toCsgQ.RewardFree := by decide +kernel

/-- Getting home. -/
def gkRHome : Finset (Fin gkR.nStates) := {3}

#eval gkR.reachLowerRun gkRHome 0 2
-- expect: the tables of `gkRLo` below

/-- Two lower steps from `0`: home, then slipping. The hiding place and the gate stay at `0`. -/
def gkRLo : ReachRun where
  vals := [[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1/3, 1, 0]]
  rows := []
  cols := [[[(2, 1)], [(0, 1)], [(0, 1)], [], [(0, 1)]],
           [[(2, 1)], [(0, 1)], [(0, 1)], [], [(0, 1)]]]

#eval gkR.reachUpperRun gkRHome (fun s => ([0, 0, 1/3, 1, 0] : List ℚ).getD s.val 0)
-- expect: both vectors `[0, 0, 1/3, 1, 0]`

/-- The upper vector `(0, 0, 1/3, 1, 0)`, with the strategies of the thrower and the keeper:
    throw at the hiding place, shut at the gate. -/
def gkRHi : ReachRun where
  vals := [[0, 0, 1/3, 1, 0]]
  rows := [[[(1, 1)], [(6, 1)], [(0, 1)], [], [(0, 1)]]]
  cols := []

/-- **The runner alone gets home with exactly the probabilities `(0, 0, 1/3, 1, 0)`**: the two
    vectors coincide. -/
theorem gkR_reach :
    gkR.toCsgQ.Answers gkR_wf (Objective.reach gkRHome)
      (Answer.interval (gkRLo.val 2) (gkRHi.val 0)) :=
  gkR.answers_reach_of_bounds gkR_shape gkR_stochastic gkR_rewardFree gkRHome gkRLo gkRHi 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## All three together -/

/-- The two-sided game in which all three players maximise. The row side has no player. -/
abbrev gkAll : ModelData := gk.reduceMax [0, 1, 2]

instance : NeZero gkAll.nStates := ⟨by decide +kernel⟩

instance : NeZero gkAll.nAct1 := ⟨by decide +kernel⟩

instance : NeZero gkAll.nAct2 := ⟨by decide +kernel⟩

theorem gkAll_shape : gkAll.Shape := by decide +kernel

theorem gkAll_stochastic : gkAll.Stochastic := by decide +kernel

theorem gkAll_wf : gkAll.toCsgQ.WellFormed :=
  gkAll.wellFormed gkAll_shape gkAll_stochastic

theorem gkAll_rewardFree : gkAll.toCsgQ.RewardFree := by decide +kernel

/-- Getting home. -/
def gkAllHome : Finset (Fin gkAll.nStates) := {3}

#eval gkAll.reachLowerRun gkAllHome 0 4
-- expect: the tables of `gkAllLo` below

/-- Four lower steps from `0`. The code of a joint choice is the runner's digit, plus three times
    the thrower's, plus nine times the keeper's: `5` is hide from a throw, `8` is hide from a
    wait, `9` is open and `18` is shut. Where several choices are as good, the search returns the
    one with the largest code. -/
def gkAllLo : ReachRun where
  vals := [[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1/3, 1, 0], [1, 1, 1/3, 1, 0],
           [1, 1, 2/3, 1, 0]]
  rows := []
  cols := [[[(8, 1)], [(18, 1)], [(0, 1)], [], [(0, 1)]],
           [[(8, 1)], [(9, 1)], [(0, 1)], [], [(0, 1)]],
           [[(5, 1)], [(9, 1)], [(0, 1)], [], [(0, 1)]],
           [[(8, 1)], [(18, 1)], [(0, 1)], [], [(0, 1)]]]

/-- The upper vector `(1, 1, 2/3, 1, 0)`. The row side has one action everywhere. -/
def gkAllHi : ReachRun where
  vals := [[1, 1, 2/3, 1, 0]]
  rows := [[[(0, 1)], [(0, 1)], [(0, 1)], [], [(0, 1)]]]
  cols := []

/-- **All three together get home with exactly the probabilities `(1, 1, 2/3, 1, 0)`.** -/
theorem gkAll_reach :
    gkAll.toCsgQ.Answers gkAll_wf (Objective.reach gkAllHome)
      (Answer.interval (gkAllLo.val 4) (gkAllHi.val 0)) :=
  gkAll.answers_reach_of_bounds gkAll_shape gkAll_stochastic gkAll_rewardFree gkAllHome gkAllLo
    gkAllHi 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The three answers at the hiding place -/

/-- **The runner alone never gets home from the hiding place.** -/
theorem gk_runner_alone :
    (((gkR.toCsgQ.toCSG gkR_wf).reachOp (· ∈ gkRHome)
      (CsgQ.toCSG_r_zero gkR.toCsgQ gkR_wf gkR_rewardFree)).lfp 0 : ℝ) = 0 := by
  have h := CsgQ.reach_bounds_of_answers gkR.toCsgQ gkR_wf gkR_rewardFree gkR_reach 0
  have hl : gkRLo.val 2 (0 : Fin gkR.nStates) = 0 := by decide +kernel
  have hu : gkRHi.val 0 (0 : Fin gkR.nStates) = 0 := by decide +kernel
  have hl' : ((gkRLo.val 2 (0 : Fin gkR.nStates) : ℚ) : ℝ) = 0 := by
    rw [hl]
    norm_num
  have hu' : ((gkRHi.val 0 (0 : Fin gkR.nStates) : ℚ) : ℝ) = 0 := by
    rw [hu]
    norm_num
  exact le_antisymm (h.2.trans_eq hu') (hl'.ge.trans h.1)

/-- **With the keeper, the runner gets home from the hiding place with probability between
    `12/25` and `1/2`.** -/
theorem gk_runner_and_keeper :
    (12 / 25 : ℝ) ≤ (((gkRK.toCsgQ.toCSG gkRK_wf).reachOp (· ∈ gkRKHome)
        (CsgQ.toCSG_r_zero gkRK.toCsgQ gkRK_wf gkRK_rewardFree)).lfp 0 : ℝ) ∧
      (((gkRK.toCsgQ.toCSG gkRK_wf).reachOp (· ∈ gkRKHome)
        (CsgQ.toCSG_r_zero gkRK.toCsgQ gkRK_wf gkRK_rewardFree)).lfp 0 : ℝ) ≤ 1 / 2 := by
  have h := CsgQ.reach_bounds_of_answers gkRK.toCsgQ gkRK_wf gkRK_rewardFree gkRK_reach 0
  have hl : gkRKLo.val 13 (0 : Fin gkRK.nStates) = 12 / 25 := by decide +kernel
  have hu : gkRKHi.val 0 (0 : Fin gkRK.nStates) = 1 / 2 := by decide +kernel
  have hl' : (12 / 25 : ℝ) = ((gkRKLo.val 13 (0 : Fin gkRK.nStates) : ℚ) : ℝ) := by
    rw [hl]
    norm_num
  have hu' : ((gkRKHi.val 0 (0 : Fin gkRK.nStates) : ℚ) : ℝ) = 1 / 2 := by
    rw [hu]
    norm_num
  exact ⟨hl'.le.trans h.1, h.2.trans_eq hu'⟩

/-- **All three together get the runner home from the hiding place for certain.** -/
theorem gk_all_together :
    (((gkAll.toCsgQ.toCSG gkAll_wf).reachOp (· ∈ gkAllHome)
      (CsgQ.toCSG_r_zero gkAll.toCsgQ gkAll_wf gkAll_rewardFree)).lfp 0 : ℝ) = 1 := by
  have h := CsgQ.reach_bounds_of_answers gkAll.toCsgQ gkAll_wf gkAll_rewardFree gkAll_reach 0
  have hl : gkAllLo.val 4 (0 : Fin gkAll.nStates) = 1 := by decide +kernel
  have hu : gkAllHi.val 0 (0 : Fin gkAll.nStates) = 1 := by decide +kernel
  have hl' : ((gkAllLo.val 4 (0 : Fin gkAll.nStates) : ℚ) : ℝ) = 1 := by
    rw [hl]
    norm_num
  have hu' : ((gkAllHi.val 0 (0 : Fin gkAll.nStates) : ℚ) : ℝ) = 1 := by
    rw [hu]
    norm_num
  exact le_antisymm (h.2.trans_eq hu') (hl'.ge.trans h.1)

end GateKeeper

end Comp
