/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.RaggedQ
import Comp.ModelDataReach

/-!
# Reaching the goal in the ragged stand-off, quantitatively

**Status: confirmed by a clean `lake build`.** `Comp/RaggedQ.lean` answers the three qualitative
questions about its model. This file asks the quantitative one: with what probability can the
column player force the goal, state `1`, to be reached, against a row player who minimises it?

**The answer here.** After four steps up from `0` and one step down from `1`, the reachability
value lies in `[3/5, 1]` at the stand-off, is `1` at the goal, and lies in `[0, 1]` at state `2`
and at the sink (`ragged_reach`). `ragged_reach_standoff` states the stand-off's lower bound as an
inequality between real numbers.

**What the two runs do.** At the stand-off the stage game against a vector `v` is, on the enabled
actions (rows wait and run, columns throw and wait),

    [[(v 0 + 1) / 2, v 0], [v 3, 1]]

since waiting out a throw is the fair coin between staying and reaching the goal. From `0` its
value climbs `0, 0, 1/3, 1/2, 3/5, …` by `x ↦ (x + 1) / (3 - x)`, towards `1`. State `2` stays at
`0`, because the row player, who minimises here, can walk from it into the sink.

The upper run does not move. The sink is not a target and nothing leaves it, so from `1` it stays
at `1`, and every other state stays at `1` with it. The true value at the sink is `0`; the
interval is sound there and uninformative, and tightening it needs the qualitative regions.

**How it is checked.** The two `#eval`s print the runs. They are pasted below as literals, and the
four hypotheses of `ModelData.answers_reach_of_runs` are each closed by `decide +kernel`. The
strategies have one entry per global action: at the stand-off row action `1` and column action
`0` are disabled and carry weight `0`.
-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

namespace Ragged

/-- No state reward and no transition reward anywhere. -/
theorem ragged_rewardFree : ragged.toCsgQ.RewardFree := by decide +kernel

/-! ## The search -/

#eval ragged.reachRun raggedTarget 0 4
-- expect: the tables of `raggedLo` below

#eval ragged.reachRun raggedTarget 1 1
-- expect: the tables of `raggedHi` below

/-! ## The runs, as literals -/

/-- Four steps up from `0`. -/
def raggedLo : ReachRun where
  vals := [[0, 0, 0, 0], [0, 1, 0, 0], [1/3, 1, 0, 0], [1/2, 1, 0, 0], [3/5, 1, 0, 0]]
  rows := [[[0, 0, 1], [], [0, 0, 1], [0, 0, 1]],
           [[1/3, 0, 2/3], [], [0, 0, 1], [0, 0, 1]],
           [[1/4, 0, 3/4], [], [0, 0, 1], [0, 0, 1]],
           [[1/5, 0, 4/5], [], [0, 0, 1], [0, 0, 1]]]
  cols := [[[0, 0, 1], [], [0, 0, 1], [0, 0, 1]],
           [[0, 2/3, 1/3], [], [0, 0, 1], [0, 0, 1]],
           [[0, 1/2, 1/2], [], [0, 0, 1], [0, 0, 1]],
           [[0, 2/5, 3/5], [], [0, 0, 1], [0, 0, 1]]]

/-- One step down from `1`. Every stage game is constant at `1`. -/
def raggedHi : ReachRun where
  vals := [[1, 1, 1, 1], [1, 1, 1, 1]]
  rows := [[[0, 0, 1], [], [0, 0, 1], [0, 0, 1]]]
  cols := [[[0, 0, 1], [], [0, 0, 1], [0, 0, 1]]]

/-! ## The answer -/

/-- **Reaching the goal, from the model.** The reachability value of the game `ragged` denotes
    lies between the fourth lower iterate and the first upper one, at every state. -/
theorem ragged_reach :
    ragged.toCsgQ.Answers ragged_wf (Objective.reach raggedTarget)
      (Answer.interval (raggedLo.val 4) (raggedHi.val 1)) :=
  ragged.answers_reach_of_runs ragged_shape ragged_stochastic ragged_rewardFree raggedTarget
    raggedLo raggedHi 4 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- **At the stand-off, the goal is reached with probability at least `3/5`.** The same fact as
    `ragged_reach` at state `0`, as an inequality between real numbers about the least fixed point
    of `Csg/ReachOp.lean`'s operator. -/
theorem ragged_reach_standoff :
    (3 / 5 : ℝ) ≤ (((ragged.toCsgQ.toCSG ragged_wf).reachOp (· ∈ raggedTarget)
      (CsgQ.toCSG_r_zero ragged.toCsgQ ragged_wf ragged_rewardFree)).lfp 0 : ℝ) := by
  have h :=
    (CsgQ.reach_bounds_of_answers ragged.toCsgQ ragged_wf ragged_rewardFree ragged_reach 0).1
  have hv : raggedLo.val 4 (0 : Fin ragged.nStates) = 3 / 5 := by decide +kernel
  have h3 : (3 / 5 : ℝ) = ((raggedLo.val 4 (0 : Fin ragged.nStates) : ℚ) : ℝ) := by
    rw [hv]
    norm_num
  exact h3.le.trans h

end Ragged

end Comp
