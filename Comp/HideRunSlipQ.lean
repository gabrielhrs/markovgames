/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ReachDeflate

/-!
# Hide, run or slip: an upper bound that iteration does not reach

**Status: confirmed by a clean `lake build`.** A three-state game after the hide-run-or-slip
example of Grobelna, Křetínský and Weininger, *Stopping Criteria for Value Iteration on Concurrent
Stochastic Reachability and Safety Games* (arXiv:2505.21087). Iterating the reachability operator
from above stays at `1` in it, while the value is `1/2`. This file certifies the interval
`[12/25, 1/2]` at the hiding place, with the one-sided checks of `Comp/ReachBounds.lean`.

**The game.** State `0` is the hiding place, state `1` is home and the target, state `2` is wet;
home and wet are terminal. The column player, who maximises the probability of getting home, runs
(action `0`) or hides (action `1`). The row player, who minimises it, throws (action `0`) or waits
(action `1`). Running into a throw ends wet. Hiding from a throw gets home. Running past a
waiting opponent gets home, ends wet, or lands back in hiding, a third each. Hiding from a waiting
opponent stays in hiding.

Against a vector that is `x` at the hiding place, `1` at home and `0` at wet, the stage game at
the hiding place is, with rows throw and wait and columns run and hide,

    [[0, 1], [(x + 1) / 3, x]]

For `x < 1/2` its value is `(x + 1) / (4 - 2 * x)`, which is above `x`. For `x ≥ 1/2` the pair
(wait, hide) is a saddle point and the value is `x`. So every `x` in `[1/2, 1]` gives a fixed
point of the operator, and the least of them, `1/2`, is the reachability value.

**The stall.** The row player can surely keep the play away from home only at wet (`hrsAvoid`),
so the tightened upper start of `Comp/ReachTrace.lean` is `(1, 1, 0)`. One step of the operator
returns it (`hrs_naive_stalls`): hiding secures the column player the current bound whatever the
row player does.

**The upper bound.** `(1/2, 1, 0)` is a pre-fixed point: at the hiding place the row player's
wait holds both columns to `1/2`. That is the whole upper certificate, `hrsHi`, one row strategy
per state. Any `x ≥ 1/2` in place of `1/2` passes the same check.

**Searching for it.** The hiding place is a closed component on its own: waiting against hiding
stays there. Its exit value against `x` is `(x + 1) / 3`, what running pays against a wait, since
against a wait hiding does not leave. `Comp/ReachDeflate.lean`'s search, run without rounding,
therefore moves the bound `1, 2/3, 5/9, 14/27, 41/81, 122/243, 365/729, …` towards `1/2`, one
deflation per round, and the vector it returns after six rounds is certified in
`hrs_reach_searched`.

**The lower bound.** From `0`, the exact iterates at the hiding place are
`1/4, 5/14, 19/46, 65/146, 211/454, 665/1394, …`. The lower run `hrsLo` rounds each value down to
hundredths before the next step, giving `1/4, 7/20, 2/5, 43/100, 9/20, 23/50, 47/100, 12/25`, and
each step is certified by the column player's strategy alone.

**How it is checked.** The `#eval`s print the region and the runs. The runs are pasted below as
literals, and every hypothesis is closed by `decide +kernel`.
-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

namespace HideRunSlip

/-! ## The model -/

/-- Hide, run or slip, as sparse data. Home and wet declare no transition, so they are terminal
    and `ModelData.transOf` supplies their self-loops. -/
abbrev hrs : ModelData where
  nAct1 := 2
  nAct2 := 2
  states :=
    [ -- state 0, the hiding place: rows {0 throw, 1 wait}, columns {0 run, 1 hide}
      ⟨0, [⟨0, 0, [(2, 1)], 0⟩, ⟨0, 1, [(1, 1)], 0⟩,
           ⟨1, 0, [(0, 1/3), (1, 1/3), (2, 1/3)], 0⟩, ⟨1, 1, [(0, 1)], 0⟩]⟩,
      -- state 1, home: terminal
      ⟨0, []⟩,
      -- state 2, wet: terminal
      ⟨0, []⟩ ]

instance : NeZero hrs.nStates := ⟨by decide⟩

instance : NeZero hrs.nAct1 := ⟨by decide⟩

instance : NeZero hrs.nAct2 := ⟨by decide⟩

/-! ## Validity -/

theorem hrs_shape : hrs.Shape := by decide

theorem hrs_nonzero : hrs.Nonzero := by decide +kernel

theorem hrs_stochastic : hrs.Stochastic := by decide +kernel

theorem hrs_wf : hrs.toCsgQ.WellFormed :=
  hrs.wellFormed hrs_shape hrs_stochastic

/-- No state reward and no transition reward anywhere. -/
theorem hrs_rewardFree : hrs.toCsgQ.RewardFree := by decide +kernel

/-- Getting home. -/
def hrsTarget : Finset (Fin hrs.nStates) := {1}

/-! ## The stall -/

#eval hrs.gRegionTr hrs_shape (Finset.univ \ hrsTarget)
-- expect: {2}    the set `hrsAvoid` below

/-- Where the row player can surely keep the play away from home: wet, and nowhere else. -/
def hrsAvoid : Finset (Fin hrs.nStates) := {2}

#eval hrs.reachRun hrsTarget (fun s => if s ∈ hrsAvoid then 0 else 1) 1
-- expect: both vectors `[1, 1, 0]`

/-- One step down from `0` on `hrsAvoid` and `1` elsewhere. At the hiding place the row player
    waits and the column player hides. -/
def hrsNaive : ReachRun where
  vals := [[1, 1, 0], [1, 1, 0]]
  rows := [[[(1, 1)], [], [(0, 1)]]]
  cols := [[[(1, 1)], [], [(0, 1)]]]

/-- **The upper iteration does not move.** One exact step of the reachability operator from
    `(1, 1, 0)` returns `(1, 1, 0)`. -/
theorem hrs_naive_stalls :
    hrs.ReachStepEn hrs_shape hrsTarget (hrsNaive.val 0) (hrsNaive.val 1) (hrsNaive.row 0)
      (hrsNaive.col 0) := by
  decide +kernel

/-! ## The two bounds -/

#eval hrs.reachUpperRun hrsTarget (fun s => ([1/2, 1, 0] : List ℚ).getD s.val 0)
-- expect: both vectors `[1/2, 1, 0]`, so the candidate is pre-fixed

/-- The upper vector `(1/2, 1, 0)`, one step of the operator from it, and the row strategies
    that certify it: at the hiding place the row player waits. -/
def hrsHi : ReachRun where
  vals := [[1/2, 1, 0], [1/2, 1, 0]]
  rows := [[[(1, 1)], [], [(0, 1)]]]
  cols := []

#eval hrs.reachLowerRun hrsTarget 100 9
-- expect: the values of `hrsLo` below

/-- Nine lower steps from `0`, each value rounded down to hundredths, with the column player's
    strategies. The first step only reaches the target; the hiding place moves from the second. -/
def hrsLo : ReachRun where
  vals := [[0, 0, 0], [0, 1, 0], [1/4, 1, 0], [7/20, 1, 0], [2/5, 1, 0], [43/100, 1, 0],
           [9/20, 1, 0], [23/50, 1, 0], [47/100, 1, 0], [12/25, 1, 0]]
  rows := []
  cols := [[[(1, 1)], [], [(0, 1)]],
           [[(0, 3/4), (1, 1/4)], [], [(0, 1)]],
           [[(0, 9/14), (1, 5/14)], [], [(0, 1)]],
           [[(0, 13/22), (1, 9/22)], [], [(0, 1)]],
           [[(0, 9/16), (1, 7/16)], [], [(0, 1)]],
           [[(0, 171/314), (1, 143/314)], [], [(0, 1)]],
           [[(0, 33/62), (1, 29/62)], [], [(0, 1)]],
           [[(0, 81/154), (1, 73/154)], [], [(0, 1)]],
           [[(0, 53/102), (1, 49/102)], [], [(0, 1)]]]

#eval hrs.reachDeflateRun hrs_shape hrsTarget 0 6
-- expect: both vectors `[365/729, 1, 0]`

/-- The upper vector the deflation search returns after six rounds, with the row strategies that
    certify it. -/
def hrsDeflated : ReachRun where
  vals := [[365/729, 1, 0], [365/729, 1, 0]]
  rows := [[[(1, 1)], [], [(0, 1)]]]
  cols := []

/-! ## The answer -/

/-- **Getting home, from the model.** The reachability value of the game `hrs` denotes lies
    between the ninth vector of the lower run and the pre-fixed vector `(1/2, 1, 0)`, at every
    state. -/
theorem hrs_reach :
    hrs.toCsgQ.Answers hrs_wf (Objective.reach hrsTarget)
      (Answer.interval (hrsLo.val 9) (hrsHi.val 0)) :=
  hrs.answers_reach_of_bounds hrs_shape hrs_stochastic hrs_rewardFree hrsTarget hrsLo hrsHi 9
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The same, with the upper vector found by search.** The lower run of `hrs_reach`, and the
    vector `(365/729, 1, 0)` that six rounds of deflation return. -/
theorem hrs_reach_searched :
    hrs.toCsgQ.Answers hrs_wf (Objective.reach hrsTarget)
      (Answer.interval (hrsLo.val 9) (hrsDeflated.val 0)) :=
  hrs.answers_reach_of_bounds hrs_shape hrs_stochastic hrs_rewardFree hrsTarget hrsLo
    hrsDeflated 9 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **From the hiding place, home is reached with probability between `12/25` and `1/2`.**
    `hrs_reach` at state `0`, as two inequalities between real numbers about the least fixed
    point of `Csg/ReachOp.lean`'s operator. -/
theorem hrs_reach_hiding :
    (12 / 25 : ℝ) ≤ (((hrs.toCsgQ.toCSG hrs_wf).reachOp (· ∈ hrsTarget)
        (CsgQ.toCSG_r_zero hrs.toCsgQ hrs_wf hrs_rewardFree)).lfp 0 : ℝ) ∧
      (((hrs.toCsgQ.toCSG hrs_wf).reachOp (· ∈ hrsTarget)
        (CsgQ.toCSG_r_zero hrs.toCsgQ hrs_wf hrs_rewardFree)).lfp 0 : ℝ) ≤ 1 / 2 := by
  have h := CsgQ.reach_bounds_of_answers hrs.toCsgQ hrs_wf hrs_rewardFree hrs_reach 0
  have hl : hrsLo.val 9 (0 : Fin hrs.nStates) = 12 / 25 := by decide +kernel
  have hu : hrsHi.val 0 (0 : Fin hrs.nStates) = 1 / 2 := by decide +kernel
  have hl' : (12 / 25 : ℝ) = ((hrsLo.val 9 (0 : Fin hrs.nStates) : ℚ) : ℝ) := by
    rw [hl]
    norm_num
  have hu' : ((hrsHi.val 0 (0 : Fin hrs.nStates) : ℚ) : ℝ) = 1 / 2 := by
    rw [hu]
    norm_num
  exact ⟨hl'.le.trans h.1, h.2.trans_eq hu'⟩

end HideRunSlip

end Comp
