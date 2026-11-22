/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ReachDeflate

/-!
# Hiding twice: the value to within `1/100`, from a search and two checks

**Status: confirmed by a clean `lake build`.** A six-state game built from the hiding place of
`Comp/HideRunSlipQ.lean`. The deflation search of `Comp/ReachDeflate.lean` proposes an upper
vector, a rounded lower run supplies the other side, and the kernel checks both. The conclusion
is `ht_reach_within`: at every state the lower vector is within `1/100` of the reachability value.
No strategy for the whole game is produced or examined, only one mixed action per state and step.

**The game.** The column player maximises the probability of getting home, by running (action
`0`) or hiding (action `1`); the row player minimises it, by throwing (action `0`) or waiting
(action `1`). Home, state `4`, is the target, and wet, state `5`, is lost; both are terminal.

* State `0`, the start: a fair coin between the outer hiding place and the lone one.
* State `3`, the lone hiding place, is the hiding place of `Comp/HideRunSlipQ.lean`.
* State `2`, the inner hiding place, differs from it in one entry: hiding from a waiting opponent
  stays there or falls back to the outer place, half each.
* State `1`, the outer hiding place. Running into a throw ends wet. Hiding from a throw moves to
  the inner place. Running past a waiting opponent stays, moves to the inner place, or ends wet,
  a third each. Hiding from a waiting opponent stays.

Write `a` for the value at the inner place and `b` at the outer one. The stage game at the outer
place is `[[0, a], [(a + b) / 3, b]]`, rows throw and wait, columns run and hide, and for every
`b` between `a / 2` and `a` the pair (wait, hide) is a saddle point with value `b`. So the
operator leaves the outer place wherever it is in that range. The least choice, `b = a / 2`, and
the inner place's own equation give `a = 2/5` and `b = 1/5`; with `1/2` at the lone place the
start is worth `7/20`. The intervals certified below are around those four numbers.

**What the search meets here.**

* The start is on no cycle, so it belongs to no closed component and is only ever updated by
  steps of the operator.
* The states that are neither home nor wet split into two closed components, the two hiding
  places in sequence and the lone one.
* The component `{1, 2}` needs deflating twice in a round. Its best exit is at the inner place,
  where running past a wait pays `(a + 1) / 3`. At the outer place the exit value is `0`: against
  a throw, hiding moves inward and does not leave, and running ends wet. Once the component is
  capped, the inner place is removed, the outer place is a closed component on its own, and its
  exit value `(a + b) / 3` caps it again.

**Rounding.** Unrounded, the search's values reach eleven-digit denominators in three rounds
here. Rounded up to thousandths it settles in ten rounds at `(0.352, 0.202, 0.402, 0.501)` on the
four live states. The lower run, rounded down to thousandths, reaches
`(0.346, 0.195, 0.397, 0.498)` in fifteen steps.

**How it is checked.** The `#eval`s print the region, the components and the runs. The runs are
pasted below as literals, and every hypothesis is closed by `decide +kernel`.
-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

namespace HideTwice

/-! ## The model -/

/-- Hiding twice, as sparse data. The start enables one joint action; home and wet declare no
    transition and are terminal. -/
abbrev ht : ModelData where
  nAct1 := 2
  nAct2 := 2
  states :=
    [ -- state 0, the start: a fair coin between the outer hiding place and the lone one
      ⟨0, [⟨0, 0, [(1, 1/2), (3, 1/2)], 0⟩]⟩,
      -- state 1, the outer hiding place: rows {0 throw, 1 wait}, columns {0 run, 1 hide}
      ⟨0, [⟨0, 0, [(5, 1)], 0⟩, ⟨0, 1, [(2, 1)], 0⟩,
           ⟨1, 0, [(1, 1/3), (2, 1/3), (5, 1/3)], 0⟩, ⟨1, 1, [(1, 1)], 0⟩]⟩,
      -- state 2, the inner hiding place
      ⟨0, [⟨0, 0, [(5, 1)], 0⟩, ⟨0, 1, [(4, 1)], 0⟩,
           ⟨1, 0, [(2, 1/3), (4, 1/3), (5, 1/3)], 0⟩, ⟨1, 1, [(2, 1/2), (1, 1/2)], 0⟩]⟩,
      -- state 3, the lone hiding place
      ⟨0, [⟨0, 0, [(5, 1)], 0⟩, ⟨0, 1, [(4, 1)], 0⟩,
           ⟨1, 0, [(3, 1/3), (4, 1/3), (5, 1/3)], 0⟩, ⟨1, 1, [(3, 1)], 0⟩]⟩,
      -- state 4, home: terminal
      ⟨0, []⟩,
      -- state 5, wet: terminal
      ⟨0, []⟩ ]

instance : NeZero ht.nStates := ⟨by decide⟩

instance : NeZero ht.nAct1 := ⟨by decide⟩

instance : NeZero ht.nAct2 := ⟨by decide⟩

/-! ## Validity -/

theorem ht_shape : ht.Shape := by decide

theorem ht_nonzero : ht.Nonzero := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']

theorem ht_stochastic : ht.Stochastic := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']

theorem ht_wf : ht.toCsgQ.WellFormed :=
  ht.wellFormed ht_shape ht_stochastic

/-- No state reward and no transition reward anywhere. -/
theorem ht_rewardFree : ht.toCsgQ.RewardFree := by decide +kernel

/-- Getting home. -/
def htTarget : Finset (Fin ht.nStates) := {4}

/-! ## The stall, and the sets the search deflates -/

#eval ht.gRegionTr ht_shape (Finset.univ \ htTarget)
-- expect: {5}    the set `htAvoid` below

/-- Where the row player can surely keep the play away from home: wet, and nowhere else. -/
def htAvoid : Finset (Fin ht.nStates) := {5}

#eval ht.reachRun htTarget (fun s => if s ∈ htAvoid then 0 else 1) 1
-- expect: both vectors `[1, 1, 1, 1, 1, 0]`

/-- One step down from `0` on `htAvoid` and `1` elsewhere. At each hiding place the row player
    waits and the column player hides. -/
def htNaive : ReachRun where
  vals := [[1, 1, 1, 1, 1, 0], [1, 1, 1, 1, 1, 0]]
  rows := [[[0, 1], [0, 1], [0, 1], [0, 1], [], [0, 1]]]
  cols := [[[0, 1], [0, 1], [0, 1], [0, 1], [], [0, 1]]]

/-- **The upper iteration does not move.** One exact step of the reachability operator from
    `(1, 1, 1, 1, 1, 0)` returns it. -/
theorem ht_naive_stalls :
    ht.toCsgQ.ReachStep htTarget (htNaive.val 0) (htNaive.val 1) (htNaive.row 0)
      (htNaive.col 0) := by
  decide +kernel

#eval ht.closedComps ht_shape (ht.nStates + 1) ((Finset.univ \ htTarget) \ htAvoid)
-- expect: [{2, 1}, {3}]    the two hiding places in sequence, and the lone one

/-! ## The upper vector, by search -/

#eval ht.reachDeflateRun ht_shape htTarget 0 2
-- expect: first vector `[5/9, 472/1485, 28/55, 5/9, 1, 0]`    two rounds, unrounded

#eval ht.reachDeflateRun ht_shape htTarget 1000 10
-- expect: the tables of `htHi` below

/-- The upper vector the deflation search returns after ten rounds in thousandths, one step of
    the operator from it, and the row strategies that certify it. At the inner hiding place the
    row player mixes. -/
def htHi : ReachRun where
  vals := [[44/125, 101/500, 201/500, 501/1000, 1, 0],
           [703/2000, 101/500, 701/1748, 501/1000, 1, 0]]
  rows := [[[0, 1], [0, 1], [62/437, 375/437], [0, 1], [], [0, 1]]]
  cols := []

/-! ## The lower run -/

#eval ht.reachLowerRun htTarget 1000 15
-- expect: the tables of `htLo` below

/-- Fifteen lower steps from `0`, each value rounded down to thousandths, with the column
    player's strategies. -/
def htLo : ReachRun where
  vals := [[0, 0, 0, 0, 0, 0],
           [0, 0, 0, 0, 1, 0],
           [0, 0, 1/4, 1/4, 1, 0],
           [1/8, 31/500, 161/500, 357/1000, 1, 0],
           [209/1000, 53/500, 44/125, 103/250, 1, 0],
           [259/1000, 67/500, 46/125, 111/250, 1, 0],
           [289/1000, 153/1000, 189/500, 58/125, 1, 0],
           [77/250, 83/500, 48/125, 119/250, 1, 0],
           [321/1000, 7/40, 97/250, 121/250, 1, 0],
           [329/1000, 181/1000, 391/1000, 489/1000, 1, 0],
           [67/200, 93/500, 393/1000, 123/250, 1, 0],
           [339/1000, 189/1000, 79/200, 247/500, 1, 0],
           [341/1000, 191/1000, 99/250, 62/125, 1, 0],
           [343/1000, 193/1000, 397/1000, 497/1000, 1, 0],
           [69/200, 97/500, 397/1000, 249/500, 1, 0],
           [173/500, 39/200, 397/1000, 249/500, 1, 0]]
  rows := []
  cols := [[[0, 1], [0, 1], [0, 1], [0, 1], [], [0, 1]],
           [[0, 1], [0, 1], [3/4, 1/4], [3/4, 1/4], [], [0, 1]],
           [[0, 1], [3/4, 1/4], [21/31, 10/31], [9/14, 5/14], [], [0, 1]],
           [[0, 1], [65/97, 32/97], [1212/1873, 661/1873], [1929/3286, 1357/3286], [], [0, 1]],
           [[0, 1], [369/598, 229/598], [2313/3665, 1352/3665], [441/794, 353/794], [], [0, 1]],
           [[0, 1], [351/602, 251/602], [749/1205, 456/1205], [417/778, 361/778], [], [0, 1]],
           [[0, 1], [75/134, 59/134], [339/551, 212/551], [67/128, 61/128], [], [0, 1]],
           [[0, 1], [327/602, 275/602], [2175/3559, 1384/3559], [131/254, 123/254], [], [0, 1]],
           [[0, 1], [639/1202, 563/1202], [4311/7087, 2776/7087], [387/758, 371/758], [], [0, 1]],
           [[0, 1], [315/601, 286/601], [2142/3533, 1391/3533], [1533/3022, 1489/3022], [],
            [0, 1]],
           [[0, 1], [207/400, 193/400], [609/1007, 398/1007], [381/754, 373/754], [], [0, 1]],
           [[0, 1], [309/601, 292/601], [236/391, 155/391], [253/502, 249/502], [], [0, 1]],
           [[0, 1], [615/1202, 587/1202], [4239/7031, 2792/7031], [189/376, 187/376], [], [0, 1]],
           [[0, 1], [306/601, 295/601], [2115/3512, 1397/3512], [503/1002, 499/1002], [], [0, 1]],
           [[0, 1], [203/400, 197/400], [4227/7021, 2794/7021], [753/1502, 749/1502], [], [0, 1]]]

/-! ## The answer -/

/-- **Getting home, from the model.** The reachability value of the game `ht` denotes lies
    between the fifteenth vector of the lower run and the vector the deflation search returned,
    at every state. -/
theorem ht_reach :
    ht.toCsgQ.Answers ht_wf (Objective.reach htTarget)
      (Answer.interval (htLo.val 15) (htHi.val 0)) :=
  ht.answers_reach_of_bounds ht_shape ht_stochastic ht_rewardFree htTarget htLo htHi 15
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The two vectors are within `1/100` of each other at every state. -/
theorem ht_gap : ∀ s : Fin ht.nStates, htHi.val 0 s - htLo.val 15 s ≤ 1 / 100 := by
  decide +kernel

/-- **The lower vector is within `1/100` of the reachability value, at every state.** `ht_reach`
    and `ht_gap`, as a statement between real numbers about the least fixed point of
    `Csg/ReachOp.lean`'s operator. -/
theorem ht_reach_within (s : Fin ht.nStates) :
    |(((ht.toCsgQ.toCSG ht_wf).reachOp (· ∈ htTarget)
        (CsgQ.toCSG_r_zero ht.toCsgQ ht_wf ht_rewardFree)).lfp s : ℝ)
      - ((htLo.val 15 s : ℚ) : ℝ)| ≤ 1 / 100 := by
  have h := CsgQ.reach_bounds_of_answers ht.toCsgQ ht_wf ht_rewardFree ht_reach s
  have hq : ((htHi.val 0 s - htLo.val 15 s : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (ht_gap s)
  have hg : ((htHi.val 0 s : ℚ) : ℝ) - ((htLo.val 15 s : ℚ) : ℝ) ≤ 1 / 100 := by
    push_cast at hq
    linarith
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2, hg]⟩

end HideTwice

end Comp
