/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelDataQualitative

/-!
# Hide-or-run from a model: the almost-sure/limit-sure separation, computed

**Status: confirmed by a clean `lake build`.**

The end of the line that began with `Comp/Basic.lean`. A model arrives as data; two objectives are
posed of it; both are answered by running an algorithm and checking the result with `decide`; and
the answers differ, in the way de Alfaro-Henzinger-Kupferman's hide-or-run game exists to show.

`Comp/HideOrRunQ.lean` proves the same two facts about the same game with the operators written out
for it directly -- its own support table, its own `aC`/`bC`/`lStepC`, its own `lw_fixed`, its own
middle and outer chains. Here the game is thirty lines of lists and everything above them is
`Comp/ModelDataQualitative.lean`, which is generic in the model.

**The two answers.** State `0` is the stand-off, `1` the goal, `2` death; row action `0` is *run*
and `1` is *wait*; column action `0` is *throw* and `1` is *wait*.

* `LF {1} = {0, 1}` -- from the stand-off the runner reaches the goal with probability arbitrarily
  close to one, by randomising.
* `AF {1} = {1}` -- but no strategy gets there almost surely.

`hrd_separation` states the gap directly, through `Comp/Objective.lean`'s extraction lemmas: the
two objectives go in as data and the two set equalities come back out, with nothing assumed in
between.

**What each answer costs the caller: one `decide`**, naming a region. `Comp/FixLoop.lean`'s loops
locate their own fixed points and are proved to terminate at one, so no iteration count and no
fixed-point check appears in this file.

Both answers are also proved the counted way -- `hrd_answers_LF_counted`, `hrd_AF_le_winning`,
`hrd_AF_le_target` and `hrd_lw` -- which exhibits the descent one step at a time and lets the build
check that the two routes agree. Driving the limit-sure line that way requires `hrd_lw`, a `decide`
over every pair of regions and every state: `2 ^ 3 × 2 ^ 3 × 3` instances here, and
`2 ^ 30 × 2 ^ 30 × 30` at thirty states.

**No weight is ever evaluated.** The kernel is all point masses here, but that is incidental: the
weights appear in `hrd_nonneg`, `hrd_nonzero` and `hrd_stochastic`, and nowhere in any of the
chains. `Comp/LeakyGateQ.lean` is the same machinery on a kernel full of halves.

-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

namespace HideOrRunData

/-! ## The model -/

/-- Hide-or-run as sparse data. Every row is a point mass, and the game is reward-free. -/
abbrev hrd : ModelData where
  nRow := 2
  nCol := 2
  states :=
    [ -- state 0, the stand-off: run into a throw dies, run into a wait arrives,
      -- waiting out a throw arrives, waiting against a wait stays
      ⟨0, [[⟨[(2, 1)], 0⟩, ⟨[(1, 1)], 0⟩],
           [⟨[(1, 1)], 0⟩, ⟨[(0, 1)], 0⟩]]⟩,
      -- state 1, the goal: absorbing
      ⟨0, [[⟨[(1, 1)], 0⟩, ⟨[(1, 1)], 0⟩],
           [⟨[(1, 1)], 0⟩, ⟨[(1, 1)], 0⟩]]⟩,
      -- state 2, death: absorbing
      ⟨0, [[⟨[(2, 1)], 0⟩, ⟨[(2, 1)], 0⟩],
           [⟨[(2, 1)], 0⟩, ⟨[(2, 1)], 0⟩]]⟩ ]

instance : NeZero hrd.nStates := ⟨by decide⟩

instance : NeZero hrd.nRow := ⟨by decide⟩

instance : NeZero hrd.nCol := ⟨by decide⟩

/-! ## Validity -/

theorem hrd_inRange : hrd.InRange := by decide

theorem hrd_nonneg : hrd.Nonneg := by
  intro s a1 a2
  fin_cases s <;> fin_cases a1 <;> fin_cases a2 <;>
    norm_num [ModelData.rowAt, ModelData.stateAt]

theorem hrd_nonzero : hrd.Nonzero := by
  intro s a1 a2
  fin_cases s <;> fin_cases a1 <;> fin_cases a2 <;>
    norm_num [ModelData.rowAt, ModelData.stateAt]

theorem hrd_stochastic : hrd.Stochastic := by
  intro s a1 a2
  fin_cases s <;> fin_cases a1 <;> fin_cases a2 <;>
    norm_num [ModelData.rowAt, ModelData.stateAt]

theorem hrd_wf : hrd.toCsgQ.WellFormed :=
  hrd.wellFormed hrd_inRange hrd_stochastic

/-! ## The question, and the regions the runs produce -/

/-- Reaching the goal. -/
def hrdTarget : Finset (Fin hrd.nStates) := {1}

/-- The value-1 set: the goal, and the stand-off. -/
def hrdWinning : Finset (Fin hrd.nStates) := {0, 1}

#eval decide hrd.InRange
-- expect: true

#eval (hrd.midOf hrd_inRange 2 hrdTarget Finset.univ)^[2] ∅
-- expect: {0, 1}      the limit-sure middle chain at `univ`

#eval (hrd.afStepOf hrd_inRange hrdTarget hrdWinning)^[1] ∅
-- expect: {1}         the almost-sure chain, one outer step later, loses the stand-off

/-! ## The innermost iteration, once and for all

`LW` climbs on `Finset (Fin 2)`, which has height two, so two steps bound a monotone climb; this
states that rather than relying on it. One `decide`, over every pair of regions and every state,
which is `2 ^ 3 × 2 ^ 3 × 3` instances.

Only the counted route needs it. `Comp/FixLoop.lean` proves the innermost loop terminates, so
`ModelData.lwOf` is `CSG.LW` at every `x` without a hypothesis. -/

theorem hrd_lw : ∀ (x y : Finset (Fin hrd.nStates)) (s : Fin hrd.nStates),
    hrd.lStepOf hrd_inRange x y s ((hrd.lStepOf hrd_inRange x y s)^[2] ∅)
      = (hrd.lStepOf hrd_inRange x y s)^[2] ∅ := by
  decide

/-! ## Limit-sure reachability -/

#eval hrd.lfRegion hrd_inRange hrdTarget
-- expect: {0, 1}      three nested loops, run to termination

/-- One outer step: `{0, 1}` bounds `LF` from above. The descent, one step at a time. -/
theorem hrd_LF_le : (hrd.toCsgQ.toCSG hrd_wf).LF ↑hrdTarget
    ≤ (↑hrdWinning : Set (Fin hrd.nStates)) :=
  hrd.LF_le_of_data_step hrd_inRange hrd_stochastic hrd_nonzero 2 hrdTarget Finset.univ
    hrdWinning 2 (fun x s => hrd_lw x Finset.univ s) (by decide) (by decide)
    (CsgQ.LF_le_univ hrd.toCsgQ hrd_wf hrdTarget)

/-- **The value-1 set, from the model.** One `decide`, naming the region.

    This is the line the whole loop exercise was for. Driving it by hand costs `hrd_lw` -- 192
    `decide` instances at three states, and `2 ^ 30` at thirty -- plus an iteration count at each of
    three nested levels. Here the three loops find their own fixed points and the caller says only
    what came back. -/
theorem hrd_answers_LF :
    hrd.toCsgQ.Answers hrd_wf (Objective.limitReach hrdTarget) (Answer.region hrdWinning) :=
  hrd.answers_limitReach_of_fix hrd_inRange hrd_stochastic hrd_nonzero hrdTarget hrdWinning
    (by decide)

/-- The counted form of the same statement, kept so the build checks both routes agree. -/
theorem hrd_answers_LF_counted :
    hrd.toCsgQ.Answers hrd_wf (Objective.limitReach hrdTarget) (Answer.region hrdWinning) :=
  hrd.answers_limitReach_of_data hrd_inRange hrd_stochastic hrd_nonzero 2 hrdTarget hrdWinning 2
    (fun x s => hrd_lw x hrdWinning s) (by decide) (by decide) hrd_LF_le

/-! ## Almost-sure reachability -/

/-- First outer step: the two modes still agree. -/
theorem hrd_AF_le_winning : (hrd.toCsgQ.toCSG hrd_wf).AF ↑hrdTarget
    ≤ (↑hrdWinning : Set (Fin hrd.nStates)) :=
  hrd.AF_le_of_data_step hrd_inRange hrd_stochastic hrd_nonzero hrdTarget Finset.univ
    hrdWinning 2 (by decide) (by decide) (CsgQ.AF_le_univ hrd.toCsgQ hrd_wf hrdTarget)

/-- Second outer step: and here they part. Restricted to the row actions safe for `{0, 1}`, the
    runner can only wait, and waiting against a wait returns to the stand-off. -/
theorem hrd_AF_le_target : (hrd.toCsgQ.toCSG hrd_wf).AF ↑hrdTarget
    ≤ (↑hrdTarget : Set (Fin hrd.nStates)) :=
  hrd.AF_le_of_data_step hrd_inRange hrd_stochastic hrd_nonzero hrdTarget hrdWinning
    hrdTarget 1 (by decide) (by decide) hrd_AF_le_winning

#eval hrd.afRegion hrd_inRange hrdTarget
-- expect: {1}         the nested loops, run to termination

/-- **Almost-sure reachability, from the model**: the goal alone.

    One `decide`, naming the region. The two outer steps above are the same descent taken one step
    at a time, which shows *where* the stand-off is lost; `afRegion` locates it without being given
    a step count. -/
theorem hrd_answers_AF :
    hrd.toCsgQ.Answers hrd_wf (Objective.almostReach hrdTarget) (Answer.region hrdTarget) :=
  hrd.answers_almostReach_of_fix hrd_inRange hrd_stochastic hrd_nonzero hrdTarget hrdTarget
    (by decide)

/-! ## The separation -/

/-- **The gap, from a model given as data.** The stand-off is a value-1 state for reaching the goal
    from which no strategy wins almost surely.

    Both halves come out of the `Answers` relation through `Comp/Objective.lean`'s extraction
    lemmas, which is what they are for: two objectives go in as data, two set equalities come back,
    and the statement below assumes nothing that was not computed.

    `SetLike.mem_coe` strips the `Finset`-to-`Set` coercion and `decide` finishes. The second half
    needs the state count: in `Fin n` the elements `0` and `1` are equal exactly when `n = 1`, so
    `0 ≠ 1` here is `hrd.nStates ≠ 1`, which is why it is `decide` and not `simp`. -/
theorem hrd_separation :
    (0 : Fin hrd.nStates) ∈ (hrd.toCsgQ.toCSG hrd_wf).LF ↑hrdTarget ∧
      (0 : Fin hrd.nStates) ∉ (hrd.toCsgQ.toCSG hrd_wf).AF ↑hrdTarget := by
  have hlf := CsgQ.LF_eq_of_answers hrd.toCsgQ hrd_wf hrd_answers_LF
  have haf := CsgQ.AF_eq_of_answers hrd.toCsgQ hrd_wf hrd_answers_AF
  refine ⟨?_, ?_⟩
  · rw [hlf]
    simp only [Fin.isValue, SetLike.mem_coe]
    decide
  · rw [haf]
    simp only [Fin.isValue, SetLike.mem_coe]
    decide

end HideOrRunData

end Comp
