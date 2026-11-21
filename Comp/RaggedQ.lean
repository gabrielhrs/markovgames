/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelDataQualitative

/-!
# A model whose action sets vary by state: the ragged stand-off

**Status: confirmed by a clean `lake build`.**

`Comp/LeakyGateQ.lean` and `Comp/HideOrRunDataQ.lean` enable every action in every state, so for
them a state's enabled set is the whole namespace, padding never selects anything, and the narrowed
operators of `Comp/ModelDataQualitative.lean` range over exactly what the dense ones do. This model
is the one where they do not:

* three row actions and three column actions globally, and no state enables all of both;
* state `0` enables two of each, state `1` one row action and all three column actions, state `2`
  the reverse;
* state `3` declares no transition at all, so it is terminal and `ModelData.transOf` supplies its
  self-loop.

**The game.** State `1` is the goal and state `3` the sink.

* State `0` is a stand-off. The row player waits (action `2`) or runs (action `0`); the column
  player throws (action `1`) or waits (action `2`). Running into a throw ends in the sink and
  running past a waiting opponent arrives. Waiting out a throw arrives half the time and otherwise
  stays; both waiting stays.
* State `1` is the column player's alone: stay, or move to state `2`.
* State `2` is the row player's alone: stay, move to the goal, or walk into the sink.

**The answers.**

* Sure safety of `{0, 1, 2}`: all of it. The sink can be avoided for certain from everywhere else.
* Almost-sure reachability of `{1}`: `{1, 2}`.
* Limit-sure reachability of `{1}`: `{0, 1, 2}`.

So the two reachability modes separate at the stand-off, as they do in
`Comp/HideOrRunDataQ.lean` -- here with a fractional weight in the kernel, action sets that differ
from state to state, and a terminal state.

**What padding looks like.** At the stand-off the row action `1` is disabled, and the kernel a
`CSG` needs is total, so `1` is read as the action of the state's first listed transition, which
is `2`. `ragged_aSet_standoff` and `ragged_lw_standoff` show the dense operators carrying `1`
wherever they carry `2`; `ragged_aTr_standoff` and `ragged_lwTr_standoff` show the narrowed ones
returning the enabled part of the same sets. The entry points run the narrowed loops, and
`ModelData.gRegionTr_eq`, `afRegionTr_eq` and `lfRegionTr_eq` are why the regions are the dense
ones.
-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

namespace Ragged

/-! ## The model -/

/-- The ragged stand-off, as sparse data. Each transition names its joint action, and a state
    lists only the pairs it enables. -/
abbrev ragged : ModelData where
  nAct1 := 3
  nAct2 := 3
  states :=
    [ -- state 0, the stand-off: rows {2 wait, 0 run}, columns {1 throw, 2 wait}
      ⟨0, [⟨2, 1, [(0, 1/2), (1, 1/2)], 0⟩, ⟨2, 2, [(0, 1)], 0⟩,
           ⟨0, 1, [(3, 1)], 0⟩,             ⟨0, 2, [(1, 1)], 0⟩]⟩,
      -- state 1, the goal: one row action, three column actions
      ⟨0, [⟨1, 0, [(1, 1)], 0⟩, ⟨1, 1, [(2, 1)], 0⟩, ⟨1, 2, [(1, 1)], 0⟩]⟩,
      -- state 2: three row actions, one column action
      ⟨0, [⟨0, 2, [(2, 1)], 0⟩, ⟨1, 2, [(1, 1)], 0⟩, ⟨2, 2, [(3, 1)], 0⟩]⟩,
      -- state 3, the sink: terminal, nothing declared
      ⟨0, []⟩ ]

instance : NeZero ragged.nStates := ⟨by decide⟩

instance : NeZero ragged.nAct1 := ⟨by decide⟩

instance : NeZero ragged.nAct2 := ⟨by decide⟩

/-! ## Validity

`Shape` covers the declared transitions and the sink's supplied self-loop alike, since every
condition quantifies over `transOf`. In particular `Total` holds at each state of its own enabled
product -- two by two, one by three, three by one, one by one -- and not of the three-by-three
namespace. -/

theorem ragged_shape : ragged.Shape := by decide

theorem ragged_nonneg : ragged.Nonneg := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']

theorem ragged_nonzero : ragged.Nonzero := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']

theorem ragged_stochastic : ragged.Stochastic := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']

theorem ragged_wf : ragged.toCsgQ.WellFormed :=
  ragged.wellFormed ragged_shape ragged_stochastic

/-! ## Enabled actions, padding, and the terminal state -/

#eval ragged.enabled1 ragged_shape 0
-- expect: {2, 0}      wait and run, in the order the transitions list them

#eval ragged.enabled2 ragged_shape 0
-- expect: {1, 2}      throw and wait

#eval ragged.enabled1 ragged_shape 3
-- expect: {0}         the sink's supplied self-loop is on the joint action (0, 0)

#eval ragged.supportOf ragged_shape 0 2 1
-- expect: {0, 1}      waiting out a throw: the coin

#eval ragged.supportOf ragged_shape 0 1 0
-- expect: {0, 1}      both actions disabled; read as (2, 1), the first transition's

#eval ragged.supportOf ragged_shape 3 2 1
-- expect: {3}         the sink, whatever is played

/-! ## The regions -/

/-- Every state but the sink: the safe set, and as it turns out both the sure-safety region and
    the value-1 set. -/
def raggedLive : Finset (Fin ragged.nStates) := {0, 1, 2}

/-- Reaching the goal. -/
def raggedTarget : Finset (Fin ragged.nStates) := {1}

/-- The almost-sure region: the goal, and the state from which the row player walks to it. -/
def raggedAlmost : Finset (Fin ragged.nStates) := {1, 2}

#eval ragged.gRegionTr ragged_shape raggedLive
-- expect: {0, 1, 2}

#eval ragged.gRegionTr ragged_shape {0, 1}
-- expect: ∅           the goal leaks to state 2, and then the stand-off cannot be held either

#eval ragged.afRegionTr ragged_shape raggedTarget
-- expect: {2, 1}

#eval ragged.lfRegionTr ragged_shape raggedTarget
-- expect: {0, 2, 1}

#eval Qual.afRegion (ragged.supportOf ragged_shape) raggedTarget
-- expect: {2, 1}      the dense loops, over all nine joint actions at every state

#eval Qual.lfRegion (ragged.supportOf ragged_shape) raggedTarget
-- expect: {0, 2, 1}

/-! ## Sure safety -/

/-- **The sink can be avoided for certain from every other state.** At the stand-off by waiting,
    at state `2` by not walking in, and at the goal because the column player's moves stay inside
    `{1, 2}`. -/
theorem ragged_answers_safe :
    ragged.toCsgQ.Answers ragged_wf (Objective.sureSafe raggedLive)
      (Answer.region raggedLive) :=
  ragged.answers_sureSafe_of_fix ragged_shape ragged_stochastic ragged_nonzero raggedLive
    raggedLive (by decide)

/-! ## Almost-sure and limit-sure reachability -/

/-- **Almost-sure reachability of the goal**: the goal and state `2`, and not the stand-off. A
    row player who never runs can be made to wait for ever, and one who runs risks the sink. -/
theorem ragged_answers_AF :
    ragged.toCsgQ.Answers ragged_wf (Objective.almostReach raggedTarget)
      (Answer.region raggedAlmost) :=
  ragged.answers_almostReach_of_fix ragged_shape ragged_stochastic ragged_nonzero raggedTarget
    raggedAlmost (by decide)

/-- **The value-1 set**: the stand-off as well. Running with small probability arrives with
    probability as close to one as desired. -/
theorem ragged_answers_LF :
    ragged.toCsgQ.Answers ragged_wf (Objective.limitReach raggedTarget)
      (Answer.region raggedLive) :=
  ragged.answers_limitReach_of_fix ragged_shape ragged_stochastic ragged_nonzero raggedTarget
    raggedLive (by decide)

/-- **The separation, on a model with per-state action sets.** The stand-off is a value-1 state
    from which no strategy reaches the goal almost surely. -/
theorem ragged_separation :
    (0 : Fin ragged.nStates) ∈ (ragged.toCsgQ.toCSG ragged_wf).LF ↑raggedTarget ∧
      (0 : Fin ragged.nStates) ∉ (ragged.toCsgQ.toCSG ragged_wf).AF ↑raggedTarget := by
  have hlf := CsgQ.LF_eq_of_answers ragged.toCsgQ ragged_wf ragged_answers_LF
  have haf := CsgQ.AF_eq_of_answers ragged.toCsgQ ragged_wf ragged_answers_AF
  refine ⟨?_, ?_⟩
  · rw [hlf]
    simp only [Fin.isValue, SetLike.mem_coe]
    decide
  · rw [haf]
    simp only [Fin.isValue, SetLike.mem_coe]
    decide

/-! ## The two families, side by side at the stand-off

The row actions safe for `{0, 1, 2}` at state `0`, and the innermost `μW` climb's result there,
computed both ways. The dense sets contain the disabled action `1` exactly when they contain `2`,
its representative -- pad-saturation, on an instance -- and the narrowed sets are their
intersections with `enabled1 0 = {0, 2}`. -/

/-- Dense: waiting is safe, and the disabled action `1` is carried along with it. -/
theorem ragged_aSet_standoff :
    Qual.aSet (ragged.supportOf ragged_shape) ∅ raggedLive 0 = {1, 2} := by decide

/-- Narrowed: waiting is safe. -/
theorem ragged_aTr_standoff : ragged.aTr ragged_shape ∅ raggedLive 0 = {2} := by decide

/-- Dense: the climb ends at the whole namespace, running having joined once the throw is
    answered. -/
theorem ragged_lw_standoff :
    Qual.lw (ragged.supportOf ragged_shape) raggedTarget raggedLive 0 = Finset.univ := by decide

/-- Narrowed: it ends at the two actions the state enables. -/
theorem ragged_lwTr_standoff :
    ragged.lwTr ragged_shape raggedTarget raggedLive 0 = {0, 2} := by decide

end Ragged

end Comp
