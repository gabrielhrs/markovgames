/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelDataQualitative

/-!
# A probabilistic model, as data: the leaky gate

**Status: confirmed by a clean `lake build`.**

The first game in this project whose kernel contains a genuine fraction *and* whose answer is
checked by the kernel. Four states, two actions each, written as sparse data rather than as a Lean
definition, with a sure-safety objective.

**The game.** State `3` is the sink. The row player wants to stay out of it.

* States `0` and `1` form a pair the row player can hold: its action `0` keeps the play inside
  `{0, 1}` whatever the column player does, in one case by a coin flip between the two.
* State `2` is the leak. Its action `0` risks the sink on a coin flip and its action `1` walks into
  the sink outright, so there is no safe move there at all.
* `safe` is everything but the sink, and the answer is `{0, 1}`: the descent gives
  `univ ⊇ {0,1,2} ⊇ {0,1}`, losing state `2` once the iteration can see one step past it.

The rewards are set but irrelevant -- a reward of `1` for sitting in the sink, and `1` for the
action that jumps there deliberately. A sure-safety objective reads neither, which is worth seeing
in a file where both fields are populated.

**What makes the `decide`s possible.** Lean's kernel cannot evaluate `(1/2 : ℚ)` at all, because
the literal is a *division* and `Nat.gcd` is beyond its reduction
(`Comp/RockPaperScissorsQ.lean` works the case through). The other worked instances in `Comp/` have
`0`/`1` kernels, where the question does not arise.

It arises here, and the answer is that nothing in the computation looks at a weight.
`Comp/ModelData.lean`'s `supportOf` is built from `keysNat`, the row's keys, which is `ℕ` data; the
weights are confined to three side conditions (`Nonneg`, `Nonzero`, `Stochastic`) that are proved
once, by `norm_num`, outside the computation. Above that line the qualitative operators are finite
set arithmetic over `Fin 4` and `Fin 2`, and `gate_answers` closes both of its fixed-point checks
with `decide`.

So the division of labour is: `norm_num` for the arithmetic, once per model; `decide` for the
algorithm, however many iterations it takes. It is the same split as the per-instance quarantine
lemmas in `Comp/SafetyChainQ.lean` and `Comp/HideOrRunQ.lean`, sited in the data layer rather than
written per game, and it extends to fractional weights.

**Two objectives, one model.** The second half of the file asks a different question of the same
data -- almost-sure reachability of state `0` -- which is the point of keeping the objective a
separate datum. The answer is `{0, 1}`: from state `1` the row player reaches `0` almost surely,
not by forcing it but by taking a coin flip repeatedly, and that is a conclusion about a `1/2` that
the kernel checks without ever evaluating one.

-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

namespace LeakyGate

/-! ## The model -/

/-- The leaky gate, as sparse data. `abbrev` so that instance search can see the numerals through
    the projections -- `nStates` is `states.length`, so there is one more layer here than with a
    stored count. -/
abbrev gate : ModelData where
  nRow := 2
  nCol := 2
  states :=
    [ -- state 0: action 0 holds the pair, action 1 risks the sink
      ⟨0, [[⟨[(0, 1/2), (1, 1/2)], 0⟩, ⟨[(1, 1)], 0⟩],
           [⟨[(3, 1)], 1⟩, ⟨[(0, 1)], 0⟩]]⟩,
      -- state 1: same shape, mirrored
      ⟨0, [[⟨[(0, 1/2), (1, 1/2)], 0⟩, ⟨[(0, 1)], 0⟩],
           [⟨[(3, 1)], 1⟩, ⟨[(1, 1)], 0⟩]]⟩,
      -- state 2: the leak -- every row action can be answered into the sink
      ⟨0, [[⟨[(2, 1/2), (3, 1/2)], 0⟩, ⟨[(2, 1)], 0⟩],
           [⟨[(3, 1)], 1⟩, ⟨[(2, 1)], 0⟩]]⟩,
      -- state 3: the sink, and the only state with a reward
      ⟨1, [[⟨[(3, 1)], 0⟩, ⟨[(3, 1)], 0⟩],
           [⟨[(3, 1)], 0⟩, ⟨[(3, 1)], 0⟩]]⟩ ]

instance : NeZero gate.nStates := ⟨by decide⟩

instance : NeZero gate.nRow := ⟨by decide⟩

instance : NeZero gate.nCol := ⟨by decide⟩

/-! ## Validity: the only rational arithmetic in the file

Three conditions, each a finite collection of facts about literal weights. `InRange` is pure `ℕ` and
goes by `decide`; the other three mention the weights and so go by `norm_num`, which is the whole
rational content of this instance. -/

/-- Every successor index is a state. Pure `ℕ`. -/
theorem gate_inRange : gate.InRange := by decide

/-- No weight is negative. -/
theorem gate_nonneg : gate.Nonneg := by
  intro s a1 a2
  fin_cases s <;> fin_cases a1 <;> fin_cases a2 <;>
    norm_num [ModelData.rowAt, ModelData.stateAt]

/-- No weight is zero -- so a row's keys are its support, which is what keeps the kernel out of
    the rationals. -/
theorem gate_nonzero : gate.Nonzero := by
  intro s a1 a2
  fin_cases s <;> fin_cases a1 <;> fin_cases a2 <;>
    norm_num [ModelData.rowAt, ModelData.stateAt]

/-- Every row is a distribution -- the condition the fractional weights have to meet. -/
theorem gate_stochastic : gate.Stochastic := by
  intro s a1 a2
  fin_cases s <;> fin_cases a1 <;> fin_cases a2 <;>
    norm_num [ModelData.rowAt, ModelData.stateAt]

/-- …and hence a well-formed game. -/
theorem gate_wf : gate.toCsgQ.WellFormed :=
  gate.wellFormed gate_inRange gate_stochastic

/-! ## Running it -/

/-- Everything but the sink. -/
def gateSafe : Finset (Fin gate.nStates) := {0, 1, 2}

/-- The answer: the pair the row player can hold. -/
def gateGood : Finset (Fin gate.nStates) := {0, 1}

#eval decide gate.InRange
-- expect: true

#eval decide gate.Stochastic
-- expect: true        (compiled code has no trouble with the halves)

#eval gate.supportOf gate_inRange 0 0 0
-- expect: {0, 1}      the coin flip's two outcomes, read off the row

#eval gate.supportOf gate_inRange 2 0 0
-- expect: {2, 3}      the leak

#eval gate.gStepOf gate_inRange gateSafe Finset.univ
-- expect: {0, 1, 2}   one step only removes the sink

#eval (gate.gStepOf gate_inRange gateSafe)^[2] Finset.univ
-- expect: {0, 1}      and the second removes the leak

#eval (gate.gStepOf gate_inRange gateSafe)^[3] Finset.univ
-- expect: {0, 1}      stabilised

#eval gate.gRegion gate_inRange gateSafe
-- expect: {0, 1}      and the same, without being told how many steps to take

/-! ## The answer -/

/-- **A probabilistic model, computed and checked.** The sure-safety region of a game whose kernel
    contains halves, as an answer to an objective, with both fixed-point checks closed by `decide`.

    The weights took part in the three validity theorems above and nowhere else: the descent itself
    never evaluated one. That is what makes the `decide`s possible, and it is the point of the whole
    sparse layer.

    No iteration count and no fixed-point check: `gRegion` runs `Comp/FixLoop.lean`'s loop --
    apply, compare, stop -- which is proved to terminate at a fixed point, so the single `decide`
    states only which region came back and the `#eval`s above are illustrative. -/
theorem gate_answers :
    gate.toCsgQ.Answers gate_wf (Objective.sureSafe gateSafe) (Answer.region gateGood) :=
  gate.answers_sureSafe_of_fix gate_inRange gate_stochastic gate_nonzero gateSafe gateGood
    (by decide)

/-- The same statement by way of `answers_sureSafe_of_data`, the counted interface, which takes the
    step count as an argument. -/
theorem gate_answers_counted :
    gate.toCsgQ.Answers gate_wf (Objective.sureSafe gateSafe) (Answer.region gateGood) :=
  gate.answers_sureSafe_of_data gate_inRange gate_stochastic gate_nonzero gateSafe gateGood 2
    (by decide) (by decide)

/-! ## A second objective: almost-sure reachability

The same model, a different question. `Comp/ModelDataQualitative.lean` carries `A`, `B`, `Apre1`
and the almost-sure middle step over to the rows, so nothing here is specific to this game: the
three wrappers take `decide`-able facts about the data and return statements about `CSG.AF`.

Asking for almost-sure reachability of state `0`, the answer is `{0, 1}` -- state `1` is *not* in
the target and the row player cannot force a move to `0` in one step, but it can play the coin
flip, and repeated coin flips reach `0` with probability one. That is a genuinely probabilistic
conclusion, and the kernel reaches it without evaluating a single weight.

The outer descent takes one step (`univ`, then `{0, 1}`, then stop) and each inner chain takes two
(`∅`, `{0}`, `{0, 1}`). -/

/-- Reaching state `0`. -/
def gateTarget : Finset (Fin gate.nStates) := {0}

#eval gate.afStepOf gate_inRange gateTarget Finset.univ ∅
-- expect: {0}         the target itself, after one inner step

#eval (gate.afStepOf gate_inRange gateTarget Finset.univ)^[2] ∅
-- expect: {1, 0}      and state 1 joins it, via the coin

#eval (gate.afStepOf gate_inRange gateTarget gateGood)^[2] ∅
-- expect: {1, 0}      the outer chain has already stabilised

-- (printed in the order the computation inserted them, which is not the order `gateGood`'s own
-- literal is written in; the `Finset`s are equal, as `gate_answers_AF` below records.)

#eval gate.afRegion gate_inRange gateTarget
-- expect: {1, 0}      both loops, run to termination, with no counts supplied

/-- The first outer step's inner `μX` fixed point, at `Finset.univ`. -/
theorem gate_afInner_at_univ :
    ((gate.toCsgQ.toCSG gate_wf).AFInner ↑gateTarget
        ↑(Finset.univ : Finset (Fin gate.nStates))).lfp = (↑gateGood : Set (Fin gate.nStates)) :=
  gate.afInner_eq_of_data gate_inRange gate_stochastic gate_nonzero gateTarget Finset.univ
    gateGood 2 (by decide) (by decide)

/-- …so `{0, 1}` bounds `AF` from above. -/
theorem gate_AF_le_good :
    (gate.toCsgQ.toCSG gate_wf).AF ↑gateTarget ≤ (↑gateGood : Set (Fin gate.nStates)) :=
  gate.AF_le_of_data_step gate_inRange gate_stochastic gate_nonzero gateTarget Finset.univ
    gateGood 2 (by decide) (by decide) (CsgQ.AF_le_univ gate.toCsgQ gate_wf gateTarget)

/-- **Almost-sure reachability, computed from the model.** `{0, 1}` is its own inner `μX` fixed
    point and the descent has reached it, so it *is* `CSG.AF {0}` -- and the nested loops of
    `Comp/FixLoop.lean` find it without being told how far either of them has to go.

    The single `decide` names the region; that it is the inner `μX` fixed point and that the outer
    descent has reached it are theorems rather than hypotheses. The three lemmas above exhibit the
    same run through the counted interface. -/
theorem gate_answers_AF :
    gate.toCsgQ.Answers gate_wf (Objective.almostReach gateTarget) (Answer.region gateGood) :=
  gate.answers_almostReach_of_fix gate_inRange gate_stochastic gate_nonzero gateTarget gateGood
    (by decide)

end LeakyGate

end Comp
