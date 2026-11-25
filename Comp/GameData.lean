/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelData

/-!
# A game with any number of players, as data

**Status: confirmed by a clean `lake build`.** `Comp/ModelData.lean` describes a game with two
sides, a row player who minimises and a column player who maximises. That is the form in which a
zero-sum question is solved, and it is not a description of a model: a model has players, and who
is allied with whom, and to what end, is part of a question asked of it. This file describes the
model, and builds the two-sided game for a given split of its players.

**The elements, and why each is there.**

* *Players and their actions.* `nActs` gives the size of each player's action namespace, and
  the number of players is its length, so the two cannot disagree.
* *Idling.* A transition lists one choice per player: `some a` for the player's action `a`, or
  `none` when the player idles. Idling is not an action of the namespace. A player idles at a
  state exactly when it has no action enabled there, so it is never something chosen.
* *Choice sets.* What a player can choose at a state is read off the state's transitions
  (`GameState.choices`), as the enabled actions of `ModelData` are. There is no second table to
  keep consistent with the transitions.
* *Probabilistic steps.* A state at which every player idles has one transition, and it needs no
  kind of its own.
* *Terminal states.* A state with no transition is terminal, as in `ModelData`.
* *Rewards.* One for being in a state and one for a joint choice, as in `ModelData`.

Nothing here refers to how a model was written. In a modelling language with modules, the
transitions of a built model are already products over the modules, and the modules are gone.

**What a well-formed model is** (`GameData.Shape`). Every transition has one choice per player,
within that player's namespace, and leads to real states. No joint choice is listed twice. A
player either idles in every transition of a state or in none (`IdleOrAct`). And the transitions
of a state are all the combinations of its players' choices (`Total`): the players choose
independently, so every combination must lead somewhere.

**The two-sided game** (`GameData.reduce`). Given the set of players on the row side, each
transition keeps its distribution and its reward, and its joint choice is split in two: the
choices of the row-side players become one row action, and the others' one column action. A
side's joint choice is coded as a single number in mixed radix, a player with `n` actions
contributing a digit in `0, …, n`, with `0` for idling (`encodeFrom`). A side all of whose
players idle, and a side with no player at all, therefore has the single action `0`.
`reduceMax C` puts the coalition `C` on the column side, where it maximises, and `reduceMin C`
on the row side.

The reduction is for zero-sum questions. A question that is not zero-sum is asked of the model
itself and does not pass through it.

**Validity of a reduction is checked, not inherited.** The result is a `ModelData`, and its own
decidable conditions (`ModelData.Shape`, `Stochastic`) are checked on it like on any other. That
`GameData.Shape` implies them for every split of the players is true and is not proved here.

**Not here:** labels; several named reward structures; a real-valued denotation of the model
with its players, and its agreement with `Csg/Coalition.lean`'s `NCSG.reduceMin` and
`reduceMax`.
-/

namespace Comp

/-- One transition of a game with several players. -/
structure JointTransition where
  /-- One choice per player: `some a` for the player's action `a`, `none` when it idles. -/
  acts : List (Option ℕ)
  /-- Successors with their weights. Only the ones that occur. -/
  dist : List (ℕ × ℚ)
  /-- Reward for this joint choice in this state. -/
  rew : ℚ

/-- One state: its own reward, and its transitions. -/
structure GameState where
  /-- Reward for being in this state. -/
  rew : ℚ
  /-- The transitions available here, each carrying its joint choice. -/
  trans : List JointTransition

/-- A game with any number of players, in adjacency form. -/
structure GameData where
  /-- The size of each player's action namespace. The number of players is the length. -/
  nActs : List ℕ
  /-- The states, in index order. -/
  states : List GameState

/-- The choices of player `i` at a state: what the state's transitions list for it. `[none]`
    when the player idles there, and empty at a terminal state. -/
def GameState.choices (st : GameState) (i : ℕ) : List (Option ℕ) :=
  (st.trans.map fun t => t.acts.getD i none).dedup

/-! ## Coding a side's joint choice -/

/-- The digit of a choice: `0` for idling, `a + 1` for the action `a`. -/
def choiceDigit : Option ℕ → ℕ
  | none => 0
  | some a => a + 1

/-- The code of the choices of the players selected by `sel`, among the players numbered from
    `i` on with namespace sizes `ns`. Mixed radix: a selected player with `n` actions contributes
    a digit below `n + 1`. -/
def encodeFrom (sel : ℕ → Bool) : ℕ → List ℕ → List (Option ℕ) → ℕ
  | _, [], _ => 0
  | i, n :: ns, acts =>
    if sel i then
      choiceDigit (acts.headD none) + (n + 1) * encodeFrom sel (i + 1) ns acts.tail
    else encodeFrom sel (i + 1) ns acts.tail

/-- The number of codes: the product of `n + 1` over the selected players, and `1` when none is
    selected. Never `0`. -/
def sizeFrom (sel : ℕ → Bool) : ℕ → List ℕ → ℕ
  | _, [] => 1
  | i, n :: ns => if sel i then (n + 1) * sizeFrom sel (i + 1) ns else sizeFrom sel (i + 1) ns

namespace GameData

/-- The number of players -- derived, not stored. -/
def nPlayers (d : GameData) : ℕ := d.nActs.length

/-- The number of states -- derived, not stored. -/
def nStates (d : GameData) : ℕ := d.states.length

/-! ## Well-formedness -/

/-- Every transition lists one choice per player. -/
def Arity (d : GameData) : Prop :=
  ∀ st ∈ d.states, ∀ t ∈ st.trans, t.acts.length = d.nPlayers

/-- Every action is in its player's namespace. -/
def ActsInRange (d : GameData) : Prop :=
  ∀ st ∈ d.states, ∀ t ∈ st.trans, ∀ p ∈ t.acts.zip d.nActs, choiceDigit p.1 ≤ p.2

/-- Every successor index is a real state. -/
def InRange (d : GameData) : Prop :=
  ∀ st ∈ d.states, ∀ t ∈ st.trans, ∀ p ∈ t.dist, p.1 < d.nStates

/-- No two transitions of a state share a joint choice. -/
def Functional (d : GameData) : Prop :=
  ∀ st ∈ d.states, (st.trans.map fun t => t.acts).Nodup

/-- **A player idles at a state only when it has no action there.** If one transition of a state
    has the player idle, they all do. -/
def IdleOrAct (d : GameData) : Prop :=
  ∀ st ∈ d.states, ∀ i ∈ List.range d.nPlayers, none ∈ st.choices i → st.choices i = [none]

/-- **The transitions of a state are all the combinations of its players' choices.** The players
    choose independently, so each combination must have a transition. -/
def Total (d : GameData) : Prop :=
  ∀ st ∈ d.states, ∀ c ∈ ((List.range d.nPlayers).map st.choices).sections,
    c ∈ st.trans.map fun t => t.acts

/-- The structural conditions, bundled. No weight is involved in any of them. -/
def Shape (d : GameData) : Prop :=
  d.Arity ∧ d.ActsInRange ∧ d.InRange ∧ d.Functional ∧ d.IdleOrAct ∧ d.Total

instance (d : GameData) : Decidable d.Arity := by
  unfold Arity; infer_instance

instance (d : GameData) : Decidable d.ActsInRange := by
  unfold ActsInRange; infer_instance

instance (d : GameData) : Decidable d.InRange := by
  unfold InRange; infer_instance

instance (d : GameData) : Decidable d.Functional := by
  unfold Functional; infer_instance

instance (d : GameData) : Decidable d.IdleOrAct := by
  unfold IdleOrAct; infer_instance

instance (d : GameData) : Decidable d.Total := by
  unfold Total; infer_instance

instance (d : GameData) : Decidable d.Shape := by
  unfold Shape; infer_instance

/-! ## The two-sided game -/

/-- **The two-sided model for a split of the players.** The players selected by `rowSide` act
    together as the row player and all the others as the column player. Each transition keeps its
    distribution and reward; its joint choice is coded once for each side. -/
def reduce (d : GameData) (rowSide : ℕ → Bool) : ModelData where
  nAct1 := sizeFrom rowSide 0 d.nActs
  nAct2 := sizeFrom (fun i => !rowSide i) 0 d.nActs
  states := d.states.map fun st =>
    ({ rew := st.rew,
       trans := st.trans.map fun t =>
        ({ act1 := encodeFrom rowSide 0 d.nActs t.acts,
           act2 := encodeFrom (fun i => !rowSide i) 0 d.nActs t.acts,
           dist := t.dist,
           rew := t.rew } : Transition) } : StateEntry)

/-- The two-sided model in which the coalition `C` maximises: `C` is the column side and every
    other player is on the row side. -/
def reduceMax (d : GameData) (C : List ℕ) : ModelData :=
  d.reduce fun i => !C.contains i

/-- The two-sided model in which the coalition `C` minimises: `C` is the row side. -/
def reduceMin (d : GameData) (C : List ℕ) : ModelData :=
  d.reduce fun i => C.contains i

end GameData

end Comp
