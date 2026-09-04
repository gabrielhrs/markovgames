/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Basic

/-!
# Bounded reachability for concurrent stochastic games

**Status: done, confirmed by a clean `lake build`.** First half of the rock-paper-scissors
worked example: the general step-bounded reachability operator, before any concrete game is
instantiated over it. Builds on `Csg/Basic.lean` (`CSG.stageValue`); only imports
`MatrixGameMonotone.lean` for now (not yet used here) since the next artifact -- boundedness of
`reachBounded` in `[0, 1]`, checked against a concrete instance -- will want it immediately.

`reachBounded goal k s`: the value, at state `s`, of reaching a `goal` state within `k` steps,
played optimally by both players (row minimising, column maximising, `MatrixGame.lean`'s own
convention). Per the discussion in `PHASE0-NOTES.md`: this is the *opposite* of the row-maximises/
column-minimises convention the FMSD paper itself uses, deliberately not threaded through the rest
of the project as a sign flip -- so whichever player benefits from reaching `goal` is the *column*
player here, regardless of which paper-side "player 1"/"player 2" label it carries in a given
property. This computes plain step-bounded reachability, `F<=k goal` (equivalently `rPATL`'s
`Pmax=? [true U<=k goal]`) -- exactly the shape of the property in the rock-paper-scissors example
this is being built for.

Structurally this is `bwInd` (`BackwardInduction.lean`) with one real difference: `bwInd` has no
notion of a goal at all, so its only per-step choice is "play the stage game." `reachBounded` folds
a goal-absorption check into *every* level, not just the base case -- a `goal` state is worth `1`
immediately, at any budget, rather than needing the recursion to "discover" that through the stage
game (which it never could: a state's transition kernel has no way to know it *is* the goal). This
is the structural fact that will let a truly absorbing target state (self-looping, reward `0`) end
up with value exactly `1` at every step count, once a concrete example is built over this.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- **Bounded reachability.** `reachBounded goal k s` is the value, at state `s`, of reaching a
    `goal` state within `k` steps. `0` steps taken: only already-`goal` states count (`F<=0 goal`
    is `goal` itself). `k + 1` steps available: a `goal` state is worth `1` immediately
    (absorption, regardless of remaining budget); any other state plays its stage game
    (`CSG.stageGame`/`stageValue`) against the `k`-budget continuation. Always defined for every
    `k` and every `goal`: `CSG.stageValue` needs no side condition, same as `bwInd`. -/
noncomputable def reachBounded (goal : S → Prop) [DecidablePred goal] : ℕ → S → ℝ
  | 0 => fun s => if goal s then 1 else 0
  | k + 1 => fun s => if goal s then 1 else C.stageValue s (reachBounded goal k)

@[simp] theorem reachBounded_zero (goal : S → Prop) [DecidablePred goal] (s : S) :
    C.reachBounded goal 0 s = if goal s then 1 else 0 := rfl

theorem reachBounded_succ (goal : S → Prop) [DecidablePred goal] (k : ℕ) (s : S) :
    C.reachBounded goal (k + 1) s =
      if goal s then 1 else C.stageValue s (C.reachBounded goal k) := rfl

/-- A `goal` state is worth `1` at *every* step budget, not just `0` -- the whole point of folding
    the absorption check into every level rather than only the base case. -/
theorem reachBounded_of_goal (goal : S → Prop) [DecidablePred goal] (k : ℕ) {s : S}
    (hs : goal s) : C.reachBounded goal k s = 1 := by
  cases k with
  | zero => rw [reachBounded_zero, if_pos hs]
  | succ k => rw [reachBounded_succ, if_pos hs]

end CSG
end Csg
