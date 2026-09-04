/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Csg.MatrixGame

/-!
# Finite-state concurrent stochastic games

**Status: confirmed by a clean `lake build` after the `MatrixGame` section (`value` and its
supporting API) was moved OUT of this file and into `MatrixGame.lean`, where it belongs -- see that
file's own "Update" note; no fix round needed.** Builds on the now-confirmed `Csg.MatrixGame`
(`MatrixGame.lean`), which now supplies `value` directly rather than through this file, matching
how `ValueIteration.lean`/`PolicyIteration.lean` build on `Basic.lean` in the MDP line.

One thing happens in this file now: `CSG`, the concurrent-stochastic-game analogue of
`DiscountedMDP` (`Basic.lean`, the MDP-line file of the same name): same
`K : S → A1 → A2 → PMF S`/`r : S → A1 → A2 → ℝ` shape, but with two independently-chosen
actions per step instead of one, since both players move simultaneously at each state. No
discount factor -- per the CSG scoping in `PHASE0-NOTES.md`, bounded objectives use backward
induction and infinite-horizon objectives use undiscounted reachability/until, neither of which
needs one. Same simplification `DiscountedMDP` already makes: every action available in every
state (Isabelle's per-state `A1 s`/`A2 s` restriction is a TODO there too, not done here
either).

`CSG.stageGame`/`CSG.stageValue` are the actual point of this file: the per-state, per-continuation
one-shot matrix game that a `Backward_Induction.thy`-style recursion calls at each step, replacing
`DiscountedMDP.bellman v s`'s `Finset.sup'` with a `MatrixGame.value`. Nothing about backward
induction itself (the recursion, `bw_ind_aux`-style, or its correctness) is in this file -- that's
the next artifact, once this structure exists to state it over.
-/

namespace Csg

/-- A finite-state, finite-action concurrent stochastic game: at each state, the row player
    (minimizer) and column player (maximizer) pick actions `a1`/`a2` simultaneously, and the
    joint action determines both the transition and the immediate reward. This is `DiscountedMDP`
    (`Basic.lean`)'s shape with the single action `a` replaced by an independently-chosen pair
    `(a1, a2)` -- the defining feature of a *concurrent* game, as opposed to a turn-based one.
    `DecidableEq` on the action types plays exactly the role it does for `MatrixGame`: exhibiting a
    nonempty mixed strategy at each state's stage game. -/
structure CSG (S A1 A2 : Type*) [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
    [DecidableEq A1] [DecidableEq A2] where
  /-- Transition kernel: `K s a1 a2` is the distribution over next states after the row player
      plays `a1` and the column player plays `a2` simultaneously in state `s`. -/
  K : S → A1 → A2 → PMF S
  /-- Reward for the joint action `(a1, a2)` in state `s`, paid by the row player to the column
      player -- matching `MatrixGame`'s own row-minimizes/column-maximizes convention. -/
  r : S → A1 → A2 → ℝ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

namespace CSG

variable (C : CSG S A1 A2)

/-- Expected value of `v` one step after the joint action `(a1, a2)` in state `s`. Corresponds
    exactly to `DiscountedMDP.expect` (`Basic.lean`), specialised to two independent action
    coordinates instead of one. -/
noncomputable def expect (s : S) (a1 : A1) (a2 : A2) (v : S → ℝ) : ℝ :=
  ∑ s', (C.K s a1 a2 s').toReal * v s'

/-- The one-shot matrix game played at state `s` against continuation value `v`: the row player's
    `a1` and the column player's `a2` are chosen simultaneously, and the payoff is the immediate
    reward plus the expected continuation value -- exactly the per-state aggregation step that
    replaces `DiscountedMDP.bellman`'s `Finset.sup'` for concurrent games (see the CSG scoping
    notes in `PHASE0-NOTES.md`). -/
noncomputable def stageGame (s : S) (v : S → ℝ) : MatrixGame A1 A2 where
  A a1 a2 := C.r s a1 a2 + C.expect s a1 a2 v

/-- The value of state `s`'s stage game against continuation `v` -- what a
    `Backward_Induction.thy`-style recursion calls at each step, in place of
    `DiscountedMDP.bellman v s`. Existence and well-definedness are free: `stageGame` is always a
    genuine finite zero-sum matrix game (`MatrixGame.exists_optimal_strategies` needs nothing
    beyond finiteness/nonemptiness of the action types, already assumed throughout), so `.value`
    is always defined, with no side condition on `v`. -/
noncomputable def stageValue (s : S) (v : S → ℝ) : ℝ := (C.stageGame s v).value

end CSG

end Csg
