/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Csg.MatrixGame

/-!
# Finite-state concurrent stochastic games

**Status: done, confirmed by a clean `lake build`, including the later addition
`MatrixGame.value_unique` (relocated here from `MatchingPennies.lean` once
`MatrixGameMonotone.lean` needed it too -- see that file's own note).** Builds on the now-confirmed
`Csg.MatrixGame` (`MatrixGame.lean`) without touching that file, matching how
`ValueIteration.lean`/`PolicyIteration.lean` build on `Basic.lean` in the MDP line rather than
reopening it.

Two things happen in this file:

1. `MatrixGame` gets a `value : ℝ` (plus the two accessor strategies it was built from),
   extracted from `exists_optimal_strategies` via `Classical.choose`. `MatrixGame.lean` itself
   deliberately stopped at bare existence -- turning that into a usable real number is exactly the
   "follow-up work" flagged in that file's own docstring.
2. `CSG`, the concurrent-stochastic-game analogue of `DiscountedMDP` (`Basic.lean`): same
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

namespace MatrixGame

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
variable (G : MatrixGame I J)

/-- A row (minimizing player's) mixed strategy witnessing `exists_optimal_strategies` -- one
    specific choice among possibly several, extracted via `Classical.choose` since Mathlib's
    saddle-point existence doesn't come with a canonical one. -/
noncomputable def optimalRow : I → ℝ := G.exists_optimal_strategies.choose

/-- A column (maximizing player's) mixed strategy witnessing `exists_optimal_strategies`,
    optimal against `optimalRow`. -/
noncomputable def optimalCol : J → ℝ := G.exists_optimal_strategies.choose_spec.2.choose

/-- **The game's value.** The payoff at the optimal strategy pair -- what neither player can do
    better than, given the other holds still (`value_row_optimal`/`value_col_optimal` below). -/
noncomputable def value : ℝ := G.payoff G.optimalRow G.optimalCol

theorem optimalRow_mem : G.optimalRow ∈ stdSimplex ℝ I := by
  unfold optimalRow
  exact G.exists_optimal_strategies.choose_spec.1

theorem optimalCol_mem : G.optimalCol ∈ stdSimplex ℝ J := by
  unfold optimalCol
  exact G.exists_optimal_strategies.choose_spec.2.choose_spec.1

/-- The row player cannot lower the payoff below `value` by unilaterally deviating from
    `optimalRow`, while the column player holds `optimalCol` fixed. -/
theorem value_row_optimal : ∀ p' ∈ stdSimplex ℝ I, G.value ≤ G.payoff p' G.optimalCol := by
  unfold value
  exact G.exists_optimal_strategies.choose_spec.2.choose_spec.2.1

/-- The column player cannot raise the payoff above `value` by unilaterally deviating from
    `optimalCol`, while the row player holds `optimalRow` fixed. -/
theorem value_col_optimal : ∀ q' ∈ stdSimplex ℝ J, G.payoff G.optimalRow q' ≤ G.value := by
  unfold value
  exact G.exists_optimal_strategies.choose_spec.2.choose_spec.2.2

/-- The game's value doesn't depend on which saddle point exhibits it: *any* mixed-strategy pair
    `p, q` satisfying the two no-unilateral-improvement conditions relative to each other has
    `payoff p q = value`, not just the particular pair `value` was built from via
    `Classical.choose`. Standard minimax fact (the *value* of a zero-sum game is unique even when
    optimal strategies are not), proved directly from `value_row_optimal`/`value_col_optimal` by
    chaining both pairs' optimality conditions against each other.

    **Relocated here from `MatchingPennies.lean`**, where it was first proved, once
    `MatrixGameMonotone.lean`'s `value_add_const` needed it too: a general fact about `value` that
    doesn't depend on anything CSG- or worked-example-specific belongs beside `value` itself, not
    behind a worked-example file downstream consumers would otherwise have to import for no reason
    but this one lemma. Pure relocation -- the statement and proof are unchanged from
    `MatchingPennies.lean`'s original. -/
theorem value_unique {p : I → ℝ} {q : J → ℝ} (hp : p ∈ stdSimplex ℝ I) (hq : q ∈ stdSimplex ℝ J)
    (hrow : ∀ p' ∈ stdSimplex ℝ I, G.payoff p q ≤ G.payoff p' q)
    (hcol : ∀ q' ∈ stdSimplex ℝ J, G.payoff p q' ≤ G.payoff p q) :
    G.payoff p q = G.value := by
  apply le_antisymm
  · calc G.payoff p q ≤ G.payoff G.optimalRow q := hrow G.optimalRow G.optimalRow_mem
      _ ≤ G.value := G.value_col_optimal q hq
  · calc G.value ≤ G.payoff p G.optimalCol := G.value_row_optimal p hp
      _ ≤ G.payoff p q := hcol G.optimalCol G.optimalCol_mem

end MatrixGame

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
