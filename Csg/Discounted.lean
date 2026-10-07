/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Discounted concurrent stochastic games: the Shapley operator

**Status: confirmed by a clean `lake build`.**

Adds a discount factor to `CSG` and defines the operator Shapley (1953) built the theory of
discounted stochastic games on: at each state, play the one-shot matrix game whose payoff is the
immediate reward plus the `l`-discounted expected continuation value, and take its value. This is
the concurrent-game analogue of `DiscountedMDP.bellman` (`Mdp/Basic.lean`) in exactly the sense
`CSG.stageValue` already is of a single Bellman step -- a `MatrixGame.value` where the MDP has a
`Finset.sup'`.

**Why a discount, when `Csg/Basic.lean` deliberately omits one.** That omission is right for what
it scopes: bounded objectives use backward induction, and the infinite-horizon objectives built so
far (`reachOp`, `untilOp`, `SafetyOp`, `BuchiOp`/`CoBuchiOp`) are undiscounted. The cost, recorded
in `PHASE0-NOTES.md`'s scoping note on executable algorithms, is that an undiscounted operator has
no contraction ratio and therefore no computable stopping bound -- `ReachConverge.lean` gets
convergence of the naive iterate sequence but no rate, and says so. A discount supplies the ratio,
which is what a value iteration needs in order to stop. Nothing here replaces or competes with the
undiscounted operators; it sits beside them as the one shape that carries an error bound.

**Why the contraction proof is short: both halves are already here.** `CSG.expect` is
`1`-Lipschitz in the continuation (`CsgMonotone.lean`'s `expect_lipschitz`), so scaling it by `l`
makes the stage payoff `l`-Lipschitz entrywise; and `MatrixGame.value` is `1`-Lipschitz in the
sup-norm on the payoff matrix (`MatrixGame.lean`'s `abs_value_sub_le`), which carries that
entrywise bound through `.value`. What results is `Mdp/Basic.lean`'s `bellman_contracting` with
`abs_value_sub_le` substituted for `abs_sup'_sub_sup'_le` -- same skeleton, same glue
(`dist_pi_le_iff` to go from a per-state bound to a `dist` on `S → ℝ`, `dist_le_pi_dist` to feed
each state's hypothesis).

Maps to `Mdp/Basic.lean`:

* `shapleyGame`/`shapley` -- `bellman`, whose `Finset.sup'` over actions these replace.
* `shapleyGame_A_lipschitz`/`shapley_lipschitz` -- the inner `calc` of `bellman_contracting`,
  split out as named lemmas because `CsgMonotone.lean` already states the undiscounted versions
  (`stageGame_A_lipschitz`/`stageValue_lipschitz`) that way, and these are their `l`-scaled
  counterparts.
* `shapley_contracting`, `lNN`, `lipschitzWith_shapley`, `contractingWith_shapley`,
  `exists_unique_fixedPoint` -- the identically-named facts there.

**A standing convention in this file:** parent fields and `CSG`-namespace functions are reached
through an explicit `D.toCSG.` prefix (`D.toCSG.r`, `D.toCSG.expect`) rather than relying on dot
notation to resolve `D.expect` through `extends`. Plain field access would resolve, but `expect`
and `expect_lipschitz` are a `def` and a `theorem` in the `CSG` namespace rather than fields, so
being explicit costs one qualifier and removes the question.

**Not here:** the fixed point as a named `vOpt`, convergence of the iterates to it, and the a
posteriori bound -- those mirror `Mdp/ValueIteration.lean` and belong in the next file, as does
the stopping rule itself (`Mdp/ValueIterationAlgorithm.lean`'s `numIters`/`valueIteration`).
Also not here: the `A1 = Unit` specialization collapsing `shapley` to `DiscountedMDP.bellman` (a
one-row matrix game's value is the maximum over its columns, so the minimising player drops out).
Stating that needs a file importing both libraries, which does not exist yet, and it must not be
`Mdp/` importing `Csg/` -- that would make the ported AFP material depend on new material and
break the provenance split `README.md` maintains.
-/

namespace Csg

/-- A discounted concurrent stochastic game: a `CSG` together with a discount factor in `[0, 1)`.
    Exactly `DiscountedMDP`'s relationship to a bare transition-kernel-and-reward pair, one level
    up: the game data is reused unchanged through `extends`, and only `l` and its two bounds are
    new. Kept as an extension rather than a new field on `CSG` itself so that nothing already
    built on `CSG` (every operator and certificate in the `Csg/` tree) has to change, and so that
    the undiscounted objectives stay free of a discount they have no use for. -/
structure DiscountedCSG (S A1 A2 : Type*) [Fintype S] [Fintype A1] [Fintype A2]
    [Nonempty A1] [Nonempty A2] [DecidableEq A1] [DecidableEq A2] extends CSG S A1 A2 where
  /-- Discount factor. Corresponds to `l` in `DiscountedMDP` (`Mdp/Basic.lean`). -/
  l : ℝ
  l_nonneg : 0 ≤ l
  l_lt_one : l < 1

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

namespace DiscountedCSG

variable (D : DiscountedCSG S A1 A2)

/-- The one-shot matrix game played at state `s` against continuation `v`, discounted: the row
    player's `a1` and the column player's `a2` are chosen simultaneously, and the payoff is the
    immediate reward plus `l` times the expected continuation value.

    This is `CSG.stageGame` with the continuation term scaled by `l`. The two agree exactly when
    `l = 1`, and `stageGame` is the one the undiscounted operators use; the scaled version is kept
    separate rather than defined as `stageGame` at the rescaled continuation `fun s' => l * v s'`
    (which it also equals, by linearity of `expect` in `v`) so that the operator below reads as
    the Shapley operator rather than as a reparametrisation of something else. -/
noncomputable def shapleyGame (s : S) (v : S → ℝ) : MatrixGame A1 A2 where
  A a1 a2 := D.toCSG.r s a1 a2 + D.l * D.toCSG.expect s a1 a2 v

/-- **The Shapley operator.** The value of each state's discounted stage game against continuation
    `v` -- the concurrent-game replacement for `DiscountedMDP.bellman v s`, with that operator's
    `Finset.sup'` over the single player's actions replaced by the `MatrixGame.value` of a game
    both players move in simultaneously.

    Well-definedness is free, exactly as for `CSG.stageValue`: `shapleyGame` is always a genuine
    finite zero-sum matrix game, and `MatrixGame.value` needs nothing of its payoff matrix beyond
    finiteness and nonemptiness of the two action types, which are standing assumptions here. So
    there is no side condition on `v`, and in particular no boundedness hypothesis -- unlike the
    undiscounted reachability operators, which live on `S → Set.Icc (0:ℝ) 1` precisely because
    they have no contraction to keep them in range. Argument order follows `bellman`'s (`v` then
    `s`), not `stageGame`'s (`s` then `v`); each matches its own counterpart. -/
noncomputable def shapley (v : S → ℝ) (s : S) : ℝ := (D.shapleyGame s v).value

/-- The discounted stage game's payoff matrix moves by at most `l * ε` when the continuation moves
    by at most `ε`, entrywise. The reward term does not depend on `v`, so it cancels out of the
    difference exactly, leaving `l` times `expect_lipschitz`'s bound. The `l`-scaled counterpart of
    `CsgMonotone.lean`'s `stageGame_A_lipschitz`, and the step that turns a `1`-Lipschitz
    continuation dependence into a genuine contraction. -/
theorem shapleyGame_A_lipschitz {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) (a1 : A1) (a2 : A2) :
    |(D.shapleyGame s v).A a1 a2 - (D.shapleyGame s w).A a1 a2| ≤ D.l * ε := by
  have heq : (D.shapleyGame s v).A a1 a2 - (D.shapleyGame s w).A a1 a2
      = D.l * (D.toCSG.expect s a1 a2 v - D.toCSG.expect s a1 a2 w) := by
    change (D.toCSG.r s a1 a2 + D.l * D.toCSG.expect s a1 a2 v)
        - (D.toCSG.r s a1 a2 + D.l * D.toCSG.expect s a1 a2 w) = _
    ring
  rw [heq, abs_mul, abs_of_nonneg D.l_nonneg]
  exact mul_le_mul_of_nonneg_left (D.toCSG.expect_lipschitz hε h) D.l_nonneg

/-- The Shapley operator moves by at most `l * ε` at each state when the continuation moves by at
    most `ε`: `MatrixGame.abs_value_sub_le` applied to `shapleyGame_A_lipschitz`. The `l`-scaled
    counterpart of `CsgMonotone.lean`'s `stageValue_lipschitz`, and the per-state form of the
    contraction below. -/
theorem shapley_lipschitz {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) : |D.shapley v s - D.shapley w s| ≤ D.l * ε := by
  change |(D.shapleyGame s v).value - (D.shapleyGame s w).value| ≤ D.l * ε
  exact MatrixGame.abs_value_sub_le fun a1 a2 => D.shapleyGame_A_lipschitz hε h a1 a2

/-- **The theorem this file exists for.** The Shapley operator is an `l`-Lipschitz contraction in
    sup distance -- the concurrent-game analogue of `contraction_ℒ` as ported in
    `Mdp/Basic.lean`'s `bellman_contracting`, and the fact that makes a *terminating* value
    iteration possible for discounted concurrent games where the undiscounted operators admit no
    stopping bound at all.

    Same three moves as the MDP proof: `dist_pi_le_iff` turns the goal into a per-state bound,
    `dist_le_pi_dist` supplies that state's pointwise hypothesis from the ambient `dist v u`, and
    `shapley_lipschitz` does the work in between. Shapley's own 1953 argument is this contraction
    plus Banach; the contraction is the part that needs the game theory, and it is exactly where
    `MatrixGame.abs_value_sub_le` is doing the work a `sup'` does for free in the MDP case. -/
theorem shapley_contracting (v u : S → ℝ) :
    dist (D.shapley v) (D.shapley u) ≤ D.l * dist v u := by
  rw [dist_pi_le_iff (mul_nonneg D.l_nonneg dist_nonneg)]
  intro s
  rw [Real.dist_eq]
  refine D.shapley_lipschitz dist_nonneg fun s' => ?_
  rw [← Real.dist_eq]
  exact dist_le_pi_dist v u s'

/-- `D.l` repackaged as an `NNReal`, the form `LipschitzWith`/`ContractingWith` want their constant
    in. Mirrors `DiscountedMDP.lNN`; `l_nonneg` is exactly the side condition the subtype needs. -/
noncomputable def lNN (D : DiscountedCSG S A1 A2) : NNReal := ⟨D.l, D.l_nonneg⟩

/-- `shapley_contracting` restated in the `edist`-based `LipschitzWith` vocabulary that
    `ContractingWith` is built on. -/
theorem lipschitzWith_shapley : LipschitzWith D.lNN D.shapley :=
  LipschitzWith.of_dist_le_mul fun v u => D.shapley_contracting v u

/-- The Shapley operator is a genuine contraction: Lipschitz with constant `< 1`. -/
theorem contractingWith_shapley : ContractingWith D.lNN D.shapley :=
  ⟨by exact_mod_cast D.l_lt_one, D.lipschitzWith_shapley⟩

/-- **The payoff.** The Shapley operator has exactly one fixed point -- the value vector of the
    discounted concurrent game. Existence is `ContractingWith.exists_fixedPoint` (Banach, over the
    complete space `S → ℝ`); uniqueness is the same short argument `Mdp/Basic.lean` uses, two
    fixed points each being a contraction factor away from the other and so at distance `0`.
    `(0 : S → ℝ)` as the iteration basepoint is arbitrary.

    This is the existence half of Shapley (1953) for the finite discounted case. Note what it does
    *not* say: nothing here identifies the fixed point with a strategic notion of game value, i.e.
    with what either coalition can guarantee under optimal play over infinite horizons. That is a
    separate theorem, and the project has its analogue only for the bounded case
    (`BackwardInduction.lean`) and for the undiscounted objectives via their own operators. -/
theorem exists_unique_fixedPoint : ∃! v : S → ℝ, D.shapley v = v := by
  obtain ⟨v, hv_fix, -, -⟩ := D.contractingWith_shapley.exists_fixedPoint 0 (edist_ne_top _ _)
  refine ⟨v, hv_fix, fun w hw_fix => ?_⟩
  by_contra hne
  have hpos : 0 < dist v w := dist_pos.mpr (Ne.symm hne)
  have hshrink : dist v w ≤ D.l * dist v w := by
    have := D.shapley_contracting v w
    rwa [hv_fix, hw_fix] at this
  nlinarith [D.l_lt_one]

end DiscountedCSG

end Csg
