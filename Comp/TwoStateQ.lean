/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Iterate

/-!
# A worked discounted concurrent game: computed, then certified exactly

**Status: confirmed by a clean `lake build`.**

The first instance in `Comp/` with *states*, and so the first thing that exercises
`DiscountedCsgQ.shapleyGameQ`, `shapley_eq_of_valueCert`, and both bounds in `Comp/Iterate.lean`.
`Comp/RockPaperScissorsQ.lean` is a single matrix game; nothing there touches the iteration.

**The game.** Two states over `Bool`. In the live state `true` the reward is `0` and the players'
actions decide the move: matching actions stay, mismatching actions fall through to the absorbing
state `false`, whose reward is `1` forever. The discount is `1/2`. The stage game at `true` is
therefore matching-pennies-shaped -- the minimiser wants to stay in the cheap state, the maximiser
wants to escape to the paying one -- so this is a genuinely concurrent instance, not a turn-based
one in disguise, and its optimal play is mixed.

**It has an exact rational value.** Solving by hand: `v false = 1 + (1/2) v false`, so
`v false = 2`; and `v true` is the value of `(1/2)` times the matrix with `v true` on the diagonal
and `2` off it, which for a matching-pennies shape is `(v true + 2)/4`. Hence `v true = 2/3`, and
`vOpt = (2/3, 2)`.

That makes this instance able to demonstrate the *strong* route rather than only an `ε` bound. The
fixed point is rational, so certifying both stage games at it and appealing to uniqueness
(`Csg/Discounted.lean`'s contraction) pins `vOpt` exactly -- `twoGame_vOpt` below. Worth stressing
that this is luck about this game, not the general case: concurrent games have algebraic and
usually irrational values, which is why `Comp/Iterate.lean` is built around `ε` bounds and treats
exactness as the windfall.

**Both routes appear**, so neither is left untested: `twoGame_vOpt` for the exact value, and
`twoGame_v2_error` for the `ε` guarantee after a step that is *not* at the fixed point.

**The `#eval`s are the recipe in action.** They tabulate a Shapley step per state, which is how the
literals below were obtained in the first place. Expected output, confirmed against an independent
run of the same algorithm outside Lean:

* from `v1 = (0, 1)`: values `(1/4, 3/2)`, mixed uniformly at `true`, pure at `false`;
* at `vStar = (2/3, 2)`: values `(2/3, 2)` -- the fixed point reproduces itself.

The strategy lists are ordered by `bothBools`, so `[1/2, 1/2]` is uniform and `[0, 1]` puts all
weight on `false`. Note that the absorbing state's reported strategy is `[0, 1]` while `pure2`
below is `[1, 0]`: both are optimal, because that stage game is constant and so *every* strategy
is, and `ValueCert` is indifferent to which optimal pair it is handed. Which one the search picks
is an artefact of the order `Comp/Search.lean`'s `sublistsOf` enumerates supports in. The literals
below therefore match the search's *values* everywhere, and its strategies everywhere they are
determined.

Iterating from `(0, 0)` gives `(0, 1)`, `(1/4, 3/2)`, `(7/16, 7/4)`, …, with successive differences
`1`, `1/2`, `1/4` and the a posteriori bound `l·d/(1-l)` exactly equal to the true error at every
step -- the bound is tight here, not merely valid.
-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

open Csg

/-! ## The game -/

/-- Reward: nothing in the live state, `1` per step once absorbed. -/
def twoR : Bool → Bool → Bool → ℚ
  | true, _, _ => 0
  | false, _, _ => 1

/-- Transition weights. From `true`, matching actions stay and mismatching ones absorb; `false` is
    absorbing. Written as weights rather than a `PMF`, with `CsgQ.WellFormed` carrying the
    distribution conditions as a decidable side condition instead of a proof field. -/
def twoK : Bool → Bool → Bool → Bool → ℚ
  | true, a1, a2, s' => if s' = (a1 == a2) then 1 else 0
  | false, _, _, s' => if s' = false then 1 else 0

/-- The game, with discount `1/2`. -/
def twoGame : DiscountedCsgQ Bool Bool Bool where
  K := twoK
  r := twoR
  l := 1 / 2

/-- Both actions and both states, as lists, for the search and for tabulating `#eval`. -/
def bothBools : List Bool := [true, false]

/-- `twoGame` really is a discounted game: nonnegative kernel rows summing to one, and a discount
    in `[0, 1)`. All four clauses are finite case splits. -/
theorem twoGame_wf : twoGame.WellFormed := by
  refine ⟨⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩, ?_, ?_⟩
  · cases s <;> cases a1 <;> cases a2 <;> cases s' <;> simp [twoGame, twoK]
  · cases s <;> cases a1 <;> cases a2 <;>
      rw [Fintype.sum_bool] <;> simp [twoGame, twoK]
  · norm_num [twoGame]
  · norm_num [twoGame]

/-! ## The stage games, entry by entry

Isolating the unfolding here keeps the certificates below to pure arithmetic. Each goes through
`CsgQ.expectQ`'s own `Bool`-indexed sum, which is why `Fintype.sum_bool` appears twice over. -/

/-- The live state's payoff matrix: `l` times the continuation at whichever state the pair of
    actions sends the game to. Matching-pennies-shaped whenever `v true < v false`. -/
theorem stage_true_A (v : Bool → ℚ) (a1 a2 : Bool) :
    (twoGame.shapleyGameQ true v).A a1 a2 = 1 / 2 * (if a1 = a2 then v true else v false) := by
  cases a1 <;> cases a2 <;>
    simp [DiscountedCsgQ.shapleyGameQ, twoGame, twoK, twoR, CsgQ.expectQ, Fintype.sum_bool]

/-- The absorbing state's payoff matrix is constant: the actions are irrelevant there. -/
theorem stage_false_A (v : Bool → ℚ) (a1 a2 : Bool) :
    (twoGame.shapleyGameQ false v).A a1 a2 = 1 + 1 / 2 * v false := by
  simp [DiscountedCsgQ.shapleyGameQ, twoGame, twoK, twoR, CsgQ.expectQ, Fintype.sum_bool]

/-! ## Iterates and strategies, as literals -/

/-- The first iterate from `0`. -/
def v1 : Bool → ℚ
  | true => 0
  | false => 1

/-- The second iterate. -/
def v2 : Bool → ℚ
  | true => 1 / 4
  | false => 3 / 2

/-- The exact value vector. -/
def vStar : Bool → ℚ
  | true => 2 / 3
  | false => 2

/-- The uniform mixed strategy, optimal in the live state. -/
def unif2 : Bool → ℚ := fun _ => 1 / 2

/-- A pure strategy, used in the absorbing state. Any strategy certifies there, since that stage
    game is constant -- see the module docstring on why this need not be the one the search
    reports. -/
def pure2 : Bool → ℚ
  | true => 1
  | false => 0

/-! ## Running it

These are the step tabulations the literals above came from. They run compiled code, not kernel
reduction -- see `Comp/Search.lean` on why that distinction matters. -/

#eval twoGame.stepWitnesses bothBools bothBools bothBools v1

#eval twoGame.stepWitnesses bothBools bothBools bothBools vStar

#eval twoGame.stepValues bothBools bothBools bothBools v2

/-! ## The exact value, via uniqueness -/

/-- The live state's stage game at `vStar` has value `vStar true`, certified by uniform play. -/
theorem cert_true_star :
    (twoGame.shapleyGameQ true vStar).ValueCert (vStar true) unif2 unif2 := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · norm_num [unif2]
  · rw [Fintype.sum_bool]; norm_num [unif2]
  · norm_num [unif2]
  · rw [Fintype.sum_bool]; norm_num [unif2]
  · rw [Fintype.sum_bool]; simp only [stage_true_A]
    cases j <;> norm_num [unif2, vStar]
  · rw [Fintype.sum_bool]; simp only [stage_true_A]
    cases i <;> norm_num [unif2, vStar]

/-- The absorbing state's stage game at `vStar` has value `vStar false`. -/
theorem cert_false_star :
    (twoGame.shapleyGameQ false vStar).ValueCert (vStar false) pure2 pure2 := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · cases i <;> norm_num [pure2]
  · rw [Fintype.sum_bool]; norm_num [pure2]
  · cases j <;> norm_num [pure2]
  · rw [Fintype.sum_bool]; norm_num [pure2]
  · rw [Fintype.sum_bool]; simp only [stage_false_A]
    norm_num [pure2, vStar]
  · rw [Fintype.sum_bool]; simp only [stage_false_A]
    norm_num [pure2, vStar]

/-- `vStar` is a fixed point of the Shapley operator, state by state. -/
theorem twoGame_fixed : ∀ s, (twoGame.toDiscountedCSG twoGame_wf).shapley
    (fun s' => ((vStar s' : ℚ) : ℝ)) s = ((vStar s : ℚ) : ℝ) := by
  intro s
  cases s with
  | false => exact DiscountedCsgQ.shapley_eq_of_valueCert twoGame twoGame_wf cert_false_star
  | true => exact DiscountedCsgQ.shapley_eq_of_valueCert twoGame twoGame_wf cert_true_star

/-- **The exact value of this concurrent game**, as a statement about the real-valued `vOpt` of
    `Csg/DiscountedValueIteration.lean`: `(2/3, 2)`, with no error term. The Shapley operator is a
    contraction, so its fixed point is unique, and exhibiting one rational fixed point therefore
    identifies `vOpt` outright. -/
theorem twoGame_vOpt :
    (fun s => ((vStar s : ℚ) : ℝ)) = (twoGame.toDiscountedCSG twoGame_wf).vOpt :=
  DiscountedCsgQ.eq_vOpt_of_fixed twoGame twoGame_wf twoGame_fixed

/-! ## An error bound for a step away from the fixed point -/

/-- The live state's stage game at `v1` has value `v2 true`. -/
theorem cert_true_v1 :
    (twoGame.shapleyGameQ true v1).ValueCert (v2 true) unif2 unif2 := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · norm_num [unif2]
  · rw [Fintype.sum_bool]; norm_num [unif2]
  · norm_num [unif2]
  · rw [Fintype.sum_bool]; norm_num [unif2]
  · rw [Fintype.sum_bool]; simp only [stage_true_A]
    cases j <;> norm_num [unif2, v1, v2]
  · rw [Fintype.sum_bool]; simp only [stage_true_A]
    cases i <;> norm_num [unif2, v1, v2]

/-- The absorbing state's stage game at `v1` has value `v2 false`. -/
theorem cert_false_v1 :
    (twoGame.shapleyGameQ false v1).ValueCert (v2 false) pure2 pure2 := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · cases i <;> norm_num [pure2]
  · rw [Fintype.sum_bool]; norm_num [pure2]
  · cases j <;> norm_num [pure2]
  · rw [Fintype.sum_bool]; norm_num [pure2]
  · rw [Fintype.sum_bool]; simp only [stage_false_A]
    norm_num [pure2, v1, v2]
  · rw [Fintype.sum_bool]; simp only [stage_false_A]
    norm_num [pure2, v1, v2]

/-- `v2` is the Shapley image of `v1`, state by state. -/
theorem twoGame_step : ∀ s, (twoGame.toDiscountedCSG twoGame_wf).shapley
    (fun s' => ((v1 s' : ℚ) : ℝ)) s = ((v2 s : ℚ) : ℝ) := by
  intro s
  cases s with
  | false => exact DiscountedCsgQ.shapley_eq_of_valueCert twoGame twoGame_wf cert_false_v1
  | true => exact DiscountedCsgQ.shapley_eq_of_valueCert twoGame twoGame_wf cert_true_v1

/-- **An `ε` guarantee for a genuinely computed step.** `v1` and `v2` differ by at most `1/2`, and
    `2 · l · (1/2) = 1/2 < 1 = 2 · (1 - l)`, so the stopping test fires at `ε = 2` and `v2` is
    within `1` of the game's value.

    Loose here only because the instance is tiny: with `vOpt true = 2/3` the true error is `1/2`,
    exactly `l·d/(1-l)`, so the underlying bound in `dist_vOpt_le_of_step` is tight and it is the
    conversion to a strict `ε` that gives up the slack. The point is that the hypothesis
    `2 * l * d < ε * (1 - l)` is a comparison of rationals, discharged below by `norm_num` rather
    than searched for. -/
theorem twoGame_v2_error :
    2 * dist (fun s => ((v2 s : ℚ) : ℝ)) (twoGame.toDiscountedCSG twoGame_wf).vOpt
      < ((2 : ℚ) : ℝ) := by
  refine DiscountedCsgQ.two_dist_vOpt_lt_of_step twoGame twoGame_wf (d := 1 / 2) (by norm_num)
    (fun s => ?_) twoGame_step (by norm_num [twoGame])
  cases s <;> norm_num [v1, v2]

end Comp
