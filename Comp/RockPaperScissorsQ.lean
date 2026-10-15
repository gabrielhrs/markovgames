/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Shapley
import Csg.RockPaperScissors

/-!
# Worked instances: rock-paper-scissors and matching pennies, computed and checked

**Status: confirmed by a clean `lake build`.**

The first place anything in `Comp/` is pointed at a real game. Two instances deliberately:
rock-paper-scissors on the project's own three-action `RPSAction`, and matching pennies on `Bool`.

**The recipe, and why it is shaped this way.** `Comp/Search.lean` records that `#eval` runs compiled
code while `decide` reduces in the kernel, and that the kernel gets stuck on `solveQ`. So a worked
instance never proves anything *about* the search. It goes:

1. `#eval` the search to discover the value and the optimal strategies;
2. write them into the file as literals;
3. prove `ValueCert` on those literals -- finitely many rational comparisons, no recursion -- by
   `norm_num` after expanding the sums (see the note below on why not `decide`);
4. apply `MatrixGameQ.value_eq_of_valueCert`.

Nothing in the resulting theorem mentions `findValueCert`, so the solver is never trusted and its
completeness never matters. This is `README.md`'s certificate methodology with `#eval` supplying the
candidate in place of a human.

**One practical wrinkle.** `findValueCert` returns strategies as *functions*, and `#eval` cannot
print a function, so evaluating it directly shows nothing useful. Tabulate them over the action list
instead:

    #eval (rpsMatrixQ.findValueCert rpsActions rpsActions).map
            (fun c => (c.1, rpsActions.map c.2.1, rpsActions.map c.2.2))
    -- expect: some (0, [1/3, 1/3, 1/3], [1/3, 1/3, 1/3])

    #eval (mpMatrixQ.findValueCert mpActions mpActions).map
            (fun c => (c.1, mpActions.map c.2.1, mpActions.map c.2.2))
    -- expect: some (0, [1/2, 1/2], [1/2, 1/2])

**`decide` cannot discharge these, and the reason is a standing rule rather than a property of this
game.** It is not the size of the game. `decide` asks the kernel to reduce a `Decidable` instance,
and a rational literal such as `1 / 3` normalises through `Nat.gcd`, which is defined by
well-founded recursion and does not reduce there: reduction stops at `(rpsUnif _).blt 0`, before
reaching any part of the game, and the two-action instance below stops in the same place. So **no
amount of rational arithmetic is reachable by `decide`**, however small, and `norm_num` is the tool
for it, discharging `ℚ` goals by verified reflection rather than kernel reduction.

What that leaves is expanding the `Fintype` quantifiers and sums by hand before `norm_num` takes
over: `Csg/RockPaperScissors.lean`'s own `rpsAction_sum` for the three-action sums, and
`Fintype.sum_bool` for the two-action ones, then a `cases` on the free action. The same route
`Csg/RockPaperScissorsLfp.lean` takes for the analogous job over `ℝ`.

This does not change the architecture -- step 3 of the recipe above is still a finite, mechanical
check on literals with the solver outside the trusted path. It only changes which tactic performs
it, and it means `ValueCert`'s decidability buys type-level tidiness rather than a usable `decide`.
-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

open Csg

/-! ## Rock-paper-scissors -/

/-- The three actions, as a list, for tabulating `#eval` output and for feeding the search. -/
def rpsActions : List RPSAction := [.rock, .paper, .scissors]

/-- The one-shot payoff, in `MatrixGame`'s convention: what the row player pays the column player.
    The row player pays `1` exactly when the column player's action beats theirs, so the matrix is
    antisymmetric with a zero diagonal -- which is already enough to see that the value must be `0`,
    since the game is symmetric under swapping the players. -/
def rpsPayoffQ : RPSAction → RPSAction → ℚ
  | .rock, .rock => 0
  | .rock, .paper => 1
  | .rock, .scissors => -1
  | .paper, .rock => -1
  | .paper, .paper => 0
  | .paper, .scissors => 1
  | .scissors, .rock => 1
  | .scissors, .paper => -1
  | .scissors, .scissors => 0

/-- Rock-paper-scissors as a rational matrix game. -/
def rpsMatrixQ : MatrixGameQ RPSAction RPSAction where
  A := rpsPayoffQ

/-- The uniform mixed strategy, which is optimal for both players here. -/
def rpsUnif : RPSAction → ℚ := fun _ => 1 / 3

/-- The certificate: uniform play holds the row player's loss to `0` against every pure column and
    guarantees the column player `0` against every pure row. Closed by `decide`, which is the whole
    point of the exercise -- finitely many exact rational comparisons, no recursion, nothing about
    how the witnesses were found. -/
theorem rps_valueCert : rpsMatrixQ.ValueCert 0 rpsUnif rpsUnif := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · norm_num [rpsUnif]
  · rw [rpsAction_sum]; norm_num [rpsUnif]
  · norm_num [rpsUnif]
  · rw [rpsAction_sum]; norm_num [rpsUnif]
  · rw [rpsAction_sum]; cases j <;> norm_num [rpsUnif, rpsMatrixQ, rpsPayoffQ]
  · rw [rpsAction_sum]; cases i <;> norm_num [rpsUnif, rpsMatrixQ, rpsPayoffQ]

/-- **The value of rock-paper-scissors is zero**, as a statement about the real-valued
    `MatrixGame.value` of `MatrixGame.lean` -- not about a rational approximation of it. The
    equality is exact because a rational matrix game has a rational value. -/
theorem rps_value : rpsMatrixQ.toMatrixGame.value = 0 := by
  simpa using MatrixGameQ.value_eq_of_valueCert rps_valueCert

/-! ## Matching pennies

The two-action control. Same shape throughout, so a failure here but not above (or vice versa)
isolates whether kernel reduction is struggling with the action count or with something else. -/

/-- The two actions, as a list. -/
def mpActions : List Bool := [true, false]

/-- Matching pennies: the row player receives `1` when the coins match and pays `1` when they do
    not, so in the pay-to-column convention the matching entries are `-1`. -/
def mpPayoffQ : Bool → Bool → ℚ
  | true, true => -1
  | true, false => 1
  | false, true => 1
  | false, false => -1

/-- Matching pennies as a rational matrix game. -/
def mpMatrixQ : MatrixGameQ Bool Bool where
  A := mpPayoffQ

/-- The uniform mixed strategy on two actions. -/
def mpUnif : Bool → ℚ := fun _ => 1 / 2

/-- The certificate for matching pennies. -/
theorem mp_valueCert : mpMatrixQ.ValueCert 0 mpUnif mpUnif := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · norm_num [mpUnif]
  · rw [Fintype.sum_bool]; norm_num [mpUnif]
  · norm_num [mpUnif]
  · rw [Fintype.sum_bool]; norm_num [mpUnif]
  · rw [Fintype.sum_bool]; cases j <;> norm_num [mpUnif, mpMatrixQ, mpPayoffQ]
  · rw [Fintype.sum_bool]; cases i <;> norm_num [mpUnif, mpMatrixQ, mpPayoffQ]

/-- **The value of matching pennies is zero.** -/
theorem mp_value : mpMatrixQ.toMatrixGame.value = 0 := by
  simpa using MatrixGameQ.value_eq_of_valueCert mp_valueCert

-- expect: some (0, [1/3, 1/3, 1/3], [1/3, 1/3, 1/3])
#eval (rpsMatrixQ.findValueCert rpsActions rpsActions).map
        (fun c => (c.1, rpsActions.map c.2.1, rpsActions.map c.2.2))

-- expect: some (0, [1/2, 1/2], [1/2, 1/2])
#eval (mpMatrixQ.findValueCert mpActions mpActions).map
        (fun c => (c.1, mpActions.map c.2.1, mpActions.map c.2.2))

end Comp
