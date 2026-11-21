/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Worked example: matching pennies

**Status: confirmed by a clean `lake build`.** A concrete instantiation of the whole CSG
stack (`MatrixGame`, `CSG`, `bwInd`), checked against a hand-solved closed form -- the same role
`RecyclingRobot.lean` played for the MDP side, extended here to a genuinely *concurrent* game.

Matching pennies is the canonical example motivating mixed strategies in the first place: row
picks `i : Fin 2`, column picks `j : Fin 2` simultaneously, row wins (payoff `-1`, since row
minimizes) by matching, column wins (payoff `1`) by mismatching. Neither player has a dominant
pure action -- unlike a degenerate game whose value some `Finset.sup'`/`Finset.inf'` could already
compute, this genuinely exercises `Sion.exists_isSaddlePointOn`'s mixed-strategy content. Textbook
answer: value `0`, both players optimal at the uniform mixed strategy `(1/2, 1/2)`.

What happens here: the matching-pennies matrix itself, wrapped in a single-state `CSG` (`Unit` as
the state type, trivial self-loop transition), and `bwInd`'s first step on it -- checked to equal
`0` exactly, via `MatrixGame.value_eq_of_certificate` at the uniform strategy pair: the row and
column sums of the payoff matrix both vanish, so uniform play holds every pure reply to exactly
`0`. -/

namespace Csg

/-- The matching-pennies payoff matrix: row (minimizing) wins by matching column's choice, column
    (maximizing) wins by mismatching. -/
noncomputable def penniesMatrix : MatrixGame (Fin 2) (Fin 2) where
  A i j := if i = j then -1 else 1

/-- The uniform mixed strategy over two actions -- the textbook-optimal strategy for both players
    in matching pennies. -/
noncomputable def unif2 : Fin 2 → ℝ := fun _ => 1 / 2

theorem unif2_mem : unif2 ∈ stdSimplex ℝ (Fin 2) :=
  ⟨fun i => by simp only [unif2]; norm_num, by simp only [unif2, Fin.sum_univ_two]; norm_num⟩

private theorem penniesMatrix_row_sum_zero (i : Fin 2) : ∑ j, penniesMatrix.A i j = 0 := by
  fin_cases i <;> simp [penniesMatrix, Fin.sum_univ_two]

private theorem penniesMatrix_col_sum_zero (j : Fin 2) : ∑ i, penniesMatrix.A i j = 0 := by
  fin_cases j <;> simp [penniesMatrix, Fin.sum_univ_two]

/-- **The payoff, part one.** Matching pennies has value exactly `0` -- the textbook answer, not
    an approximation of it. The uniform strategy on each side is the certificate: every column of
    the payoff matrix sums to `0`, so uniform row play holds each pure column to `0`, and every
    row sums to `0`, so uniform column play secures `0` against each pure row.

    `simp only`, not plain `simp`: the default simp set includes `Fin.sum_univ_two`, which expands
    the sum into numeral terms before `penniesMatrix_col_sum_zero`/`_row_sum_zero` can fire on
    the still-general `∑ i, penniesMatrix.A i j`. -/
theorem penniesMatrix_value : penniesMatrix.value = 0 := by
  refine penniesMatrix.value_eq_of_certificate unif2_mem unif2_mem
    (fun j => le_of_eq ?_) (fun i => le_of_eq (Eq.symm ?_))
  · simp only [unif2, ← Finset.mul_sum, penniesMatrix_col_sum_zero, mul_zero]
  · simp only [unif2, ← Finset.sum_mul, penniesMatrix_row_sum_zero, zero_mul]

/-- Matching pennies as a `CSG` with a single state: `Unit`, self-looping with probability `1`
    regardless of the joint action, so the continuation value never actually varies with a "next"
    state -- there's only one. The reward at every joint action is exactly `penniesMatrix`'s
    payoff. The simplest possible genuinely-concurrent validation instance. -/
noncomputable def penniesCSG : CSG Unit (Fin 2) (Fin 2) where
  K _ _ _ := PMF.pure ()
  r _ i j := penniesMatrix.A i j

theorem penniesCSG_expect (i j : Fin 2) (v : Unit → ℝ) :
    penniesCSG.expect () i j v = v () := by
  change ∑ s' : Unit, (penniesCSG.K () i j s').toReal * v s' = v ()
  simp [penniesCSG, PMF.pure_apply]

theorem penniesCSG_stageGame_A (i j : Fin 2) :
    (penniesCSG.stageGame () (0 : Unit → ℝ)).A i j = penniesMatrix.A i j := by
  change penniesCSG.r () i j + penniesCSG.expect () i j 0 = penniesMatrix.A i j
  rw [penniesCSG_expect]
  simp [penniesCSG]

/-- With zero terminal reward, the stage game at the single state is `penniesMatrix` itself. -/
theorem penniesCSG_stageGame_zero :
    penniesCSG.stageGame () (0 : Unit → ℝ) = penniesMatrix := by
  have hA : (penniesCSG.stageGame () (0 : Unit → ℝ)).A = penniesMatrix.A := by
    funext i j
    exact penniesCSG_stageGame_A i j
  exact congrArg MatrixGame.mk hA

/-- **The payoff, part two.** With zero terminal reward, one step of backward induction on the
    matching-pennies `CSG` gives exactly the matrix game's own value, `0` -- the whole stack
    (`CSG.stageGame`, `CSG.stageValue`, `MatrixGame.value`) computes the textbook answer on a
    concrete instance, not just something that type-checks. -/
theorem penniesCSG_stageValue_zero : penniesCSG.stageValue () (0 : Unit → ℝ) = 0 := by
  change (penniesCSG.stageGame () (0 : Unit → ℝ)).value = 0
  rw [penniesCSG_stageGame_zero]
  exact penniesMatrix_value

/-- **The payoff, part three.** One step of backward induction on the whole `CSG`, from zero
    terminal reward, equals `0` -- the fully-assembled `bwInd`/`CSG`/`MatrixGame` stack agrees
    with the textbook matching-pennies value, end to end. -/
theorem penniesCSG_bwInd_one : penniesCSG.bwInd (0 : Unit → ℝ) 1 () = 0 := by
  rw [CSG.bwInd_succ, CSG.bwInd_zero]
  exact penniesCSG_stageValue_zero

end Csg
