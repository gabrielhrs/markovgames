/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Worked example: matching pennies

**Status: drafted, not yet run through `lake build`.** A concrete instantiation of the whole CSG
stack (`MatrixGame`, `CSG`, `bwInd`), checked against a hand-solved closed form -- the same role
`RecyclingRobot.lean` played for the MDP side, extended here to a genuinely *concurrent* game.
This is also, by a wide margin, the most tactic-heavy file in the project so far: several small
lemmas rather than one big proof, none individually deep, but with more chances for a naming or
unfolding mismatch than any single-theorem file shipped previously. Treat a `lake build` round
here as more likely than usual, not as a sign something is architecturally wrong.

Matching pennies is the canonical example motivating mixed strategies in the first place: row
picks `i : Fin 2`, column picks `j : Fin 2` simultaneously, row wins (payoff `-1`, since row
minimizes) by matching, column wins (payoff `1`) by mismatching. Neither player has a dominant
pure action -- unlike a degenerate game whose value some `Finset.sup'`/`Finset.inf'` could already
compute, this genuinely exercises `Sion.exists_isSaddlePointOn`'s mixed-strategy content. Textbook
answer: value `0`, both players optimal at the uniform mixed strategy `(1/2, 1/2)`.

What happens here: the matching-pennies matrix itself, wrapped in a single-state `CSG` (`Unit` as
the state type, trivial self-loop transition), and `bwInd`'s first step on it -- checked to equal
`0` exactly, via `MatrixGame.value_unique` plus the row/column sums of the payoff matrix both
vanishing (the concrete fact underlying "uniform is optimal here").

**`MatrixGame.value_unique` itself now lives in `Csg/Basic.lean`, not here.** It was first proved
in this file -- a general fact `MatrixGame.lean`/`Csg/Basic.lean` didn't need at the time and so
never proved (*any* strategy pair satisfying the two no-improvement conditions has the same payoff
as `value`, not just the particular `Classical.choose`-extracted pair `value` is built from --
standard minimax fact, the game's *value* is unique even when optimal strategies are not). It
moved once `MatrixGameMonotone.lean`'s `value_add_const` needed it too and, being imported only
through this worked-example file, wasn't available there -- a build failure caught this rather
than a design review, fixed by relocating the theorem (statement and proof unchanged) to sit
beside `value` itself in `Basic.lean`, where any future general-infrastructure consumer can reach
it without importing a worked example. -/

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

/-- Against the uniform column strategy, *every* row strategy pays exactly `0` -- not just an
    inequality, an identity, since each row of the payoff matrix already sums to `0`. Holds for
    any `p' : Fin 2 → ℝ` whatsoever, no simplex membership needed: it's the payoff matrix's row
    sums vanishing, not a convexity argument. Deliberately `simp only`, not plain `simp`: the
    default simp set includes `Fin.sum_univ_two`, which would expand both finite sums into
    concrete numeral terms *before* the abstract `penniesMatrix_row_sum_zero` gets a chance to
    fire on the still-general `∑ j, penniesMatrix.A i j` pattern, leaving a residual goal neither
    lemma can close (the bug in the version this file was first drafted with). Naming the exact
    lemmas needed, in the order they're needed, avoids that ordering trap entirely. -/
theorem penniesMatrix_payoff_row (p' : Fin 2 → ℝ) : penniesMatrix.payoff p' unif2 = 0 := by
  simp only [MatrixGame.payoff_eq_sum_mul, unif2, ← Finset.sum_mul, penniesMatrix_row_sum_zero,
    zero_mul, mul_zero, Finset.sum_const_zero]

/-- Symmetric counterpart of `penniesMatrix_payoff_row`: against the uniform row strategy, every
    column strategy also pays exactly `0`. Same `simp only`-not-`simp` reasoning applies. -/
theorem penniesMatrix_payoff_col (q' : Fin 2 → ℝ) : penniesMatrix.payoff unif2 q' = 0 := by
  simp only [MatrixGame.payoff_eq_sum_mul', unif2, ← Finset.mul_sum, penniesMatrix_col_sum_zero,
    mul_zero, zero_mul, Finset.sum_const_zero]

/-- **The payoff, part one.** Matching pennies has value exactly `0` -- the textbook answer, not
    an approximation of it. Uniform vs. uniform is a saddle point (both no-improvement conditions
    are equalities, `0 ≤ 0`, from `penniesMatrix_payoff_row`/`_col`), so `value_unique` pins the
    value down exactly. -/
theorem penniesMatrix_value : penniesMatrix.value = 0 := by
  have huu : penniesMatrix.payoff unif2 unif2 = 0 := penniesMatrix_payoff_row unif2
  have hrow : ∀ p' ∈ stdSimplex ℝ (Fin 2),
      penniesMatrix.payoff unif2 unif2 ≤ penniesMatrix.payoff p' unif2 := fun p' _ =>
    le_of_eq (huu.trans (penniesMatrix_payoff_row p').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ (Fin 2),
      penniesMatrix.payoff unif2 q' ≤ penniesMatrix.payoff unif2 unif2 := fun q' _ =>
    le_of_eq ((penniesMatrix_payoff_col q').trans huu.symm)
  have hval := penniesMatrix.value_unique unif2_mem unif2_mem hrow hcol
  rw [← hval]
  exact huu

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

theorem penniesCSG_stageGame_zero_payoff (x y : Fin 2 → ℝ) :
    (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff x y = penniesMatrix.payoff x y := by
  unfold MatrixGame.payoff
  simp only [penniesCSG_stageGame_A]

/-- **The payoff, part two.** With zero terminal reward, one step of backward induction on the
    matching-pennies `CSG` gives exactly the matrix game's own value, `0` -- the whole stack
    (`CSG.stageGame`, `CSG.stageValue`, `MatrixGame.value`) computes the textbook answer on a
    concrete instance, not just something that type-checks. -/
theorem penniesCSG_stageValue_zero : penniesCSG.stageValue () (0 : Unit → ℝ) = 0 := by
  change (penniesCSG.stageGame () (0 : Unit → ℝ)).value = 0
  have huu : (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff unif2 unif2 = 0 := by
    rw [penniesCSG_stageGame_zero_payoff]
    exact penniesMatrix_payoff_row unif2
  have hrow : ∀ p' ∈ stdSimplex ℝ (Fin 2),
      (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff unif2 unif2 ≤
        (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff p' unif2 := by
    intro p' _
    rw [huu, penniesCSG_stageGame_zero_payoff]
    exact (penniesMatrix_payoff_row p').ge
  have hcol : ∀ q' ∈ stdSimplex ℝ (Fin 2),
      (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff unif2 q' ≤
        (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff unif2 unif2 := by
    intro q' _
    rw [huu, penniesCSG_stageGame_zero_payoff]
    exact (penniesMatrix_payoff_col q').le
  have hval := (penniesCSG.stageGame () (0 : Unit → ℝ)).value_unique unif2_mem unif2_mem hrow hcol
  rw [← hval]
  exact huu

/-- **The payoff, part three.** One step of backward induction on the whole `CSG`, from zero
    terminal reward, equals `0` -- the fully-assembled `bwInd`/`CSG`/`MatrixGame` stack agrees
    with the textbook matching-pennies value, end to end. -/
theorem penniesCSG_bwInd_one : penniesCSG.bwInd (0 : Unit → ℝ) 1 () = 0 := by
  rw [CSG.bwInd_succ, CSG.bwInd_zero]
  exact penniesCSG_stageValue_zero

end Csg
