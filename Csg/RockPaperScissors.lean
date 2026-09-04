/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.BoundedReachability
import Csg.MatchingPennies

/-!
# Worked example: rock-paper-scissors

**Status: done, confirmed by a clean `lake build` after one real fix round (a typeclass-search
gap -- a goal predicate defined via plain `def` rather than `abbrev`, blocking automatic
`DecidablePred` synthesis and cascading into several downstream errors, plus three smaller misses
-- see `PHASE0-NOTES.md`).** Stage B of the reachability worked example,
straight from the FMSD paper: rock-paper-scissors as a four-state CSG
(`initial`, `win1`, `win2`, `draw`), checked against plain step-bounded reachability, `F<=k win2`
(the paper's own `Pmax=? [!win2 U<=k win2]`, restated in the clearer `F<=k` form -- see
`BoundedReachability.lean`'s own docstring) for concrete `k`. Convention: this
project's `MatrixGame` is row-minimises/column-maximises (the opposite of the paper's own
row-maximises/column-minimises), not worth a sign flip -- so `win2`, the state the maximising
*column* player benefits from, corresponds to whichever player the paper calls "P1" for this
property. Target states are absorbing and valued at `1`, exactly matching `reachBounded`'s design.

Both players choose `rock`/`paper`/`scissors` simultaneously at `initial`; the joint choice decides
the outcome (`win1` if row's action beats column's, `win2` if column's beats row's, `draw` if equal)
with certainty, no randomness beyond the players' own choices. `win1`/`win2` then self-loop
(absorbing -- the single round is over once someone wins) and `draw` transitions straight back to
`initial` to replay. Reward `≡ 0` throughout: this is a pure reachability property, not a
reward-accumulation one.

Three pieces:

1. `MatrixGame.value_eq_of_forall_eq`: a one-line corollary of `MatrixGameMonotone.lean`'s two
   sandwich lemmas -- a *constant* payoff matrix has that constant as its value. This is exactly
   what makes `win1` and `draw`'s stage games trivial: their transition doesn't depend on the joint
   action at all, so the payoff matrix is constant in both arguments.
2. `rpsCSG_stageValue_win1`/`_draw`/`_initial`: the stage-game value at each state, for an
   *arbitrary* continuation `v` -- `win1`'s is `v win1` (dead end, self-loop), `draw`'s is
   `v initial` (deterministic pass-through), and `initial`'s is the interesting one,
   `(v win1 + v win2 + v draw) / 3`, via the *same* `value_unique` + uniform-strategy argument
   `MatchingPennies.lean` used for matching pennies, generalised from a `2`-way zero-sum payoff to a
   `3`-way cyclic one: against uniform play, every fixed action of the other player sees exactly one
   losing, one winning, and one drawing response, so the payoff is the same constant regardless of
   what either player does -- the same "row/column sums are balanced" fact matching pennies relied
   on, just with three terms instead of two summing to a nonzero constant instead of zero.
3. Concrete `reachBounded` values at `initial` for `k = 0, 1, 2, 3, 4`: `0, 1/3, 1/3, 4/9, 4/9` --
   checked by hand against the paper's numbers before any of this was written. The repeated pairs
   are real, not a mistake: `draw` costs a genuine extra step (it's its own state, not folded into
   the same step as `initial`), so each "round" of the game consumes two
   raw `CSG` steps except when it resolves immediately, and the sequence's *distinct* values are
   exactly the naive one-step-per-round recursion `x_{n+1} = 1/3 + x_n / 3` (solving to the
   textbook `x_n \to 1/2`), each now appearing at two consecutive `k`. The exact `k \to \infty`
   limit is not proved here -- that needs the `OrderHom.lfp` machinery scoped in `PHASE0-NOTES.md`,
   not yet built.
-/

namespace Csg.MatrixGame

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I]
  [DecidableEq J] (G : MatrixGame I J)

/-- A constant payoff matrix has that constant as its value -- immediate from sandwiching `value`
    between the same constant from both sides (`MatrixGameMonotone.lean`). Exactly what makes a
    self-looping / deterministically-passing-through state's stage game trivial to evaluate below:
    its payoff matrix doesn't depend on the joint action at all. -/
theorem value_eq_of_forall_eq {c : ℝ} (h : ∀ i j, G.A i j = c) : G.value = c :=
  le_antisymm (G.value_le_of_forall_le fun i j => (h i j).le)
    (G.le_value_of_forall_le fun i j => (h i j).ge)

end Csg.MatrixGame

namespace Csg

/-- The three rock-paper-scissors actions, available to both players. -/
inductive RPSAction
  | rock
  | paper
  | scissors
  deriving DecidableEq, Inhabited

/-- Same `deriving Fintype` toolchain workaround as `RecyclingRobot.lean`'s `RobotState`/
    `RobotAction`: hand-written instead of derived. -/
instance : Fintype RPSAction where
  elems := {RPSAction.rock, RPSAction.paper, RPSAction.scissors}
  complete := by intro x; cases x <;> decide

/-- Expand a sum over all of `RPSAction` into its three terms, matching `RecyclingRobot.lean`'s
    `robotState_sum` idiom for the two-element case. Not `private`: `RockPaperScissorsSteps.lean`
    reuses this and the two `outcome_*_sum` facts below directly, rather than re-deriving them. -/
theorem rpsAction_sum {β : Type*} [AddCommMonoid β] (f : RPSAction → β) :
    ∑ a : RPSAction, f a = f .rock + f .paper + f .scissors := by
  have huniv : (Finset.univ : Finset RPSAction) = {RPSAction.rock, RPSAction.paper, .scissors} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

/-- The four rock-paper-scissors states: no round played yet, row/column won the last round
    (absorbing), or the last round was a draw (passes straight back to `initial`). -/
inductive RPSState
  | initial
  | win1
  | win2
  | draw
  deriving DecidableEq, Inhabited

instance : Fintype RPSState where
  elems := {RPSState.initial, RPSState.win1, RPSState.win2, RPSState.draw}
  complete := by intro x; cases x <;> decide

/-- The outcome of one round: `rock` beats `scissors`, `scissors` beats `paper`, `paper` beats
    `rock`, matching beats matching is a draw. Row wins (`win1`) when row's action beats column's;
    column wins (`win2`) when column's beats row's. -/
def outcome : RPSAction → RPSAction → RPSState
  | .rock, .rock => .draw
  | .rock, .paper => .win2
  | .rock, .scissors => .win1
  | .paper, .rock => .win1
  | .paper, .paper => .draw
  | .paper, .scissors => .win2
  | .scissors, .rock => .win2
  | .scissors, .paper => .win1
  | .scissors, .scissors => .draw

/-- For any fixed row action, the three possible column responses realise `win1`, `win2`, and
    `draw` exactly once each -- the concrete fact underlying "uniform is optimal here", the same
    role the vanishing row/column sums played for matching pennies. Not `private`: reused directly
    by `RockPaperScissorsSteps.lean`'s own uniform-strategy argument for a different (reward-1)
    stage game over the same `outcome` structure. -/
theorem outcome_row_sum (a1 : RPSAction) (v : RPSState → ℝ) :
    v (outcome a1 .rock) + v (outcome a1 .paper) + v (outcome a1 .scissors) =
      v .win1 + v .win2 + v .draw := by
  cases a1 <;> simp only [outcome] <;> ring

/-- Symmetric counterpart of `outcome_row_sum`, for a fixed column action. -/
theorem outcome_col_sum (a2 : RPSAction) (v : RPSState → ℝ) :
    v (outcome .rock a2) + v (outcome .paper a2) + v (outcome .scissors a2) =
      v .win1 + v .win2 + v .draw := by
  cases a2 <;> simp only [outcome] <;> ring

/-- The transition kernel: `initial` resolves the joint action deterministically via `outcome`;
    `win1`/`win2` self-loop (the round is over once someone wins); `draw` passes straight back to
    `initial` to replay, regardless of the next actions (irrelevant, since nothing depends on
    them). -/
noncomputable def rpsK : RPSState → RPSAction → RPSAction → PMF RPSState
  | .initial, a1, a2 => PMF.pure (outcome a1 a2)
  | .win1, _, _ => PMF.pure .win1
  | .win2, _, _ => PMF.pure .win2
  | .draw, _, _ => PMF.pure .initial

/-- No accumulated reward: this is a pure reachability property, not a discounted- or
    bounded-reward one. -/
noncomputable def rpsR : RPSState → RPSAction → RPSAction → ℝ := fun _ _ _ => 0

/-- Rock-paper-scissors as a `CSG`. -/
noncomputable def rpsCSG : CSG RPSState RPSAction RPSAction where
  K := rpsK
  r := rpsR

theorem rpsCSG_expect_win1 (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSG.expect .win1 a1 a2 v = v .win1 := by
  change ∑ s' : RPSState, (rpsK .win1 a1 a2 s').toReal * v s' = v .win1
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]

theorem rpsCSG_expect_draw (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSG.expect .draw a1 a2 v = v .initial := by
  change ∑ s' : RPSState, (rpsK .draw a1 a2 s').toReal * v s' = v .initial
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]

theorem rpsCSG_expect_initial (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSG.expect .initial a1 a2 v = v (outcome a1 a2) := by
  change ∑ s' : RPSState, (rpsK .initial a1 a2 s').toReal * v s' = v (outcome a1 a2)
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]

/-- `win1`'s stage game is a constant matrix (the transition ignores the joint action entirely),
    so its value is that constant -- one round already in `win1`, the game is over, worth exactly
    `v win1` forever. -/
theorem rpsCSG_stageValue_win1 (v : RPSState → ℝ) : rpsCSG.stageValue .win1 v = v .win1 := by
  have hA : ∀ a1 a2, (rpsCSG.stageGame .win1 v).A a1 a2 = v .win1 := by
    intro a1 a2
    change rpsCSG.r .win1 a1 a2 + rpsCSG.expect .win1 a1 a2 v = v .win1
    rw [rpsCSG_expect_win1]
    simp [rpsCSG, rpsR]
  exact (rpsCSG.stageGame .win1 v).value_eq_of_forall_eq hA

/-- Symmetric counterpart of `rpsCSG_stageValue_win1` for the deterministic pass-through state
    `draw`: its stage game is also a constant matrix, equal to `v initial`. -/
theorem rpsCSG_stageValue_draw (v : RPSState → ℝ) : rpsCSG.stageValue .draw v = v .initial := by
  have hA : ∀ a1 a2, (rpsCSG.stageGame .draw v).A a1 a2 = v .initial := by
    intro a1 a2
    change rpsCSG.r .draw a1 a2 + rpsCSG.expect .draw a1 a2 v = v .initial
    rw [rpsCSG_expect_draw]
    simp [rpsCSG, rpsR]
  exact (rpsCSG.stageGame .draw v).value_eq_of_forall_eq hA

theorem rpsCSG_stageGame_initial_A (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    (rpsCSG.stageGame .initial v).A a1 a2 = v (outcome a1 a2) := by
  change rpsCSG.r .initial a1 a2 + rpsCSG.expect .initial a1 a2 v = v (outcome a1 a2)
  rw [rpsCSG_expect_initial]
  simp [rpsCSG, rpsR]

/-- The uniform strategy over the three actions -- optimal for both players at `initial`, exactly
    as in matching pennies. -/
noncomputable def unif3 : RPSAction → ℝ := fun _ => 1 / 3

theorem unif3_mem : unif3 ∈ stdSimplex ℝ RPSAction :=
  ⟨fun a => by simp only [unif3]; norm_num, by simp only [unif3, rpsAction_sum]; norm_num⟩

/-- Against the uniform column strategy, *every* row strategy pays exactly `(win1+win2+draw)/3` --
    `outcome_row_sum` says the inner sum is this constant regardless of the row action, so the
    outer weighted average (any weights summing to `1`) is the same constant too. -/
theorem rpsCSG_stageGame_initial_payoff_row (v : RPSState → ℝ) {p' : RPSAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSG.stageGame .initial v).payoff p' unif3 = (v .win1 + v .win2 + v .draw) / 3 := by
  have hinner : ∀ a1, ∑ a2, (rpsCSG.stageGame .initial v).A a1 a2 * unif3 a2 =
      (v .win1 + v .win2 + v .draw) / 3 := by
    intro a1
    have hsum := outcome_row_sum a1 v
    rw [rpsAction_sum]
    simp only [rpsCSG_stageGame_initial_A, unif3]
    linarith [hsum]
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2, (rpsCSG.stageGame .initial v).A a1 a2 * unif3 a2
      = ∑ a1, p' a1 * ((v .win1 + v .win2 + v .draw) / 3) :=
        Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * ((v .win1 + v .win2 + v .draw) / 3) := by rw [← Finset.sum_mul]
    _ = (v .win1 + v .win2 + v .draw) / 3 := by rw [hp'.2, one_mul]

/-- Symmetric counterpart of `rpsCSG_stageGame_initial_payoff_row` for the column player. -/
theorem rpsCSG_stageGame_initial_payoff_col (v : RPSState → ℝ) {q' : RPSAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSG.stageGame .initial v).payoff unif3 q' = (v .win1 + v .win2 + v .draw) / 3 := by
  have hinner : ∀ a2, ∑ a1, unif3 a1 * (rpsCSG.stageGame .initial v).A a1 a2 =
      (v .win1 + v .win2 + v .draw) / 3 := by
    intro a2
    have hsum := outcome_col_sum a2 v
    rw [rpsAction_sum]
    simp only [rpsCSG_stageGame_initial_A, unif3]
    linarith [hsum]
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, unif3 a1 * (rpsCSG.stageGame .initial v).A a1 a2) * q' a2
      = ∑ a2, ((v .win1 + v .win2 + v .draw) / 3) * q' a2 :=
        Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = ((v .win1 + v .win2 + v .draw) / 3) * ∑ a2, q' a2 := by rw [← Finset.mul_sum]
    _ = (v .win1 + v .win2 + v .draw) / 3 := by rw [hq'.2, mul_one]

/-- **The payoff.** `initial`'s stage-game value, for *any* continuation `v`: the average of `v` at
    the three possible outcomes. Same `value_unique` + uniform-strategy-is-a-saddle-point argument
    `MatchingPennies.lean` used, generalised from two actions to three. -/
theorem rpsCSG_stageValue_initial (v : RPSState → ℝ) :
    rpsCSG.stageValue .initial v = (v .win1 + v .win2 + v .draw) / 3 := by
  have huu : (rpsCSG.stageGame .initial v).payoff unif3 unif3 =
      (v .win1 + v .win2 + v .draw) / 3 := rpsCSG_stageGame_initial_payoff_row v unif3_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ RPSAction,
      (rpsCSG.stageGame .initial v).payoff unif3 unif3 ≤
        (rpsCSG.stageGame .initial v).payoff p' unif3 := fun p' hp' =>
    le_of_eq (huu.trans (rpsCSG_stageGame_initial_payoff_row v hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ RPSAction,
      (rpsCSG.stageGame .initial v).payoff unif3 q' ≤
        (rpsCSG.stageGame .initial v).payoff unif3 unif3 := fun q' hq' =>
    le_of_eq ((rpsCSG_stageGame_initial_payoff_col v hq').trans huu.symm)
  have hval := (rpsCSG.stageGame .initial v).value_unique unif3_mem unif3_mem hrow hcol
  change (rpsCSG.stageGame .initial v).value = (v .win1 + v .win2 + v .draw) / 3
  rw [← hval]
  exact huu

/-- The property being computed: reachability of `win2`, i.e. plain step-bounded reachability
    `F<=k win2` (see `BoundedReachability.lean`). An `abbrev`, not a `def`:
    plain `def`s aren't unfolded during typeclass search, so `DecidablePred rpsGoalWin2` (needed
    implicitly everywhere `reachBounded rpsGoalWin2` appears below) would otherwise fail to
    synthesize even though `RPSState` itself has decidable equality. -/
abbrev rpsGoalWin2 : RPSState → Prop := fun s => s = .win2

/-- `win1` is a dead end for reaching `win2`: once there, permanently worth `0`, at every step
    budget -- direct consequence of `rpsCSG_stageValue_win1` plus induction on the budget. -/
theorem rpsCSG_reachBounded_win1 (k : ℕ) : rpsCSG.reachBounded rpsGoalWin2 k .win1 = 0 := by
  induction k with
  | zero => simp [CSG.reachBounded_zero, rpsGoalWin2]
  | succ k ih =>
      rw [CSG.reachBounded_succ, if_neg (show ¬ rpsGoalWin2 .win1 by decide),
        rpsCSG_stageValue_win1, ih]

/-- `win2` is worth `1` at every step budget -- direct from `reachBounded_of_goal`. -/
theorem rpsCSG_reachBounded_win2 (k : ℕ) : rpsCSG.reachBounded rpsGoalWin2 k .win2 = 1 :=
  rpsCSG.reachBounded_of_goal rpsGoalWin2 k rfl

/-- `draw`'s value at `k + 1` steps remaining is exactly `initial`'s value at `k` steps -- the
    genuine extra step `draw`, as its own state, costs. -/
theorem rpsCSG_reachBounded_draw_succ (k : ℕ) :
    rpsCSG.reachBounded rpsGoalWin2 (k + 1) .draw = rpsCSG.reachBounded rpsGoalWin2 k .initial := by
  rw [CSG.reachBounded_succ, if_neg (show ¬ rpsGoalWin2 .draw by decide), rpsCSG_stageValue_draw]

/-- The general one-step recursion at `initial`, with `win2`'s constant value already substituted
    in -- `win1`'s constant `0` is substituted next, in `rpsCSG_reachBounded_initial_succ'`. -/
theorem rpsCSG_reachBounded_initial_succ (k : ℕ) :
    rpsCSG.reachBounded rpsGoalWin2 (k + 1) .initial =
      (rpsCSG.reachBounded rpsGoalWin2 k .win1 + 1 +
        rpsCSG.reachBounded rpsGoalWin2 k .draw) / 3 := by
  rw [CSG.reachBounded_succ, if_neg (show ¬ rpsGoalWin2 .initial by decide),
    rpsCSG_stageValue_initial, rpsCSG_reachBounded_win2]

/-- **The payoff.** The recursion reduces to a single term: `x_{k+1} = (1 + d_k) / 3`, matching the
    hand-derivation worked out before any of this was written. -/
theorem rpsCSG_reachBounded_initial_succ' (k : ℕ) :
    rpsCSG.reachBounded rpsGoalWin2 (k + 1) .initial =
      (1 + rpsCSG.reachBounded rpsGoalWin2 k .draw) / 3 := by
  rw [rpsCSG_reachBounded_initial_succ, rpsCSG_reachBounded_win1]
  ring

theorem rpsCSG_reachBounded_initial_zero : rpsCSG.reachBounded rpsGoalWin2 0 .initial = 0 := by
  simp [CSG.reachBounded_zero, rpsGoalWin2]

theorem rpsCSG_reachBounded_draw_zero : rpsCSG.reachBounded rpsGoalWin2 0 .draw = 0 := by
  simp [CSG.reachBounded_zero, rpsGoalWin2]

/-- **The payoff.** `x_1 = 1/3`: within one step, `win2` is reached exactly when the very first
    round is won outright, which under optimal (uniform) play happens with probability `1/3`. -/
theorem rpsCSG_reachBounded_initial_one : rpsCSG.reachBounded rpsGoalWin2 1 .initial = 1 / 3 := by
  rw [rpsCSG_reachBounded_initial_succ', rpsCSG_reachBounded_draw_zero]
  norm_num

theorem rpsCSG_reachBounded_draw_one : rpsCSG.reachBounded rpsGoalWin2 1 .draw = 0 := by
  rw [rpsCSG_reachBounded_draw_succ, rpsCSG_reachBounded_initial_zero]

/-- `x_2 = 1/3`, same as `x_1`: a second step can only help by resolving a draw, and there wasn't
    one to resolve yet within budget `1`. -/
theorem rpsCSG_reachBounded_initial_two : rpsCSG.reachBounded rpsGoalWin2 2 .initial = 1 / 3 := by
  rw [rpsCSG_reachBounded_initial_succ', rpsCSG_reachBounded_draw_one]
  norm_num

theorem rpsCSG_reachBounded_draw_two : rpsCSG.reachBounded rpsGoalWin2 2 .draw = 1 / 3 := by
  rw [rpsCSG_reachBounded_draw_succ, rpsCSG_reachBounded_initial_one]

/-- `x_3 = 4/9`: the first budget at which a resolved draw (from step `1`) can pay off. -/
theorem rpsCSG_reachBounded_initial_three :
    rpsCSG.reachBounded rpsGoalWin2 3 .initial = 4 / 9 := by
  rw [rpsCSG_reachBounded_initial_succ', rpsCSG_reachBounded_draw_two]
  norm_num

theorem rpsCSG_reachBounded_draw_three : rpsCSG.reachBounded rpsGoalWin2 3 .draw = 1 / 3 := by
  rw [rpsCSG_reachBounded_draw_succ, rpsCSG_reachBounded_initial_two]

/-- `x_4 = 4/9`, same as `x_3` -- the same pairing-up pattern as `x_1 = x_2`, matching the
    doubled-step-per-round structure `draw` (as its own genuine state) imposes. The sequence
    `0, 1/3, 1/3, 4/9, 4/9, ...` is exactly the naive one-step-per-round recursion
    `x_{n+1} = 1/3 + x_n/3` (limit `1/2`), each value now appearing twice. -/
theorem rpsCSG_reachBounded_initial_four :
    rpsCSG.reachBounded rpsGoalWin2 4 .initial = 4 / 9 := by
  rw [rpsCSG_reachBounded_initial_succ', rpsCSG_reachBounded_draw_three]
  norm_num

end Csg
