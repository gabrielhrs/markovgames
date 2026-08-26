/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.RockPaperScissors

/-!
# Worked example: expected number of steps until winning a round

**Status: drafted, not yet run through `lake build`.** The reward-until-absorption worked example
agreed with the user: instead of a probability (`Pmax=? [F win2]`, already done in
`RockPaperScissorsLfp.lean`/`RockPaperScissorsUntil.lean`), the expected number of raw `CSG` steps
until *some* round is won (`win1` or `win2`, either player), under the same uniform play that was
already optimal for every stage game in this line. Hand-solved before any code was written: let
`x` = expected steps from `initial`, `y` = expected steps from `draw`. Each round at `initial`
resolves immediately (`win1`/`win2`, contributing no further steps) with probability `2/3`, or
drifts to `draw` with probability `1/3`; `draw` always costs exactly one more step back to
`initial`. That gives `x = 1 + y/3` and `y = 1 + x`, with the unique real solution `x = 2`, `y = 3`.

**Deliberately scoped as a bespoke instance, not a general reward-until operator.** Reachability
values live in `[0, 1]`, which is what let `Set.Icc (0:ℝ) 1` be a `CompleteLattice` for free;
expected steps has no such bound (a state from which absorption isn't certain could legitimately
need `⊤`), so a fully general version needs `ℝ≥0∞`, not `ℝ`, to state `.lfp` over at all -- exactly
the layer the reachcert debrief flagged as the hard one (its own `R_inf` completeness theorem was
left `sorry` in the source). Building that first, before knowing what a concrete proof actually
needs, would repeat the mistake this project has avoided everywhere else (`RecyclingRobot.lean`,
`MatchingPennies.lean`, `RockPaperScissorsLfp.lean` all validated a concrete instance before any
generic combinator existed). So this file works directly in `ℝ`, reusing the *already fully
general* `CSG.stageGame`/`stageValue`/`MatrixGame.value` machinery -- none of which was ever
restricted to a reward-free `CSG`, only `CsgMonotone.lean`'s `[0, 1]`-boundedness lemmas needed
`C.r ≡ 0` -- against a *new* `CSG` instance, `rpsCSGSteps`, scored by a constant reward of `1` per
step instead of `rpsR`'s `0`. No new matrix-game infrastructure, no `OrderHom` bundling, no `goal`
parameter: `rpsK` (the transition kernel) is reused unchanged, and the "someone has won" absorption
is hard-coded to `win1 ∨ win2` directly in `rpsStepsStep` below, rather than threaded through as a
general predicate.

**Working in plain `ℝ`, rather than `ℝ≥0∞`, sidesteps the spurious-solution issue by construction,
not just by convenience.** Reachability's Knaster-Tarski certificate
(`OrderHom.lfp_eq_of_certificate`) was needed because `[0, 1]`-valued Bellman equations generally
admit *several* self-consistent
values (e.g. `v ≡ 0` is a valid pre-fixed point wherever no path to the goal exists), and least
fixed point is what picks out the correct one. Here, `win1`/`win2` are pinned to `0` *by
construction* -- `rpsStepsStep`'s own `if` forces this for *any* candidate, not just the guessed
one -- and the two remaining unknowns (`x`, `y`) then satisfy a genuine *linear* system with the
same coefficients regardless of which candidate is plugged in, so it has exactly one real solution.
`rpsSteps_unique` proves this directly: *any* real-valued fixed point of `rpsStepsStep` equals
`rpsSteps`, a strictly stronger statement than `RockPaperScissorsLfp.lean`'s lower-bound-only
certificate needed to make, and one that needs nothing beyond `linarith` once the two forced
equations are in hand.

**What this does *not* establish, stated honestly.** `rpsSteps` is the unique real-valued fixed
point of the natural Bellman-style recursion for "expected steps to absorption" -- it does not, on
its own, formally connect that recursion to the actual measure-theoretic expected value of the
`PMF`-driven process under uniform play. That connection is standard (the two coincide whenever
absorption is certain, i.e. a "proper" policy in Puterman's terminology), and this project has
already informally established absorption is certain here (uniform play resolves each round with
probability `2/3`, so the probability of never resolving after `n` rounds is `(1/3)^n → 0`), but a
fully formal a.s.-absorption/properness argument is exactly the piece reachcert's own `𝒟`/`𝒟_iv`
ranking-function machinery exists for, and is not attempted here -- matching how reachcert's own
`R_inf` completeness theorem was left `sorry` in its source rather than treated as a solved problem.
-/

namespace Csg

/-- Rock-paper-scissors, scored by a constant per-step cost of `1` instead of `rpsR`'s identically
    `0` -- same transition kernel `rpsK`, different bookkeeping. This is what lets the *already
    general* `CSG.stageValue` compute "cost of this step plus expected continuation" directly, with
    no new matrix-game machinery: `stageValue`'s underlying `Sion.exists_isSaddlePointOn` route was
    never conditioned on `C.r ≡ 0`, only `CsgMonotone.lean`'s separate `[0, 1]`-boundedness lemmas
    were, and this file needs no such boundedness at all. -/
noncomputable def rpsCSGSteps : CSG RPSState RPSAction RPSAction where
  K := rpsK
  r := fun _ _ _ => 1

theorem rpsCSGSteps_expect_draw (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSGSteps.expect .draw a1 a2 v = v .initial := by
  change ∑ s' : RPSState, (rpsK .draw a1 a2 s').toReal * v s' = v .initial
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]

theorem rpsCSGSteps_expect_initial (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSGSteps.expect .initial a1 a2 v = v (outcome a1 a2) := by
  change ∑ s' : RPSState, (rpsK .initial a1 a2 s').toReal * v s' = v (outcome a1 a2)
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]

/-- `draw`'s stage game is a constant matrix (same as `rpsCSG_stageValue_draw`'s argument), now
    worth `1` (this step's cost) plus `initial`'s continuation, since `draw` always passes straight
    back to `initial`. -/
theorem rpsCSGSteps_stageValue_draw (v : RPSState → ℝ) :
    rpsCSGSteps.stageValue .draw v = 1 + v .initial := by
  have hA : ∀ a1 a2, (rpsCSGSteps.stageGame .draw v).A a1 a2 = 1 + v .initial := by
    intro a1 a2
    change rpsCSGSteps.r .draw a1 a2 + rpsCSGSteps.expect .draw a1 a2 v = 1 + v .initial
    rw [rpsCSGSteps_expect_draw]
    simp [rpsCSGSteps]
  exact (rpsCSGSteps.stageGame .draw v).value_eq_of_forall_eq hA

theorem rpsCSGSteps_stageGame_initial_A (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    (rpsCSGSteps.stageGame .initial v).A a1 a2 = 1 + v (outcome a1 a2) := by
  change rpsCSGSteps.r .initial a1 a2 + rpsCSGSteps.expect .initial a1 a2 v =
    1 + v (outcome a1 a2)
  rw [rpsCSGSteps_expect_initial]
  simp [rpsCSGSteps]

/-- Against uniform column play, every row action pays exactly `1 + (v win1 + v win2 + v draw)/3`
    -- `outcome_row_sum` (now public, see `RockPaperScissors.lean`'s own note) says the sum over
    the three responses is the same constant regardless of the row action, same as
    `rpsCSG_stageGame_initial_payoff_row`'s argument, shifted by the constant step cost. -/
theorem rpsCSGSteps_stageGame_initial_payoff_row (v : RPSState → ℝ) {p' : RPSAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSGSteps.stageGame .initial v).payoff p' unif3 =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by
  have hinner : ∀ a1, ∑ a2, (rpsCSGSteps.stageGame .initial v).A a1 a2 * unif3 a2 =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by
    intro a1
    have hsum := outcome_row_sum a1 v
    rw [rpsAction_sum]
    simp only [rpsCSGSteps_stageGame_initial_A, unif3]
    linarith [hsum]
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2, (rpsCSGSteps.stageGame .initial v).A a1 a2 * unif3 a2
      = ∑ a1, p' a1 * (1 + (v .win1 + v .win2 + v .draw) / 3) :=
        Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * (1 + (v .win1 + v .win2 + v .draw) / 3) := by rw [← Finset.sum_mul]
    _ = 1 + (v .win1 + v .win2 + v .draw) / 3 := by rw [hp'.2, one_mul]

/-- Symmetric counterpart of `rpsCSGSteps_stageGame_initial_payoff_row`, for the column player. -/
theorem rpsCSGSteps_stageGame_initial_payoff_col (v : RPSState → ℝ) {q' : RPSAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSGSteps.stageGame .initial v).payoff unif3 q' =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by
  have hinner : ∀ a2, ∑ a1, unif3 a1 * (rpsCSGSteps.stageGame .initial v).A a1 a2 =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by
    intro a2
    have hsum := outcome_col_sum a2 v
    rw [rpsAction_sum]
    simp only [rpsCSGSteps_stageGame_initial_A, unif3]
    linarith [hsum]
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, unif3 a1 * (rpsCSGSteps.stageGame .initial v).A a1 a2) * q' a2
      = ∑ a2, (1 + (v .win1 + v .win2 + v .draw) / 3) * q' a2 :=
        Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = (1 + (v .win1 + v .win2 + v .draw) / 3) * ∑ a2, q' a2 := by rw [← Finset.mul_sum]
    _ = 1 + (v .win1 + v .win2 + v .draw) / 3 := by rw [hq'.2, mul_one]

/-- **The payoff.** `initial`'s stage-game value, for *any* continuation `v`: `1` (this step's
    cost) plus the average of `v` at the three possible outcomes -- the same
    `value_unique` + uniform-strategy-is-a-saddle-point argument every other stage game in this
    line has used, unaffected by the reward shift. -/
theorem rpsCSGSteps_stageValue_initial (v : RPSState → ℝ) :
    rpsCSGSteps.stageValue .initial v = 1 + (v .win1 + v .win2 + v .draw) / 3 := by
  have huu : (rpsCSGSteps.stageGame .initial v).payoff unif3 unif3 =
      1 + (v .win1 + v .win2 + v .draw) / 3 := rpsCSGSteps_stageGame_initial_payoff_row v unif3_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ RPSAction,
      (rpsCSGSteps.stageGame .initial v).payoff unif3 unif3 ≤
        (rpsCSGSteps.stageGame .initial v).payoff p' unif3 := fun p' hp' =>
    le_of_eq (huu.trans (rpsCSGSteps_stageGame_initial_payoff_row v hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ RPSAction,
      (rpsCSGSteps.stageGame .initial v).payoff unif3 q' ≤
        (rpsCSGSteps.stageGame .initial v).payoff unif3 unif3 := fun q' hq' =>
    le_of_eq ((rpsCSGSteps_stageGame_initial_payoff_col v hq').trans huu.symm)
  have hval := (rpsCSGSteps.stageGame .initial v).value_unique unif3_mem unif3_mem hrow hcol
  change (rpsCSGSteps.stageGame .initial v).value = 1 + (v .win1 + v .win2 + v .draw) / 3
  rw [← hval]
  exact huu

/-- The bespoke expected-steps-to-absorption Bellman step: `win1`/`win2` are hard-pinned to `0`
    (the round is already decided, nothing further accumulates) *regardless of what `v` says*,
    unlike `reachOp`/`untilOp`'s general `goal : S → Prop` parameter -- this file deliberately does
    not build that generality, see the module docstring. Every other state pays `rpsCSGSteps`'s
    stage value, which already includes the step cost via its own `r ≡ 1`. -/
noncomputable def rpsStepsStep (v : RPSState → ℝ) (s : RPSState) : ℝ :=
  if s = RPSState.win1 ∨ s = RPSState.win2 then 0 else rpsCSGSteps.stageValue s v

/-- The hand-solved candidate: `0` once absorbed, `2` steps from `initial`, `3` from `draw`. -/
noncomputable def rpsSteps : RPSState → ℝ
  | .win1 => 0
  | .win2 => 0
  | .initial => 2
  | .draw => 3

/-- **The payoff, part 1.** `rpsSteps` is an exact fixed point of `rpsStepsStep`. `win1`/`win2`
    close by `rfl` alone -- `rpsStepsStep`'s own absorbing branch pins them to `0` regardless of
    the continuation, matching `rpsSteps`'s own `0` there with no further reasoning needed.
    `initial`/`draw` `change` past the concrete `if` (a pure defeq jump on a closed, decidable
    condition, the same technique `RockPaperScissorsLfp.lean`'s fix rounds established) down to
    the bare stage-value equation, then close with the lemmas above plus arithmetic. -/
theorem rpsSteps_fixed : rpsStepsStep rpsSteps = rpsSteps := by
  funext s
  cases s with
  | win1 => rfl
  | win2 => rfl
  | initial =>
      change rpsCSGSteps.stageValue RPSState.initial rpsSteps = rpsSteps RPSState.initial
      rw [rpsCSGSteps_stageValue_initial]
      norm_num [rpsSteps]
  | draw =>
      change rpsCSGSteps.stageValue RPSState.draw rpsSteps = rpsSteps RPSState.draw
      rw [rpsCSGSteps_stageValue_draw]
      norm_num [rpsSteps]

/-- **The payoff, part 2, and the reason working in plain `ℝ` was worth it.** `rpsSteps` is the
    *unique* real-valued fixed point of `rpsStepsStep` -- not merely a lower bound over pre-fixed
    points the way `RockPaperScissorsLfp.lean`'s Knaster-Tarski certificate had to settle for.
    `win1`/`win2` are forced to `0` for *any* fixed point `w` by `rpsStepsStep`'s own absorbing
    branch (`change` again does the defeq work); the remaining two equations, once those zeros are
    substituted in, are a genuine invertible linear system in `w initial`/`w draw` with exactly one
    real solution, closed by `linarith` alone -- no completeness-of-`[0,1]` argument, no `sSup`, no
    interval sandwiching, just linear algebra. -/
theorem rpsSteps_unique {w : RPSState → ℝ} (hw : rpsStepsStep w = w) : w = rpsSteps := by
  have hwin1 : w RPSState.win1 = 0 := by
    have h := congrFun hw RPSState.win1
    change (0 : ℝ) = w RPSState.win1 at h
    exact h.symm
  have hwin2 : w RPSState.win2 = 0 := by
    have h := congrFun hw RPSState.win2
    change (0 : ℝ) = w RPSState.win2 at h
    exact h.symm
  have hdraw : rpsCSGSteps.stageValue RPSState.draw w = w RPSState.draw := by
    have h := congrFun hw RPSState.draw
    change rpsCSGSteps.stageValue RPSState.draw w = w RPSState.draw at h
    exact h
  have hinit : rpsCSGSteps.stageValue RPSState.initial w = w RPSState.initial := by
    have h := congrFun hw RPSState.initial
    change rpsCSGSteps.stageValue RPSState.initial w = w RPSState.initial at h
    exact h
  rw [rpsCSGSteps_stageValue_draw] at hdraw
  rw [rpsCSGSteps_stageValue_initial, hwin1, hwin2] at hinit
  have hw_init : w RPSState.initial = 2 := by linarith
  have hw_draw : w RPSState.draw = 3 := by linarith
  funext s
  cases s with
  | win1 => simp [hwin1, rpsSteps]
  | win2 => simp [hwin2, rpsSteps]
  | initial => simp [hw_init, rpsSteps]
  | draw => simp [hw_draw, rpsSteps]

/-- The number the whole exercise was after: from `initial`, expected `2` raw `CSG` steps until
    someone wins a round, under uniform (optimal) play. -/
theorem rpsSteps_initial_eq_two : rpsSteps RPSState.initial = 2 := rfl

/-- From `draw`, expected `3` -- the one genuine extra step `draw` costs, matching
    `RockPaperScissors.lean`'s own observation that `draw` doubles the raw step count per round. -/
theorem rpsSteps_draw_eq_three : rpsSteps RPSState.draw = 3 := rfl

end Csg
