/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.BackwardInduction
import Csg.CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# A non-toy `bwInd` instance: intrusion detection, sourced from PRISM-games' IDS case study

**Status: done, confirmed by a clean `lake build`.** The two hand-checked instances
(`idsV1`/`idsCSG_bwInd_one*` and `idsV2`/`idsCSG_bwInd_two*`, the first in this project to exercise
`bwInd`'s recursion against a non-uniform, state-dependent continuation) build clean, VS Code
included -- the one-round instance after the fix round below. Two further `∀ n` facts have since
been added (see that section's own docstring) and build clean too, first attempt, no fix round
needed: `idsCSG_bwInd_compromised_eq_healthy_add_one` and `idsCSG_bwInd_mono`. `idsK` uses
`PMF.pure`,
which lives in `Mathlib.Probability.ProbabilityMassFunction.Monad` (the monadic-operations file,
not `.Basic`, per that file's own docstring) -- an import this file was originally missing, since
`Csg.BackwardInduction`'s own transitive imports stop at `.Basic`. `MatchingPennies.lean` already
imports `.Monad` directly for the same reason; `RockPaperScissors.lean` gets it for free only
because it separately imports `Csg.MatchingPennies`. Traced by computing this file's actual
transitive import closure (1659 Mathlib modules) and confirming `.Monad` was absent from it -- so
VS Code's "Unknown constant `PMF.pure`" was a real, correct diagnosis, not the cosmetic
elaboration-order noise seen elsewhere in this project. Fixed by adding the missing import
directly, matching `MatchingPennies.lean`'s precedent; the fixed version compiles with zero
warnings of its own, confirmed against the build's full, unfiltered log (2998 jobs, "Build
completed successfully", nothing under `Csg.IntrusionDetection`) -- `lake build`'s default output
only ever prints a line for a module that has a warning or error to report, which is also the real
answer to why most of the project's 2998 compiled modules never show up in a pasted build log at
all, this file included.

`RockPaperScissors.lean`'s stage games are all "toy" in the specific sense flagged in
`PHASE0-NOTES.md`: at every state, the optimal strategy for both players is the *same* uniform
mixture, regardless of the continuation value. This file's stage games are not: `idsP`/`idsQ`
below are a genuinely non-uniform mixed strategy pair, and (unlike a hand-picked example) they
come from a real, published, third-party model -- PRISM-games' "Intrusion Detection Policies"
case study (Zhu & Başar 2009), `ids_simple.prism`
(<https://www.prismmodelchecker.org/casestudies/ids.php>).

Two players: `policy` (the defender, row/minimizer, actions `defend1`/`defend2`) versus
`attacker` (column/maximizer, actions `attack1`/`attack2`). Two states: `healthy`/`compromised`.
Transitions are deterministic and state-independent: `(defend1,attack1) -> healthy`,
`(defend1,attack2) -> compromised`, `(defend2,attack1) -> compromised`,
`(defend2,attack2) -> healthy`. The reward (`"damage"` in PRISM's terms, paid by `policy` to
`attacker`) is *not* symmetric between the two "mismatch" action pairs -- `idsR` below is quoted
directly from the case study's published table. That reward-side asymmetry is exactly what
`IntervalCertificate.lean`/`ReachOp.lean`/`SafetyOp.lean` cannot see (they all require
`hr : C.r ≡ 0`), which is why this instance targets `BackwardInduction.lean`'s `bwInd` instead --
see `PHASE0-NOTES.md` for the fuller comparison against PRISM's "jamming" case study, deferred as
a future `IntervalCertificate.lean` candidate for exactly the opposite reason (genuine
*transition*-side uncertainty, symmetric rewards).

This file's target is the one-step (one round remaining) instance: `idsCSG.bwInd (fun _ => 0) 1`.
Both states' stage games (continuation `fun _ => 0`, matching PRISM's convention of no reward
*at* the horizon) turn out to be solved by the *same* mixed-strategy pair `idsP`/`idsQ` -- a
genuine numeric coincidence of this particular reward table, not something engineered in, and not
something that holds at every round (the two-rounds-remaining instance, a natural follow-up, needs
a different pair). The resulting values, `1/3` at `healthy` and `4/3` at `compromised`, were
independently checked against a real local PRISM-games run reported by the user for
`<<policy>>R{"damage"}min=?[F r=rounds]` at `rounds=1`: `0.3333333333333333`, matching `1/3`
exactly.
-/

namespace Csg

/-- The two states of PRISM's `ids_simple.prism`: the system is either operating normally or has
    been compromised by the attacker. -/
inductive IDSState
  | healthy
  | compromised
  deriving DecidableEq, Inhabited

/-- Same `deriving Fintype` toolchain workaround as `RockPaperScissors.lean`'s `RPSState`. -/
instance : Fintype IDSState where
  elems := {IDSState.healthy, IDSState.compromised}
  complete := by intro s; cases s <;> decide

/-- The defender's two policies: `ids_simple.prism`'s `defend1`/`defend2`. The defender is the row
    player (minimizer), matching `MatrixGame`'s convention and PRISM's own framing of `policy` as
    trying to *minimize* expected damage. -/
inductive PolicyAction
  | defend1
  | defend2
  deriving DecidableEq, Inhabited

instance : Fintype PolicyAction where
  elems := {PolicyAction.defend1, PolicyAction.defend2}
  complete := by intro a; cases a <;> decide

/-- The attacker's two strategies: `ids_simple.prism`'s `attack1`/`attack2`. The attacker is the
    column player (maximizer). -/
inductive AttackAction
  | attack1
  | attack2
  deriving DecidableEq, Inhabited

instance : Fintype AttackAction where
  elems := {AttackAction.attack1, AttackAction.attack2}
  complete := by intro a; cases a <;> decide

/-- Expand a sum over all of `PolicyAction` into its two terms, matching `RockPaperScissors.lean`'s
    `rpsAction_sum` idiom for the three-element case. -/
theorem policyAction_sum {β : Type*} [AddCommMonoid β] (f : PolicyAction → β) :
    ∑ a : PolicyAction, f a = f .defend1 + f .defend2 := by
  have huniv : (Finset.univ : Finset PolicyAction) = {PolicyAction.defend1, .defend2} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Symmetric counterpart of `policyAction_sum` for `AttackAction`. -/
theorem attackAction_sum {β : Type*} [AddCommMonoid β] (f : AttackAction → β) :
    ∑ a : AttackAction, f a = f .attack1 + f .attack2 := by
  have huniv : (Finset.univ : Finset AttackAction) = {AttackAction.attack1, .attack2} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Deterministic, state-independent transition, exactly as `ids_simple.prism` specifies it: the
    next state depends only on the joint action just played, not on the state the joint action was
    played *in*. -/
noncomputable def idsK : IDSState → PolicyAction → AttackAction → PMF IDSState
  | _, .defend1, .attack1 => PMF.pure .healthy
  | _, .defend1, .attack2 => PMF.pure .compromised
  | _, .defend2, .attack1 => PMF.pure .compromised
  | _, .defend2, .attack2 => PMF.pure .healthy

/-- The `"damage"` reward table, quoted directly from `ids_simple.prism`: paid by the row player
    (`policy`) to the column player (`attacker`). The asymmetry that makes this a genuinely
    non-toy stage game lives entirely here, on the two "mismatch" action pairs at `healthy`
    (`0.5` vs `1`) and at `compromised` (`1.5` vs `2`) -- not in the (symmetric) transition
    kernel `idsK` above. -/
noncomputable def idsR : IDSState → PolicyAction → AttackAction → ℝ
  | .healthy, .defend1, .attack1 => 0
  | .healthy, .defend1, .attack2 => 1
  | .healthy, .defend2, .attack1 => 1 / 2
  | .healthy, .defend2, .attack2 => 0
  | .compromised, .defend1, .attack1 => 1
  | .compromised, .defend1, .attack2 => 2
  | .compromised, .defend2, .attack1 => 3 / 2
  | .compromised, .defend2, .attack2 => 1

/-- The intrusion-detection game as a `CSG`. -/
noncomputable def idsCSG : CSG IDSState PolicyAction AttackAction where
  K := idsK
  r := idsR

/-- Against the all-zero continuation (`bwInd`'s base case, `rFin := fun _ => 0`), every stage
    game's payoff matrix is exactly the immediate reward: the expected-continuation term vanishes
    since `v ≡ 0`, regardless of what `idsK` does. -/
theorem idsCSG_stageGame_A (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction) :
    (idsCSG.stageGame s (fun _ => 0)).A a1 a2 = idsR s a1 a2 := by
  have hexpect : idsCSG.expect s a1 a2 (fun _ => 0) = 0 := by
    unfold CSG.expect
    simp
  change idsCSG.r s a1 a2 + idsCSG.expect s a1 a2 (fun _ => 0) = idsR s a1 a2
  rw [hexpect, add_zero]
  rfl

/-- The one-round-remaining value at each state: `1/3` at `healthy`, `4/3` at `compromised`.
    Matches the real PRISM-games result for round `1` exactly (`0.3333333333333333`); see this
    file's docstring. -/
noncomputable def idsV1 : IDSState → ℝ
  | .healthy => 1 / 3
  | .compromised => 4 / 3

/-- The defender's mixed strategy that equalises the attacker's two pure-strategy payoffs at
    *both* states simultaneously -- `defend1` with probability `1/3`, `defend2` with probability
    `2/3`. Optimal for the one-round-remaining stage game at either state (`idsCSG_payoff_col`
    below), the same role `unif3` plays for rock-paper-scissors, but not uniform. -/
noncomputable def idsP : PolicyAction → ℝ
  | .defend1 => 1 / 3
  | .defend2 => 2 / 3

theorem idsP_mem : idsP ∈ stdSimplex ℝ PolicyAction :=
  ⟨fun a => by cases a <;> norm_num [idsP], by simp only [policyAction_sum, idsP]; norm_num⟩

/-- Symmetric counterpart of `idsP` for the attacker: `attack1` with probability `2/3`, `attack2`
    with probability `1/3`. Equalises the defender's two pure-strategy payoffs at both states
    simultaneously (`idsCSG_payoff_row` below). -/
noncomputable def idsQ : AttackAction → ℝ
  | .attack1 => 2 / 3
  | .attack2 => 1 / 3

theorem idsQ_mem : idsQ ∈ stdSimplex ℝ AttackAction :=
  ⟨fun a => by cases a <;> norm_num [idsQ], by simp only [attackAction_sum, idsQ]; norm_num⟩

/-- Against `idsQ`, *every* row strategy pays exactly `idsV1 s` -- `idsQ` equalises the two pure
    row actions' payoffs at whichever state `s` is (checked directly, by cases, since there are
    only two of each), so any weighted average of them is that same constant. Mirrors
    `RockPaperScissors.lean`'s `rpsCSG_stageGame_initial_payoff_row`, generalised from the uniform
    `unif3` to the non-uniform `idsQ`. -/
theorem idsCSG_payoff_row (s : IDSState) {p' : PolicyAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ PolicyAction) :
    (idsCSG.stageGame s (fun _ => 0)).payoff p' idsQ = idsV1 s := by
  have hinner : ∀ a1, ∑ a2, (idsCSG.stageGame s (fun _ => 0)).A a1 a2 * idsQ a2 = idsV1 s := by
    intro a1
    rw [attackAction_sum]
    cases s <;> cases a1 <;> simp [idsCSG_stageGame_A, idsR, idsQ, idsV1] <;> norm_num
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2, (idsCSG.stageGame s (fun _ => 0)).A a1 a2 * idsQ a2
      = ∑ a1, p' a1 * idsV1 s := Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * idsV1 s := by rw [← Finset.sum_mul]
    _ = idsV1 s := by rw [hp'.2, one_mul]

/-- Symmetric counterpart of `idsCSG_payoff_row` for the column player. -/
theorem idsCSG_payoff_col (s : IDSState) {q' : AttackAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ AttackAction) :
    (idsCSG.stageGame s (fun _ => 0)).payoff idsP q' = idsV1 s := by
  have hinner : ∀ a2, ∑ a1, idsP a1 * (idsCSG.stageGame s (fun _ => 0)).A a1 a2 = idsV1 s := by
    intro a2
    rw [policyAction_sum]
    cases s <;> cases a2 <;> simp [idsCSG_stageGame_A, idsR, idsP, idsV1] <;> norm_num
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, idsP a1 * (idsCSG.stageGame s (fun _ => 0)).A a1 a2) * q' a2
      = ∑ a2, idsV1 s * q' a2 := Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = idsV1 s * ∑ a2, q' a2 := by rw [← Finset.mul_sum]
    _ = idsV1 s := by rw [hq'.2, mul_one]

/-- **The payoff.** The one-round-remaining stage-game value at either state, matching `idsV1`.
    Same `value_unique` + shared-saddle-point argument `RockPaperScissors.lean`'s
    `rpsCSG_stageValue_initial` uses, with `idsP`/`idsQ` in place of the uniform `unif3`. -/
theorem idsCSG_stageValue (s : IDSState) : idsCSG.stageValue s (fun _ => 0) = idsV1 s := by
  have huu : (idsCSG.stageGame s (fun _ => 0)).payoff idsP idsQ = idsV1 s :=
    idsCSG_payoff_row s idsP_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ PolicyAction,
      (idsCSG.stageGame s (fun _ => 0)).payoff idsP idsQ ≤
        (idsCSG.stageGame s (fun _ => 0)).payoff p' idsQ := fun p' hp' =>
    le_of_eq (huu.trans (idsCSG_payoff_row s hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ AttackAction,
      (idsCSG.stageGame s (fun _ => 0)).payoff idsP q' ≤
        (idsCSG.stageGame s (fun _ => 0)).payoff idsP idsQ := fun q' hq' =>
    le_of_eq ((idsCSG_payoff_col s hq').trans huu.symm)
  have hval := (idsCSG.stageGame s (fun _ => 0)).value_unique idsP_mem idsQ_mem hrow hcol
  change (idsCSG.stageGame s (fun _ => 0)).value = idsV1 s
  rw [← hval]
  exact huu

/-- **The headline result.** One round remaining, `bwInd`'s recursive step applied once to the
    all-zero terminal reward: `idsV1`. -/
theorem idsCSG_bwInd_one (s : IDSState) : idsCSG.bwInd (fun _ => 0) 1 s = idsV1 s := by
  rw [CSG.bwInd_succ, CSG.bwInd_zero]
  exact idsCSG_stageValue s

/-- Numeric form at `healthy`, matching the real PRISM-games result for round `1`
    (`0.3333333333333333`) exactly. -/
theorem idsCSG_bwInd_one_healthy : idsCSG.bwInd (fun _ => 0) 1 .healthy = 1 / 3 :=
  idsCSG_bwInd_one .healthy

/-- Numeric form at `compromised`. -/
theorem idsCSG_bwInd_one_compromised : idsCSG.bwInd (fun _ => 0) 1 .compromised = 4 / 3 :=
  idsCSG_bwInd_one .compromised

/-!
## Two rounds remaining: the first genuine exercise of `bwInd`'s recursion

Everything above stops at one round, where `bwInd`'s recursive step is applied to the literal
terminal reward `fun _ => 0` -- itself not the product of a previous `bwInd` call. This section
feeds `idsV1` back in as the continuation, the step that actually exercises `bwInd_succ`'s
recursion against a non-uniform, state-dependent value function for the first time in this
project. The resulting values, `25/21` at `healthy` and `46/21` at `compromised`, were
independently checked against the same real PRISM-games run reported by the user, at `rounds=2`:
`1.1904761904762453`, matching `25/21` exactly (`25/21 = 1.190476190476...`).

The optimal strategies change from `idsP`/`idsQ` to a new pair, `idsP2`/`idsQ2` -- again shared
between both states, this time because `idsR`'s `compromised` row is `idsR`'s `healthy` row plus
the constant `1` at every joint action (visible directly in the reward table above), so the two
states' two-rounds-remaining stage games differ only by that same additive constant throughout,
and `MatrixGameMonotone.lean`'s `value_add_const` says shifting every payoff by a constant never
changes which strategies are optimal, only the value. That structural fact isn't invoked directly
below (the two states are still checked by separate, explicit `cases s` computations, matching
this file's style so far), but it is the real reason a single strategy pair keeps working, at both
rounds computed so far.
-/

/-- The deterministic next state reached by a joint action, independent of the state played in --
    exactly `idsK`'s own case split, pulled out as a plain function so an arbitrary continuation
    can be evaluated at it directly. Mirrors `RockPaperScissors.lean`'s `outcome`. -/
def idsNext : PolicyAction → AttackAction → IDSState
  | .defend1, .attack1 => .healthy
  | .defend1, .attack2 => .compromised
  | .defend2, .attack1 => .compromised
  | .defend2, .attack2 => .healthy

/-- The expected continuation value after any joint action, for *any* continuation `v`: since
    `idsK` is deterministic and state-independent, this is just `v` evaluated at `idsNext a1 a2`,
    regardless of `s`. Generalises `idsCSG_stageGame_A` (that theorem's `hexpect` step, specialised
    to `v = fun _ => 0`) to an arbitrary continuation, which the two-rounds-remaining stage game
    (continuation `idsV1`, not the zero function) actually needs. -/
theorem idsCSG_expect (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction) (v : IDSState → ℝ) :
    idsCSG.expect s a1 a2 v = v (idsNext a1 a2) := by
  change ∑ s' : IDSState, (idsK s a1 a2 s').toReal * v s' = v (idsNext a1 a2)
  cases a1 <;> cases a2 <;> simp [idsK, idsNext, PMF.pure_apply, apply_ite ENNReal.toReal]

/-- The stage-game payoff matrix against an arbitrary continuation `v`, generalising
    `idsCSG_stageGame_A` (which only covers `v = fun _ => 0`). -/
theorem idsCSG_stageGame_A' (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction)
    (v : IDSState → ℝ) :
    (idsCSG.stageGame s v).A a1 a2 = idsR s a1 a2 + v (idsNext a1 a2) := by
  have hexpect : idsCSG.expect s a1 a2 v = v (idsNext a1 a2) := idsCSG_expect s a1 a2 v
  change idsCSG.r s a1 a2 + idsCSG.expect s a1 a2 v = idsR s a1 a2 + v (idsNext a1 a2)
  rw [hexpect]
  rfl

/-- The two-rounds-remaining value at each state: `25/21` at `healthy`, `46/21` at `compromised`.
    Matches the real PRISM-games result for round `2` exactly (`1.1904761904762453`); see this
    section's docstring. -/
noncomputable def idsV2 : IDSState → ℝ
  | .healthy => 25 / 21
  | .compromised => 46 / 21

/-- The defender's mixed strategy for the two-rounds-remaining stage game: `defend1` with
    probability `3/7`, `defend2` with probability `4/7` -- a different pair from `idsP`, but again
    shared by both states (see this section's docstring). -/
noncomputable def idsP2 : PolicyAction → ℝ
  | .defend1 => 3 / 7
  | .defend2 => 4 / 7

theorem idsP2_mem : idsP2 ∈ stdSimplex ℝ PolicyAction :=
  ⟨fun a => by cases a <;> norm_num [idsP2], by simp only [policyAction_sum, idsP2]; norm_num⟩

/-- Symmetric counterpart of `idsP2` for the attacker: `attack1` with probability `4/7`, `attack2`
    with probability `3/7`. -/
noncomputable def idsQ2 : AttackAction → ℝ
  | .attack1 => 4 / 7
  | .attack2 => 3 / 7

theorem idsQ2_mem : idsQ2 ∈ stdSimplex ℝ AttackAction :=
  ⟨fun a => by cases a <;> norm_num [idsQ2], by simp only [attackAction_sum, idsQ2]; norm_num⟩

/-- Against `idsQ2`, every row strategy pays exactly `idsV2 s`, for the two-rounds-remaining stage
    game (continuation `idsV1`). Same technique as `idsCSG_payoff_row`, via `idsCSG_stageGame_A'`
    in place of `idsCSG_stageGame_A`. -/
theorem idsCSG_payoff_row_two (s : IDSState) {p' : PolicyAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ PolicyAction) :
    (idsCSG.stageGame s idsV1).payoff p' idsQ2 = idsV2 s := by
  have hinner : ∀ a1, ∑ a2, (idsCSG.stageGame s idsV1).A a1 a2 * idsQ2 a2 = idsV2 s := by
    intro a1
    rw [attackAction_sum]
    cases s <;> cases a1 <;>
      simp [idsCSG_stageGame_A', idsR, idsNext, idsQ2, idsV1, idsV2] <;> norm_num
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2, (idsCSG.stageGame s idsV1).A a1 a2 * idsQ2 a2
      = ∑ a1, p' a1 * idsV2 s := Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * idsV2 s := by rw [← Finset.sum_mul]
    _ = idsV2 s := by rw [hp'.2, one_mul]

/-- Symmetric counterpart of `idsCSG_payoff_row_two` for the column player. -/
theorem idsCSG_payoff_col_two (s : IDSState) {q' : AttackAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ AttackAction) :
    (idsCSG.stageGame s idsV1).payoff idsP2 q' = idsV2 s := by
  have hinner : ∀ a2, ∑ a1, idsP2 a1 * (idsCSG.stageGame s idsV1).A a1 a2 = idsV2 s := by
    intro a2
    rw [policyAction_sum]
    cases s <;> cases a2 <;>
      simp [idsCSG_stageGame_A', idsR, idsNext, idsP2, idsV1, idsV2] <;> norm_num
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, idsP2 a1 * (idsCSG.stageGame s idsV1).A a1 a2) * q' a2
      = ∑ a2, idsV2 s * q' a2 := Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = idsV2 s * ∑ a2, q' a2 := by rw [← Finset.mul_sum]
    _ = idsV2 s := by rw [hq'.2, mul_one]

/-- **The payoff.** The two-rounds-remaining stage-game value at either state, matching `idsV2`. -/
theorem idsCSG_stageValue_two (s : IDSState) : idsCSG.stageValue s idsV1 = idsV2 s := by
  have huu : (idsCSG.stageGame s idsV1).payoff idsP2 idsQ2 = idsV2 s :=
    idsCSG_payoff_row_two s idsP2_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ PolicyAction,
      (idsCSG.stageGame s idsV1).payoff idsP2 idsQ2 ≤
        (idsCSG.stageGame s idsV1).payoff p' idsQ2 := fun p' hp' =>
    le_of_eq (huu.trans (idsCSG_payoff_row_two s hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ AttackAction,
      (idsCSG.stageGame s idsV1).payoff idsP2 q' ≤
        (idsCSG.stageGame s idsV1).payoff idsP2 idsQ2 := fun q' hq' =>
    le_of_eq ((idsCSG_payoff_col_two s hq').trans huu.symm)
  have hval := (idsCSG.stageGame s idsV1).value_unique idsP2_mem idsQ2_mem hrow hcol
  change (idsCSG.stageGame s idsV1).value = idsV2 s
  rw [← hval]
  exact huu

/-- **The headline result.** Two rounds remaining: `bwInd`'s recursive step applied to `idsV1`
    (itself the one-round-remaining `bwInd` value, not the raw terminal reward) -- the first place
    in this project `bwInd`'s recursion is actually exercised, rather than applied once to a
    literal constant. -/
theorem idsCSG_bwInd_two (s : IDSState) : idsCSG.bwInd (fun _ => 0) 2 s = idsV2 s := by
  rw [CSG.bwInd_succ]
  rw [show idsCSG.bwInd (fun _ => 0) 1 = idsV1 from funext idsCSG_bwInd_one]
  exact idsCSG_stageValue_two s

/-- Numeric form at `healthy`, matching the real PRISM-games result for round `2`
    (`1.1904761904762453`) exactly. -/
theorem idsCSG_bwInd_two_healthy : idsCSG.bwInd (fun _ => 0) 2 .healthy = 25 / 21 :=
  idsCSG_bwInd_two .healthy

/-- Numeric form at `compromised`. -/
theorem idsCSG_bwInd_two_compromised : idsCSG.bwInd (fun _ => 0) 2 .compromised = 46 / 21 :=
  idsCSG_bwInd_two .compromised

/-!
## Two `∀ n` facts, beyond the two hand-checked rounds above

Both worked instances above stop at a fixed `n` (`1` or `2`), checked by hand and cross-referenced
against a real PRISM-games run. Two genuinely general facts, quantified over every round, follow
from what is already in this file plus already-existing general lemmas -- neither needs a new
worked instance or new numbers, only noticing what the existing pieces already give for free.
-/

/-- The two states' stage-game payoff matrices differ by exactly the constant `1`, at *every*
    joint action and against *any* continuation `v` -- not just the zero continuation or `idsV1`.
    Immediate from `idsCSG_stageGame_A'` plus the reward table's own structure (`idsR`'s
    `compromised` row is its `healthy` row plus `1`, pointwise): the expected-continuation term is
    identical between the two states for the same `v`, since `idsK` is state-independent, so only
    the reward term's `+ 1` survives. -/
theorem idsCSG_stageGame_compromised_eq_healthy_add_one (v : IDSState → ℝ) (a1 : PolicyAction)
    (a2 : AttackAction) :
    (idsCSG.stageGame .compromised v).A a1 a2 = (idsCSG.stageGame .healthy v).A a1 a2 + 1 := by
  rw [idsCSG_stageGame_A', idsCSG_stageGame_A']
  cases a1 <;> cases a2 <;> simp [idsR] <;> ring

/-- **The general fact.** `compromised`'s stage value is always exactly `healthy`'s plus `1`, for
    *any* continuation `v` -- `MatrixGameMonotone.lean`'s `value_add_const` (shifting every payoff
    entry of a matrix game by a constant shifts the value by that same constant) applied to the
    fact above. This is the real, structural reason the same mixed-strategy pair solved *both*
    states' stage games at both `k = 1` and `k = 2` above: it was never a coincidence specific to
    either round, it holds automatically at every stage of `bwInd`'s recursion, with no induction
    on the round count needed to see it. -/
theorem idsCSG_stageValue_compromised_eq_healthy_add_one (v : IDSState → ℝ) :
    idsCSG.stageValue .compromised v = idsCSG.stageValue .healthy v + 1 :=
  MatrixGame.value_add_const 1 (idsCSG_stageGame_compromised_eq_healthy_add_one v)

/-- **For all `n ≥ 1`.** Unfolding `bwInd`'s recursive step once turns the fact above into a
    statement about `bwInd` itself: `compromised`'s `n`-round value is always exactly `healthy`'s
    plus `1`, at *every* round from one onward, not just the two rounds hand-checked above. This
    genuinely needs `n ≥ 1` (equivalently, is stated here as `n + 1`): at `n = 0`, `bwInd`'s base
    case is the literal terminal reward `fun _ => 0` for both states alike, so the gap is exactly
    `0`, not `1` -- the asymmetry only enters once the reward table is actually consulted, at the
    first stage-game evaluation. -/
theorem idsCSG_bwInd_compromised_eq_healthy_add_one (n : ℕ) :
    idsCSG.bwInd (fun _ => 0) (n + 1) .compromised =
      idsCSG.bwInd (fun _ => 0) (n + 1) .healthy + 1 := by
  rw [CSG.bwInd_succ, CSG.bwInd_succ]
  exact idsCSG_stageValue_compromised_eq_healthy_add_one _

/-- **`bwInd`'s sequence is nondecreasing in the round count, at every state.** Reward accumulates
    without discounting here, and every entry of `idsR` is nonnegative, so one more round of play
    never lowers the value -- a genuine induction on `n`, unlike the fact above, leaning on
    `CsgMonotone.lean`'s `stageValue_mono`. Notably, `stageValue_mono` needs no `hr : C.r ≡ 0`
    hypothesis -- monotonicity in the continuation never depended on the reward-free assumption
    every previous worked instance in this project happened to satisfy, only boundedness did. -/
theorem idsCSG_bwInd_mono (n : ℕ) (s : IDSState) :
    idsCSG.bwInd (fun _ => 0) n s ≤ idsCSG.bwInd (fun _ => 0) (n + 1) s := by
  induction n generalizing s with
  | zero =>
      have h0 : idsCSG.bwInd (fun _ => 0) 0 s = 0 := rfl
      rw [h0, idsCSG_bwInd_one s]
      cases s <;> norm_num [idsV1]
  | succ n ih =>
      rw [CSG.bwInd_succ, CSG.bwInd_succ]
      exact idsCSG.stageValue_mono ih

end Csg
