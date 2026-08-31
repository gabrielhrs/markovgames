/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.SafetyCertificate
import Csg.RockPaperScissorsLfp

/-!
# Worked example: a genuine safety property for rock-paper-scissors

**Status: drafted, not yet run through `lake build`.** The first concrete instance for
`SafetyOp.lean`/`SafetyCertificate.lean`, which until now had no worked example anywhere in the
project -- only the general operator and certificate combinator, dual to `reachOp`/
`ReachCertificate.lean` via `.gfp`, but never exercised against an actual `CSG`.

**Finding a safety property on rock-paper-scissors at all takes some care.** `win1 ↦ 0`,
`win2 ↦ 1`, `initial ↦ draw ↦ 1/2` (`RockPaperScissorsLfp.lean`'s `rpsVStar`) is already the value
of *reaching* `win2`; the more obvious candidate, `safe := (· ≠ win1)` ("always avoid row
winning"), turns out to have the *same* value on this game, for the same reason
`RockPaperScissorsUntil.lean` already flagged for `!win1 U win2`: `win1` is absorbing, so on this
particular game "never `win1`" and "eventually `win2`" coincide as events (whichever one holds,
the other holds too, almost surely). Building that property would validate `SafetyCertificate.lean`
mechanically but produce nothing numerically new.

**The property here instead**, `rpsSafeUnresolved := (· ∉ {win1, win2})` ("the round has not yet
been decided"), gives a genuinely different answer. Once `win1`/`win2` are *both* absorbing
violations, `initial`'s stage game against a continuation `v` collapses (via the already-general
`rpsCSG_stageValue_initial`, no new stage-game reasoning needed) to `(v win1 + v win2 + v draw)/3`;
since a violation contributes `0` regardless of *which* win state it is, the payoff matrix's
off-diagonal entries are uniformly `0` and only the diagonal (`draw`, worth `v draw`) survives. That
symmetry forces the greatest fixed point to be the constant `0` function: staying forever in
`{initial, draw}` -- i.e. the round never resolving -- turns out to have probability `0` under
optimal adversarial play. Concretely, no strategy can force perpetual limbo against an opponent who
wants a decisive result; decisive resolution is a genuine "safety" guarantee in the *opposite*
direction from what one might first expect (the property that's guaranteed here is `G(¬resolved)`
*failing* almost surely, not holding).

**No new fact about `rpsCSG`'s stage games is needed.** `rpsSafeUnresolved`'s two violating states,
`win1` and `win2`, are both handled by `safetyOpFun`'s own absorption branch directly (`if_neg`,
pinned to `0` regardless of the continuation) -- unlike `RockPaperScissorsLfp.lean`'s `reachOp`,
which needs `rpsCSG_stageValue_win1` because `win1` there is merely a dead end, still playing its
own (trivial) stage game rather than being an operator-level absorbing state.
`rpsCSG_stageValue_draw` and `rpsCSG_stageValue_initial`, both already proved fully generally in
`RockPaperScissors.lean`, are the only two stage-value facts this file reuses.

**The candidate**, `rpsVStarSafety`, is the constant `0` function. `rpsVStarSafety_fixed` (an exact
fixed point) is immediate: `win1`/`win2` close by `rfl` (the concrete, decidable `¬safe` condition
collapses the `ite` to `0` definitionally, the same idiom `RockPaperScissorsLfp.lean`'s `win2` case
used for `reachOp`'s `goal` branch); `draw`/`initial` reduce to `rpsCSG_stageValue_draw`/`_initial`
plus arithmetic, exactly as in the reachability file.

`rpsVStarSafety_upper_bound` (`0` upper-bounds every post-fixed point `b`, i.e. every `b` with
`b ≤ safetyOp safe hr b`) is the real content: `win1`/`win2` are forced to `0` immediately (sand-
wiched between the ambient `[0, 1]`-membership lower bound and the `0` the absorption branch
supplies as an upper bound); `draw`'s inequality gives `b draw ≤ b initial`, and `initial`'s gives
`b initial ≤ (b win1 + b win2 + b draw)/3 = b draw / 3` once `b win1 = b win2 = 0` are substituted
in -- chaining `b draw ≤ b initial ≤ b draw / 3` forces `b draw ≤ 0`, hence (with the ambient lower
bound) `b draw = 0`, and then `b initial = 0` too. The same finite-case-split-plus-`linarith` shape
`RockPaperScissorsLfp.lean` already used for the dual (`lfp`) direction.
-/

namespace Csg

/-- The property "the round has not yet been decided" -- neither player has won yet, so the game
    could still, in principle, continue. An `abbrev`, not a `def`, for the same reason
    `rpsGoalWin2` is (`RockPaperScissors.lean`): `DecidablePred rpsSafeUnresolved`, needed
    implicitly everywhere `safetyOp rpsSafeUnresolved` appears below, only synthesises if the
    predicate unfolds during typeclass search. -/
abbrev rpsSafeUnresolved : RPSState → Prop := fun s => s ≠ .win1 ∧ s ≠ .win2

/-- The guessed greatest-fixed-point candidate: the constant `0` function. Every state is worth
    `0` -- `win1`/`win2` because they are outright violations, `initial`/`draw` because, as
    `rpsVStarSafety_upper_bound` below shows, no strategy can keep the round unresolved forever
    against an adversary. -/
noncomputable def rpsVStarSafety : RPSState → Set.Icc (0 : ℝ) 1 :=
  fun _ => ⟨0, by norm_num, by norm_num⟩

/-- **The payoff, part 1.** `rpsVStarSafety` is an exact fixed point of `safetyOp`: `win1`/`win2`
    close by `rfl` alone (the concrete `¬safe` condition collapses `safetyOpFun`'s `ite` to the
    constant `0` branch definitionally, matching both sides exactly); `initial`/`draw` reduce to
    `RockPaperScissors.lean`'s own stage-value lemmas plus arithmetic. -/
theorem rpsVStarSafety_fixed :
    rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero rpsVStarSafety = rpsVStarSafety := by
  funext s
  apply Subtype.ext
  cases s with
  | win1 => rfl
  | win2 => rfl
  | initial =>
      change rpsCSG.stageValue RPSState.initial (fun s' => (rpsVStarSafety s' : ℝ)) =
        (rpsVStarSafety RPSState.initial : ℝ)
      rw [rpsCSG_stageValue_initial]
      norm_num [rpsVStarSafety]
  | draw =>
      change rpsCSG.stageValue RPSState.draw (fun s' => (rpsVStarSafety s' : ℝ)) =
        (rpsVStarSafety RPSState.draw : ℝ)
      rw [rpsCSG_stageValue_draw]
      simp only [rpsVStarSafety]

/-- **The payoff, part 2.** `rpsVStarSafety` upper-bounds every post-fixed point `b` of
    `safetyOp` -- `win1`/`win2` are forced to exactly `0` first (sandwiched between the ambient
    `[0, 1]`-membership lower bound and the absorption branch's `0` upper bound), then `draw`'s and
    `initial`'s own post-fixed-point inequalities chain via `linarith` to force `b draw = 0` and
    hence `b initial = 0` too. The dual, in shape, of `rpsVStar_le_of_prefixed`'s own case split. -/
theorem rpsVStarSafety_upper_bound {b : RPSState → Set.Icc (0 : ℝ) 1}
    (hb : b ≤ rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero b) : b ≤ rpsVStarSafety := by
  have hwin1_le : (b RPSState.win1 : ℝ) ≤ 0 := hb RPSState.win1
  have hwin2_le : (b RPSState.win2 : ℝ) ≤ 0 := hb RPSState.win2
  have hwin1_eq : (b RPSState.win1 : ℝ) = 0 := le_antisymm hwin1_le (b RPSState.win1).2.1
  have hwin2_eq : (b RPSState.win2 : ℝ) = 0 := le_antisymm hwin2_le (b RPSState.win2).2.1
  have hdraw_le : (b RPSState.draw : ℝ) ≤ (b RPSState.initial : ℝ) := by
    have hle : (b RPSState.draw : ℝ) ≤
        rpsCSG.stageValue RPSState.draw (fun s' => (b s' : ℝ)) := hb RPSState.draw
    rwa [rpsCSG_stageValue_draw] at hle
  have hinit_le : (b RPSState.initial : ℝ) ≤
      ((b RPSState.win1 : ℝ) + (b RPSState.win2 : ℝ) + (b RPSState.draw : ℝ)) / 3 := by
    have hle : (b RPSState.initial : ℝ) ≤
        rpsCSG.stageValue RPSState.initial (fun s' => (b s' : ℝ)) := hb RPSState.initial
    rwa [rpsCSG_stageValue_initial] at hle
  have hdraw_eq : (b RPSState.draw : ℝ) = 0 := by
    have hb_draw_nonneg : (0 : ℝ) ≤ (b RPSState.draw : ℝ) := (b RPSState.draw).2.1
    rw [hwin1_eq, hwin2_eq] at hinit_le
    linarith
  intro s
  cases s with
  | win1 => exact hwin1_eq.le
  | win2 => exact hwin2_eq.le
  | draw =>
      change (b RPSState.draw : ℝ) ≤ (rpsVStarSafety RPSState.draw : ℝ)
      simp only [rpsVStarSafety]
      linarith
  | initial =>
      change (b RPSState.initial : ℝ) ≤ (rpsVStarSafety RPSState.initial : ℝ)
      simp only [rpsVStarSafety]
      linarith

/-- **The headline result.** `rpsVStarSafety` -- the constant `0` function -- *is* the greatest
    fixed point of `safetyOp rpsSafeUnresolved`, on the nose: the two payoff lemmas above fed into
    `SafetyCertificate.lean`'s reusable `CSG.safetyOp_gfp_eq_of_certificate` combinator. The first
    real exercise of that combinator against a concrete instance, not just the fully general
    statement it specialises. -/
theorem rpsCSG_safetyOp_gfp_eq :
    (rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero).gfp = rpsVStarSafety :=
  rpsCSG.safetyOp_gfp_eq_of_certificate rpsSafeUnresolved rpsR_zero rpsVStarSafety
    rpsVStarSafety_fixed fun _ hb => rpsVStarSafety_upper_bound hb

/-- The number the whole exercise was after: no strategy can keep rock-paper-scissors from
    resolving into a decisive round forever, against an adversary -- the safety value of "the round
    stays unresolved" is exactly `0` from `initial`, in stark contrast to `win2`'s reachability
    value of `1/2` (`rpsCSG_reachOp_lfp_initial`, `RockPaperScissorsLfp.lean`). -/
theorem rpsCSG_safetyOp_gfp_initial :
    ((rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero).gfp RPSState.initial : ℝ) = 0 := by
  rw [rpsCSG_safetyOp_gfp_eq]
  simp [rpsVStarSafety]

end Csg
