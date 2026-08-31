/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.UntilOp
import Csg.RockPaperScissorsLfp

/-!
# Worked example: rock-paper-scissors as a genuine `until` property

**Status: done, confirmed by a clean `lake build` on the first attempt, no fix round needed.**
`RockPaperScissorsLfp.lean` computed
`(rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp`, i.e. `Pmax=? [F win2]` -- plain reachability. But the
property actually discussed against the user's own FMSD paper is a genuine `until`: the maximising
coalition (this project's *column* player, per the convention note in `RockPaperScissors.lean`'s own
docstring -- row-minimises/column-maximises, the opposite of the paper's own convention) wants to
reach its own win state while never letting the other side win first. In this project's naming that
is **`!win1 U win2`** -- avoid `win1` (row winning) until `win2` (column winning) -- not the mirror
image `!win2 U win1` a naive relabelling might suggest, since the maximising role and the "column
wins" state both live on the same (`win2`) side once the convention flip is accounted for.

Unlike `!win2 U win2` (what `RockPaperScissorsLfp.lean` actually encoded, a tautological rewriting
of `F win2` true for *any* predicate: `¬φ U φ ≡ F φ`), `!win1 U win2` is a genuine constraint --
`safe` and `goal` are different predicates, so the "stay safe" clause is not automatically
satisfied. It happens to have the *same value*, `1/2`, as plain `F win2` in this particular game --
`win1` self-loops forever, so reaching `win2` after visiting `win1` is already impossible under
plain reachability, and requiring "never visit `win1` first" costs nothing extra on top of that.
But the two formulas are not the same statement, and this file proves the until-shaped one directly
through `UntilOp.lean`'s genuine three-way operator, rather than resting on the coincidence.

The payoff for doing this properly rather than just asserting the coincidence: `win1`'s value now
falls out of `untilOpFun`'s own dead-end branch (`¬goal ∧ ¬safe`) as a bare `rfl`, the same way
`win2`'s value already did in the reachability version -- no self-loop/fixed-point reasoning needed
for it at all, since the operator itself pins non-goal, non-safe states to `0` regardless of the
continuation. The one thing genuinely reused from `RockPaperScissorsLfp.lean`: the *candidate*,
`rpsVStar`, is identical -- same four numbers, since the two properties agree on this game -- and so
is the harder half of the lower-bound argument (`draw`/`initial`'s pre-fixed-point inequalities),
since neither state's stage-game equation changes between the two properties.

The headline result, `rpsCSG_untilOp_lfp_eq_reachOp_lfp`, is a genuine (if RPS-specific) instance of
the general `reachOp goal hr = untilOp (fun _ => True) goal hr` corollary deferred out of
`UntilOp.lean` -- not that corollary itself (this file's `safe` is `¬win1`, not the trivially `True`
predicate that corollary needs), but concrete evidence that the two operators can agree on a real
worked example, ahead of tackling the fully general statement.
-/

namespace Csg

/-- The safety condition for the genuine `until` reading of this property: never let `win1` (row
    winning) happen. An `abbrev`, not a `def`, for the same reason `rpsGoalWin2` is -- plain `def`s
    aren't unfolded during typeclass search, so `DecidablePred rpsSafeNotWin1` would otherwise fail
    to synthesize even though `RPSState` has decidable equality. -/
abbrev rpsSafeNotWin1 : RPSState → Prop := fun s => s ≠ RPSState.win1

/-- **The payoff, part 1.** `rpsVStar` -- the *same* candidate `RockPaperScissorsLfp.lean` used for
    plain reachability -- is also an exact fixed point of the genuine `until` operator. `win1` and
    `win2` both close by `rfl` alone now: `win1` is neither `goal` nor `safe`, so `untilOpFun` pins
    it to `0` directly (no self-loop reasoning needed, unlike the reachability version); `win2` is
    `goal`, pinned to `1` as before. `initial`/`draw` play the *same* stage game as the reachability
    version (their `safe`/`goal` status routes to the same stage-value branch either way), so their
    proofs carry over unchanged. -/
theorem rpsVStar_fixed_until :
    rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero rpsVStar = rpsVStar := by
  funext s
  apply Subtype.ext
  cases s with
  | win1 => rfl
  | win2 => rfl
  | initial =>
      change rpsCSG.stageValue RPSState.initial (fun s' => (rpsVStar s' : ℝ)) =
        (rpsVStar RPSState.initial : ℝ)
      rw [rpsCSG_stageValue_initial]
      norm_num [rpsVStar]
  | draw =>
      change rpsCSG.stageValue RPSState.draw (fun s' => (rpsVStar s' : ℝ)) =
        (rpsVStar RPSState.draw : ℝ)
      rw [rpsCSG_stageValue_draw]
      simp only [rpsVStar]

/-- **The payoff, part 2.** `rpsVStar` lower-bounds every pre-fixed point of the `until` operator --
    the *same* argument `rpsVStar_le_of_prefixed` used, unaffected by the change of operator: `win2`
    is still forced to `1` (the `goal` branch is identical between the two operators), `win1`'s
    membership lower bound `0` is already all `rpsVStar win1` needs (the `until` operator's own
    dead-end pinning at `win1` gives no *additional* information beyond what `[0, 1]` membership
    already provides), and `draw`/`initial`'s pre-fixed-point inequalities are literally the same
    stage-game facts as before, since neither state's `safe`/`goal` status changes which branch of
    `untilOpFun` they route through relative to `reachOpFun`. -/
theorem rpsVStar_le_of_prefixed_until {b : RPSState → Set.Icc (0 : ℝ) 1}
    (hb : rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero b ≤ b) : rpsVStar ≤ b := by
  have hwin1 : (0 : ℝ) ≤ (b RPSState.win1 : ℝ) := (b RPSState.win1).2.1
  have hwin2 : (b RPSState.win2 : ℝ) = 1 := by
    have hle : (1 : ℝ) ≤ (b RPSState.win2 : ℝ) := hb RPSState.win2
    exact le_antisymm (b RPSState.win2).2.2 hle
  have hdraw_ge : (b RPSState.initial : ℝ) ≤ (b RPSState.draw : ℝ) := by
    have hle : rpsCSG.stageValue RPSState.draw (fun s' => (b s' : ℝ)) ≤
        (b RPSState.draw : ℝ) := hb RPSState.draw
    rwa [rpsCSG_stageValue_draw] at hle
  have hinit_ge : ((b RPSState.win1 : ℝ) + 1 + (b RPSState.draw : ℝ)) / 3 ≤
      (b RPSState.initial : ℝ) := by
    have hle : rpsCSG.stageValue RPSState.initial (fun s' => (b s' : ℝ)) ≤
        (b RPSState.initial : ℝ) := hb RPSState.initial
    rw [rpsCSG_stageValue_initial, hwin2] at hle
    linarith
  have hinit_half : (1 : ℝ) / 2 ≤ (b RPSState.initial : ℝ) := by linarith
  intro s
  cases s with
  | win1 => exact hwin1
  | win2 => exact hwin2.ge
  | initial =>
      change (rpsVStar RPSState.initial : ℝ) ≤ (b RPSState.initial : ℝ)
      simp only [rpsVStar]
      linarith
  | draw =>
      change (rpsVStar RPSState.draw : ℝ) ≤ (b RPSState.draw : ℝ)
      simp only [rpsVStar]
      linarith

/-- **The headline result.** The genuine `until` reading of this property has *exactly* the same
    least fixed point as the plain-reachability reading -- concrete, if RPS-specific, evidence for
    the general `reachOp goal hr = untilOp (fun _ => True) goal hr` corollary deferred out of
    `UntilOp.lean` (not that statement itself, since `rpsSafeNotWin1` isn't the always-`True`
    predicate that corollary needs, but the same underlying phenomenon: a safety clause that turns
    out to cost nothing on this particular game). -/
theorem rpsCSG_untilOp_lfp_eq :
    (rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero).lfp = rpsVStar :=
  OrderHom.lfp_eq_of_certificate (rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero) rpsVStar
    rpsVStar_fixed_until fun _ hb => rpsVStar_le_of_prefixed_until hb

/-- Both readings of the property -- `Pmax=? [F win2]` and `Pmax=? [!win1 U win2]` -- agree on the
    nose, not just at `initial`: the two operators have the *same* least fixed point, `rpsVStar`. -/
theorem rpsCSG_untilOp_lfp_eq_reachOp_lfp :
    (rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero).lfp =
      (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp := by
  rw [rpsCSG_untilOp_lfp_eq, rpsCSG_reachOp_lfp_eq]

/-- The number itself, reconfirmed through the genuine `until` operator: `1/2`, matching
    `rpsCSG_reachOp_lfp_initial`. -/
theorem rpsCSG_untilOp_lfp_initial :
    ((rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) = 1 / 2 := by
  rw [rpsCSG_untilOp_lfp_eq]
  simp [rpsVStar]

end Csg
