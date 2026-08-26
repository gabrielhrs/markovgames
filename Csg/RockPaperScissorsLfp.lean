/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.ReachCertificate
import Csg.RockPaperScissors

/-!
# Worked example: the exact least fixed point for rock-paper-scissors

**Status: drafted, not yet run through `lake build`.** Closes out the reachability worked example:
`(rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp` -- the genuine infinite-horizon value, not merely a
`reachBounded` sequence approximating it -- computed exactly, matching `RockPaperScissors.lean`'s
own concrete `reachBounded` values (`0, 1/3, 1/3, 4/9, 4/9, ...`) at their shared limit `1/2`.

**The technique, and which parts of it generalise.** Mathlib's Knaster-Tarski gives two lemmas for
pinning down a least fixed point exactly, without any limiting argument
(`OrderHom.lfp_eq_sSup_iterate`, `ωScottContinuous`, etc.): `OrderHom.lfp_le_fixed`, which says any
*exact* fixed point of `f` is an upper bound on `f.lfp`, and `OrderHom.le_lfp`, which says any
lower bound on every *pre*-fixed point of `f` (`f b ≤ b`) is itself a lower bound on `f.lfp`.
Together, via `le_antisymm`, a *guessed* candidate that is both an exact fixed point and a lower
bound on every pre-fixed point is provably `f.lfp` on the nose. This pinning technique is fully
general -- it applies to `reachOp` for *any* `CSG` and *any* reachability goal, not just this one
-- and that assembly step now lives as its own reusable combinator,
`CSG.reachOp_lfp_eq_of_certificate` in `ReachCertificate.lean`, rather than inlined here.

What is **not** general is the rest of this file: solving for the candidate by hand, and proving
it a lower bound via a finite case split closed by `linarith`. That relies on three properties
special to rock-paper-scissors, none of which a larger or less symmetric game would have: a tiny
four-state space, making the case split tractable at all; `initial`'s stage-game value collapsing
to the *linear* formula `(v win1 + v win2 + v draw) / 3` (`rpsCSG_stageValue_initial`), a
consequence of the uniform strategy being optimal *regardless of the continuation* -- a symmetry
specific to rock-paper-scissors's cyclic payoff structure, not something a general matrix game's
minimax value does (in general it is piecewise-linear and convex-concave in the continuation, not
a single affine formula); and the resulting system of pre-fixed-point inequalities being small and
linear enough to solve and verify directly. A larger or less symmetric `CSG` would need either the
numerical `sSup`-of-iterates route, or an interval-certificate version of this same pinning idea
(bounding `f.lfp` rather than pinning it exactly).

**The candidate**, `rpsVStar`: `win1 ↦ 0` (a dead end for reaching `win2`, worth nothing),
`win2 ↦ 1` (the goal itself), `initial ↦ 1/2`, `draw ↦ 1/2` (matching the fact, already visible in
`RockPaperScissors.lean`'s own `reachBounded` computation, that `draw` costs a genuine extra step
back to `initial` and so shares its limiting value). Two things need proving about it:

1. `rpsVStar_fixed`: it is an exact fixed point of `reachOp`. `win2`'s equation closes by `rfl`
   alone (goal states are pinned to `1` by a purely structural `ite` on a concrete, decidable
   state comparison -- no stage game involved at all); `win1`, `initial`, `draw` first `change`
   the goal past the `OrderHom`/`ite` packaging down to a bare `stageValue` equation (the same
   defeq idiom `ReachOp.lean`'s own fix round established, safer here than `simp`-based `ite`
   unfolding -- see the fix-round note once this file is confirmed), then close with
   `RockPaperScissors.lean`'s own stage-value lemmas plus `norm_num` arithmetic.
2. `rpsVStar_le_of_prefixed`: it lower-bounds every pre-fixed point `b`. Forced facts first --
   `b win2 = 1` (sandwiched between the goal-state lower bound and the `[0, 1]` membership upper
   bound) and `b win1 ≥ 0` (free, from `[0, 1]` membership) -- then the two remaining pre-fixed-
   point inequalities, at `draw` (`b initial ≤ b draw`) and `initial`
   (`(b win1 + b win2 + b draw) / 3 ≤ b initial`), chain together via `linarith` to force
   `b initial ≥ 1/2`, and hence `b draw ≥ 1/2` too.
-/

namespace Csg

/-- `rpsCSG`'s reward is identically zero, exactly the hypothesis `CsgMonotone.lean`/`ReachOp.lean`
    need to keep `stageValue` (and hence `reachOp`) landing back in `[0, 1]`. Immediate from
    `rpsR`'s own definition, same `simp [rpsCSG, rpsR]` idiom `RockPaperScissors.lean` already
    used three times to unfold the same structure projection. -/
theorem rpsR_zero : ∀ s a1 a2, rpsCSG.r s a1 a2 = 0 := by
  intro s a1 a2
  simp [rpsCSG, rpsR]

/-- The guessed least-fixed-point candidate: `win1` (a dead end) worth nothing, `win2` (the goal)
    worth everything, `initial` and `draw` worth `1/2` each -- matching the shared limit of
    `RockPaperScissors.lean`'s own `reachBounded` sequence. Each value is packaged into
    `Set.Icc (0:ℝ) 1` via the same three-way flattened anonymous constructor `ReachOp.lean` used
    (`Mathlib/Topology/UnitInterval.lean`'s own idiom for this type). -/
noncomputable def rpsVStar : RPSState → Set.Icc (0 : ℝ) 1
  | .win1 => ⟨0, by norm_num, by norm_num⟩
  | .win2 => ⟨1, by norm_num, by norm_num⟩
  | .initial => ⟨1 / 2, by norm_num, by norm_num⟩
  | .draw => ⟨1 / 2, by norm_num, by norm_num⟩

/-- **The payoff, part 1.** `rpsVStar` is an exact fixed point of `reachOp`: a per-state case
    split. `win2` closes by `rfl` alone -- no stage game involved, just a purely structural `ite`
    on a concrete state comparison. The other three `change` the goal past the `OrderHom`/`ite`
    packaging directly to a bare `stageValue` equation (a defeq jump the elaborator can make in
    one step, since the condition is a concrete, decidable comparison between two `RPSState`
    constructors) and close with `RockPaperScissors.lean`'s own stage-value lemmas plus
    arithmetic. -/
theorem rpsVStar_fixed :
    rpsCSG.reachOp rpsGoalWin2 rpsR_zero rpsVStar = rpsVStar := by
  funext s
  apply Subtype.ext
  cases s with
  | win1 =>
      change rpsCSG.stageValue RPSState.win1 (fun s' => (rpsVStar s' : ℝ)) =
        (rpsVStar RPSState.win1 : ℝ)
      rw [rpsCSG_stageValue_win1]
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

/-- **The payoff, part 2.** `rpsVStar` lower-bounds every pre-fixed point `b` of `reachOp`, forcing
    `b win2 = 1` and `b win1 ≥ 0` first, then chaining `draw`'s and `initial`'s own pre-fixed-point
    inequalities via `linarith` to pin `b initial ≥ 1/2` (and hence `b draw ≥ 1/2` too). This is
    the one part of the argument that is genuinely rock-paper-scissors-specific, not reusable
    as-is (see the module docstring). -/
theorem rpsVStar_le_of_prefixed {b : RPSState → Set.Icc (0 : ℝ) 1}
    (hb : rpsCSG.reachOp rpsGoalWin2 rpsR_zero b ≤ b) : rpsVStar ≤ b := by
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

/-- **The headline result.** `rpsVStar` *is* the least fixed point, on the nose -- no limiting
    argument, just the two payoff lemmas above fed into `ReachCertificate.lean`'s reusable
    `CSG.reachOp_lfp_eq_of_certificate` combinator (`VERIFICATION-FRAMEWORK.md`'s first concrete
    artifact), rather than an inlined `le_antisymm`. Re-deriving this same confirmed result
    through the generic combinator, rather than the hand-rolled proof the previous round shipped,
    is itself the regression check that the generalisation is real and not cosmetic. -/
theorem rpsCSG_reachOp_lfp_eq :
    (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp = rpsVStar :=
  rpsCSG.reachOp_lfp_eq_of_certificate rpsGoalWin2 rpsR_zero rpsVStar rpsVStar_fixed
    fun _ hb => rpsVStar_le_of_prefixed hb

/-- The number the whole exercise was after: the exact infinite-horizon value of reaching `win2`
    from `initial` under optimal play is `1/2`, matching the FMSD paper's claim and the shared
    limit of `RockPaperScissors.lean`'s own `reachBounded` sequence
    (`0, 1/3, 1/3, 4/9, 4/9, ...`). -/
theorem rpsCSG_reachOp_lfp_initial :
    ((rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) = 1 / 2 := by
  rw [rpsCSG_reachOp_lfp_eq]
  simp [rpsVStar]

end Csg
