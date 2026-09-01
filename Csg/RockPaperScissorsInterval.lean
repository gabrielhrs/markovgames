/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.IntervalCertificate
import Csg.RockPaperScissorsLfp

/-!
# Worked example: a genuine interval, not an exact pin, for rock-paper-scissors

**Status: `lake build` clean throughout; one real fix round caught by the interactive elaborator,
not by batch compilation.** `rpsCSG_reachOp_lfp_mem_Icc`'s certificate application originally
passed `rpsLo_le_of_prefixed` point-free where `CSG.reachOp_lfp_mem_Icc_of_certificate` expects a
`∀ b, ...` -- `rpsLo_le_of_prefixed` has an implicit leading `{b}`, and every other certificate
application in this project (`rpsVStar_le_of_prefixed`, `rpsVStarSafety_upper_bound`) wraps this
in an explicit `fun _ hb => ...` for exactly that reason; this file initially broke that
convention and VS Code caught it as a genuine application type mismatch, not a postponed-
elaboration artifact like `ReachConverge.lean`'s. `rpsCSG_reachOp_lfp_initial_mem_Icc` also had two
`simpa [...] using h` bridging steps replaced with the plain term-mode application `⟨h1, h2⟩` --
per `ReachOp.lean`'s own docstring on this toolchain's duplicate `Subtype.LE` instance, bare
`exact`/defeq sees through the mismatch reliably where `simp`'s own rewriting does not. This is the
first file in the project working with a genuine *inequality*-shaped pre-fixed-point hypothesis,
`f hi ≤ hi`, rather than the equality-shaped `f hi = hi` every prior worked instance used -- the
`change`/`rw` idiom that closed those goals by ending on a bare equation instead ends on an
arithmetic inequality here, closed by `norm_num`/`linarith` rather than falling out for free. The
first concrete instance for `IntervalCertificate.lean`, which until now had no worked example
anywhere in the project -- only the general combinator, dual on both the `lfp` and `gfp` sides but
never exercised against an actual `CSG`.

**Honest framing: this is a smoke test, not the technique's real motivating case.**
`RockPaperScissorsLfp.lean` already pins `(rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp` down
*exactly* -- `win1 ↦ 0`, `win2 ↦ 1`, `initial ↦ draw ↦ 1/2` -- precisely because rock-paper-scissors
is small and symmetric enough to hand-solve. Building an interval certificate here does not
demonstrate a case where the interval technique was *necessary*; it demonstrates that the general
combinator (`CSG.reachOp_lfp_mem_Icc_of_certificate`) actually works, against an instance simple
enough to check by hand that the sandwich is correct. The real payoff `VERIFICATION-FRAMEWORK.md`
flags this technique for -- a `CSG` too large or asymmetric to solve exactly -- is not attempted
here; this file's candidates are deliberately *not* tightened all the way to `1/2`, so the interval
stays genuinely non-degenerate rather than silently smuggling in the exact answer via two copies of
`rpsVStar`.

**The candidates.** `rpsLo`/`rpsHi` agree with `rpsVStar` at the absorbing states (`win1 ↦ 0`,
`win2 ↦ 1` -- both operator-level absorbing, so no candidate has any freedom there) and diverge
symmetrically around `1/2` at `initial`/`draw`: `rpsLo ↦ 1/3`, `rpsHi ↦ 2/3`. `1/3` is not an
arbitrary guess -- it is `RockPaperScissors.lean`'s own `reachBounded` value at `k = 1`, a natural
"one confirmed step of progress" lower bound; `2/3` is its mirror image, chosen for the same reason
rather than tightened toward `1/2` by hand-solving.

**`rpsHi_prefixed`, the interval-specific half.** `rpsHi` is *not* an exact fixed point --
`reachOp rpsHi` at `initial` comes out to `(0 + 1 + 2/3)/3 = 5/9`, strictly less than `rpsHi`'s own
`2/3` there, the gap being exactly the slack this technique trades away in exchange for not having
to solve for it exactly. `draw`'s equation is tight (`reachOp rpsHi draw = rpsHi initial = 2/3 =
rpsHi draw` on the nose), and `win1`/`win2` are tight by construction (both operator-level
absorbing). Checking `f hi ≤ hi` state by state is the same case-split-plus-arithmetic shape every
worked instance in this project has used, just closing on `≤` instead of `=`.

**`rpsLo_le_of_prefixed`.** Unchanged in substance from `RockPaperScissorsLfp.lean`'s own
`rpsVStar_le_of_prefixed` -- `lo`'s lower-bound obligation is exactly the same hypothesis shape the
exact certificate already needed, so this half of the proof is not new content, only re-run against
a looser numeric target (`1/3` in place of `1/2`) that a simpler chain of inequalities reaches
without needing the mutual `draw`/`initial` reinforcement the exact proof's tighter target forced.
-/

namespace Csg

/-- The lower candidate: `1/3` at `initial`/`draw`, matching `RockPaperScissors.lean`'s own
    `reachBounded` value at `k = 1` -- a genuine, checkable "one step of progress" bound, not
    tightened toward the known exact answer `1/2`. -/
noncomputable def rpsLo : RPSState → Set.Icc (0 : ℝ) 1
  | .win1 => ⟨0, by norm_num, by norm_num⟩
  | .win2 => ⟨1, by norm_num, by norm_num⟩
  | .initial => ⟨1 / 3, by norm_num, by norm_num⟩
  | .draw => ⟨1 / 3, by norm_num, by norm_num⟩

/-- The upper candidate: `2/3` at `initial`/`draw`, the mirror image of `rpsLo` around the known
    exact value `1/2`, chosen the same way rather than tightened by hand-solving. -/
noncomputable def rpsHi : RPSState → Set.Icc (0 : ℝ) 1
  | .win1 => ⟨0, by norm_num, by norm_num⟩
  | .win2 => ⟨1, by norm_num, by norm_num⟩
  | .initial => ⟨2 / 3, by norm_num, by norm_num⟩
  | .draw => ⟨2 / 3, by norm_num, by norm_num⟩

/-- **The payoff, lower half.** `rpsLo` lower-bounds every pre-fixed point `b` of `reachOp` --
    `win2` forces `b win2 ≥ 1` directly from the pre-fixed-point hypothesis, `win1` is free from
    `[0, 1]`-membership, and `initial`'s own inequality (using only `b win1 ≥ 0`, `b win2 ≥ 1`,
    `b draw ≥ 0`, all free) already forces `b initial ≥ 1/3`; `draw`'s inequality then chains
    through that to force `b draw ≥ 1/3` too. Substantively the same argument
    `RockPaperScissorsLfp.lean`'s `rpsVStar_le_of_prefixed` makes, re-run against the looser
    target `1/3` rather than `1/2`. -/
theorem rpsLo_le_of_prefixed {b : RPSState → Set.Icc (0 : ℝ) 1}
    (hb : rpsCSG.reachOp rpsGoalWin2 rpsR_zero b ≤ b) : rpsLo ≤ b := by
  have hwin1 : (0 : ℝ) ≤ (b RPSState.win1 : ℝ) := (b RPSState.win1).2.1
  have hwin2 : (1 : ℝ) ≤ (b RPSState.win2 : ℝ) := hb RPSState.win2
  have hdraw_nonneg : (0 : ℝ) ≤ (b RPSState.draw : ℝ) := (b RPSState.draw).2.1
  have hinit_ge : ((b RPSState.win1 : ℝ) + (b RPSState.win2 : ℝ) + (b RPSState.draw : ℝ)) / 3 ≤
      (b RPSState.initial : ℝ) := by
    have hle : rpsCSG.stageValue RPSState.initial (fun s' => (b s' : ℝ)) ≤
        (b RPSState.initial : ℝ) := hb RPSState.initial
    rwa [rpsCSG_stageValue_initial] at hle
  have hinit_third : (1 : ℝ) / 3 ≤ (b RPSState.initial : ℝ) := by linarith
  have hdraw_ge_init : (b RPSState.initial : ℝ) ≤ (b RPSState.draw : ℝ) := by
    have hle : rpsCSG.stageValue RPSState.draw (fun s' => (b s' : ℝ)) ≤
        (b RPSState.draw : ℝ) := hb RPSState.draw
    rwa [rpsCSG_stageValue_draw] at hle
  intro s
  cases s with
  | win1 => exact hwin1
  | win2 => exact hwin2
  | initial =>
      change (rpsLo RPSState.initial : ℝ) ≤ (b RPSState.initial : ℝ)
      simp only [rpsLo]
      linarith
  | draw =>
      change (rpsLo RPSState.draw : ℝ) ≤ (b RPSState.draw : ℝ)
      simp only [rpsLo]
      linarith

/-- **The payoff, upper half, and the interval-specific content.** `rpsHi` is a pre-fixed point of
    `reachOp` -- `win1`/`win2` close by the same `change`/`rw` idiom every worked instance uses,
    landing on a trivial `x ≤ x` rather than `RockPaperScissorsLfp.lean`'s `x = x`; `draw` is tight
    (`reachOp rpsHi draw = rpsHi initial = rpsHi draw` exactly); `initial` is the one genuinely
    slack inequality, `5/9 ≤ 2/3`, checked directly by `norm_num` rather than forced by any
    symmetry argument. -/
theorem rpsHi_prefixed : rpsCSG.reachOp rpsGoalWin2 rpsR_zero rpsHi ≤ rpsHi := by
  intro s
  cases s with
  | win1 =>
      change (rpsCSG.stageValue RPSState.win1 (fun s' => (rpsHi s' : ℝ)) : ℝ) ≤
        (rpsHi RPSState.win1 : ℝ)
      rw [rpsCSG_stageValue_win1]
  | win2 => exact le_refl _
  | initial =>
      change (rpsCSG.stageValue RPSState.initial (fun s' => (rpsHi s' : ℝ)) : ℝ) ≤
        (rpsHi RPSState.initial : ℝ)
      rw [rpsCSG_stageValue_initial]
      norm_num [rpsHi]
  | draw =>
      change (rpsCSG.stageValue RPSState.draw (fun s' => (rpsHi s' : ℝ)) : ℝ) ≤
        (rpsHi RPSState.draw : ℝ)
      rw [rpsCSG_stageValue_draw]
      norm_num [rpsHi]

/-- **The headline result.** `(rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp` lies in `[1/3, 2/3]` --
    the two payoff lemmas above fed into `IntervalCertificate.lean`'s
    `CSG.reachOp_lfp_mem_Icc_of_certificate`, the first real exercise of that combinator against a
    concrete instance. `RockPaperScissorsLfp.lean`'s own `rpsCSG_reachOp_lfp_eq` already gives the
    exact value `1/2`, comfortably inside this sandwich, confirming the interval technique doesn't
    contradict the exact one -- exactly the cross-check a genuinely new proof route deserves before
    trusting it for a model where no exact answer is available to check against. -/
theorem rpsCSG_reachOp_lfp_mem_Icc :
    rpsLo ≤ (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp ∧
      (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp ≤ rpsHi :=
  rpsCSG.reachOp_lfp_mem_Icc_of_certificate rpsGoalWin2 rpsR_zero rpsLo rpsHi
    (fun _ hb => rpsLo_le_of_prefixed hb) rpsHi_prefixed

/-- The concrete numeric consequence at `initial`: `1/3 ≤ 1/2 ≤ 2/3`, the interval certificate's
    sandwich next to the exact value it brackets. -/
theorem rpsCSG_reachOp_lfp_initial_mem_Icc :
    (1 : ℝ) / 3 ≤ ((rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) ∧
      ((rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) ≤ 2 / 3 :=
  ⟨rpsCSG_reachOp_lfp_mem_Icc.1 RPSState.initial, rpsCSG_reachOp_lfp_mem_Icc.2 RPSState.initial⟩

end Csg
