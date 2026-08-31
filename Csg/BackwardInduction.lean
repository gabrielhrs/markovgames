/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Basic

/-!
# Backward induction for bounded-horizon concurrent stochastic games

**Status: done, confirmed by a clean `lake build`, zero `sorry`s (one caught-and-fixed regression
along the way, from a mistaken self-review edit to the recursive call in `bwInd` -- see
`PHASE0-NOTES.md`).** Builds on the now-confirmed `Csg.Basic`
(`CSG`, `CSG.stageGame`, `CSG.stageValue`, `MatrixGame.value`) without touching that file, same
pattern as `Basic.lean` → `Csg/Basic.lean`.

This is the actual point of the CSG scoping worked out in the heavy debrief (`PHASE0-NOTES.md`):
bounded rPATL objectives (everything except `until`/reachability) reduce to a backward-induction
recursion, mirroring this project's own `MDP-Algorithms/Backward_Induction.thy`

```
function bw_ind_aux where
  "bw_ind_aux n s = (
    if n = N then r_fin s else if n > N then 0 else
      \<Squnion>a \<in> A s. (r (s,a) +
        measure_pmf.expectation (K (s,a)) (\<lambda>s'. bw_ind_aux (Suc n) s')))"
```

with the per-stage `\<Squnion>a \<in> A s` (an MDP's single-player supremum,
`DiscountedMDP.bellman`'s `Finset.sup'` in this project's own Phase 1/2 port) replaced by
`CSG.stageValue`, the two-player zero-sum matrix game's value. Per the debrief, this swap is
licensed because the whole
`Backward_Induction.thy` correctness pipeline only ever uses two facts about the per-stage
aggregation step: that it exists, and that it's monotone in the continuation -- both of which
`MatrixGame.value` has too (existence unconditionally, from `Sion.exists_isSaddlePointOn`; this
file doesn't yet need or prove monotonicity, since `bwInd` below doesn't compare two different
reward functions against each other).

One simplification relative to the Isabelle source, in the same spirit as `ValueIteration.lean`
sidestepping Isabelle's well-founded-recursion termination proof: `bwInd` is parametrised by steps
*remaining* rather than an absolute index into a fixed horizon `N`, so there is no `n = N`/`n > N`
case split to carry around -- plain structural recursion on `ℕ` (`0` steps remaining ⇒ the terminal
reward; `n + 1` ⇒ play the stage game against the `n`-steps-remaining value) says the same thing
more directly, reindexed.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- Backward induction on a concurrent stochastic game: `bwInd rFin n s` is the value of state `s`
    with `n` steps remaining before the terminal reward `rFin` is taken. `0` steps remaining takes
    `rFin` directly; `n + 1` steps remaining plays the stage game (`CSG.stageGame`, hence
    `MatrixGame.value`) against the `n`-steps-remaining value as continuation. Always defined, for
    every `n` and every `rFin`: `MatrixGame.value` needs no side condition on the payoff matrix
    beyond the finiteness/nonemptiness already assumed of `A1`/`A2` throughout. -/
noncomputable def bwInd (rFin : S → ℝ) : ℕ → S → ℝ
  | 0 => rFin
  | n + 1 => fun s => C.stageValue s (bwInd rFin n)

@[simp] theorem bwInd_zero (rFin : S → ℝ) : C.bwInd rFin 0 = rFin := rfl

theorem bwInd_succ (rFin : S → ℝ) (n : ℕ) (s : S) :
    C.bwInd rFin (n + 1) s = C.stageValue s (C.bwInd rFin n) := rfl

/-- **The payoff.** Backward induction actually computes the stage game's value, not just a
    recursion that happens to type-check: with `n + 1` steps remaining, the row player cannot
    lower the value below `bwInd rFin (n + 1) s` by unilaterally deviating from the stage game's
    optimal row strategy while the column player holds its optimal strategy fixed. A direct
    instantiation of `MatrixGame.value_row_optimal` at `C.stageGame s (C.bwInd rFin n)`. -/
theorem bwInd_succ_row_optimal (rFin : S → ℝ) (n : ℕ) (s : S) :
    ∀ p' ∈ stdSimplex ℝ A1,
      C.bwInd rFin (n + 1) s ≤ (C.stageGame s (C.bwInd rFin n)).payoff p'
        (C.stageGame s (C.bwInd rFin n)).optimalCol := by
  simp only [bwInd, stageValue]
  exact (C.stageGame s (C.bwInd rFin n)).value_row_optimal

/-- Symmetric counterpart of `bwInd_succ_row_optimal`: the column player cannot raise the value
    above `bwInd rFin (n + 1) s` by unilaterally deviating from the stage game's optimal column
    strategy while the row player holds its optimal strategy fixed. -/
theorem bwInd_succ_col_optimal (rFin : S → ℝ) (n : ℕ) (s : S) :
    ∀ q' ∈ stdSimplex ℝ A2,
      (C.stageGame s (C.bwInd rFin n)).payoff
        (C.stageGame s (C.bwInd rFin n)).optimalRow q' ≤ C.bwInd rFin (n + 1) s := by
  simp only [bwInd, stageValue]
  exact (C.stageGame s (C.bwInd rFin n)).value_col_optimal

end CSG
end Csg
