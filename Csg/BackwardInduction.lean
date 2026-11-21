/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Basic

/-!
# Backward induction for bounded-horizon concurrent stochastic games

**Status: confirmed by a clean `lake build`.** Builds on `Csg/Basic.lean` (`CSG`,
`CSG.stageGame`, `CSG.stageValue`, `MatrixGame.value`).

Bounded rPATL objectives (everything except `until`/reachability) reduce to a backward-induction
recursion, mirroring `MDP-Algorithms/Backward_Induction.thy`

```
function bw_ind_aux where
  "bw_ind_aux n s = (
    if n = N then r_fin s else if n > N then 0 else
      \<Squnion>a \<in> A s. (r (s,a) +
        measure_pmf.expectation (K (s,a)) (\<lambda>s'. bw_ind_aux (Suc n) s')))"
```

with the per-stage `\<Squnion>a \<in> A s` (an MDP's single-player supremum,
`DiscountedMDP.bellman`'s `Finset.sup'` in `Mdp/`) replaced by `CSG.stageValue`, the two-player
zero-sum matrix game's value. The swap is licensed because the `Backward_Induction.thy`
correctness pipeline only ever uses two facts about the per-stage aggregation step: that it
exists, and that it is monotone in the continuation -- both of which `MatrixGame.value` has too
(existence unconditionally, from `Sion.exists_isSaddlePointOn`; monotonicity is
`MatrixGame.value_mono`, not needed in this file, since `bwInd` does not compare two reward
functions against each other).

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

end CSG
end Csg
