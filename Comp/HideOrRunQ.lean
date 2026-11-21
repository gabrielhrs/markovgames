/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Objective
import Comp.Qualitative
import Comp.QualBridge

/-!
# Hide-or-run, computed: a value-1 state that cannot be won almost surely

**Status: confirmed by a clean `lake build`.**

The acceptance test for the limit-sure line, on the game that makes limit-sure the *necessary*
notion: de Alfaro-Henzinger-Kupferman's hide-or-run. Three states, two actions each, and
`LF {goal} = {live, goal}` computed through all three nested fixed points and identified exactly
with the real-valued operator.

**The game.** At `live` the runner (`a1`, `true` = run) wants to reach `goal`; the hider (`a2`,
`true` = throw) has one snowball.

* run into a throw: `dead`;
* run into a wait: `goal`;
* wait out a throw: `goal` -- the snowball is spent;
* wait against a wait: back to `live`.

Run too early and you die; wait forever and you never arrive. The runner's optimal play is to
randomise, running with small probability each round, which reaches `goal` with probability
arbitrarily close to -- but never equal to -- one. So `live` is a value-1 state that *no* strategy
wins almost surely. `AF {goal}` is `{goal}` alone; `LF {goal}` is `{live, goal}`, and `LF` is the
operator that gets the answer right.

Both sides are proved below: `hr_LF` gives `LF {goal} = {live, goal}`, `hr_AF` gives
`AF {goal} = {goal}`, and `hr_live_limit_sure_not_almost_sure` is the separation itself. The
contrast is the whole reason this file exists.

**The descent is exhibited a step at a time**, through `Comp/QualBridge.lean`'s counted lemmas:
each middle chain is run for a stated number of steps and seen to stop, and each outer step is its
own theorem. That route asks for the innermost fixed point `LW` at every region the middle chain
visits, and the game is small enough to settle it for all of them at once: `lw_fixed` checks, by
`decide`, that two steps from `∅` reach a fixed point for **every** pair of regions and every
state -- eight times eight times three instances. With that in hand `hr_LW` is a general lemma and
`Qual.mid supp 2` is a computable `Finset HR → Finset HR` that `Function.iterate` drives.

That check is `2 ^ |S| · 2 ^ |S| · |S|` instances, three states here. `Qual.lfRegion` computes the
same region with no such hypothesis, since `Comp/FixLoop.lean` proves the innermost loop stops;
`Comp/HideOrRunDataQ.lean` runs this game both ways.

**Where the arithmetic stops.** As in `Comp/SafetyChainQ.lean`, `supportF_eq_supp` is the last
rational statement in the file: it identifies the kernel's supports with the table `supp`, and
`supp_spec` passes that on as the one hypothesis `Comp/QualBridge.lean` needs. Everything after it
is `Comp/QualOps.lean`'s operators applied to `supp` -- finite set computation, which is why every
check below is a one-word `decide`. Here the kernel is deterministic, so the quarantine costs even
less than it did there: a single `dirac` lemma does it.

-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

open Csg

namespace HideOrRun

/-! ## The state space -/

/-- Three states: the stand-off, the goal, and death. -/
inductive HR
  | live
  | goal
  | dead
  deriving DecidableEq, Inhabited, Repr

/-- Hand-written, as `Csg/RockPaperScissors.lean` does it: `deriving Fintype` is unavailable in
    this toolchain. -/
instance : Fintype HR where
  elems := {HR.live, HR.goal, HR.dead}
  complete := by intro x; cases x <;> decide

/-! ## A deterministic kernel, and its one support lemma -/

/-- A point mass at `t`. The kernel is deterministic, so this is the only row shape needed. -/
def dirac (t : HR) : HR → ℚ := fun s' => if s' = t then 1 else 0

theorem dirac_nonneg (t s' : HR) : 0 ≤ dirac t s' := by
  unfold dirac
  split_ifs <;> norm_num

theorem sum_dirac (t : HR) : ∑ s' : HR, dirac t s' = 1 := by
  unfold dirac
  simp

theorem dirac_ne_zero_iff (t s' : HR) : dirac t s' ≠ 0 ↔ s' = t := by
  unfold dirac
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The transition kernel. `a1 = true` is *run*, `a2 = true` is *throw*. -/
def kernel : HR → Bool → Bool → (HR → ℚ)
  | .live, true, true => dirac .dead
  | .live, true, false => dirac .goal
  | .live, false, true => dirac .goal
  | .live, false, false => dirac .live
  | .goal, _, _ => dirac .goal
  | .dead, _, _ => dirac .dead

/-- The game. Rewards are unused by the qualitative operators. -/
def game : CsgQ HR Bool Bool where
  K := kernel
  r := fun _ _ _ => 0

theorem kernel_dirac (s : HR) (a1 a2 : Bool) : ∃ t, game.K s a1 a2 = dirac t := by
  cases s <;> cases a1 <;> cases a2 <;> exact ⟨_, rfl⟩

theorem game_wf : game.WellFormed := by
  refine ⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩
  · obtain ⟨t, ht⟩ := kernel_dirac s a1 a2
    rw [ht]
    exact dirac_nonneg t s'
  · obtain ⟨t, ht⟩ := kernel_dirac s a1 a2
    rw [ht]
    exact sum_dirac t

/-- The support table. -/
def supp : HR → Bool → Bool → Finset HR
  | .live, true, true => {.dead}
  | .live, true, false => {.goal}
  | .live, false, true => {.goal}
  | .live, false, false => {.live}
  | .goal, _, _ => {.goal}
  | .dead, _, _ => {.dead}

/-- **The quarantine.** Past this lemma there is no `ℚ` in the file. -/
theorem supportF_eq_supp (s : HR) (a1 a2 : Bool) : game.supportF s a1 a2 = supp s a1 a2 := by
  have key : ∀ t : HR, game.K s a1 a2 = dirac t → game.supportF s a1 a2 = {t} := by
    intro t ht
    ext s'
    simp only [CsgQ.mem_supportF, ht, dirac_ne_zero_iff, Finset.mem_singleton]
  cases s <;> cases a1 <;> cases a2 <;> exact key _ rfl

/-- **The table is the support of the game's kernel**, which is the one hypothesis
    `Comp/QualBridge.lean` asks for. -/
theorem supp_spec (s : HR) (a1 a2 : Bool) :
    ((game.toCSG game_wf).K s a1 a2).support = (↑(supp s a1 a2) : Set HR) := by
  rw [CsgQ.toCSG_support, supportF_eq_supp]

/-! ## The innermost fixed point, for every region at once -/

/-- Two steps of the innermost climb reach a fixed point, for every pair of regions and every
    state: eight times eight times three instances, checked outright. `Finset Bool` has height two,
    so two steps is all a monotone climb can take, but nothing below relies on that argument. -/
theorem lw_fixed : ∀ (x y : Finset HR) (s : HR),
    Qual.lStep supp x y s ((Qual.lStep supp x y s)^[2] ∅) = (Qual.lStep supp x y s)^[2] ∅ := by
  decide

/-- `LW`, for every pair of regions and state at once. -/
theorem hr_LW (x y : Finset HR) (s : HR) :
    (game.toCSG game_wf).LW ↑x ↑y s = (↑((Qual.lStep supp x y s)^[2] ∅) : Set Bool) :=
  Qual.LW_eq_coe_iter (game.toCSG game_wf) supp supp_spec 2 x y s (lw_fixed x y s)

/-! ## Running it -/

/-- Reaching the goal. -/
def target : Finset HR := {HR.goal}

/-- The answer: the goal, and the stand-off state. -/
def winning : Finset HR := {HR.live, HR.goal}

#eval decide game.WellFormed
-- expect: true

#eval Qual.mid supp 2 target Finset.univ ∅
-- expect: {goal}

#eval (Qual.mid supp 2 target Finset.univ)^[2] ∅
-- expect: {live, goal}

#eval (Qual.mid supp 2 target winning)^[2] ∅
-- expect: {live, goal}      the outer chain has already stabilised

#eval (Qual.lStep supp winning winning HR.live)^[2] ∅
-- expect: {true, false}     at `live` both actions are eventually witnesses

#eval (Qual.lStep supp winning winning HR.dead)^[2] ∅
-- expect: ∅                 nothing escapes from `dead`

/-! ## The value-1 set -/

/-- The first outer step: the `μX` fixed point at `Finset.univ`. -/
theorem inner_at_univ :
    ((game.toCSG game_wf).LFInner ↑target ↑(Finset.univ : Finset HR)).lfp =
      (↑winning : Set HR) :=
  Qual.lfInner_eq_coe_of_mid_fixed (game.toCSG game_wf) supp supp_spec 2 target Finset.univ
    winning 2 (fun x s => lw_fixed x Finset.univ s) (by decide) (by decide)

/-- …which makes `winning` an upper bound on `LF target`. -/
theorem LF_le_winning : (game.toCSG game_wf).LF ↑target ≤ (↑winning : Set HR) :=
  Qual.LF_le_of_step (game.toCSG game_wf) target Finset.univ winning inner_at_univ
    (Qual.LF_le_univ _ target)

/-- And the outer chain has stopped: `winning` is its own `μX` fixed point. -/
theorem inner_at_winning :
    ((game.toCSG game_wf).LFInner ↑target ↑winning).lfp = (↑winning : Set HR) :=
  Qual.lfInner_eq_coe_of_mid_fixed (game.toCSG game_wf) supp supp_spec 2 target winning
    winning 2 (fun x s => lw_fixed x winning s) (by decide) (by decide)

/-- **The value-1 set of hide-or-run.** `live` can reach `goal` with probability arbitrarily close
    to one, and `LF` says so -- through three nested fixed points, none of them given an iteration
    bound, all of them run and checked. -/
theorem hr_LF : (game.toCSG game_wf).LF ↑target = (↑winning : Set HR) :=
  Qual.LF_eq_coe_of_fixed (game.toCSG game_wf) target winning inner_at_winning LF_le_winning

/-! ## The almost-sure contrast

Everything above computed `LF`. The same machinery with `Apre1` in place of `Lpre1` computes `AF`,
and the two disagree -- which is the separation this game exists to exhibit. It is also cheaper:
`Apre1` has no inner fixed point, so there is no witness family, `Qual.afStep supp` is a function
of `x` alone, and the chain carries no per-step hypothesis. -/

#eval (Qual.afStep supp target Finset.univ)^[2] ∅
-- expect: {live, goal}     the same as the limit-sure chain at `univ`

#eval (Qual.afStep supp target winning)^[1] ∅
-- expect: {goal}           and here the two part company

/-- The first outer step, which agrees with the limit-sure one. -/
theorem afInner_at_univ :
    ((game.toCSG game_wf).AFInner ↑target ↑(Finset.univ : Finset HR)).lfp =
      (↑winning : Set HR) :=
  Qual.afInner_eq_coe_of_fixed (game.toCSG game_wf) supp supp_spec target Finset.univ winning 2
    (by decide) (by decide)

theorem AF_le_winning : (game.toCSG game_wf).AF ↑target ≤ (↑winning : Set HR) :=
  Qual.AF_le_of_step (game.toCSG game_wf) target Finset.univ winning afInner_at_univ
    (Qual.AF_le_univ _ target)

/-- The second outer step, where almost-sure mode loses `live`. Restricted to the row actions that
    are safe for `winning`, the runner can only *wait* -- running risks `dead`, which lies outside
    `winning` -- and waiting against a wait returns to `live`. So the middle chain never grows past
    the goal itself. -/
theorem afInner_at_winning :
    ((game.toCSG game_wf).AFInner ↑target ↑winning).lfp = (↑target : Set HR) :=
  Qual.afInner_eq_coe_of_fixed (game.toCSG game_wf) supp supp_spec target winning target 1
    (by decide) (by decide)

theorem AF_le_target : (game.toCSG game_wf).AF ↑target ≤ (↑target : Set HR) :=
  Qual.AF_le_of_step (game.toCSG game_wf) target winning target afInner_at_winning AF_le_winning

/-- And the outer chain has stopped. -/
theorem afInner_at_target :
    ((game.toCSG game_wf).AFInner ↑target ↑target).lfp = (↑target : Set HR) :=
  Qual.afInner_eq_coe_of_fixed (game.toCSG game_wf) supp supp_spec target target target 1
    (by decide) (by decide)

/-- **Almost-sure reachability gets a strictly smaller answer**: the goal alone. -/
theorem hr_AF : (game.toCSG game_wf).AF ↑target = (↑target : Set HR) :=
  Qual.AF_eq_coe_of_fixed (game.toCSG game_wf) target target afInner_at_target AF_le_target

/-- **The separation, as a theorem.** `live` is a value-1 state for reaching `goal` from which no
    strategy wins almost surely -- the gap that makes `LF`, and not `AF`, the operator a
    probabilistic reachability precomputation has to use. -/
theorem hr_live_limit_sure_not_almost_sure :
    HR.live ∈ (game.toCSG game_wf).LF ↑target ∧
      HR.live ∉ (game.toCSG game_wf).AF ↑target := by
  refine ⟨?_, ?_⟩
  · rw [hr_LF]
    simp [winning]
  · rw [hr_AF]
    simp [target]

/-! ## The same two results, as answers to objectives

`Comp/Objective.lean` separates the question from the model. These are the two theorems above
restated through that interface: one model, two objectives, two answers. -/

theorem hr_answers_LF :
    game.Answers game_wf (Objective.limitReach target) (Answer.region winning) :=
  .limitReach hr_LF

theorem hr_answers_AF :
    game.Answers game_wf (Objective.almostReach target) (Answer.region target) :=
  .almostReach hr_AF

end HideOrRun

end Comp
