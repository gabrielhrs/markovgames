/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelData
import Comp.Objective
import Comp.QualitativeAlmostFinset
import Comp.QualitativeLimitReach

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

**One trick makes the nest manageable.** `Comp/QualitativeLimitReach.lean` gives the middle and
outer levels as single-step lemmas, because `LW`'s first argument is the middle chain's own
variable, so the witness family changes at every step. Here the game is small enough to discharge
`LW` *once and for all*: `lw_fixed` checks, by `decide`, that two steps from `∅` reach a fixed point
for **every** pair of regions and every state -- eight times eight times three instances. With that
in hand `hr_LW` is a general lemma, the witness family becomes a function of `x` alone, and
`midStep` is an honest computable `Finset HR → Finset HR` that `Function.iterate` can drive.

That exponential check is affordable at three states and would not be at thirty; the per-step
lemmas remain the route for anything larger. Worth knowing which lever is which.

**Where the arithmetic stops.** As in `Comp/SafetyChainQ.lean`, `supportF_eq_supp` is the last
rational statement in the file. Everything above it -- `aC`, `bC`, `lStepC`, `lwC`, `lpre1C`,
`midStep` -- is finite set computation, which is why every check below is a one-word `decide`.
Here the kernel is deterministic, so the quarantine costs even less than it did there: a single
`dirac` lemma does it.

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

/-! ## `A`, `B` and `LW`, combinatorially -/

/-- `aF` with the support table substituted. -/
def aC (v2 : Finset Bool) (y : Finset HR) (s : HR) : Finset Bool :=
  Finset.univ.filter fun a1 => ∀ a2, a2 ∈ v2 ∨ supp s a1 a2 ⊆ y

theorem aF_eq_aC (v2 : Finset Bool) (y : Finset HR) (s : HR) : game.aF v2 y s = aC v2 y s := by
  ext a1
  simp only [CsgQ.mem_aF, aC, Finset.mem_filter, Finset.mem_univ, true_and, supportF_eq_supp]

/-- `bF` with the support table substituted. -/
def bC (v1 : Finset Bool) (x : Finset HR) (s : HR) : Finset Bool :=
  Finset.univ.filter fun a2 => ∃ a1 ∈ v1, (supp s a1 a2 ∩ x).Nonempty

theorem bF_eq_bC (v1 : Finset Bool) (x : Finset HR) (s : HR) : game.bF v1 x s = bC v1 x s := by
  ext a2
  simp only [CsgQ.mem_bF, bC, Finset.mem_filter, Finset.mem_univ, true_and, supportF_eq_supp]

/-- `lStepF` with the support table substituted. -/
def lStepC (x y : Finset HR) (s : HR) (w : Finset Bool) : Finset Bool := aC (bC w x s) y s

theorem lStepF_eq (x y : Finset HR) (s : HR) : game.lStepF x y s = lStepC x y s := by
  funext w
  unfold CsgQ.lStepF lStepC
  rw [bF_eq_bC, aF_eq_aC]

/-- The row-action witness set, two steps from `∅`. `Finset Bool` has height two, so two steps is
    all a monotone climb can take -- but nothing below *relies* on that argument: `lw_fixed`
    checks it. -/
def lwC (x y : Finset HR) (s : HR) : Finset Bool := (lStepC x y s)^[2] ∅

/-- Two steps really do suffice, for every pair of regions and every state: eight times eight
    times three instances, checked outright. This is what turns `hr_LW` into a general lemma and so
    makes `midStep` a function of `x` alone. -/
theorem lw_fixed : ∀ (x y : Finset HR) (s : HR), lStepC x y s (lwC x y s) = lwC x y s := by
  decide

/-- `LW`, for every pair of regions and state at once. -/
theorem hr_LW (x y : Finset HR) (s : HR) :
    (game.toCSG game_wf).LW ↑x ↑y s = (↑(lwC x y s) : Set Bool) :=
  CsgQ.LW_eq_coe_of_fixed game game_wf x y s (lwC x y s) 2 (by rw [lStepF_eq]; rfl)
    (by rw [lStepF_eq]; exact lw_fixed x y s)

/-! ## The middle chain -/

/-- `lpre1F` with the support table substituted. -/
def lpre1C (w : HR → Finset Bool) (x : Finset HR) : Finset HR :=
  Finset.univ.filter fun s => bC (w s) x s = Finset.univ

theorem lpre1F_eq_lpre1C (w : HR → Finset Bool) (x : Finset HR) :
    game.lpre1F w x = lpre1C w x := by
  ext s
  simp only [CsgQ.mem_lpre1F, lpre1C, Finset.mem_filter, Finset.mem_univ, true_and, bF_eq_bC]

/-- One turn of the middle chain, fully computable: the witness family is `lwC` at the current `x`,
    which is exactly what `hr_LW`'s generality buys. -/
def midStep (b y x : Finset HR) : Finset HR := lpre1C (fun s => lwC x y s) x ∪ b

theorem coe_midStep (b y x : Finset HR) :
    (game.toCSG game_wf).LFInner ↑b ↑y ↑x = (↑(midStep b y x) : Set HR) := by
  rw [CsgQ.coe_LFInner_apply game game_wf b y x (fun s => lwC x y s) (fun s => hr_LW x y s),
    lpre1F_eq_lpre1C]
  rfl

/-- Every stage of the middle climb is a lower bound on the `μX` fixed point. -/
theorem mid_le (b y : Finset HR) (m : ℕ) :
    (↑((midStep b y)^[m] ∅) : Set HR) ≤ ((game.toCSG game_wf).LFInner ↑b ↑y).lfp := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      set x := (midStep b y)^[m] ∅ with hx
      refine CsgQ.le_lfInner_of_step game game_wf b y x (midStep b y x)
        (fun s => lwC x y s) (fun s => hr_LW x y s) ih ?_
      unfold midStep
      rw [lpre1F_eq_lpre1C]

/-- A middle chain that was run and seen to stop pins the `μX` fixed point exactly. -/
theorem mid_eq (b y c : Finset HR) (m : ℕ) (hiter : (midStep b y)^[m] ∅ = c)
    (hfix : midStep b y c = c) :
    ((game.toCSG game_wf).LFInner ↑b ↑y).lfp = (↑c : Set HR) := by
  have hle : (↑c : Set HR) ≤ ((game.toCSG game_wf).LFInner ↑b ↑y).lfp := by
    have h := mid_le b y m
    rwa [hiter] at h
  refine CsgQ.lfInner_eq_coe_of_fixed game game_wf b y c (fun s => lwC c y s)
    (fun s => hr_LW c y s) ?_ hle
  rw [lpre1F_eq_lpre1C]
  exact hfix.symm

/-! ## Running it -/

/-- Reaching the goal. -/
def target : Finset HR := {HR.goal}

/-- The answer: the goal, and the stand-off state. -/
def winning : Finset HR := {HR.live, HR.goal}

#eval decide game.WellFormed
-- expect: true

#eval midStep target Finset.univ ∅
-- expect: {goal}

#eval (midStep target Finset.univ)^[2] ∅
-- expect: {live, goal}

#eval (midStep target winning)^[2] ∅
-- expect: {live, goal}      the outer chain has already stabilised

#eval lwC winning winning HR.live
-- expect: {true, false}     at `live` both actions are eventually witnesses

#eval lwC winning winning HR.dead
-- expect: {}                nothing escapes from `dead`

/-! ## The value-1 set -/

/-- The first outer step: the `μX` fixed point at `Finset.univ`. -/
theorem inner_at_univ :
    ((game.toCSG game_wf).LFInner ↑target ↑(Finset.univ : Finset HR)).lfp =
      (↑winning : Set HR) :=
  mid_eq target Finset.univ winning 2 (by decide) (by decide)

/-- …which makes `winning` an upper bound on `LF target`. -/
theorem LF_le_winning : (game.toCSG game_wf).LF ↑target ≤ (↑winning : Set HR) :=
  CsgQ.LF_le_of_step game game_wf target Finset.univ winning inner_at_univ
    (CsgQ.LF_le_univ game game_wf target)

/-- And the outer chain has stopped: `winning` is its own `μX` fixed point. -/
theorem inner_at_winning :
    ((game.toCSG game_wf).LFInner ↑target ↑winning).lfp = (↑winning : Set HR) :=
  mid_eq target winning winning 2 (by decide) (by decide)

/-- **The value-1 set of hide-or-run.** `live` can reach `goal` with probability arbitrarily close
    to one, and `LF` says so -- through three nested fixed points, none of them given an iteration
    bound, all of them run and checked. -/
theorem hr_LF : (game.toCSG game_wf).LF ↑target = (↑winning : Set HR) :=
  CsgQ.LF_eq_coe_of_fixed game game_wf target winning inner_at_winning LF_le_winning

/-! ## The almost-sure contrast

Everything above computed `LF`. The same machinery with `Apre1` in place of `Lpre1` computes `AF`,
and the two disagree -- which is the separation this game exists to exhibit. It is also cheaper:
`Apre1` has no inner fixed point, so there is no witness family, `afStepC` is a function of `x`
alone, and the chain carries no per-step hypothesis. -/

/-- `apre1F` with the support table substituted. The row-action pool `aC ∅ y s` is read off
    directly. -/
def apre1C (x y : Finset HR) : Finset HR :=
  Finset.univ.filter fun s => bC (aC ∅ y s) x s = Finset.univ

theorem apre1F_eq_apre1C (x y : Finset HR) : game.apre1F x y = apre1C x y := by
  ext s
  simp only [CsgQ.mem_apre1F, apre1C, Finset.mem_filter, Finset.mem_univ, true_and, bF_eq_bC,
    aF_eq_aC]

/-- One turn of the almost-sure middle chain, combinatorially. -/
def afStepC (b y x : Finset HR) : Finset HR := apre1C x y ∪ b

theorem afStepF_eq (b y : Finset HR) : game.afStepF b y = afStepC b y := by
  funext x
  change game.apre1F x y ∪ b = apre1C x y ∪ b
  rw [apre1F_eq_apre1C]

#eval (afStepC target Finset.univ)^[2] ∅
-- expect: {live, goal}     the same as the limit-sure chain at `univ`

#eval (afStepC target winning)^[1] ∅
-- expect: {goal}           and here the two part company

/-- The first outer step, which agrees with the limit-sure one. -/
theorem afInner_at_univ :
    ((game.toCSG game_wf).AFInner ↑target ↑(Finset.univ : Finset HR)).lfp =
      (↑winning : Set HR) :=
  CsgQ.afInner_eq_coe_of_fixed game game_wf target Finset.univ winning 2
    (by rw [afStepF_eq]; decide) (by rw [afStepF_eq]; decide)

theorem AF_le_winning : (game.toCSG game_wf).AF ↑target ≤ (↑winning : Set HR) :=
  CsgQ.AF_le_of_step game game_wf target Finset.univ winning afInner_at_univ
    (CsgQ.AF_le_univ game game_wf target)

/-- The second outer step, where almost-sure mode loses `live`. Restricted to the row actions that
    are safe for `winning`, the runner can only *wait* -- running risks `dead`, which lies outside
    `winning` -- and waiting against a wait returns to `live`. So the middle chain never grows past
    the goal itself. -/
theorem afInner_at_winning :
    ((game.toCSG game_wf).AFInner ↑target ↑winning).lfp = (↑target : Set HR) :=
  CsgQ.afInner_eq_coe_of_fixed game game_wf target winning target 1
    (by rw [afStepF_eq]; decide) (by rw [afStepF_eq]; decide)

theorem AF_le_target : (game.toCSG game_wf).AF ↑target ≤ (↑target : Set HR) :=
  CsgQ.AF_le_of_step game game_wf target winning target afInner_at_winning AF_le_winning

/-- And the outer chain has stopped. -/
theorem afInner_at_target :
    ((game.toCSG game_wf).AFInner ↑target ↑target).lfp = (↑target : Set HR) :=
  CsgQ.afInner_eq_coe_of_fixed game game_wf target target target 1
    (by rw [afStepF_eq]; decide) (by rw [afStepF_eq]; decide)

/-- **Almost-sure reachability gets a strictly smaller answer**: the goal alone. -/
theorem hr_AF : (game.toCSG game_wf).AF ↑target = (↑target : Set HR) :=
  CsgQ.AF_eq_coe_of_fixed game game_wf target target afInner_at_target AF_le_target

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

/-! ## The same game as data

`Comp/ModelData.lean` lets a model arrive as literal tables instead of a `match`. This section is
that format pointed at the game above, which makes it a test of two claims at once.

The first is routine: the data layer really does produce a usable `CsgQ`. The second is the
interesting one. Everything earlier in this file needed `supportF_eq_supp` to get `ℚ` out of the
way before `decide` could work, because a kernel entry like `1/2` normalises through `Nat.gcd`. A
`DetModelData`'s entries are `if _ then 1 else 0` instead, and deciding `1 ≠ 0` in `ℚ` compares
numerator and denominator without adding or dividing -- so there should be no quarantine lemma
needed here at all, and `gameData_answers` below closes both of its checks with a bare `decide`.

Deliberately *not* claimed: that this is the same game as `game` above. Relating the two would need
`CSG`-level invariance under relabelling the state type, which does not exist (the relabelling
lemmas in `Csg/MatrixGame.lean` are action-side). The two agree because the tables below were
written from the same transition structure, and the sure-safety region computed here is the one that
structure has -- not because anything transports.

State `0` is the stand-off, `1` the goal, `2` death; row action `0` is *run* and `1` is *wait*;
column action `0` is *throw* and `1` is *wait*. -/

/-- Hide-or-run's transition graph, as a successor table. Reward-free, so both reward tables are
    empty and every lookup defaults to `0`. `abbrev`, so that instance search can see the numerals
    through the projections. -/
abbrev gameData : DetModelData where
  nStates := 3
  nRow := 2
  nCol := 2
  succ := [[[2, 1], [1, 0]], [[1, 1], [1, 1]], [[2, 2], [2, 2]]]
  stateReward := []
  actionReward := []

/-- Belt and braces for the instances the `Fin` types need, in case the projections do not reduce
    during instance search. -/
instance : NeZero gameData.nStates := ⟨by decide⟩

instance : NeZero gameData.nRow := ⟨by decide⟩

instance : NeZero gameData.nCol := ⟨by decide⟩

/-- The successor table is in range -- pure `ℕ`, so `decide`. -/
theorem gameData_inRange : gameData.InRange := by decide

/-- …and hence a well-formed game, with no rational arithmetic anywhere in the proof. -/
theorem gameData_wf : gameData.toCsgQ.WellFormed :=
  DetModelData.wellFormed gameData gameData_inRange

/-- Everything but death. -/
def dataSafe : Finset (Fin gameData.nStates) := {0, 1}

#eval decide gameData.toCsgQ.WellFormed
-- expect: true

#eval gameData.toCsgQ.supportF 0 1 0
-- expect: {1}        waiting out a throw reaches the goal

#eval gameData.toCsgQ.gStepF dataSafe Finset.univ
-- expect: {0, 1}     one step already removes death

#eval (gameData.toCsgQ.gStepF dataSafe)^[2] Finset.univ
-- expect: {0, 1}     and it is stable

/-- **The claim.** The sure-safety region of a model given as *data*, as an answer to an objective,
    with both checks closed by `decide` -- no support table, no bridge lemma, no `norm_num`. So the
    arithmetic quarantine is a cost only genuinely probabilistic kernels have to pay. -/
theorem gameData_answers :
    gameData.toCsgQ.Answers gameData_wf (Objective.sureSafe dataSafe) (Answer.region dataSafe) :=
  CsgQ.answers_sureSafe gameData.toCsgQ gameData_wf dataSafe dataSafe 1 (by decide) (by decide)

end HideOrRun

end Comp
