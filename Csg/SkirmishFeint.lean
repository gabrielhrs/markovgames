/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# SKIRMISH with a third thrower action: `value(M) ≠ value(Mᵀ)` for a real instance

**Status: confirmed by a clean `lake build`, after one real fix round.** Round 1 caught three
independent issues, none touching the actual mathematics: (1)
`PMF.pure`/`PMF.pure_apply` (from `Mathlib...Monad`) and `PMF.ofFinset` (from
`Mathlib...Constructions`) came back "Unknown constant" even though `Csg.Basic` already imports
`Mathlib...ProbabilityMassFunction.Basic` -- this project's toolchain (`lean4:v4.34.0-rc2`) is on
Lean 4's newer module system, where a plain `import` does not re-export the imported module's names
to further downstream importers; `Csg.ConcurrentCoBuchiExample.lean` already works around exactly
this by importing `Mathlib...Monad`/`Mathlib...Uniform` directly rather than relying on getting them
transitively through its `Csg.*` imports, so the fix here is the same: import both PMF modules
directly (added above), rather than assuming anything reachable via `Csg.MatrixGameLP` is already in
scope. (2) `throwerAction_sum`/`skirmishState_sum` (the three-term `_sum` expansions) left an
unsolved associativity goal (`f a + (f b + f c)` from nested `Finset.sum_insert` versus the stated
`f a + f b + f c`) -- missed the trailing `abel` that `Csg.ConcurrentCoBuchiExample.cbState_sum`'s
own five-term version already needed for exactly this reason; added to both. (3) `throwerMinMix`/
`throwerMaxMix` (real-number-valued witnesses using genuine division, e.g. `4/5`, `2/7`) were
missing `noncomputable`, unlike `hiderPureHide`/`hiderPureHideCol` (only `0`/`1`, computable) --
added. Clean on resubmission, no further rounds needed.

**What this is and why.** SKIRMISH (de Alfaro & Henzinger, LICS 2000): a hider at a hiding spot
(`s_hide`) can `hide` or `run` for home (`s_home`); a thrower can `wait` or `throw`. The plain
two-action-per-side version is *never* asymmetric under transposing the payoff matrix: any `2×2`
zero-sum matrix game's closed-form value `(ad-bc)/(a+d-b-c)` is invariant under swapping `b↔c`,
which is exactly what transposing does -- checked by hand for every `2×2` instance already in this
project (`RockPaperScissors`'s reduced game, `IntrusionDetection`'s reach game, plain SKIRMISH
itself), all of which failed for this reason to show `value(M) ≠ value(Mᵀ)`. A third thrower action,
`feint`, breaks this: `2×3`/`3×2` matrix games have no such closed form and no reason to be
transpose-invariant in general, and the instance below is a genuine, hand-verified case where they
differ.

**The parameters**, chosen (numerically, via `scipy.optimize.linprog`, then confirmed exactly by
hand) so that both directions land on clean, distinct rationals:

* `(hide, wait) → s_hide` (unchanged from the original game: hiding while the thrower waits changes
  nothing).
* `(hide, throw) → s_home` w.p. `4/5`, `s_wet` w.p. `1/5` -- perturbed from the original SKIRMISH's
  `(hide,throw) = 1` (a throw at a hidden target always misses) down to `4/5`, since keeping it at
  exactly `1` is what forces this project's earlier attempts into the degenerate boundary value `1`
  regardless of `feint`'s own parameters (checked numerically: value-iteration on the un-perturbed
  design converges asymptotically to `1` over thousands of steps, never settling on an interior
  fraction).
* `(hide, feint) → s_home` w.p. `1/2`, `s_wet` w.p. `1/2`.
* `(run, wait) → s_home`, `(run, throw) → s_wet` (both unchanged from the original game: running
  while the thrower waits always succeeds, running into a throw always fails).
* `(run, feint) → s_home` w.p. `3/10`, `s_wet` w.p. `7/10`.

`feint`'s two outcomes (`1/2` at `hide`, `3/10` at `run`) are *not* a fixed convex mixture
`r · (hide,wait or throw) + (1-r) · (·)` of `wait`'s and `throw`'s outcomes for any single `r` held
across both rows -- solving for a common `r` against both rows simultaneously forces the
self-referential `s_hide` value itself to `-1/5`, outside `[0,1]`, so no such `r` exists. This
matters: a new action whose every outcome is such a fixed re-mixture of existing actions is
*always* dominated (a general fact, checked by hand while designing this file, not stated or used
as a lemma anywhere below) and could never affect either game's value regardless of its weight --
`feint` avoids that trap by construction, and indeed gets nonzero optimal weight in one of the two
directions below.

**The two matrix games, and why they are transposes of each other.** `jointK`/`jointR` below fix
the transition/reward for the joint action `(hiderAction, throwerAction)`, in that order, once and
for all -- one source of truth for the actual game mechanics. `skirmishMinCSG` and `skirmishMaxCSG`
both build their `CSG.K`/`CSG.r` from `jointK`/`jointR`, the first taking `(hider, thrower)` as
`(A1, A2)` (hider row/minimising, thrower column/maximising -- `Csg.Basic`'s fixed convention,
confirmed by `Gabriel`'s own read of every matrix-game file in this project: the column player is
*always* the maximiser here), the second taking `(thrower, hider)` as `(A1, A2)` (thrower
row/minimising, hider column/maximising). Since both reduce to literally the same `jointK`/`jointR`
call, just with the two arguments swapped, `skirmishMaxCSG.stageGame s v`'s payoff matrix is
`skirmishMinCSG.stageGame s v`'s own matrix with rows and columns swapped -- the transpose relation
holds *by construction* here, not merely numerically. This is deliberately the `Csg.Coalition`
picture, one level down: `reduceMin {hider}` puts the hider in the row/minimising slot (`⟨⟨hider⟩⟩
P_min`), `reduceMax {hider}` puts the hider in the column/maximising slot (`⟨⟨hider⟩⟩ P_max`) --
`skirmishMinCSG`/`skirmishMaxCSG` are the plain two-player shape those two reductions would produce
for a genuinely two-player `NCSG`, without yet paying for `CoalitionAction`/`ComplementAction`'s
dependent-product bookkeeping (`Csg.Coalition`'s own docstring flags relating `reduceMin {p1}` back
to a bare two-action-type `CSG` as needing new infrastructure -- an `Equiv`-invariance lemma for
`MatrixGame.value` -- not yet exercised anywhere; `MatrixGameCongr.value_relabelRow` is exactly that
lemma, so lifting this file to a genuine `NCSG` instance through `Csg.Coalition` is believed
straightforward, but is deliberately left for a follow-up file, matching this project's practice of
shipping one new piece of infrastructure at a time).

**The two values**, each pinned down by `MatrixGameLP.lean`'s
`value_isLeast_rowLPFeasible`/`value_isGreatest_colLPFeasible` (`le_antisymm` between one witness
strategy per side, exactly the reuse that file's own docstring anticipated -- neither
`RockPaperScissors.lean` nor `MatchingPennies.lean` needed this route, since both exploit a
row/column-sum symmetry `MatrixGameLP.lean` predicted wouldn't always be available):

* `stageValue_min_eq`: with the hider row/minimising, the thrower column/maximising, the
  self-consistent value at `s_hide` is exactly `4/5` -- witnessed by the hider always hiding
  (`p = (1, 0)`) against the thrower mixing `q = (4/5, 1/5, 0)` (`feint` unused).
* `stageValue_max_eq`: with the thrower row/minimising, the hider column/maximising, the
  self-consistent value at `s_hide` is exactly `1/2` -- witnessed by the thrower mixing
  `p = (2/7, 0, 5/7)` (`wait`/`feint`, `throw` unused) against the hider always hiding
  (`q = (1, 0)`).
* `value_ne`: `4/5 ≠ 1/2`, so the two stage games -- transposes of each other by construction --
  have different values. This is the file's actual point: `value(M) ≠ value(Mᵀ)` in general, and
  `feint` (the one new action beyond plain SKIRMISH) is exactly what makes it possible, by turning
  a `2×2` instance (always transpose-invariant, see above) into a `2×3`/`3×2` one (not).

**Not attempted here.** Both theorems above are self-consistency statements ("if the continuation
already carries this state's own eventual value at `s_hide`, the one-shot stage value matches"),
not a proof that `4/5`/`1/2` are the *actual* infinite-horizon reachability values -- lifting that
requires `reachOp`/`.lfp`, deliberately deferred (matching how `CoalitionComplement.lean`'s own
`stageValue`-level equality was kept separate from the `reachOp`-level theorem it enables). Also not
attempted: the genuine `NCSG`/`Csg.Coalition` instance mentioned above, and any reward (`r ≠ 0`)
formulation -- `jointR ≡ 0` throughout, all the payoff information sitting in `jointK`'s split
between `s_home`/`s_wet` and the continuation `v` supplying `v s_home = 1`/`v s_wet = 0`.
-/

namespace Csg

/-! ## The hider's and thrower's actions, and the three states -/

/-- The hider's two actions: stay hidden, or make a run for home. Unchanged from plain SKIRMISH. -/
inductive HiderAction
  | hide
  | run
  deriving DecidableEq, Inhabited

instance : Fintype HiderAction where
  elems := {HiderAction.hide, .run}
  complete := by intro a; cases a <;> decide

/-- Expand a sum over all of `HiderAction` into its two terms, matching this project's established
    `_sum` idiom (`Csg.ConcurrentCoBuchiExample.rowMove_sum` and others). -/
theorem hiderAction_sum {β : Type*} [AddCommMonoid β] (f : HiderAction → β) :
    ∑ a : HiderAction, f a = f .hide + f .run := by
  have huniv : (Finset.univ : Finset HiderAction) = {HiderAction.hide, .run} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The thrower's three actions: wait, throw at the hiding spot, or feint -- the one addition
    beyond plain SKIRMISH's two, discussed at length in the module docstring above. -/
inductive ThrowerAction
  | wait
  | throw
  | feint
  deriving DecidableEq, Inhabited

instance : Fintype ThrowerAction where
  elems := {ThrowerAction.wait, .throw, .feint}
  complete := by intro a; cases a <;> decide

/-- Expand a sum over all of `ThrowerAction` into its three terms. -/
theorem throwerAction_sum {β : Type*} [AddCommMonoid β] (f : ThrowerAction → β) :
    ∑ a : ThrowerAction, f a = f .wait + f .throw + f .feint := by
  have huniv : (Finset.univ : Finset ThrowerAction) = {ThrowerAction.wait, .throw, .feint} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-- The three states: still hiding at the spot (self-referential -- `(hide,wait)` loops back
    here), safely home, caught wet. Matches the `s_hide`/`s_home`/`s_wet` origin from de Alfaro &
    Henzinger's own SKIRMISH. -/
inductive SkirmishState
  | hide
  | home
  | wet
  deriving DecidableEq, Inhabited

instance : Fintype SkirmishState where
  elems := {SkirmishState.hide, .home, .wet}
  complete := by intro s; cases s <;> decide

/-- Expand a sum over all of `SkirmishState` into its three terms. -/
theorem skirmishState_sum {β : Type*} [AddCommMonoid β] (f : SkirmishState → β) :
    ∑ s : SkirmishState, f s = f .hide + f .home + f .wet := by
  have huniv : (Finset.univ : Finset SkirmishState) = {SkirmishState.hide, .home, .wet} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-! ## A two-point distribution over `s_home`/`s_wet`, weight `p`/`1-p` -/

/-- Lands on `s_home` with probability `p` and `s_wet` with probability `1-p` (never on `s_hide`).
    `p` is taken as a plain real (not `ℝ≥0∞`) with explicit `0 ≤ p ≤ 1` side conditions,
    specifically so that recovering it via `.toReal` later is the one-line `ENNReal.toReal_ofReal`,
    rather than fighting `ℝ≥0∞`'s own truncated division/subtraction on numeral weights. -/
noncomputable def homeWetSplit (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF SkirmishState :=
  PMF.ofFinset
    (fun s => match s with
      | .home => ENNReal.ofReal p
      | .wet => ENNReal.ofReal (1 - p)
      | .hide => 0)
    {SkirmishState.home, .wet}
    (by
      have hne : (SkirmishState.home : SkirmishState) ≠ .wet := by decide
      rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
      show ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1
      rw [← ENNReal.ofReal_add hp0 (by linarith), show p + (1 - p) = 1 by ring, ENNReal.ofReal_one])
    (by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      push_neg at hs
      rcases s with _ | _ | _
      · rfl
      · exact absurd rfl hs.1
      · exact absurd rfl hs.2)

theorem homeWetSplit_home (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    homeWetSplit p hp0 hp1 .home = ENNReal.ofReal p := rfl

theorem homeWetSplit_wet (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    homeWetSplit p hp0 hp1 .wet = ENNReal.ofReal (1 - p) := rfl

theorem homeWetSplit_hide (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    homeWetSplit p hp0 hp1 .hide = 0 := rfl

/-! ## The joint transition, shared by both directions -/

/-- The transition kernel for the joint action `(hiderAction, throwerAction)`, in that fixed
    order, regardless of which of `skirmishMinCSG`/`skirmishMaxCSG` below ends up calling it --
    one source of truth for the actual game mechanics, exactly so that the two `CSG`s' payoff
    matrices are transposes of each other *by construction* (see the module docstring). `s_home`/
    `s_wet` are absorbing. -/
noncomputable def jointK : SkirmishState → HiderAction → ThrowerAction → PMF SkirmishState
  | .home, _, _ => PMF.pure .home
  | .wet, _, _ => PMF.pure .wet
  | .hide, .hide, .wait => PMF.pure .hide
  | .hide, .hide, .throw => homeWetSplit (4 / 5) (by norm_num) (by norm_num)
  | .hide, .hide, .feint => homeWetSplit (1 / 2) (by norm_num) (by norm_num)
  | .hide, .run, .wait => PMF.pure .home
  | .hide, .run, .throw => PMF.pure .wet
  | .hide, .run, .feint => homeWetSplit (3 / 10) (by norm_num) (by norm_num)

/-- Reward-free throughout, matching `Csg.ConcurrentCoBuchiExample.cbR`'s convention -- all payoff
    information lives in `jointK`'s split between `s_home`/`s_wet`, read off through the
    continuation `v`. -/
noncomputable def jointR : SkirmishState → HiderAction → ThrowerAction → ℝ := fun _ _ _ => 0

/-- `s_hide`'s expected continuation value, one joint action at a time -- six cases, one per
    `(hiderAction, throwerAction)` pair, each reused by *both* `skirmishMinCSG` and
    `skirmishMaxCSG` below (they call `jointK .hide` with the same two arguments, just assembled
    into the matrix in opposite row/column roles). -/
theorem jointExpect_hide_wait (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .hide .wait s').toReal * v s' = v .hide := by
  simp [jointK, skirmishState_sum, PMF.pure_apply]

theorem jointExpect_hide_throw (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .hide .throw s').toReal * v s' =
      (4 / 5) * v .home + (1 / 5) * v .wet := by
  have h0 : (0:ℝ) ≤ (4 / 5 : ℝ) := by norm_num
  have h0' : (0:ℝ) ≤ 1 - (4 / 5 : ℝ) := by norm_num
  simp only [jointK, skirmishState_sum, homeWetSplit_home, homeWetSplit_wet, homeWetSplit_hide,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h0', ENNReal.toReal_zero]
  ring

theorem jointExpect_hide_feint (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .hide .feint s').toReal * v s' =
      (1 / 2) * v .home + (1 / 2) * v .wet := by
  have h0 : (0:ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  have h0' : (0:ℝ) ≤ 1 - (1 / 2 : ℝ) := by norm_num
  simp only [jointK, skirmishState_sum, homeWetSplit_home, homeWetSplit_wet, homeWetSplit_hide,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h0', ENNReal.toReal_zero]
  ring

theorem jointExpect_run_wait (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .run .wait s').toReal * v s' = v .home := by
  simp [jointK, skirmishState_sum, PMF.pure_apply]

theorem jointExpect_run_throw (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .run .throw s').toReal * v s' = v .wet := by
  simp [jointK, skirmishState_sum, PMF.pure_apply]

theorem jointExpect_run_feint (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .run .feint s').toReal * v s' =
      (3 / 10) * v .home + (7 / 10) * v .wet := by
  have h0 : (0:ℝ) ≤ (3 / 10 : ℝ) := by norm_num
  have h0' : (0:ℝ) ≤ 1 - (3 / 10 : ℝ) := by norm_num
  simp only [jointK, skirmishState_sum, homeWetSplit_home, homeWetSplit_wet, homeWetSplit_hide,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h0', ENNReal.toReal_zero]
  ring

/-! ## The two directions -/

/-- Hider row/minimising, thrower column/maximising -- `⟨⟨hider⟩⟩ P_min`'s shape (`Csg.Coalition`'s
    `reduceMin {hider}`, one level down: see the module docstring). -/
noncomputable def skirmishMinCSG : CSG SkirmishState HiderAction ThrowerAction where
  K s a1 a2 := jointK s a1 a2
  r s a1 a2 := jointR s a1 a2

/-- Thrower row/minimising, hider column/maximising -- `⟨⟨hider⟩⟩ P_max`'s shape (`reduceMax
    {hider}`, one level down). Built from the very same `jointK`/`jointR`, arguments swapped, so
    its payoff matrix is `skirmishMinCSG`'s own matrix transposed, by construction. -/
noncomputable def skirmishMaxCSG : CSG SkirmishState ThrowerAction HiderAction where
  K s a2 a1 := jointK s a1 a2
  r s a2 a1 := jointR s a1 a2

/-- The hider always hides: `p = (1, 0)`, the row-side witness for `stageValue_min_eq`. -/
def hiderPureHide : HiderAction → ℝ
  | .hide => 1
  | .run => 0

/-- The thrower mixes `wait`/`throw` only: `q = (4/5, 1/5, 0)`, the column-side witness for
    `stageValue_min_eq` -- `feint` unused in this direction. -/
noncomputable def throwerMinMix : ThrowerAction → ℝ
  | .wait => 4 / 5
  | .throw => 1 / 5
  | .feint => 0

/-- **The `⟨⟨hider⟩⟩ P_min`-shaped value.** With the hider row/minimising and the thrower
    column/maximising, the stage game at `s_hide` -- once the continuation already carries `s_hide`
    itself at the self-consistent value `4/5` -- has value exactly `4/5`. Witnessed on the row side
    by `hiderPureHide` (always hide) and on the column side by `throwerMinMix`
    (`wait`/`throw`, `4/5`-`1/5`) via `le_antisymm` between `MatrixGameLP.lean`'s two LP
    characterizations, exactly the reuse that file's own docstring anticipated. -/
theorem stageValue_min_eq (v : SkirmishState → ℝ) (vhide : v .hide = 4 / 5) (vhome : v .home = 1)
    (vwet : v .wet = 0) :
    (skirmishMinCSG.stageGame .hide v).value = 4 / 5 := by
  set G := skirmishMinCSG.stageGame .hide v with hG
  have hA : ∀ a1 a2, G.A a1 a2 = jointR .hide a1 a2 + ∑ s', (jointK .hide a1 a2 s').toReal * v s' :=
    fun a1 a2 => rfl
  have hAhw : G.A .hide .wait = 4 / 5 := by norm_num [hA, jointR, jointExpect_hide_wait, vhide]
  have hAht : G.A .hide .throw = 4 / 5 := by
    norm_num [hA, jointR, jointExpect_hide_throw, vhome, vwet]
  have hAhf : G.A .hide .feint = 1 / 2 := by
    norm_num [hA, jointR, jointExpect_hide_feint, vhome, vwet]
  have hArw : G.A .run .wait = 1 := by norm_num [hA, jointR, jointExpect_run_wait, vhome]
  have hArt : G.A .run .throw = 0 := by norm_num [hA, jointR, jointExpect_run_throw, vwet]
  have hArf : G.A .run .feint = 3 / 10 := by
    norm_num [hA, jointR, jointExpect_run_feint, vhome, vwet]
  apply le_antisymm
  · have hmem : (4 / 5 : ℝ) ∈ G.rowLPFeasible := by
      refine ⟨hiderPureHide, ⟨fun a => by cases a <;> norm_num [hiderPureHide],
        by simp only [hiderAction_sum, hiderPureHide]; norm_num⟩, ?_⟩
      intro j
      simp only [hiderAction_sum]
      cases j <;> norm_num [hiderPureHide, hAhw, hAht, hAhf]
    exact G.value_isLeast_rowLPFeasible.2 hmem
  · have hmem : (4 / 5 : ℝ) ∈ G.colLPFeasible := by
      refine ⟨throwerMinMix, ⟨fun a => by cases a <;> norm_num [throwerMinMix],
        by simp only [throwerAction_sum, throwerMinMix]; norm_num⟩, ?_⟩
      intro i
      simp only [throwerAction_sum]
      cases i <;> norm_num [throwerMinMix, hAhw, hAht, hAhf, hArw, hArt, hArf]
    exact G.value_isGreatest_colLPFeasible.2 hmem

/-- The thrower mixes `wait`/`feint` only: `p = (2/7, 0, 5/7)`, the row-side witness for
    `stageValue_max_eq` -- `throw` unused in this direction, `feint` essential. -/
noncomputable def throwerMaxMix : ThrowerAction → ℝ
  | .wait => 2 / 7
  | .throw => 0
  | .feint => 5 / 7

/-- The hider always hides: `q = (1, 0)`, the column-side witness for `stageValue_max_eq`. -/
def hiderPureHideCol : HiderAction → ℝ
  | .hide => 1
  | .run => 0

/-- **The `⟨⟨hider⟩⟩ P_max`-shaped value.** With the thrower row/minimising and the hider
    column/maximising, the stage game at `s_hide` -- once the continuation already carries `s_hide`
    itself at the self-consistent value `1/2` -- has value exactly `1/2`. Witnessed on the row side
    by `throwerMaxMix` (`wait`/`feint`, `2/7`-`5/7`, `throw` unused) and on the column side by
    `hiderPureHideCol` (always hide). -/
theorem stageValue_max_eq (v : SkirmishState → ℝ) (vhide : v .hide = 1 / 2) (vhome : v .home = 1)
    (vwet : v .wet = 0) :
    (skirmishMaxCSG.stageGame .hide v).value = 1 / 2 := by
  set G := skirmishMaxCSG.stageGame .hide v with hG
  have hA : ∀ a2 a1, G.A a2 a1 = jointR .hide a1 a2 + ∑ s', (jointK .hide a1 a2 s').toReal * v s' :=
    fun a2 a1 => rfl
  have hAwh : G.A .wait .hide = 1 / 2 := by norm_num [hA, jointR, jointExpect_hide_wait, vhide]
  have hAwr : G.A .wait .run = 1 := by norm_num [hA, jointR, jointExpect_run_wait, vhome]
  have hAth : G.A .throw .hide = 4 / 5 := by
    norm_num [hA, jointR, jointExpect_hide_throw, vhome, vwet]
  have hAtr : G.A .throw .run = 0 := by norm_num [hA, jointR, jointExpect_run_throw, vwet]
  have hAfh : G.A .feint .hide = 1 / 2 := by
    norm_num [hA, jointR, jointExpect_hide_feint, vhome, vwet]
  have hAfr : G.A .feint .run = 3 / 10 := by
    norm_num [hA, jointR, jointExpect_run_feint, vhome, vwet]
  apply le_antisymm
  · have hmem : (1 / 2 : ℝ) ∈ G.rowLPFeasible := by
      refine ⟨throwerMaxMix, ⟨fun a => by cases a <;> norm_num [throwerMaxMix],
        by simp only [throwerAction_sum, throwerMaxMix]; norm_num⟩, ?_⟩
      intro j
      simp only [throwerAction_sum]
      cases j <;> norm_num [throwerMaxMix, hAwh, hAwr, hAth, hAtr, hAfh, hAfr]
    exact G.value_isLeast_rowLPFeasible.2 hmem
  · have hmem : (1 / 2 : ℝ) ∈ G.colLPFeasible := by
      refine ⟨hiderPureHideCol, ⟨fun a => by cases a <;> norm_num [hiderPureHideCol],
        by simp only [hiderAction_sum, hiderPureHideCol]; norm_num⟩, ?_⟩
      intro i
      simp only [hiderAction_sum]
      cases i <;> norm_num [hiderPureHideCol, hAwh, hAth, hAfh]
    exact G.value_isGreatest_colLPFeasible.2 hmem

/-- **The point of this file.** The two directions disagree: `⟨⟨hider⟩⟩ P_max`-shaped value `1/2`
    is not `⟨⟨hider⟩⟩ P_min`-shaped value `4/5`, for two stage games that are transposes of each
    other by construction (see the module docstring) -- a genuine, hand-verified instance of
    `value(M) ≠ value(Mᵀ)`, unreachable at `2×2` (every such instance in this project collapses,
    see above) and made possible here by `feint`, the one new action beyond plain SKIRMISH. -/
theorem value_ne (vMin vMax : SkirmishState → ℝ)
    (vMinHide : vMin .hide = 4 / 5) (vMinHome : vMin .home = 1) (vMinWet : vMin .wet = 0)
    (vMaxHide : vMax .hide = 1 / 2) (vMaxHome : vMax .home = 1) (vMaxWet : vMax .wet = 0) :
    (skirmishMaxCSG.stageGame .hide vMax).value ≠ (skirmishMinCSG.stageGame .hide vMin).value := by
  rw [stageValue_max_eq vMax vMaxHide vMaxHome vMaxWet,
    stageValue_min_eq vMin vMinHide vMinHome vMinWet]
  norm_num

end Csg
