/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Plain SKIRMISH: the LICS 2000 sure/almost/limit divergence witness

**Status: confirmed by a clean `lake build`.** The plain, two-action-per-side, fully
deterministic SKIRMISH game from L. de Alfaro and T. Henzinger, "Concurrent Omega-Regular Games,"
LICS 2000 -- confirmed directly against `prism-games`'s own test fixture
`prism-tests/functionality/verify/csgs/qualitative/skirmish.prism` (and its accompanying
`skirmish.prism.props`, which records the 14 concrete `sure`/`almost`/`limit` results this model is
meant to reproduce). This is a *different* model from `Csg.SkirmishFeint` (`SoldierMove`/
`SniperMove`/`SkirmishPos` below, versus that file's `HiderAction`/`ThrowerAction`/`SkirmishState`)
deliberately given fresh names to avoid any collision in this shared `Csg` namespace:
`SkirmishFeint.lean` perturbs the original game with a third, *probabilistic* thrower action
(`feint`) to exhibit `value(M) ≠ value(Mᵀ)` for the quantitative line; this file is the
*unperturbed*, fully deterministic original, needed because the sure/almost/limit qualitative
divergence the property file records depends on the transitions being exactly as plain SKIRMISH
specifies them -- `feint`'s presence or absence isn't the point here, certainty/probability-1/
limiting-probability-1 is.

**The model, read directly off `skirmish.prism`.** Three states -- `hide` (`s=0`), `wet` (`s=1`),
`home` (`s=2`) -- with `hide` initial. Player 1 (`p1`, the soldier, our row/minimising `A1`) moves
`hide` or `run`; player 2 (`p2`, the sniper, our column/maximising `A2`) moves `wait` or `throw`.
From `hide`: `(hide,wait) → hide` (staying put is always available against a non-committal
sniper); `(hide,throw) → home` (a throw at an already-hidden target misses, and lands you home);
`(run,wait) → home` (running while the sniper waits always succeeds); `(run,throw) → wet` (running
into a thrown shot always fails). `wet` is absorbing (`[] (s=1) → (s'=1)`); `home` auto-returns to
`hide` on the next step (`[] (s=2) → (s'=0)`), the one construction detail that makes "visit `home`
infinitely often" (`G F`) a meaningful, non-degenerate objective rather than a one-shot reach:
every visit to `home` immediately re-exposes you to the whole game again. Every transition is
deterministic (`PMF.pure`); all randomness in the "almost"/"limit" distinction comes entirely from
mixed *strategies* over these deterministic joint actions, not from any stochastic transition --
exactly the concurrent-game (as opposed to Markov-chain) source of the sure/almost/limit gap LICS
2000 is about.

**Reward-free**, matching `Csg.SkirmishFeint.jointR`'s convention and every other qualitative
worked instance in this project (`Csg.QualitativeSure`/`Csg.QualitativeAlmostSure`/
`Csg.QualitativeLimitSure`'s own operators never read `r` at all) -- `skirmishR ≡ 0` is present only
because `CSG` requires an `r` field, never consulted by anything downstream of this file.

**What this file does and does not contain.** Just the model (`SoldierMove`, `SniperMove`,
`SkirmishPos`, their `Fintype`/`DecidableEq`/`Inhabited` instances, `skirmishK`/`skirmishR`/
`skirmishCSG`) plus the six case-by-case transition equalities and their `.support` corollaries
(`PMF.support_pure`), which is exactly the raw material every qualitative operator (`Pre1`, `A`,
`B`, ...) unfolds to. The actual 14 `sure`/`almost`/`limit` facts from `skirmish.prism.props` are
deliberately left to a follow-up file, per the agreed easier-first pacing: get the model itself
confirmed clean before building any fixed-point argument on top of it.
-/

namespace Csg

/-! ## The two players' moves, and the three positions -/

/-- The soldier's (player 1's, row/minimising `A1`) two moves: stay hidden, or make a run for
    home. -/
inductive SoldierMove
  | hide
  | run
  deriving DecidableEq, Inhabited

instance : Fintype SoldierMove where
  elems := {SoldierMove.hide, .run}
  complete := by intro a; cases a <;> decide

/-- The sniper's (player 2's, column/maximising `A2`) two moves: wait, or throw at the hiding
    spot. -/
inductive SniperMove
  | wait
  | throw
  deriving DecidableEq, Inhabited

instance : Fintype SniperMove where
  elems := {SniperMove.wait, .throw}
  complete := by intro a; cases a <;> decide

/-- The three positions: still hiding at the spot (`s=0` in the PRISM model), caught wet
    (`s=1`, absorbing), safely home (`s=2`, auto-returns to `hide` next step). -/
inductive SkirmishPos
  | hide
  | wet
  | home
  deriving DecidableEq, Inhabited

instance : Fintype SkirmishPos where
  elems := {SkirmishPos.hide, .wet, .home}
  complete := by intro s; cases s <;> decide

/-! ## The transition kernel, read directly off `skirmish.prism` -/

/-- The transition kernel, matching `skirmish.prism`'s `module ob` line for line: `wet` and `home`
    ignore the joint move entirely (`wet` absorbing, `home` auto-returning to `hide`); `hide`
    branches on the joint move into exactly the four cases the PRISM model's `module ob` lists. -/
noncomputable def skirmishK : SkirmishPos → SoldierMove → SniperMove → PMF SkirmishPos
  | .wet, _, _ => PMF.pure .wet
  | .home, _, _ => PMF.pure .hide
  | .hide, .hide, .wait => PMF.pure .hide
  | .hide, .hide, .throw => PMF.pure .home
  | .hide, .run, .wait => PMF.pure .home
  | .hide, .run, .throw => PMF.pure .wet

/-- Reward-free throughout: every qualitative operator this file's follow-up will use (`Pre1`, `A`,
    `B`, ...) reads only `K`'s support, never `r`. -/
noncomputable def skirmishR : SkirmishPos → SoldierMove → SniperMove → ℝ := fun _ _ _ => 0

/-- The plain SKIRMISH game: soldier row/minimising, sniper column/maximising, matching PRISM's
    own `<<p1>>` (the soldier is the coalition whose forcing ability the property file's `sure`/
    `almost`/`limit` queries ask about, and our `Pre1`/`A`/`B`-based operators quantify `∃a1 ∀a2`
    over exactly that role). -/
noncomputable def skirmishCSG : CSG SkirmishPos SoldierMove SniperMove where
  K := skirmishK
  r := skirmishR

/-! ## The six transition cases, and their supports -/

theorem skirmishK_wet (a1 : SoldierMove) (a2 : SniperMove) :
    skirmishCSG.K .wet a1 a2 = PMF.pure .wet := rfl

theorem skirmishK_home (a1 : SoldierMove) (a2 : SniperMove) :
    skirmishCSG.K .home a1 a2 = PMF.pure .hide := rfl

theorem skirmishK_hide_hide_wait : skirmishCSG.K .hide .hide .wait = PMF.pure .hide := rfl

theorem skirmishK_hide_hide_throw : skirmishCSG.K .hide .hide .throw = PMF.pure .home := rfl

theorem skirmishK_hide_run_wait : skirmishCSG.K .hide .run .wait = PMF.pure .home := rfl

theorem skirmishK_hide_run_throw : skirmishCSG.K .hide .run .throw = PMF.pure .wet := rfl

/-- **The payoff.** `wet`'s support, for any joint move -- the raw material `Pre1`/`A`/`B` will
    unfold to whenever the current position is `wet`. -/
theorem skirmishK_support_wet (a1 : SoldierMove) (a2 : SniperMove) :
    (skirmishCSG.K .wet a1 a2).support = {SkirmishPos.wet} := by
  rw [skirmishK_wet]; exact PMF.support_pure _

/-- **The payoff.** `home`'s support, for any joint move. -/
theorem skirmishK_support_home (a1 : SoldierMove) (a2 : SniperMove) :
    (skirmishCSG.K .home a1 a2).support = {SkirmishPos.hide} := by
  rw [skirmishK_home]; exact PMF.support_pure _

/-- **The payoff.** `hide`'s support against `(hide,wait)`. -/
theorem skirmishK_support_hide_hide_wait :
    (skirmishCSG.K .hide .hide .wait).support = {SkirmishPos.hide} := by
  rw [skirmishK_hide_hide_wait]; exact PMF.support_pure _

/-- **The payoff.** `hide`'s support against `(hide,throw)`. -/
theorem skirmishK_support_hide_hide_throw :
    (skirmishCSG.K .hide .hide .throw).support = {SkirmishPos.home} := by
  rw [skirmishK_hide_hide_throw]; exact PMF.support_pure _

/-- **The payoff.** `hide`'s support against `(run,wait)`. -/
theorem skirmishK_support_hide_run_wait :
    (skirmishCSG.K .hide .run .wait).support = {SkirmishPos.home} := by
  rw [skirmishK_hide_run_wait]; exact PMF.support_pure _

/-- **The payoff.** `hide`'s support against `(run,throw)`. -/
theorem skirmishK_support_hide_run_throw :
    (skirmishCSG.K .hide .run .throw).support = {SkirmishPos.wet} := by
  rw [skirmishK_hide_run_throw]; exact PMF.support_pure _

end Csg
