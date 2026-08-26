/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Basic

/-!
# A reusable reward-until-absorption certificate, in plain `ℝ`

**Status: drafted, not yet run through `lake build`.** Generalises `RockPaperScissorsSteps.lean`'s
bespoke `rpsStepsStep`/`rpsSteps_fixed`/`rpsSteps_unique` pattern from a hard-coded `win1 ∨ win2`
goal to an arbitrary `CSG` and `goal : S → Prop`, exactly the way `ReachCertificate.lean`
generalised `RockPaperScissorsLfp.lean`'s `rpsVStar`-specific certificate. The user asked for this
after `RockPaperScissorsSteps.lean` built clean, and chose the `ℝ`-valued route explicitly over a
fully general `ℝ≥0∞`-valued `CSG.rewardUntilOp` (see the `AskUserQuestion` decision recorded in
this session, and `PHASE0-NOTES.md`'s writeup of the extended-value minimax obstruction that
choice sidesteps: `Sion.exists_isSaddlePointOn`, which every stage-value computation in this
project relies on, needs a genuine real topological vector space, and `ℝ≥0∞` is not one).

**Deliberately still bespoke in one respect, by design, not by oversight.** Reachability's
`reachOp`/`untilOp` are bundled `OrderHom`s on the complete lattice `S → Set.Icc (0:ℝ) 1`, so
Knaster-Tarski hands back a *canonical* least fixed point (`.lfp`) before any certificate is even
supplied -- the certificate's job there is only to *identify* that already-existing least fixed
point with a concrete candidate. Plain `S → ℝ` under the natural reward-until step has no such
free existence theorem (no boundedness to make it a complete lattice, no `OrderHom.lfp` to appeal
to), so there is no operator here to bundle and no `.lfp` to equate `v` with. The certificate
below states the corresponding fact at the level this setting actually supports: `v` together with
`hfixed`/`huniq` witnesses that the reward-until step has *a* fixed point and that it is the
*only* one (`∃!`), which is exactly the pair of facts `rpsSteps_fixed`/`rpsSteps_unique` already
proved by hand for one instance. The two hypotheses are not discharged by this file -- exactly the
`ReachCertificate.lean` precedent of automating only the assembly, not the underlying mathematics,
which for a linear system this size is a handful of `linarith` calls, and for a larger or
cyclic-transition model would realistically need an external argument (see the note below on how
this connects to `untilOp`/`reachOp`'s own `.lfp` machinery).

**Design informed by PRISM-games' `CSGModelChecker.java`** (`computeReachRewardsInfinity`,
`valInfinity`, fetched per the user's pointer to the upstream source), without importing any of
its machinery. PRISM does not solve infinite-valued reward-until with an extended-value minimax
theorem; it first runs a purely qualitative almost-sure-reachability precomputation (`AF`) marking
every state outside it `∞`, then solves the finite real-valued residual game normally, pruning any
action that can only lead to an already-`∞` state as dominated (`valInfinity`). That two-phase
shape -- a qualitative gate, then a real-valued computation over what the gate certifies is
finite -- is exactly what this project's own `untilOp`/`reachOp`'s `.lfp` already computes (hitting
probability `1` is PRISM's `AF`). So the natural way a caller would discharge `huniq` for a model
where absorption is not simply "obviously certain by symmetry" (as it was for
`RockPaperScissorsSteps.lean`) is to first establish an a.s.-reachability certificate via
`untilOp`/`reachOp`, then argue uniqueness of the real-valued recursion *given* that gate -- but
this combinator stays agnostic to that, exactly as `ReachCertificate.lean` stays agnostic to how
its own `hfixed`/`hlb` get discharged.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The reward-until-absorption Bellman step, on plain `S → ℝ`: a `goal` state contributes no
    further reward (absorption, same idea as `reachOpFun`'s `goal`-true branch, but pinned to `0`
    here since this measures *accumulated cost to reach* the goal rather than *probability of*
    reaching it); any other state plays its stage game against the continuation, via the already
    fully general `CSG.stageValue` (never restricted to `C.r ≡ 0` or `≡ 1` -- only
    `CsgMonotone.lean`'s separate `[0, 1]`-boundedness lemmas needed that). Generalises
    `RockPaperScissorsSteps.lean`'s `rpsStepsStep`, whose `if s = win1 ∨ s = win2 then 0 else ...`
    is this definition specialised to `goal := fun s => s = win1 ∨ s = win2`. -/
noncomputable def rewardUntilStep (goal : S → Prop) [DecidablePred goal] (v : S → ℝ) (s : S) : ℝ :=
  if goal s then 0 else C.stageValue s v

/-- **The payoff.** A candidate `v` that is an exact fixed point of `rewardUntilStep`, together
    with a proof that *any* real-valued fixed point of the same step equals `v`, witnesses that
    `rewardUntilStep goal` has a unique fixed point, namely `v` -- the reward-until-absorption
    analogue of `reachOp_lfp_eq_of_certificate`/`OrderHom.lfp_eq_of_certificate`, stated as an
    `∃!` rather than an `.lfp` equation since plain `S → ℝ` carries no complete-lattice structure
    to hang a canonical least fixed point on here. Generalises `RockPaperScissorsSteps.lean`'s
    `rpsSteps_fixed`/`rpsSteps_unique` pair (which are exactly `hfixed`/`huniq` for
    `rpsCSGSteps`/`rpsStepsStep`/`rpsSteps`) into a single reusable statement for an arbitrary
    `CSG`, `goal`, and candidate. As with `ReachCertificate.lean`, this combinator automates only
    the assembly of the two hypotheses into the `∃!` conclusion, not the (model-specific)
    mathematics of `hfixed`/`huniq` themselves. -/
theorem rewardUntilOp_eq_of_certificate (goal : S → Prop) [DecidablePred goal] (v : S → ℝ)
    (hfixed : C.rewardUntilStep goal v = v)
    (huniq : ∀ w : S → ℝ, C.rewardUntilStep goal w = w → w = v) :
    ∃! w : S → ℝ, C.rewardUntilStep goal w = w :=
  ⟨v, hfixed, huniq⟩

end CSG
end Csg
