/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# `healthy` recurs infinitely often, almost surely, against an oblivious attacker

**Status: confirmed by a clean `lake build`.** Notes on the Mathlib interfaces this file leans
on:

* `PMF.uniformOfFintype` lives in `Mathlib.Probability.Distributions.Uniform` and `PMF.map` in
  `Mathlib.Probability.ProbabilityMassFunction.Constructions`; both are imported directly.
* `iIndepFun_infinitePi` (`Mathlib/Probability/Independence/InfinitePi.lean`) wants a *per-factor*
  function `X i : Ω_i → 𝓧` and produces the coordinate-composed family `fun i ω ↦ X i (ω i)`
  itself. `idsRoundHealthy` below is that per-factor map (`PolicyAction × AttackAction → Bool`,
  the same function at every round, since `idsNext` does not depend on the round number).
* Measurability on these discrete types is `MeasurableSet.of_discrete`/`Measurable.of_discrete`.
* There is no one-step lemma taking `iIndepFun` to `iIndepSet`. `idsPlay_indepSet_healthy` goes
  through `iIndepFun_iff_measure_inter_preimage_eq_mul`, which restates `iIndepFun` as a measure
  identity over finite intersections of preimages, and `iIndepSet_iff_iIndepSets_singleton` with
  `iIndepSets_singleton_iff`, which restate `iIndepSet` as the same shape of identity for the
  events themselves; instantiating the first at the target set `{true}` at every index lands on
  the second, with no σ-algebra bookkeeping.
* `infinitePi_map_eval` is declared inside `namespace MeasureTheory.Measure`, so this file opens
  `MeasureTheory Measure ProbabilityTheory`, as `InfinitePi.lean` itself does.
* `PMF.toMeasure_apply_eq_toOuterMeasure_apply` takes its `PMF` as an explicit argument before the
  `MeasurableSet` hypothesis, so it is called with dot notation.

## What this is, and what it deliberately is not

`IntrusionDetectionReach.lean` proves a plain reachability fact: `P[F healthy] = 1` from either
state, a `bwInd`/`lfp`-shaped rPATL claim. This file proves the stronger, LTL-shaped claim:
`healthy` is visited *infinitely often*, almost surely -- `P[G F healthy] = 1` -- against a
specific class of attacker: **oblivious**, meaning the attacker's round-`n` action may be
adversarially chosen per round (even a different distribution at every round), but *not* as a
function of the realized history so far. A fully **adaptive** attacker (one whose round-`n` choice
can react to everything that happened in rounds `1..n-1`) is a strictly harder, separate claim,
needing the Ionescu-Tulcea construction (`Mathlib.Probability.Kernel.IonescuTulcea.Traj`) and
Lévy's generalized Borel-Cantelli lemma (`MeasureTheory.ae_mem_limsup_atTop_iff`) in place of the
machinery this file uses; it is not attempted here. Nor does this file need the general
concurrent-Büchi-game machinery (nested `gfp(lfp(...))` fixed points, as in `BuchiOp.lean`): the
uniform defender strategy established in `IntrusionDetectionReach.lean` makes this a classical
independence argument, not a game-theoretic fixed-point one.

## The construction

Each round independently draws a defender action, uniformly, and an attacker action from whatever
distribution `q n` an adversary fixes in advance for round `n`, combined into a `PMF` over
`PolicyAction × AttackAction` via the same monadic `bind`/`map` idiom `idsK` itself already uses.
`MeasureTheory.Measure.infinitePi` turns the resulting countable family of per-round measures into a
single measure on the space of entire plays, `ℕ → PolicyAction × AttackAction`, and
`ProbabilityTheory.iIndepFun_infinitePi` confirms that any per-round functions of the individual
coordinates are mutually independent under it -- exactly the "moves are simultaneous and independent
each round" fact a `CSG`'s own definition already assumes, now made explicit at the level of an
actual probability space rather than a one-step expectation.

## The key fact, worked out by hand first

`idsNext`'s own structure (already exploited in `IntrusionDetectionReach.lean`): for *every* fixed
attacker action `a2`, exactly one of the two defender actions makes `idsNext a1 a2 = healthy` and
the other makes it `compromised` (`idsNext (D1,A1) = healthy`, `idsNext (D2,A1) = compromised`;
`idsNext (D1,A2) = compromised`, `idsNext (D2,A2) = healthy`). So if `a1` is drawn uniformly,
independently of `a2`, then for *any* distribution over `a2` whatsoever -- adversarial,
round-varying, whatever -- `P(idsNext a1 a2 = healthy) = (1/2)(q n .attack1) + (1/2)(q n .attack2)
= 1/2`, since a
`PMF` over a two-element type always has its two values summing to `1`. That makes "healthy at round
`n`" a family of independent events (functions of the disjoint, independent per-round coordinates of
`idsPlayMeasure`), each with probability exactly `1/2` -- precisely the hypotheses of the classical
second Borel-Cantelli lemma, `ProbabilityTheory.measure_limsup_eq_one`: independent events whose
probabilities sum to infinity occur infinitely often, almost surely.
-/

namespace Csg

open MeasureTheory Measure ProbabilityTheory

/-- Discrete measurable-space structure on the three finite IDS types -- nothing in this project has
    needed `Measure`/`MeasurableSpace` before now (`IntrusionDetection.lean`'s `idsK` stays at the
    raw-`PMF` level throughout, no `.toMeasure` conversion), so these are new. Every subset of a
    finite type is a valid choice of "measurable set," the standard discrete structure. -/
instance : MeasurableSpace IDSState := ⊤
instance : MeasurableSpace PolicyAction := ⊤
instance : MeasurableSpace AttackAction := ⊤

instance : DiscreteMeasurableSpace IDSState := ⟨fun _ => trivial⟩
instance : DiscreteMeasurableSpace PolicyAction := ⟨fun _ => trivial⟩
instance : DiscreteMeasurableSpace AttackAction := ⟨fun _ => trivial⟩

variable (q : ℕ → PMF AttackAction)

/-- Round `n`'s joint action distribution against an oblivious attacker sequence `q`: the defender
    uniform over `PolicyAction`, drawn independently of the attacker's own `q n`. Built with the
    same monadic `bind`/`map` idiom `idsK` itself already uses. -/
noncomputable def idsRoundPMF (n : ℕ) : PMF (PolicyAction × AttackAction) :=
  (PMF.uniformOfFintype PolicyAction).bind fun a1 => (q n).map fun a2 => (a1, a2)

/-- The whole play against `q`: independent per-round joint-action draws, combined into a single
    measure on entire plays via `Measure.infinitePi`. -/
noncomputable def idsPlayMeasure : Measure (ℕ → PolicyAction × AttackAction) :=
  Measure.infinitePi fun n => (idsRoundPMF q n).toMeasure

instance idsPlayMeasure_isProbabilityMeasure : IsProbabilityMeasure (idsPlayMeasure q) := by
  unfold idsPlayMeasure
  infer_instance

/-- Whether a round's outcome is `healthy`, as a function of *that round's own joint action alone*
    -- the same map at every round, since `idsNext` doesn't depend on the round number, only on
    the actions played in it. This is the shape `iIndepFun_infinitePi` actually wants: a per-factor
    function `Ω_i → 𝓧`, not one that already bakes in its own coordinate projection (the first
    draft's mistake -- see the module docstring). -/
def idsRoundHealthy (p : PolicyAction × AttackAction) : Bool :=
  decide (idsNext p.1 p.2 = .healthy)

theorem idsRoundHealthy_measurable : Measurable idsRoundHealthy :=
  Measurable.of_discrete

/-- **Independence.** `iIndepFun_infinitePi`, instantiated at the constant per-round map
    `idsRoundHealthy`, gives independence of the family `fun n ω => idsRoundHealthy (ω n)`
    directly -- `X` is passed explicitly (named), matching how the lemma is used in its own
    source file rather than leaving it to be inferred. -/
theorem idsPlay_indepFun_healthy :
    iIndepFun (fun n (ω : ℕ → PolicyAction × AttackAction) => idsRoundHealthy (ω n))
      (idsPlayMeasure q) :=
  iIndepFun_infinitePi (X := fun (_ : ℕ) => idsRoundHealthy) fun _ => idsRoundHealthy_measurable

/-- **The key fact.** `P(round n = healthy) = 1/2`, for *any* oblivious attacker sequence `q` -- the
    hand computation from the module docstring, now as a genuine `PMF`/outer-measure identity. The
    `Finset.univ = {.defend1, .defend2}` rewrites are a self-contained way to unfold a two-element
    `Fintype` sum without depending on whether `IntrusionDetection.lean`'s own `policyAction_sum`/
    `attackAction_sum` helpers are stated generically enough for `ℝ≥0∞` (they were written for `ℝ`
    payoffs; safer not to assume here). -/
theorem idsRoundPMF_healthy (n : ℕ) :
    (idsRoundPMF q n).toOuterMeasure {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy}
      = 1 / 2 := by
  have huniv :
      (Finset.univ : Finset PolicyAction) = {PolicyAction.defend1, PolicyAction.defend2} := by
    decide
  have huniv2 :
      (Finset.univ : Finset AttackAction) = {AttackAction.attack1, AttackAction.attack2} := by
    decide
  have huniform : ∀ a1 : PolicyAction, (PMF.uniformOfFintype PolicyAction) a1 = 1 / 2 := by
    intro a1
    rw [PMF.uniformOfFintype_apply]
    norm_num [show Fintype.card PolicyAction = 2 from by decide]
  have hD1 : (PMF.map (fun a2 => (PolicyAction.defend1, a2)) (q n)).toOuterMeasure
      {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} = q n .attack1 := by
    rw [PMF.toOuterMeasure_map_apply]
    have hpre : (fun a2 => (PolicyAction.defend1, a2)) ⁻¹'
        {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} =
        {AttackAction.attack1} := by
      ext a2; cases a2 <;> simp [idsNext]
    rw [hpre, PMF.toOuterMeasure_apply_singleton]
  have hD2 : (PMF.map (fun a2 => (PolicyAction.defend2, a2)) (q n)).toOuterMeasure
      {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} = q n .attack2 := by
    rw [PMF.toOuterMeasure_map_apply]
    have hpre : (fun a2 => (PolicyAction.defend2, a2)) ⁻¹'
        {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} =
        {AttackAction.attack2} := by
      ext a2; cases a2 <;> simp [idsNext]
    rw [hpre, PMF.toOuterMeasure_apply_singleton]
  have hsum : (q n) .attack1 + (q n) .attack2 = 1 := by
    have htotal := (q n).tsum_coe
    rwa [tsum_fintype, huniv2, Finset.sum_insert (by decide), Finset.sum_singleton] at htotal
  unfold idsRoundPMF
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, huniv,
    Finset.sum_insert (by decide), Finset.sum_singleton, huniform, huniform, hD1, hD2, ← mul_add,
    hsum, mul_one]

/-- The `.toOuterMeasure` fact above, transported to `idsPlayMeasure`'s own coordinate-`n` marginal
    via `infinitePi_map_eval` (the marginal of an infinite product measure at any one coordinate is
    exactly that coordinate's own factor measure) and the standard `PMF.toMeasure`/`toOuterMeasure`
    coincidence on measurable sets. -/
theorem idsRoundHealthy_measure_true (n : ℕ) :
    (idsPlayMeasure q) {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true}
      = 1 / 2 := by
  have hSet : {p : PolicyAction × AttackAction | idsRoundHealthy p = true} =
      {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} := by
    ext p; simp [idsRoundHealthy]
  have hT : MeasurableSet {p : PolicyAction × AttackAction | idsRoundHealthy p = true} :=
    MeasurableSet.of_discrete
  have heq : {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true} =
      (fun x : ℕ → PolicyAction × AttackAction => x n) ⁻¹'
        {p : PolicyAction × AttackAction | idsRoundHealthy p = true} := rfl
  rw [heq, ← Measure.map_apply (measurable_pi_apply n) hT]
  unfold idsPlayMeasure
  rw [infinitePi_map_eval, (idsRoundPMF q n).toMeasure_apply_eq_toOuterMeasure_apply hT, hSet,
    idsRoundPMF_healthy]

/-- Restating `idsPlay_indepFun_healthy` as independence of the *events* `{healthy at round n}`, the
    shape `measure_limsup_eq_one` expects. **The one genuine gap flagged before this file's first
    build attempt** (see the module docstring): no single ready-made Mathlib lemma performs exactly
    this `iIndepFun → iIndepSet` conversion (confirmed again by reading
    `Probability/Independence/Basic.lean` directly). Rather than the original comap/`generateFrom`
    attempt, this instead restates both sides as the *same* measure-of-intersection identity --
    `iIndepFun_iff_measure_inter_preimage_eq_mul` for the hypothesis, `iIndepSets_singleton_iff`
    (via `iIndepSet_iff_iIndepSets_singleton`) for the goal -- and instantiates the former's
    per-index target set at the constant `{true}`, landing exactly on the latter. -/
theorem idsPlay_indepSet_healthy :
    iIndepSet (fun n => {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true})
      (idsPlayMeasure q) := by
  have hmeas : ∀ n, MeasurableSet
      {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true} := fun n =>
    (idsRoundHealthy_measurable.comp (measurable_pi_apply n)) (measurableSet_singleton true)
  rw [iIndepSet_iff_iIndepSets_singleton hmeas, iIndepSets_singleton_iff]
  intro t
  have h := idsPlay_indepFun_healthy q
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  exact h t (sets := fun _ => ({true} : Set Bool)) fun _ _ => measurableSet_singleton true

/-- **The headline result.** Against any oblivious attacker sequence `q`, `healthy` is visited
    infinitely often, almost surely -- the LTL-shaped recurrence claim
    `IntrusionDetectionReach.lean`'s own docstring named and deliberately left open. -/
theorem idsGameCSG_healthy_infinitely_often :
    (idsPlayMeasure q)
      (Filter.limsup (fun n => {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true})
        Filter.atTop) = 1 := by
  apply measure_limsup_eq_one
  · exact fun n => (idsRoundHealthy_measurable.comp (measurable_pi_apply n))
      (measurableSet_singleton true)
  · exact idsPlay_indepSet_healthy q
  · simp only [idsRoundHealthy_measure_true q]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)

end Csg
