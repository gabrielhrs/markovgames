/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.BuchiOp

/-!
# Qualitative winning regions: sure mode

**Status: confirmed by a clean `lake build`.** Two small general lemmas (`G safe ⊆ safe`,
`b ⊆ SF b`, each read straight off `map_gfp`/`map_lfp`'s fixed-point equation) support
`Csg.SkirmishProperties`'s worked instances. Following L. de Alfaro
and T. Henzinger, "Concurrent Omega-Regular Games," LICS 2000, and ported directly from the
already-implemented, already-validated Java in
`prism-games`'s `explicit/CSGModelChecker.java` (methods `G`, `SF`, `SFG`, `SGF`, read directly off
that file rather than re-derived from the paper from scratch).

**Why this file, and its two siblings, exist.** The qualitative line was originally split into
four files (`QualitativeAlgorithms`/`QualitativeReachability`/`QualitativeRecurrence`/
`QualitativeLimitRecurrence`) named for *when* each fixed-point shape was built during
development, not for the axis the paper itself organises around: three *modes* -- sure,
almost-sure, limit-sure -- each computing the same four objective shapes (safety `G`, reachability
`F`, co-Büchi `FG`, Büchi `GF`). This file and its two siblings (`QualitativeAlmostSure.lean`,
`QualitativeLimitSure.lean`, importing in that order) now split along the mode axis instead. This
file is everything sure mode needs and nothing else, relocated line-for-line from its old home in
`QualitativeAlgorithms.lean` (`Pre1`, `G`, `SF`, `SFG`, `SGF`; the almost-sure combinators `A`/`B`
and `Apre1`/`AGF` that used to share that file moved to `QualitativeAlmostSure.lean`).

**Representation choice.** Winning regions live in `Set S` rather than `S → Set.Icc (0:ℝ) 1`:
`Set S` is a `CompleteBooleanAlgebra` (hence a `CompleteLattice`) unconditionally in Mathlib --
confirmed directly against the cached source (`Mathlib/Data/Set/Semiring.lean`'s own
`inferInstanceAs <| CompleteBooleanAlgebra (Set α)`) -- so `OrderHom.lfp`/`.gfp` apply to
`Set S →o Set S` for free, the same free existence every other file in `Csg/` already relies on for
its own ambient lattice. `Set.le_eq_subset` is a `rfl` in this Mathlib version (it is even marked
`deprecated "This is now a syntactic equality"`), so `≤` and `⊆` are interchangeable everywhere
below with no explicit conversion lemma needed.

Sure mode needs no probabilistic representation at all: it works directly off `CSG`'s own
`K : S → A1 → A2 → PMF S` via `PMF.support` (`p.support ⊆ x` is exactly "probability 1 of landing
in `x`," confirmed directly against `Mathlib/Probability/ProbabilityMassFunction/Basic.lean`'s own
`toMeasure_apply_eq_one_iff : p.toMeasure s = 1 ↔ p.support ⊆ s`), and every fixed-point shape
below already exists almost verbatim elsewhere in this project.

**The Java-to-Lean correspondence**, method by method:
* `pre1(mdist,x)` (∃ row ∀ col, support ⊆ x) becomes `Pre1 (x : Set S) : Set S`, direct off `C.K`.
* `G(csg,b)` = νX.(`Pre1`(X) ∧ b) becomes `G`, a single `gfp` (`GOrderHom`/`G`), the exact mirror of
  `safetyOp`.
* `SF(csg,b)` = μX.(`Pre1`(X) ∨ b) becomes `SF`, a single `lfp` (`SFOrderHom`/`SF`), the mirror of
  `reachOp`.
* `SFG(csg,b) = SF(csg, G(csg,b))` becomes `SFG b := C.SF (C.G b)` verbatim, no new fixed point.
* `SGF` (the coupled νY.μX) becomes `SGF`, built from `SGFInner`/`SGFOuter` exactly as `buchiOp`
  is built from `buchiInnerOp` plus `OrderHom.lfp_mono_of_le`.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-! ## Sure mode: no probability, just support-level certainty -/

/-- The sure one-step predecessor (`pre1` in the Java): `s` is a `Pre1 x`-state if the row player
    has *some* action `a1` that, against *every* column response `a2`, is guaranteed (the outcome's
    support lies entirely in `x`) to land in `x` -- no probability anywhere, `PMF.support ⊆ x` is
    exactly "probability 1," so this is outright certainty regardless of the actual transition
    probabilities. -/
noncomputable def Pre1 (x : Set S) : Set S := {s | ∃ a1, ∀ a2, (C.K s a1 a2).support ⊆ x}

/-- **The payoff.** `Pre1` is monotone: a wider target `x` only makes "support ⊆ x" easier, for the
    same witnessing row action. -/
theorem Pre1_mono : Monotone C.Pre1 := by
  intro x1 x2 hx s hs
  obtain ⟨a1, ha1⟩ := hs
  exact ⟨a1, fun a2 => (ha1 a2).trans hx⟩

/-- `G`'s one-step operator, bundled as an `OrderHom`: `X ↦ Pre1(X) ∩ safe` -- `Pre1_mono` plus the
    trivial monotonicity of intersecting with a fixed set. -/
noncomputable def GOrderHom (safe : Set S) : Set S →o Set S where
  toFun x := C.Pre1 x ∩ safe
  monotone' := by
    intro x1 x2 hx s hs
    exact ⟨C.Pre1_mono hx hs.1, hs.2⟩

/-- **The payoff.** Sure-mode safety (`G` in the Java): the greatest fixed point of `GOrderHom`,
    the states from which the row player can force staying in `safe` forever, with certainty.
    Exactly `safetyOp`'s own `.gfp`, with `Pre1` standing in for `stageValue`. -/
noncomputable def G (safe : Set S) : Set S := (C.GOrderHom safe).gfp

/-- **The payoff.** `G safe` always sits inside `safe` itself: unfold `GOrderHom safe`'s own
    fixed-point equation (`map_gfp`) and discard the `Pre1`-conjunct, since intersecting with
    `safe` bounds the image regardless of the argument. General infrastructure for worked
    instances -- e.g. showing a *singleton* candidate is not `G`-forceable reduces to showing the
    singleton's own `Pre1`-membership fails, once this bounds `G` inside it first. -/
theorem G_subset (safe : Set S) : C.G safe ⊆ safe := by
  intro s hs
  have h : C.GOrderHom safe (C.G safe) = C.G safe := (C.GOrderHom safe).map_gfp
  rw [← h] at hs
  exact hs.2

/-- `SF`'s one-step operator, bundled as an `OrderHom`: `X ↦ Pre1(X) ∪ b`. -/
noncomputable def SFOrderHom (b : Set S) : Set S →o Set S where
  toFun x := C.Pre1 x ∪ b
  monotone' := by
    intro x1 x2 hx s hs
    rcases hs with h | h
    · exact Or.inl (C.Pre1_mono hx h)
    · exact Or.inr h

/-- **The payoff.** Sure-mode reachability (`SF` in the Java): the least fixed point of
    `SFOrderHom`, the states from which the row player can force reaching `b`, with certainty.
    Exactly `reachOp`'s own `.lfp`, with `Pre1` standing in for `stageValue`. -/
noncomputable def SF (b : Set S) : Set S := (C.SFOrderHom b).lfp

/-- **The payoff, dual to `G_subset`.** `b` always sits inside `SF b`: unfold `SFOrderHom b`'s own
    fixed-point equation (`map_lfp`) and discard the `Pre1`-disjunct, since unioning with `b`
    bounds the image from below regardless of the argument. Makes "already inside `b`" a trivial
    corollary of `SF`/`SFG` -- reaching (or eventually always holding) a set you already occupy
    needs no strategy at all. -/
theorem subset_SF (b : Set S) : b ⊆ C.SF b := by
  intro s hs
  have h : C.SFOrderHom b (C.SF b) = C.SF b := (C.SFOrderHom b).map_lfp
  rw [← h]
  exact Or.inr hs

/-- **The payoff.** Sure-mode co-Büchi (`SFG` in the Java): reusing `SF` and `G` directly, no new
    fixed point -- "eventually always `b`" is exactly sure-reaching the maximal `b`-invariant,
    computed once (`G`) and fed into a single sure-reachability call (`SF`), matching the Java's own
    `SFG(csg,b) = SF(csg, G(csg,b))` verbatim. -/
noncomputable def SFG (b : Set S) : Set S := C.SF (C.G b)

/-- `SGF`'s **inner** (`μX`) step, for a fixed outer candidate `y`: a `b`-state plays `Pre1` against
    `y` (having just reached `b`, one more step is owed before the condition is satisfied again);
    a non-`b` state plays `Pre1` against the inner continuation `x`. Exactly `buchiInnerOpFun` with
    `stageValue` replaced by `Pre1`. -/
noncomputable def SGFInnerFun (b y x : Set S) : Set S := (C.Pre1 x ∩ bᶜ) ∪ (C.Pre1 y ∩ b)

/-- **The payoff.** `SGFInnerFun` is monotone in the inner continuation `x`, for fixed `b`/`y`. -/
theorem SGFInnerFun_mono (b y : Set S) : Monotone (C.SGFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Pre1_mono hx h.1, h.2⟩
  · exact Or.inr h

/-- The inner Bellman step, bundled as an `OrderHom` for a fixed outer candidate `y` --
    `SGFInnerFun` plus its own monotonicity, exactly `buchiInnerOp`'s own pattern. -/
noncomputable def SGFInner (b y : Set S) : Set S →o Set S where
  toFun := C.SGFInnerFun b y
  monotone' := C.SGFInnerFun_mono b y

/-- **The payoff.** `SGFInnerFun` is *also* monotone in the outer candidate `y`, for any fixed
    inner continuation `x` -- exactly `buchiInnerOpFun_mono_y`'s own shape, needed to bundle the
    outer (`νY`) level via `OrderHom.lfp_mono_of_le`. -/
theorem SGFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.SGFInnerFun b y1 x ≤ C.SGFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨C.Pre1_mono hy h.1, h.2⟩

/-- **The payoff.** The `SGF` Bellman operator, `Y ↦ μX.SGFInnerFun b Y X`, bundled as an
    `OrderHom` on `Set S` via `OrderHom.lfp_mono_of_le` applied to `SGFInnerFun_mono_y` -- imported
    unchanged from `Csg.BuchiOp`, no re-proof needed. -/
noncomputable def SGFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.SGFInner b y).lfp
  monotone' := fun y1 y2 hy => OrderHom.lfp_mono_of_le (fun x => C.SGFInnerFun_mono_y b hy x)

/-- **The payoff.** Sure-mode Büchi (`SGF` in the Java): the greatest fixed point of `SGFOuter`,
    the states from which the row player can force visiting `b` infinitely often, with certainty.
    The one sure-mode operator needing the coupled `νY.μX` attractor-of-attractor construction,
    exactly as genuine "infinitely often" needs for `buchiOp` itself. -/
noncomputable def SGF (b : Set S) : Set S := (C.SGFOuter b).gfp

end CSG
end Csg
