/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Basic

/-!
# Support, rationally

**Status: confirmed by a clean `lake build`.**

The one place the qualitative line touches a probability. `PMF.support` is the single primitive
every qualitative operator in `Csg/` rests on:

* `Csg/QualitativeSure.lean`'s `Pre1 x = {s | ∃ a1, ∀ a2, (K s a1 a2).support ⊆ x}`;
* `Csg/QualitativeAlmostSure.lean`'s `A v2 y s = {a1 | ∀ a2, a2 ∈ v2 ∨ (K s a1 a2).support ⊆ y}`
  and `B v1 x s = {a2 | ∃ a1 ∈ v1, ((K s a1 a2).support ∩ x).Nonempty}`;
* `Csg/QualitativeLimitSure.lean`'s `LW`/`Lpre1`, nested fixed points over `Set A1` built from `A`
  and `B`.

Everything else in that line is set operations, quantifiers over `Fintype`s, and fixed points;
none of it calls `MatrixGame.value`, and there is no linear programming anywhere in it. So the
whole of what a rational game has to supply is its support, as data, together with the fact that it
is the support of the game it denotes. This file supplies both:

* `supportF G s a1 a2 : Finset S`, the states a kernel row gives nonzero weight;
* `toCSG_support`, which says the cast game's `PMF` support is `supportF` under `Finset.coe`.

`toCSG_support` is the hypothesis `Comp/QualBridge.lean` asks for, so the operators of
`Comp/QualOps.lean` applied to `G.supportF` are the operators of `G.toCSG h`, with nothing further
to prove per operator.

`supportF` filters every state with a rational comparison. A caller with a cheaper description of
the same sets -- a table, or the keys of a sparse distribution -- proves it equal to `supportF`
once and runs the operators on that instead.
-/

namespace Comp

open Csg

namespace CsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

/-! ## Support, as a decidable set -/

/-- The support of a rational kernel row: the states it gives nonzero weight. Decidable, unlike
    `PMF.support`, whose membership is a disequality in `ℝ≥0∞`. -/
def supportQ (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) : Set S :=
  {s' | G.K s a1 a2 s' ≠ 0}

instance (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) :
    DecidablePred (· ∈ G.supportQ s a1 a2) := fun _ => by
  unfold supportQ
  infer_instance

/-- **The bridge.** The cast game's `PMF` support is exactly the rational support. This is the only
    place the qualitative line touches `PMF` at all.

    `ENNReal.ofReal x = 0 ↔ x ≤ 0`, so nonzero mass means a strictly positive rational weight, which
    given `WellFormed`'s nonnegativity is the same as a nonzero one. -/
theorem toPMF_support (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    (G.toPMF h s a1 a2).support = G.supportQ s a1 a2 := by
  ext s'
  have happ : G.toPMF h s a1 a2 s' = ENNReal.ofReal ((G.K s a1 a2 s' : ℚ) : ℝ) := by
    unfold toPMF
    rw [PMF.ofFintype_apply]
  have hnn : (0 : ℚ) ≤ G.K s a1 a2 s' := h.1 s a1 a2 s'
  simp only [PMF.mem_support_iff, supportQ, Set.mem_ofPred_eq, happ, ne_eq,
    ENNReal.ofReal_eq_zero, not_le]
  constructor
  · intro hpos
    have hq : (0 : ℚ) < G.K s a1 a2 s' := by exact_mod_cast hpos
    exact hq.ne'
  · intro hne
    have hq : (0 : ℚ) < G.K s a1 a2 s' := lt_of_le_of_ne hnn (Ne.symm hne)
    exact_mod_cast hq

/-! ## Support, as data -/

/-- The support of a rational kernel row as a `Finset`: `supportQ` with the states collected rather
    than merely testable. Computable, since it touches nothing but the rational table `G.K`. -/
def supportF (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) : Finset S :=
  Finset.univ.filter fun s' => G.K s a1 a2 s' ≠ 0

/-- `supportF` is `supportQ` under `Finset.coe`. -/
@[simp]
theorem coe_supportF (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) :
    (↑(G.supportF s a1 a2) : Set S) = G.supportQ s a1 a2 := by
  ext s'
  simp [supportF, supportQ]

@[simp]
theorem mem_supportF (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) (s' : S) :
    s' ∈ G.supportF s a1 a2 ↔ G.K s a1 a2 s' ≠ 0 := by
  simp [supportF]

/-- **`supportF` is the support of the game `G` denotes.** `toPMF_support` composed with
    `coe_supportF`, and the form `Comp/QualBridge.lean` takes as its hypothesis. -/
theorem toCSG_support (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    ((G.toCSG h).K s a1 a2).support = (↑(G.supportF s a1 a2) : Set S) := by
  rw [coe_supportF]
  exact toPMF_support G h s a1 a2

end CsgQ

end Comp
