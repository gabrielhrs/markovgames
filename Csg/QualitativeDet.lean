/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.QualitativeAlmostSure
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Deterministic games: the one-step operators without supports

**Status: confirmed by a clean `lake build`.** A game is *deterministic* when every transition is
a point mass: `C.K s a1 a2 = PMF.pure (next s a1 a2)` for a successor function `next`. The
qualitative one-step operators read only the support of `K`, and the support of a point mass is a
singleton, so for such a game each of them is a statement about `next` alone:

* `mem_Pre1`: `s ∈ C.Pre1 x ↔ ∃ a1, ∀ a2, next s a1 a2 ∈ x`
* `mem_A`: `a1 ∈ C.A v2 y s ↔ ∀ a2, a2 ∈ v2 ∨ next s a1 a2 ∈ y`
* `mem_B`: `a2 ∈ C.B v1 x s ↔ ∃ a1 ∈ v1, next s a1 a2 ∈ x`
* `mem_Apre1`: `s ∈ C.Apre1 x y ↔ ∀ a2, ∃ a1, (∀ a2', next s a1 a2' ∈ y) ∧ next s a1 a2 ∈ x`

For a concrete game on finite types, with a computable `next` and sets whose membership is
decidable, the right-hand sides are closed decidable propositions, so a one-step fact at given
sets is `rw` with one of these followed by `decide`. `SkirmishProperties.lean` uses them this way.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- `C` is deterministic with successor function `next`: every transition is the point mass at
    `next s a1 a2`. -/
def IsDet (next : S → A1 → A2 → S) : Prop :=
  ∀ s a1 a2, C.K s a1 a2 = PMF.pure (next s a1 a2)

namespace IsDet

variable {C} {next : S → A1 → A2 → S}

/-- The support of a deterministic transition is the singleton of its successor. -/
theorem support (h : C.IsDet next) (s : S) (a1 : A1) (a2 : A2) :
    (C.K s a1 a2).support = {next s a1 a2} := by
  rw [h s a1 a2]
  exact PMF.support_pure _

/-- "The support lies inside `x`" is "the successor is in `x`". -/
theorem support_subset_iff (h : C.IsDet next) {s : S} {a1 : A1} {a2 : A2} {x : Set S} :
    (C.K s a1 a2).support ⊆ x ↔ next s a1 a2 ∈ x := by
  rw [h.support s a1 a2]
  exact Set.singleton_subset_iff

/-- "The support meets `x`" is also "the successor is in `x`": for a point mass, landing in `x`
    surely and landing in `x` with positive probability coincide. -/
theorem support_inter_nonempty_iff (h : C.IsDet next) {s : S} {a1 : A1} {a2 : A2} {x : Set S} :
    ((C.K s a1 a2).support ∩ x).Nonempty ↔ next s a1 a2 ∈ x := by
  rw [h.support s a1 a2]
  exact Set.singleton_inter_nonempty

/-- `Pre1` for a deterministic game: some row action sends every column reply into `x`. -/
theorem mem_Pre1 (h : C.IsDet next) {x : Set S} {s : S} :
    s ∈ C.Pre1 x ↔ ∃ a1, ∀ a2, next s a1 a2 ∈ x := by
  change (∃ a1, ∀ a2, (C.K s a1 a2).support ⊆ x) ↔ ∃ a1, ∀ a2, next s a1 a2 ∈ x
  exact exists_congr fun a1 => forall_congr' fun a2 => h.support_subset_iff

/-- `A` for a deterministic game: every column reply is excused or sent into `y`. -/
theorem mem_A (h : C.IsDet next) {v2 : Set A2} {y : Set S} {s : S} {a1 : A1} :
    a1 ∈ C.A v2 y s ↔ ∀ a2, a2 ∈ v2 ∨ next s a1 a2 ∈ y := by
  change (∀ a2, a2 ∈ v2 ∨ (C.K s a1 a2).support ⊆ y) ↔ ∀ a2, a2 ∈ v2 ∨ next s a1 a2 ∈ y
  exact forall_congr' fun a2 => or_congr_right h.support_subset_iff

/-- `B` for a deterministic game: some row action in the pool sends this column reply into
    `x`. -/
theorem mem_B (h : C.IsDet next) {v1 : Set A1} {x : Set S} {s : S} {a2 : A2} :
    a2 ∈ C.B v1 x s ↔ ∃ a1 ∈ v1, next s a1 a2 ∈ x := by
  change (∃ a1 ∈ v1, ((C.K s a1 a2).support ∩ x).Nonempty) ↔ ∃ a1 ∈ v1, next s a1 a2 ∈ x
  exact exists_congr fun a1 => and_congr_right fun _ => h.support_inter_nonempty_iff

/-- `Apre1` for a deterministic game: against every column reply `a2` there is a row action that
    stays inside `y` whatever the column player does and that sends `a2` itself into `x`. This is
    `B (A ∅ y s) x s = Set.univ` read through `mem_B` and `mem_A`. -/
theorem mem_Apre1 (h : C.IsDet next) {x y : Set S} {s : S} :
    s ∈ C.Apre1 x y ↔ ∀ a2, ∃ a1, (∀ a2', next s a1 a2' ∈ y) ∧ next s a1 a2 ∈ x := by
  change C.B (C.A ∅ y s) x s = Set.univ ↔
    ∀ a2, ∃ a1, (∀ a2', next s a1 a2' ∈ y) ∧ next s a1 a2 ∈ x
  rw [Set.eq_univ_iff_forall]
  refine forall_congr' fun a2 => ?_
  rw [h.mem_B]
  refine exists_congr fun a1 => and_congr ?_ Iff.rfl
  rw [h.mem_A]
  exact forall_congr' fun a2' => or_iff_right (Set.mem_empty_iff_false a2').mp

end IsDet

end CSG
end Csg
