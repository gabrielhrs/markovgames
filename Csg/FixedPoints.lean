/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mathlib.Order.FixedPoints

/-!
# Fixed points of monotone maps: the lattice-level lemmas

**Status: confirmed by a clean `lake build`.** Facts about `OrderHom.lfp` and `OrderHom.gfp` for a
monotone self-map `f` of an arbitrary `CompleteLattice`, with no `CSG` in the statements or the
proofs. The value operators (`ReachOp.lean`, `SafetyOp.lean`, `BuchiOp.lean`, `CoBuchiOp.lean`) and
the qualitative ones (`QualitativeSure.lean` and its two successors) all sit on these, and neither
family needs the other. Everything is declared in Mathlib's `OrderHom` namespace, so that
`f.lfp_eq_of_certificate …` reads like the Mathlib lemmas it is built from.

Three groups.

* **Monotone in the operator.** `lfp_mono_of_le`, `gfp_mono_of_le`: if `f ≤ g` pointwise then
  `f.lfp ≤ g.lfp` and `f.gfp ≤ g.gfp`. Mathlib bundles `OrderHom.lfp` and `OrderHom.gfp` as
  monotone maps `(α →o α) →o α`, which is this fact; the two lemmas here state it with the
  hypothesis in the pointwise form `∀ a, f a ≤ g a`, which is how a nested fixed point supplies
  it (the inner operator, monotone in the outer variable).
* **Certificates.** `lfp_eq_of_certificate`, `gfp_eq_of_certificate` pin a fixed point to a
  candidate; `lfp_mem_Icc_of_certificate`, `gfp_mem_Icc_of_certificate` enclose it between two
  candidates under weaker, one-sided hypotheses. Each is an assembly of Knaster-Tarski's pinning
  lemmas (`lfp_le`, `le_lfp`, `le_gfp`, `gfp_le`); discharging the hypotheses for a model is the
  work, and stays with the model.
* **Two steps from the end.** `gfp_le_map_map_top`: `f.gfp ≤ f (f ⊤)`. `map_map_bot_le_lfp`:
  `f (f ⊥) ≤ f.lfp`. No continuity hypothesis; these bound a fixed point by two hand-computed
  iterates when the exact value is not needed.
-/

/-! ## Monotone in the operator -/

/-- `OrderHom.lfp` is monotone in the operator: if `f ≤ g` pointwise, then `f.lfp ≤ g.lfp`. This is
    the monotonicity of Mathlib's bundled `OrderHom.lfp : (α →o α) →o α`, with `f ≤ g` unfolded to
    `∀ a, f a ≤ g a`. -/
theorem OrderHom.lfp_mono_of_le {α : Type*} [CompleteLattice α] {f g : α →o α}
    (h : ∀ a, f a ≤ g a) : f.lfp ≤ g.lfp :=
  (OrderHom.lfp : (α →o α) →o α).monotone (show f ≤ g from h)

/-- `OrderHom.gfp` is monotone in the operator: if `f ≤ g` pointwise, then `f.gfp ≤ g.gfp`. The
    dual of `lfp_mono_of_le`, from the bundled `OrderHom.gfp`. -/
theorem OrderHom.gfp_mono_of_le {α : Type*} [CompleteLattice α] {f g : α →o α}
    (h : ∀ a, f a ≤ g a) : f.gfp ≤ g.gfp :=
  (OrderHom.gfp : (α →o α) →o α).monotone (show f ≤ g from h)

/-! ## Certificates -/

/-- A candidate `v` that is an exact fixed point of `f`, and that lower-bounds every pre-fixed
    point of `f`, *is* `f`'s least fixed point: `lfp_le_fixed` and `le_lfp` assembled by
    `le_antisymm`. -/
theorem OrderHom.lfp_eq_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α) (v : α)
    (hfixed : f v = v) (hlb : ∀ b, f b ≤ b → v ≤ b) : f.lfp = v :=
  le_antisymm (f.lfp_le_fixed hfixed) (f.le_lfp hlb)

/-- The dual of `lfp_eq_of_certificate`: a candidate `v` that is an exact fixed point of `f`, and
    that upper-bounds every post-fixed point of `f` (`b ≤ f b`), *is* `f`'s greatest fixed
    point. -/
theorem OrderHom.gfp_eq_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α) (v : α)
    (hfixed : f v = v) (hub : ∀ b, b ≤ f b → b ≤ v) : f.gfp = v :=
  le_antisymm (f.gfp_le hub) (f.le_gfp hfixed.ge)

/-- A lower bound `lo` over every pre-fixed point, together with an upper candidate `hi` that is
    itself a pre-fixed point (`f hi ≤ hi`, weaker than the exact certificate's `f hi = hi`),
    encloses `f.lfp`. The two conclusions are independent inequalities, `le_lfp` and `lfp_le`. -/
theorem OrderHom.lfp_mem_Icc_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α)
    (lo hi : α) (hlb : ∀ b, f b ≤ b → lo ≤ b) (hpre : f hi ≤ hi) :
    lo ≤ f.lfp ∧ f.lfp ≤ hi :=
  ⟨f.le_lfp hlb, f.lfp_le hpre⟩

/-- The dual of `lfp_mem_Icc_of_certificate`: a post-fixed-point lower candidate `lo`
    (`lo ≤ f lo`) together with an upper bound `hi` over every post-fixed point encloses
    `f.gfp`. -/
theorem OrderHom.gfp_mem_Icc_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α)
    (lo hi : α) (hpost : lo ≤ f lo) (hub : ∀ b, b ≤ f b → b ≤ hi) :
    lo ≤ f.gfp ∧ f.gfp ≤ hi :=
  ⟨f.le_gfp hpost, f.gfp_le hub⟩

/-! ## Two steps from the end -/

/-- `f.gfp ≤ f (f ⊤)` for any monotone `f`: Mathlib's `gfp_le_map` twice, starting from
    `f.gfp ≤ ⊤`. An upper bound on a greatest fixed point from two iterates down from `⊤`, with no
    `ωScottContinuous` hypothesis (contrast `OrderHom.gfp_eq_sInf_iterate`). -/
theorem OrderHom.gfp_le_map_map_top {α : Type*} [CompleteLattice α] (f : α →o α) :
    f.gfp ≤ f (f ⊤) :=
  f.gfp_le_map (f.gfp_le_map le_top)

/-- `f (f ⊥) ≤ f.lfp` for any monotone `f`: Mathlib's `map_le_lfp` twice, starting from
    `⊥ ≤ f.lfp`. A lower bound on a least fixed point from two iterates up from `⊥`, which is what
    showing membership in a `gfp`-of-`lfp` construction needs. -/
theorem OrderHom.map_map_bot_le_lfp {α : Type*} [CompleteLattice α] (f : α →o α) :
    f (f ⊥) ≤ f.lfp :=
  f.map_le_lfp (f.map_le_lfp bot_le)
