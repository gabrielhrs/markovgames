/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Basic
import Csg.QualitativeSure

/-!
# The qualitative line, rationally: supports, `Pre1`, and exact fixed points

**Status: confirmed by a clean `lake build`.**

The foundation for executing the qualitative algorithms. Two things are established here: that
`PMF.support` -- the single primitive every qualitative operator rests on -- has a decidable
rational counterpart, and that on these finite lattices a stabilised iterate can be pinned to the
fixed point *exactly*.

**Why `support` is the whole foundation.** Unlike the quantitative operators, none of the
qualitative ones calls `MatrixGame.value`; they are combinatorial, and each bottoms out in the same
place:

* `Csg/QualitativeSure.lean`'s `Pre1 x = {s | ∃ a1, ∀ a2, (K s a1 a2).support ⊆ x}`;
* `Csg/QualitativeAlmostSure.lean`'s `A v2 y s = {a1 | ∀ a2, a2 ∈ v2 ∨ (K s a1 a2).support ⊆ y}`
  and `B v1 x s = {a2 | ∃ a1 ∈ v1, ((K s a1 a2).support ∩ x).Nonempty}`;
* `Csg/QualitativeLimitSure.lean`'s `LW`/`Lpre1`, which are nested fixed points over `Set A1` built
  from `A` and `B`.

Everything else is set operations, quantifiers over `Fintype`s, and fixed points. So there is no
linear programming anywhere in this line, and `supportQ` below is the only bridge it needs: once
support is decidable over `ℚ`, every operator above it is too.

**Why exactness is available here but not quantitatively.** `Comp/Iterate.lean` settles for an `ε`
bound because the Shapley fixed point is algebraic and generally irrational, so no rational iterate
is ever equal to it. Here the lattices (`Set S`, `Set A1`, `Set A2` over `Fintype`s) are finite, the
iteration really does stabilise, and stabilisation is a *decidable* observation. The two halves then
meet: a fixed point is pre-fixed, so `f.lfp ≤ a`; and an iterate from `⊥` satisfies `a ≤ f.lfp`
(`Comp/Reach.lean`'s `OrderHom.le_lfp_of_step`); together `a = f.lfp`. Dually from `⊤` for a `gfp`.
That is `eq_lfp_of_fixed_of_le`/`eq_gfp_of_fixed_of_ge` below, and it needs no theorem that the
iteration terminates within `|S|` steps -- only that one has *observed* it stop.

**Which side is cheap, again.** As in `Comp/Reach.lean`, the two directions are asymmetric and it
is easy to get backwards. For an `lfp` the fixed-point check gives the *upper* half for free and the
iterate chain supplies the lower; for a `gfp` it is the other way round. Neither needs the
universally-quantified minimality hypothesis that `Csg/IntervalCertificate.lean` asks for, because
the chain, not a certificate, carries that side.

**Not here:** the operators above `Pre1`. `A`, `B`, `LW`, `Lpre1`, and the `G`/`SF`/`LF` family are
the same pattern at increasing nesting depth -- a rational restatement, a decidability instance, and
a bridge each -- and they all reduce to `supportQ`. `LF` in particular is what pins the value-1 set
for probabilistic reachability, limit-sure being the correct notion there rather than almost-sure.
-/

/-- A fixed point that is also below `f.lfp` *is* `f.lfp`. The second hypothesis is what an iterate
    from `⊥` supplies (`OrderHom.le_lfp_of_step`); the first is a decidable check on a finite
    lattice. Together they pin a least fixed point exactly, with no minimality argument and no
    bound on how many steps stabilisation takes. -/
theorem OrderHom.eq_lfp_of_fixed_of_le {α : Type*} [CompleteLattice α] (f : α →o α) {a : α}
    (hfix : f a = a) (hle : a ≤ f.lfp) : a = f.lfp :=
  le_antisymm hle (f.lfp_le hfix.le)

/-- The dual: a fixed point that is also above `f.gfp` *is* `f.gfp`, the second hypothesis coming
    from an iterate downward from `⊤`. -/
theorem OrderHom.eq_gfp_of_fixed_of_ge {α : Type*} [CompleteLattice α] (f : α →o α) {a : α}
    (hfix : f a = a) (hge : f.gfp ≤ a) : a = f.gfp :=
  le_antisymm (f.le_gfp hfix.ge) hge

/-- One step preserves being above the greatest fixed point, so iterating down from `⊤` gives a
    chain of upper bounds on a `gfp`. The mirror of `Comp/Reach.lean`'s `OrderHom.le_lfp_of_step`,
    and what supplies `eq_gfp_of_fixed_of_ge`'s second hypothesis. -/
theorem OrderHom.gfp_le_of_step {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : f.gfp ≤ a) (hb : b = f a) : f.gfp ≤ b := by
  subst hb
  calc f.gfp = f f.gfp := f.map_gfp.symm
    _ ≤ f a := f.monotone ha

namespace Comp

open Csg

namespace CsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

/-! ## Support, rationally -/

/-- The support of a rational kernel row: the states it gives nonzero weight. Decidable, unlike
    `PMF.support`, whose membership is a disequality in `ℝ≥0∞`. -/
def supportQ (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) : Set S :=
  {s' | G.K s a1 a2 s' ≠ 0}

instance (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) :
    DecidablePred (· ∈ G.supportQ s a1 a2) := fun _ => by
  unfold supportQ
  infer_instance

/-- **The bridge.** The cast game's `PMF` support is exactly the rational support. This is the only
    place the qualitative line touches `PMF` at all, and everything above it works with `supportQ`.

    `ENNReal.ofReal x = 0 ↔ x ≤ 0`, so nonzero mass means a strictly positive rational weight, which
    given `WellFormed`'s nonnegativity is the same as a nonzero one. -/
theorem toPMF_support (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    (G.toPMF h s a1 a2).support = G.supportQ s a1 a2 := by
  ext s'
  have happ : G.toPMF h s a1 a2 s' = ENNReal.ofReal ((G.K s a1 a2 s' : ℚ) : ℝ) := by
    unfold toPMF
    rw [PMF.ofFintype_apply]
  have hnn : (0 : ℚ) ≤ G.K s a1 a2 s' := h.1 s a1 a2 s'
  simp only [PMF.mem_support_iff, supportQ, Set.mem_setOf_eq, happ, ne_eq,
    ENNReal.ofReal_eq_zero, not_le]
  constructor
  · intro hpos
    have hq : (0 : ℚ) < G.K s a1 a2 s' := by exact_mod_cast hpos
    exact hq.ne'
  · intro hne
    have hq : (0 : ℚ) < G.K s a1 a2 s' := lt_of_le_of_ne hnn (Ne.symm hne)
    exact_mod_cast hq

/-! ## `Pre1`, rationally -/

/-- The minimiser's controllable predecessor, rationally: the states from which the row player has
    an action keeping every column response inside `x`. Written with `supportQ` so that it is the
    same shape as `CSG.Pre1`, which makes the bridge below immediate.

    `A1` is the minimising side in this project's convention, so this is the *minimiser's* one-step
    operator -- which is what makes `G (goalᶜ)` the set from which the goal can be surely
    avoided. -/
def Pre1Q (G : CsgQ S A1 A2) (x : Set S) : Set S :=
  {s | ∃ a1, ∀ a2, G.supportQ s a1 a2 ⊆ x}

/-- `Pre1Q`'s membership, with the set inclusion spelled out as the quantifier it is. Stated
    separately because `Set.Subset` has to be unfolded before instance search can see a decidable
    proposition underneath. -/
theorem mem_Pre1Q_iff (G : CsgQ S A1 A2) (x : Set S) (s : S) :
    s ∈ G.Pre1Q x ↔ ∃ a1, ∀ a2, ∀ s', G.K s a1 a2 s' ≠ 0 → s' ∈ x := Iff.rfl

instance (G : CsgQ S A1 A2) (x : Set S) [DecidablePred (· ∈ x)] :
    DecidablePred (· ∈ G.Pre1Q x) := fun s =>
  decidable_of_iff (∃ a1, ∀ a2, ∀ s', G.K s a1 a2 s' ≠ 0 → s' ∈ x)
    (mem_Pre1Q_iff G x s).symm

/-- **The payoff.** The cast game's `Pre1` is exactly `Pre1Q` -- so the whole sure-mode fixed-point
    machinery of `Csg/QualitativeSure.lean` can be computed over `ℚ` and transported back.

    Immediate once the supports agree, because `Pre1Q` was written in `Pre1`'s own shape: the two
    differ only in how the kernel's support is expressed. -/
theorem Pre1_toCSG (G : CsgQ S A1 A2) (h : G.WellFormed) (x : Set S) :
    (G.toCSG h).Pre1 x = G.Pre1Q x := by
  ext s
  have hsup : ∀ a1 a2, ((G.toCSG h).K s a1 a2).support = G.supportQ s a1 a2 := fun a1 a2 =>
    toPMF_support G h s a1 a2
  simp only [CSG.Pre1, Pre1Q, Set.mem_setOf_eq, hsup]

/-- The sure-safety operator, rationally: `Pre1Q x ∩ safe`, matching `CSG.GOrderHom`'s own shape.
    Decidable whenever `safe` is, so a candidate for its greatest fixed point can be checked. -/
def GStepQ (G : CsgQ S A1 A2) (safe : Set S) (x : Set S) : Set S := G.Pre1Q x ∩ safe

instance (G : CsgQ S A1 A2) (safe x : Set S) [DecidablePred (· ∈ safe)]
    [DecidablePred (· ∈ x)] : DecidablePred (· ∈ G.GStepQ safe x) := fun _ => by
  unfold GStepQ
  infer_instance

/-- The cast game's `GOrderHom` agrees with `GStepQ` pointwise -- `Pre1_toCSG` intersected with
    `safe`. With this, a rationally-computed candidate for `G safe` can be checked for being a
    fixed point and, via `OrderHom.eq_gfp_of_fixed_of_ge` together with a chain of steps from `⊤`,
    identified with `G safe` exactly. -/
theorem GOrderHom_toCSG (G : CsgQ S A1 A2) (h : G.WellFormed) (safe x : Set S) :
    (G.toCSG h).GOrderHom safe x = G.GStepQ safe x := by
  change (G.toCSG h).Pre1 x ∩ safe = G.Pre1Q x ∩ safe
  rw [Pre1_toCSG G h x]

end CsgQ

end Comp
