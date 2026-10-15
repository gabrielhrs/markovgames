/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Qualitative

/-!
# Qualitative regions as data: `Finset` iteration, and an exactly identified fixed point

**Status: confirmed by a clean `lake build`.**

`Comp/Qualitative.lean` makes membership in `Pre1Q` and `GStepQ` *decidable*. That is enough to ask
whether a given state lies in a given region, but not enough to **compute** a region: a `Set S` is
a function into `Prop`, so `f^[n] ⊥` is not something `#eval` can print, and the decidability
instances do not compose along an iteration by themselves. The fix is the obvious one -- carry the
region as data. This file re-runs the sure-mode line over `Finset S` and glues it back to the
`Set`-level development with `Finset.coe`.

**What that buys.** `gStepF` is a plain computable function `Finset S → Finset S`, so
`(G.gStepF safe)^[n] Finset.univ` is something `#eval` prints: run it until the printed set stops
changing. `G_eq_coe_of_fixed` then turns that observation into an *exact* identification of
`Csg/QualitativeSure.lean`'s real-valued `CSG.G` -- no `ε`, no approximation, and no theorem about
how many steps the iteration needs. Its two hypotheses are precisely the two halves discussed in
`Comp/Qualitative.lean`: `hiter` says the candidate *is* an iterate from `⊤`, which supplies
`gfp ≤ c` by one application of `OrderHom.gfp_le_of_step` per step, and `hfix` says it is a fixed
point, which supplies the other half for free because a post-fixed point lies above the `gfp`.

**Why `⊤` and not `⊥`.** `G safe` is a *greatest* fixed point, so the chain descends from
`Finset.univ`. For the reachability-shaped operators (`SF`, `AF`, and `LF`'s inner `μX`) it is the
other way round and the chain climbs from `∅`, with `Comp/Reach.lean`'s `OrderHom.le_lfp_of_step`
in place of `gfp_le_of_step`. Which of the two applies is fixed by whether the operator's answer is
a least or a greatest fixed point, and alternates with nesting depth.

**`DecidableEq S` appears in this file** and nowhere earlier in `Comp/`. `Finset` membership and
`⊆` need it; the `Set`-level instances of `Comp/Qualitative.lean` did not, `ℚ`'s own decidable
equality being enough to test a support condition one state at a time.

**Not here:** the `Finset` counterparts of `A`, `B`, `LW`, `Lpre1` and `LF`. They are this same
exercise at greater nesting depth -- `A` and `B` return `Finset A1`/`Finset A2`, `LW` is an `lfp`
over `Finset A1` iterated exactly as `gStepF` is iterated below, and `Lpre1` tests
`B (LW x y s) x s = univ`, which over `Finset`s is a decidable equality rather than a `Set`
extensionality. Every one of them bottoms out in `supportF` below.
-/

namespace Comp

open Csg

namespace CsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

/-! ## Support, as data -/

/-- The support of a rational kernel row as a `Finset`: `supportQ` with the states collected rather
    than merely testable. Computable, since it touches nothing but the rational table `G.K`. -/
def supportF (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) : Finset S :=
  Finset.univ.filter fun s' => G.K s a1 a2 s' ≠ 0

/-- `supportF` is `supportQ` under `Finset.coe`. The whole content of the `Finset` layer is that
    this holds and that everything above it respects coercion. -/
@[simp]
theorem coe_supportF (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) :
    (↑(G.supportF s a1 a2) : Set S) = G.supportQ s a1 a2 := by
  ext s'
  simp [supportF, supportQ]

/-! ## `Pre1`, as data -/

/-- `Pre1Q` with the region carried as data: the states from which some row action keeps every
    column response inside `x`. A computable `Finset S → Finset S`, which is exactly what makes the
    iteration below something `#eval` can run. -/
def pre1F (G : CsgQ S A1 A2) (x : Finset S) : Finset S :=
  Finset.univ.filter fun s => ∃ a1, ∀ a2, G.supportF s a1 a2 ⊆ x

/-- The bridge one level up: `pre1F` is `Pre1Q` under `Finset.coe`. Immediate, because the two were
    written in the same shape -- `coe_supportF` transported across `Finset.coe_subset`. -/
theorem coe_pre1F (G : CsgQ S A1 A2) (x : Finset S) :
    (↑(G.pre1F x) : Set S) = G.Pre1Q ↑x := by
  have key : ∀ (s : S) (a1 : A1) (a2 : A2),
      (G.supportF s a1 a2 ⊆ x) ↔ (G.supportQ s a1 a2 ⊆ (↑x : Set S)) := by
    intro s a1 a2
    rw [← coe_supportF G s a1 a2, Finset.coe_subset]
  ext s
  simp only [Finset.mem_coe, pre1F, Finset.mem_filter, Finset.mem_univ, true_and, Pre1Q,
    Set.mem_setOf_eq]
  exact exists_congr fun a1 => forall_congr' fun a2 => key s a1 a2

/-- The sure-safety step as data, in `GStepQ`'s own shape: `pre1F x ∩ safe`. -/
def gStepF (G : CsgQ S A1 A2) (safe x : Finset S) : Finset S := G.pre1F x ∩ safe

/-- `gStepF` is `GStepQ` under `Finset.coe` -- `coe_pre1F` intersected with `safe`. -/
theorem coe_gStepF (G : CsgQ S A1 A2) (safe x : Finset S) :
    (↑(G.gStepF safe x) : Set S) = G.GStepQ ↑safe ↑x := by
  simp only [gStepF, GStepQ, Finset.coe_inter, coe_pre1F]

/-! ## From a computed iterate to the exact region -/

/-- Every stage of the computed descent from `Finset.univ` is an upper bound on `G safe`. One
    `OrderHom.gfp_le_of_step` per step, with `coe_gStepF` and `GOrderHom_toCSG` identifying the
    computed step with the specification's own operator at each stage.

    This is the half that the iteration -- not a certificate -- has to supply. The other half,
    `G safe`'s *lower* bound, comes free from the fixed-point check, which is the asymmetry
    `Comp/Reach.lean` and `Csg/IntervalCertificate.lean` both turn on. -/
theorem G_le_coe_iter (G : CsgQ S A1 A2) (h : G.WellFormed) (safe : Finset S) (n : ℕ) :
    (G.toCSG h).G (↑safe : Set S) ≤ ↑((G.gStepF safe)^[n] Finset.univ) := by
  have hG : (G.toCSG h).G (↑safe : Set S) = ((G.toCSG h).GOrderHom ↑safe).gfp := rfl
  rw [hG]
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_univ]
      exact le_top
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine OrderHom.gfp_le_of_step _ ih ?_
      rw [GOrderHom_toCSG, coe_gStepF]

/-- **The payoff.** A `Finset` that was reached by iterating `gStepF` from `Finset.univ` and that
    `gStepF` leaves fixed *is* the sure-safety region of the real-valued game, on the nose.

    Both hypotheses are decidable statements about concrete `Finset`s, and both are discovered by
    `#eval` rather than proved about the search: iterate until the printed region repeats, take `n`
    and `c` from what was printed, and the fixed-point check is then a `Finset` equality. Nothing
    here assumes a bound on `n`, and nothing appeals to a theorem that the iteration terminates
    within `|S|` steps -- stabilisation is *observed*, and the two inequalities do the rest. -/
theorem G_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (safe c : Finset S) (n : ℕ)
    (hiter : (G.gStepF safe)^[n] Finset.univ = c) (hfix : G.gStepF safe c = c) :
    (G.toCSG h).G (↑safe : Set S) = ↑c := by
  have hG : (G.toCSG h).G (↑safe : Set S) = ((G.toCSG h).GOrderHom ↑safe).gfp := rfl
  have hfixS : (G.toCSG h).GOrderHom (↑safe : Set S) ↑c = (↑c : Set S) := by
    rw [GOrderHom_toCSG, ← coe_gStepF, hfix]
  have hge := G_le_coe_iter G h safe n
  rw [hiter, hG] at hge
  rw [hG]
  exact (OrderHom.eq_gfp_of_fixed_of_ge _ hfixS hge).symm

/-! ## Membership, for rewriting

The three `Finset.filter` definitions above, with their defining conditions exposed. Worked
instances rewrite with these to get out of `Finset.filter` and into the game's own data, which is
where a concrete kernel can be unfolded. -/

@[simp]
theorem mem_supportF (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) (s' : S) :
    s' ∈ G.supportF s a1 a2 ↔ G.K s a1 a2 s' ≠ 0 := by
  simp [supportF]

@[simp]
theorem mem_pre1F (G : CsgQ S A1 A2) (x : Finset S) (s : S) :
    s ∈ G.pre1F x ↔ ∃ a1, ∀ a2, G.supportF s a1 a2 ⊆ x := by
  simp [pre1F]

@[simp]
theorem mem_gStepF (G : CsgQ S A1 A2) (safe x : Finset S) (s : S) :
    s ∈ G.gStepF safe x ↔ s ∈ G.pre1F x ∧ s ∈ safe := by
  simp [gStepF]

end CsgQ

end Comp
