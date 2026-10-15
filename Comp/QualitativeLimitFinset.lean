/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.QualitativeFinset
import Comp.Reach
import Csg.QualitativeLimitSure

/-!
# `A`, `B`, and the first nested fixed point: `LW` over `Finset A1`

**Status: confirmed by a clean `lake build`.**

The one-step combinators shared by almost-sure and limit-sure mode, as data, and then the inner
fixed point they build: `LW x y s`, the row-action witness set that
`Csg/QualitativeLimitSure.lean`'s `Lpre1` tests. This is the first operator in the `Comp/` line
whose fixed point lives on a lattice *other* than `Set S`, and the first that is nested inside
another.

**Straight to `Finset` this time.** `Comp/Qualitative.lean` went through a `Set`-level layer
(`supportQ`, `Pre1Q`) before `Comp/QualitativeFinset.lean` re-ran it over `Finset`. That first layer
existed to establish *decidability*; carrying the region as data gives decidability for free, so
`aF` and `bF` below skip it and bridge directly to `Csg/QualitativeAlmostSure.lean`'s `CSG.A` and
`CSG.B`. `toCSG_support` is the one piece of the earlier file they need.

**Why the direction flips.** `Comp/QualitativeFinset.lean` descends from `Finset.univ`, because
`G safe` is a *greatest* fixed point. `LW x y s` is a *least* fixed point -- `lpreXY`'s inner loop
grows the witness set `w` from nothing -- so the chain climbs from `∅` and the soundness step is
`Comp/Reach.lean`'s `OrderHom.le_lfp_of_step` rather than `gfp_le_of_step`. `B_empty_v1`
(`Csg/QualitativeAlmostSure.lean`) is the specification-side record of what starting from `∅`
means: no row action is available to witness an escape, so the first iterate is empty.

**Why `LW_eq_coe_of_fixed` is stated per state.** `LW` is indexed by `s`, and `Lpre1` calls it once
per state before testing `B (LW x y s) x s = univ`. So the exact identification has to be available
one state at a time, and what the *outer* operator will need is the conjunction over states --
`∀ s, lStepF x y s (iterate at s) = (iterate at s)` -- as a hypothesis. That is the shape of a
nested computation whose inner exactness feeds the outer one's soundness, and it is why no single
iteration count is baked in here: `n` stays a parameter, and nothing claims the inner loop finishes
within `|A1|` steps, only that it was *seen* to.

**Above this file:** `Comp/QualitativeLimitReach.lean` takes `LW` as its input and builds `Lpre1`
and `LF` on it -- the `νY.μX` nest whose answer is the value-1 set for probabilistic reachability,
limit-sure being the right notion there.
-/

namespace Comp

open Csg

namespace CsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

/-- The cast game's `PMF` support, as the coercion of a `Finset`. `Comp/Qualitative.lean`'s
    `toPMF_support` composed with `coe_supportF`, in the form the bridges below rewrite with. -/
theorem toCSG_support (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    ((G.toCSG h).K s a1 a2).support = (↑(G.supportF s a1 a2) : Set S) := by
  rw [coe_supportF]
  exact toPMF_support G h s a1 a2

/-! ## `A`: the row actions that are safe, as data -/

/-- `CSG.A` as data: the row actions at `s` that keep every unexcused column response inside `y`.
    A `Finset A1`, computable, and decidable without any further instance work -- `Finset`
    membership and `⊆` supply what the `Set`-level version needed `Pre1Q`'s `decidable_of_iff` to
    arrange. -/
def aF (G : CsgQ S A1 A2) (v2 : Finset A2) (y : Finset S) (s : S) : Finset A1 :=
  Finset.univ.filter fun a1 => ∀ a2, a2 ∈ v2 ∨ G.supportF s a1 a2 ⊆ y

@[simp]
theorem mem_aF (G : CsgQ S A1 A2) (v2 : Finset A2) (y : Finset S) (s : S) (a1 : A1) :
    a1 ∈ G.aF v2 y s ↔ ∀ a2, a2 ∈ v2 ∨ G.supportF s a1 a2 ⊆ y := by
  simp only [aF, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `aF` is `CSG.A`. Both were written in the same shape, so this is `toCSG_support` transported
    across `Finset.coe_subset`. -/
theorem coe_aF (G : CsgQ S A1 A2) (h : G.WellFormed) (v2 : Finset A2) (y : Finset S) (s : S) :
    (↑(G.aF v2 y s) : Set A1) = (G.toCSG h).A ↑v2 ↑y s := by
  ext a1
  simp only [Finset.mem_coe, mem_aF, CSG.A, Set.mem_setOf_eq, toCSG_support G h,
    Finset.coe_subset]

/-! ## `B`: the column actions that can escape, as data -/

/-- `CSG.B` as data: the column actions at `s` against which some row action in `v1` can reach
    `x`. The escape test is a `Finset.Nonempty`, which is decidable, where the `Set`-level
    `Set.Nonempty` is not. -/
def bF (G : CsgQ S A1 A2) (v1 : Finset A1) (x : Finset S) (s : S) : Finset A2 :=
  Finset.univ.filter fun a2 => ∃ a1 ∈ v1, (G.supportF s a1 a2 ∩ x).Nonempty

@[simp]
theorem mem_bF (G : CsgQ S A1 A2) (v1 : Finset A1) (x : Finset S) (s : S) (a2 : A2) :
    a2 ∈ G.bF v1 x s ↔ ∃ a1 ∈ v1, (G.supportF s a1 a2 ∩ x).Nonempty := by
  simp only [bF, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `bF` is `CSG.B`. One step longer than `coe_aF`, because the escape test has to cross the
    coercion twice: `Finset.coe_inter` to combine the two coerced sets, then `Finset.coe_nonempty`
    to turn a nonempty coercion into a nonempty `Finset`. -/
theorem coe_bF (G : CsgQ S A1 A2) (h : G.WellFormed) (v1 : Finset A1) (x : Finset S) (s : S) :
    (↑(G.bF v1 x s) : Set A2) = (G.toCSG h).B ↑v1 ↑x s := by
  have hne : ∀ a1 : A1, ∀ a2 : A2,
      ((↑(G.supportF s a1 a2) : Set S) ∩ ↑x).Nonempty
        ↔ (G.supportF s a1 a2 ∩ x).Nonempty := by
    intro a1 a2
    rw [← Finset.coe_inter, Finset.coe_nonempty]
  ext a2
  simp only [Finset.mem_coe, mem_bF, CSG.B, Set.mem_setOf_eq, toCSG_support G h]
  exact exists_congr fun a1 => and_congr_right fun _ => (hne a1 a2).symm

/-! ## `LW`: the inner fixed point -/

/-- `CSG.LStep` as data: one turn of `lpreXY`'s inner loop, `w ↦ A (B w x s) y s`. Computable, so
    `(G.lStepF x y s)^[n] ∅` is something `#eval` prints. -/
def lStepF (G : CsgQ S A1 A2) (x y : Finset S) (s : S) (w : Finset A1) : Finset A1 :=
  G.aF (G.bF w x s) y s

/-- `lStepF` is `CSG.LStep`, applied. `coe_bF` inside `coe_aF`; the `change` is only there to strip
    the `OrderHom` coercion, as `GOrderHom_toCSG` does in `Comp/Qualitative.lean`. -/
theorem coe_lStepF (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) (s : S)
    (w : Finset A1) :
    (↑(G.lStepF x y s w) : Set A1) = (G.toCSG h).LStep ↑x ↑y s ↑w := by
  change (↑(G.aF (G.bF w x s) y s) : Set A1)
    = (G.toCSG h).A ((G.toCSG h).B ↑w ↑x s) ↑y s
  rw [← coe_bF G h w x s, coe_aF G h]

/-- Every stage of the computed climb from `∅` is a lower bound on `LW x y s`. The mirror of
    `Comp/QualitativeFinset.lean`'s `G_le_coe_iter`, with the inequality the other way up because
    this is a least fixed point. -/
theorem coe_iter_le_LW (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) (s : S) (n : ℕ) :
    (↑((G.lStepF x y s)^[n] ∅) : Set A1) ≤ (G.toCSG h).LW ↑x ↑y s := by
  have hLW : (G.toCSG h).LW (↑x : Set S) ↑y s = ((G.toCSG h).LStep ↑x ↑y s).lfp := rfl
  rw [hLW]
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine OrderHom.le_lfp_of_step _ ih ?_
      rw [coe_lStepF]

/-- **The payoff, one state at a time.** A `Finset A1` reached by iterating `lStepF` from `∅` and
    left fixed by it *is* the row-action witness set of the real-valued game at `s`.

    Both hypotheses are decidable statements about concrete `Finset`s, and `n` is a parameter rather
    than a bound to be justified: the climb is run by `#eval`, the stabilisation observed, and the
    two inequalities do the rest. `Lpre1`'s own bridge will take the `∀ s` version of `hfix` as its
    hypothesis, which is how an inner exactness becomes an outer soundness. -/
theorem LW_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) (s : S)
    (c : Finset A1) (n : ℕ) (hiter : (G.lStepF x y s)^[n] ∅ = c)
    (hfix : G.lStepF x y s c = c) :
    (G.toCSG h).LW ↑x ↑y s = ↑c := by
  have hLW : (G.toCSG h).LW (↑x : Set S) ↑y s = ((G.toCSG h).LStep ↑x ↑y s).lfp := rfl
  have hfixS : (G.toCSG h).LStep (↑x : Set S) ↑y s ↑c = (↑c : Set A1) := by
    rw [← coe_lStepF, hfix]
  have hle := coe_iter_le_LW G h x y s n
  rw [hiter] at hle
  rw [hLW] at hle
  rw [hLW]
  exact (OrderHom.eq_lfp_of_fixed_of_le _ hfixS hle).symm

end CsgQ

end Comp
