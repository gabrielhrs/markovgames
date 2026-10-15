/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.QualitativeLimitFinset

/-!
# `Apre1` and `AF`: almost-sure reachability, with no inner fixed point

**Status: confirmed by a clean `lake build`.**

The almost-sure counterpart of `Comp/QualitativeLimitReach.lean`, and by some distance the easier
of the two. `Csg/QualitativeAlmostSure.lean`'s `Apre1 x y = {s | B (A ∅ y s) x s = univ}` reads its
row-action pool straight off `A ∅ y s` instead of growing it by a fixed point, which is the single
difference between `Apre1` and `Lpre1` -- and the reason almost-sure reachability can be weaker
than limit-sure.

**What that difference costs the computation: nothing.** There is no witness family to carry, so
`apre1F` is a function of `x` and `y` alone, `afStepF` is a plain computable `Finset S → Finset S`,
and the middle chain is an honest `Function.iterate` with no hypotheses threaded through it. Two
levels instead of three, and every lemma below is unconditional. Compare
`Comp/QualitativeLimitReach.lean`, where the witness family changes at every middle step and the
middle and outer levels have to be given as single-step lemmas.

**What the difference costs the answer** is the whole point of the almost-sure/limit-sure gap:
`AF b ⊆ LF b`, sometimes strictly. `Comp/HideOrRunQ.lean` is where both are computed on one game
and come out different.

**The shape is otherwise identical** to the limit-sure file: `coe_iter_le_afInner` climbs the middle
chain from `∅` with `OrderHom.le_lfp_of_step`, `afInner_eq_coe_of_fixed` pins the `μX` fixed point
once the chain is seen to stop, and `AF_le_of_step` descends the outer `νY` chain from
`Finset.univ` with `OrderHom.gfp_le_of_step` until `AF_eq_coe_of_fixed` closes it. No level is given
an iteration bound.

**Not here:** `AGF`, `AFpre1` and `AFG`. The first is `AF` with a case split on `b`, so it is the
same two-level shape; the other two rest on the three-argument predecessor, which brings back an
inner fixed point and so looks like the limit-sure file again.
-/

namespace Comp

open Csg

namespace CsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

/-! ## `Apre1`, as data -/

/-- `aF` at the empty excused set, which is the only way `Apre1` ever calls `A` -- matching the
    Java's own `A(mdist, new BitSet(), y)`. Stated separately so the `∅` on the `Set` side and the
    `∅` on the `Finset` side are reconciled once. -/
theorem coe_aF_empty (G : CsgQ S A1 A2) (h : G.WellFormed) (y : Finset S) (s : S) :
    (↑(G.aF ∅ y s) : Set A1) = (G.toCSG h).A ∅ ↑y s := by
  rw [coe_aF G h ∅ y s, Finset.coe_empty]

/-- `CSG.Apre1` as data: the states at which every column action can be driven into `x`, the row
    player being restricted to the actions already safe for `y`. -/
def apre1F (G : CsgQ S A1 A2) (x y : Finset S) : Finset S :=
  Finset.univ.filter fun s => G.bF (G.aF ∅ y s) x s = Finset.univ

@[simp]
theorem mem_apre1F (G : CsgQ S A1 A2) (x y : Finset S) (s : S) :
    s ∈ G.apre1F x y ↔ G.bF (G.aF ∅ y s) x s = Finset.univ := by
  simp only [apre1F, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `apre1F` is `CSG.Apre1`, unconditionally -- no witness family, so no hypothesis. -/
theorem coe_apre1F (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) :
    (↑(G.apre1F x y) : Set S) = (G.toCSG h).Apre1 ↑x ↑y := by
  ext s
  simp only [Finset.mem_coe, mem_apre1F, CSG.Apre1, Set.mem_setOf_eq, ← coe_aF_empty G h,
    ← coe_bF G h, Finset.coe_eq_univ]

/-! ## The middle chain, as a plain iterate -/

/-- One turn of the `μX` chain: `Apre1(x,y) ∪ b`. A computable function of `x`, which is what
    `Apre1`'s lack of an inner fixed point buys. -/
def afStepF (G : CsgQ S A1 A2) (b y x : Finset S) : Finset S := G.apre1F x y ∪ b

theorem coe_AFInner_apply (G : CsgQ S A1 A2) (h : G.WellFormed) (b y x : Finset S) :
    (G.toCSG h).AFInner ↑b ↑y ↑x = (↑(G.afStepF b y x) : Set S) := by
  change (G.toCSG h).Apre1 (↑x : Set S) ↑y ∪ ↑b = (↑(G.apre1F x y ∪ b) : Set S)
  rw [← coe_apre1F G h x y, ← Finset.coe_union]

/-- Every stage of the middle climb from `∅` is a lower bound on the `μX` fixed point. -/
theorem coe_iter_le_afInner (G : CsgQ S A1 A2) (h : G.WellFormed) (b y : Finset S) (m : ℕ) :
    (↑((G.afStepF b y)^[m] ∅) : Set S) ≤ ((G.toCSG h).AFInner ↑b ↑y).lfp := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact OrderHom.le_lfp_of_step _ ih (coe_AFInner_apply G h b y _).symm

/-- A middle chain that was run and seen to stop pins the `μX` fixed point at `y`, exactly. -/
theorem afInner_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S) (m : ℕ)
    (hiter : (G.afStepF b y)^[m] ∅ = c) (hfix : G.afStepF b y c = c) :
    ((G.toCSG h).AFInner ↑b ↑y).lfp = (↑c : Set S) := by
  have hle := coe_iter_le_afInner G h b y m
  rw [hiter] at hle
  have hfixS : (G.toCSG h).AFInner (↑b : Set S) ↑y ↑c = (↑c : Set S) := by
    rw [coe_AFInner_apply G h b y c, hfix]
  exact (OrderHom.eq_lfp_of_fixed_of_le _ hfixS hle).symm

/-! ## The outer chain -/

/-- The outer descent's first link, free. -/
theorem AF_le_univ (G : CsgQ S A1 A2) (h : G.WellFormed) (b : Finset S) :
    (G.toCSG h).AF ↑b ≤ (↑(Finset.univ : Finset S) : Set S) := by
  rw [Finset.coe_univ]
  exact le_top

/-- One outer step, given the certified `μX` fixed point at `y`. -/
theorem AF_le_of_step (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S)
    (hinner : ((G.toCSG h).AFInner ↑b ↑y).lfp = (↑c : Set S))
    (hy : (G.toCSG h).AF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).AF ↑b ≤ (↑c : Set S) := by
  have hAF : (G.toCSG h).AF (↑b : Set S) = ((G.toCSG h).AFOuter ↑b).gfp := rfl
  have hstep : (↑c : Set S) = (G.toCSG h).AFOuter (↑b : Set S) ↑y := hinner.symm
  rw [hAF] at hy ⊢
  exact OrderHom.gfp_le_of_step _ hy hstep

/-- **The almost-sure reachability set, exactly.** A region that is its own certified `μX` fixed
    point and that the outer descent has reached *is* `AF b`. -/
theorem AF_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (b y : Finset S)
    (hinner : ((G.toCSG h).AFInner ↑b ↑y).lfp = (↑y : Set S))
    (hy : (G.toCSG h).AF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).AF ↑b = (↑y : Set S) := by
  have hAF : (G.toCSG h).AF (↑b : Set S) = ((G.toCSG h).AFOuter ↑b).gfp := rfl
  have hfixS : (G.toCSG h).AFOuter (↑b : Set S) ↑y = (↑y : Set S) := hinner
  rw [hAF] at hy ⊢
  exact (OrderHom.eq_gfp_of_fixed_of_ge _ hfixS hy).symm

end CsgQ

end Comp
