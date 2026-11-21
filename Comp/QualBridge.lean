/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.QualOps
import Csg.QualitativeLimitSure

/-!
# The qualitative operators compute what `Csg/` specifies

**Status: confirmed by a clean `lake build`.**

`Comp/QualOps.lean` writes the qualitative operators over an arbitrary support function. This file
says what they compute. Throughout, `C` is a `CSG`, `supp` a support function, and

    hsupp : ∀ s a1 a2, (C.K s a1 a2).support = ↑(supp s a1 a2)

the one hypothesis connecting them: `supp` really is the kernel's support. Under it,

* each one-step operator is `C`'s own under `Finset.coe` -- `coe_pre1`, `coe_aSet`, `coe_bSet`,
  `coe_lStep`, `coe_apre1`, `coe_lpre1`;
* each loop returns `C`'s fixed point -- `G_eq_coe_gRegion`, `LW_eq_coe_lw`,
  `AF_eq_coe_afRegion`, `LF_eq_coe_lfRegion`.

Nothing here mentions how `supp` was obtained, so the proofs are done once for every way of
obtaining one. A caller owes `hsupp` and nothing else.

**Two routes to each fixed point.** The loop theorems need no further hypothesis:
`Comp/FixLoop.lean` proves the loops stop, so where they stop is the fixed point. The *counted*
lemmas -- `G_eq_coe_of_fixed`, `LW_eq_coe_of_fixed`, `afInner_eq_coe_of_fixed`,
`lfInner_eq_coe_of_fixed` and the single outer steps -- instead take an iterate that was run for a
stated number of steps and observed to be fixed, and so exhibit a descent one step at a time. The
`_of_iter` lemmas at the end package an outer step with the middle chain that justifies it, which
is the form a worked instance calls.

**Which half is cheap.** For a least fixed point a fixed-point check bounds it from above and the
chain of iterates from `∅` bounds it from below; for a greatest fixed point it is the other way
round, with the chain descending from `Finset.univ`. The direction alternates with nesting: `LW` is
least, the middle `μX` least, the outer `νY` greatest.

**The outer steps do not mention `supp`.** `AF_le_of_step`, `AF_eq_coe_of_fixed` and their `LF`
counterparts are statements about `C` and coerced `Finset`s alone, the inner fixed point entering
as a hypothesis. They are in the first section, which for that reason does not assume
`DecidableEq S`.
-/

namespace Comp

open Csg

namespace Qual

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

/-! ## The outer `νY` descents, one step at a time -/

section Descent

variable (C : CSG S A1 A2)

/-- The almost-sure descent's first link: `Finset.univ` bounds everything. -/
theorem AF_le_univ (b : Finset S) : C.AF ↑b ≤ (↑(Finset.univ : Finset S) : Set S) := by
  rw [Finset.coe_univ]
  exact le_top

/-- One outer step: if `c` is the middle `μX` fixed point at `y`, and `y` bounds `AF b` from
    above, then so does `c`. -/
theorem AF_le_of_step (b y c : Finset S)
    (hinner : (C.AFInner ↑b ↑y).lfp = (↑c : Set S)) (hy : C.AF ↑b ≤ (↑y : Set S)) :
    C.AF ↑b ≤ (↑c : Set S) := by
  have hAF : C.AF (↑b : Set S) = (C.AFOuter ↑b).gfp := rfl
  have hstep : (↑c : Set S) = C.AFOuter (↑b : Set S) ↑y := hinner.symm
  rw [hAF] at hy ⊢
  exact OrderHom.gfp_le_of_step _ hy hstep

/-- A region that is its own middle `μX` fixed point and that the outer descent has reached is
    `AF b`. -/
theorem AF_eq_coe_of_fixed (b y : Finset S)
    (hinner : (C.AFInner ↑b ↑y).lfp = (↑y : Set S)) (hy : C.AF ↑b ≤ (↑y : Set S)) :
    C.AF ↑b = (↑y : Set S) := by
  have hAF : C.AF (↑b : Set S) = (C.AFOuter ↑b).gfp := rfl
  have hfixS : C.AFOuter (↑b : Set S) ↑y = (↑y : Set S) := hinner
  rw [hAF] at hy ⊢
  exact (OrderHom.eq_gfp_of_fixed_of_ge _ hfixS hy).symm

/-- The limit-sure descent's first link. -/
theorem LF_le_univ (b : Finset S) : C.LF ↑b ≤ (↑(Finset.univ : Finset S) : Set S) := by
  rw [Finset.coe_univ]
  exact le_top

/-- One outer step of the limit-sure descent. -/
theorem LF_le_of_step (b y c : Finset S)
    (hinner : (C.LFInner ↑b ↑y).lfp = (↑c : Set S)) (hy : C.LF ↑b ≤ (↑y : Set S)) :
    C.LF ↑b ≤ (↑c : Set S) := by
  have hLF : C.LF (↑b : Set S) = (C.LFOuter ↑b).gfp := rfl
  have hstep : (↑c : Set S) = C.LFOuter (↑b : Set S) ↑y := hinner.symm
  rw [hLF] at hy ⊢
  exact OrderHom.gfp_le_of_step _ hy hstep

/-- A region that is its own middle `μX` fixed point and that the outer descent has reached is
    `LF b`, the value-1 set for reaching `b`. -/
theorem LF_eq_coe_of_fixed (b y : Finset S)
    (hinner : (C.LFInner ↑b ↑y).lfp = (↑y : Set S)) (hy : C.LF ↑b ≤ (↑y : Set S)) :
    C.LF ↑b = (↑y : Set S) := by
  have hLF : C.LF (↑b : Set S) = (C.LFOuter ↑b).gfp := rfl
  have hfixS : C.LFOuter (↑b : Set S) ↑y = (↑y : Set S) := hinner
  rw [hLF] at hy ⊢
  exact (OrderHom.eq_gfp_of_fixed_of_ge _ hfixS hy).symm

end Descent

section Bridge

variable [DecidableEq S] (C : CSG S A1 A2) (supp : S → A1 → A2 → Finset S)

/-! ## `Pre1` and sure safety -/

/-- `pre1` is `CSG.Pre1`. The two are written in the same shape, so this is `hsupp` carried
    across `Finset.coe_subset`. -/
theorem coe_pre1 (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (x : Finset S) : (↑(pre1 supp x) : Set S) = C.Pre1 ↑x := by
  ext s
  simp only [Finset.mem_coe, mem_pre1, CSG.Pre1, Set.mem_ofPred_eq, hsupp, Finset.coe_subset]

/-- The sure-safety step is `CSG.GOrderHom`, applied. The bridge the loop takes. -/
theorem coe_gStep (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (safe x : Finset S) : (↑(gStep supp safe x) : Set S) = C.GOrderHom ↑safe ↑x := by
  change (↑(pre1 supp x ∩ safe) : Set S) = C.Pre1 ↑x ∩ ↑safe
  rw [Finset.coe_inter, coe_pre1 C supp hsupp x]

/-- **Where the loop stops is the sure-safety region.** -/
theorem G_eq_coe_gRegion (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (safe : Finset S) : C.G (↑safe : Set S) = (↑(gRegion supp safe) : Set S) :=
  gfp_eq_coe_fixFrom_univ _ _ (coe_gStep C supp hsupp safe)

/-- Every stage of the descent from `Finset.univ` bounds `G safe` from above. -/
theorem G_le_coe_iter (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (safe : Finset S) (n : ℕ) :
    C.G (↑safe : Set S) ≤ ↑((gStep supp safe)^[n] Finset.univ) := by
  have hG : C.G (↑safe : Set S) = (C.GOrderHom ↑safe).gfp := rfl
  rw [hG]
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_univ]
      exact le_top
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact OrderHom.gfp_le_of_step _ ih (coe_gStep C supp hsupp safe _)

/-- The counted form: a region reached in `n` steps from `Finset.univ` and left fixed by the step
    is `G safe`. -/
theorem G_eq_coe_of_fixed (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (safe c : Finset S) (n : ℕ) (hiter : (gStep supp safe)^[n] Finset.univ = c)
    (hfix : gStep supp safe c = c) : C.G (↑safe : Set S) = ↑c := by
  have hG : C.G (↑safe : Set S) = (C.GOrderHom ↑safe).gfp := rfl
  have hfixS : C.GOrderHom (↑safe : Set S) ↑c = (↑c : Set S) := by
    rw [← coe_gStep C supp hsupp safe c, hfix]
  have hge := G_le_coe_iter C supp hsupp safe n
  rw [hiter, hG] at hge
  rw [hG]
  exact (OrderHom.eq_gfp_of_fixed_of_ge _ hfixS hge).symm

/-! ## `A`, `B` and the innermost fixed point `LW` -/

/-- `aSet` is `CSG.A`. -/
theorem coe_aSet (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (v2 : Finset A2) (y : Finset S) (s : S) :
    (↑(aSet supp v2 y s) : Set A1) = C.A ↑v2 ↑y s := by
  ext a1
  simp only [Finset.mem_coe, mem_aSet, CSG.A, Set.mem_ofPred_eq, hsupp, Finset.coe_subset]

/-- `aSet` at the empty excused set, which is how `Apre1` calls `A`. Separate so that the `∅` on
    the `Set` side and the `∅` on the `Finset` side are reconciled once. -/
theorem coe_aSet_empty
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (y : Finset S) (s : S) : (↑(aSet supp ∅ y s) : Set A1) = C.A ∅ ↑y s := by
  rw [coe_aSet C supp hsupp ∅ y s, Finset.coe_empty]

/-- `bSet` is `CSG.B`. The escape test crosses the coercion twice: `Finset.coe_inter` to combine
    the two coerced sets, then `Finset.coe_nonempty`. -/
theorem coe_bSet (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (v1 : Finset A1) (x : Finset S) (s : S) :
    (↑(bSet supp v1 x s) : Set A2) = C.B ↑v1 ↑x s := by
  have hne : ∀ a1 : A1, ∀ a2 : A2,
      ((↑(supp s a1 a2) : Set S) ∩ ↑x).Nonempty ↔ (supp s a1 a2 ∩ x).Nonempty := by
    intro a1 a2
    rw [← Finset.coe_inter, Finset.coe_nonempty]
  ext a2
  simp only [Finset.mem_coe, mem_bSet, CSG.B, Set.mem_ofPred_eq, hsupp]
  exact exists_congr fun a1 => and_congr_right fun _ => (hne a1 a2).symm

/-- The innermost step is `CSG.LStep`, applied. -/
theorem coe_lStep (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (x y : Finset S) (s : S) (w : Finset A1) :
    (↑(lStep supp x y s w) : Set A1) = C.LStep ↑x ↑y s ↑w := by
  change (↑(aSet supp (bSet supp w x s) y s) : Set A1) = C.A (C.B ↑w ↑x s) ↑y s
  rw [← coe_bSet C supp hsupp w x s, coe_aSet C supp hsupp]

/-- **Where the innermost loop stops is `LW`.** -/
theorem LW_eq_coe_lw (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (x y : Finset S) (s : S) : C.LW ↑x ↑y s = (↑(lw supp x y s) : Set A1) :=
  lfp_eq_coe_fixFrom_empty _ _ (coe_lStep C supp hsupp x y s)

/-- Every stage of the climb from `∅` bounds `LW x y s` from below. -/
theorem coe_iter_le_LW (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (x y : Finset S) (s : S) (n : ℕ) :
    (↑((lStep supp x y s)^[n] ∅) : Set A1) ≤ C.LW ↑x ↑y s := by
  have hLW : C.LW (↑x : Set S) ↑y s = (C.LStep ↑x ↑y s).lfp := rfl
  rw [hLW]
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact OrderHom.le_lfp_of_step _ ih (coe_lStep C supp hsupp x y s _)

/-- The counted form: a set of row actions reached in `n` steps from `∅` and left fixed by the
    step is `LW x y s`. -/
theorem LW_eq_coe_of_fixed
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (x y : Finset S) (s : S) (c : Finset A1) (n : ℕ) (hiter : (lStep supp x y s)^[n] ∅ = c)
    (hfix : lStep supp x y s c = c) : C.LW ↑x ↑y s = ↑c := by
  have hLW : C.LW (↑x : Set S) ↑y s = (C.LStep ↑x ↑y s).lfp := rfl
  have hfixS : C.LStep (↑x : Set S) ↑y s ↑c = (↑c : Set A1) := by
    rw [← coe_lStep C supp hsupp x y s c, hfix]
  have hle := coe_iter_le_LW C supp hsupp x y s n
  rw [hiter, hLW] at hle
  rw [hLW]
  exact (OrderHom.eq_lfp_of_fixed_of_le _ hfixS hle).symm

/-! ## `Apre1` and almost-sure reachability -/

/-- `apre1` is `CSG.Apre1`. No witness family, so no hypothesis beyond `hsupp`. -/
theorem coe_apre1 (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (x y : Finset S) : (↑(apre1 supp x y) : Set S) = C.Apre1 ↑x ↑y := by
  ext s
  simp only [Finset.mem_coe, mem_apre1, CSG.Apre1, Set.mem_ofPred_eq,
    ← coe_aSet_empty C supp hsupp, ← coe_bSet C supp hsupp, Finset.coe_eq_univ]

/-- The almost-sure middle step is `CSG.AFInner`, applied. -/
theorem coe_afStep (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y x : Finset S) : (↑(afStep supp b y x) : Set S) = C.AFInner ↑b ↑y ↑x := by
  change (↑(apre1 supp x y ∪ b) : Set S) = C.Apre1 (↑x : Set S) ↑y ∪ ↑b
  rw [Finset.coe_union, coe_apre1 C supp hsupp x y]

/-- The middle loop lands on `AFInner`'s least fixed point. -/
theorem coe_afInner (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y : Finset S) : (↑(afInner supp b y) : Set S) = (C.AFInner ↑b ↑y).lfp :=
  (lfp_eq_coe_fixFrom_empty _ _ (coe_afStep C supp hsupp b y)).symm

/-- `AFOuter` is that least fixed point, so the middle loop is the outer loop's bridge. -/
theorem coe_afInner_outer
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y : Finset S) : (↑(afInner supp b y) : Set S) = C.AFOuter ↑b ↑y :=
  coe_afInner C supp hsupp b y

/-- **Where the two nested loops stop is the almost-sure reachability region.** -/
theorem AF_eq_coe_afRegion
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b : Finset S) : C.AF ↑b = (↑(afRegion supp b) : Set S) :=
  gfp_eq_coe_fixFrom_univ _ _ (coe_afInner_outer C supp hsupp b)

/-- Every stage of the middle climb from `∅` bounds the `μX` fixed point from below. -/
theorem coe_iter_le_afInner
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y : Finset S) (m : ℕ) :
    (↑((afStep supp b y)^[m] ∅) : Set S) ≤ (C.AFInner ↑b ↑y).lfp := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact OrderHom.le_lfp_of_step _ ih (coe_afStep C supp hsupp b y _)

/-- The counted form: a region the middle chain reached in `m` steps and that the step leaves
    fixed is the `μX` fixed point at `y`. -/
theorem afInner_eq_coe_of_fixed
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y c : Finset S) (m : ℕ) (hiter : (afStep supp b y)^[m] ∅ = c)
    (hfix : afStep supp b y c = c) : (C.AFInner ↑b ↑y).lfp = (↑c : Set S) := by
  have hle := coe_iter_le_afInner C supp hsupp b y m
  rw [hiter] at hle
  have hfixS : C.AFInner (↑b : Set S) ↑y ↑c = (↑c : Set S) := by
    rw [← coe_afStep C supp hsupp b y c, hfix]
  exact (OrderHom.eq_lfp_of_fixed_of_le _ hfixS hle).symm

/-! ## `Lpre1` and limit-sure reachability -/

/-- `lpre1` is `CSG.Lpre1`, provided the witness family is `LW`. -/
theorem coe_lpre1 (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (w : S → Finset A1) (x y : Finset S)
    (hw : ∀ s, C.LW ↑x ↑y s = (↑(w s) : Set A1)) :
    (↑(lpre1 supp w x) : Set S) = C.Lpre1 ↑x ↑y := by
  ext s
  simp only [Finset.mem_coe, mem_lpre1, CSG.Lpre1, Set.mem_ofPred_eq, hw s,
    ← coe_bSet C supp hsupp, Finset.coe_eq_univ]

/-- One turn of the limit-sure middle chain is `CSG.LFInner`, applied, for any witness family
    that is `LW` at `x`. -/
theorem coe_LFInner_apply
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y x : Finset S) (w : S → Finset A1)
    (hw : ∀ s, C.LW ↑x ↑y s = (↑(w s) : Set A1)) :
    C.LFInner ↑b ↑y ↑x = (↑(lpre1 supp w x ∪ b) : Set S) := by
  change C.Lpre1 (↑x : Set S) ↑y ∪ ↑b = (↑(lpre1 supp w x ∪ b) : Set S)
  rw [← coe_lpre1 C supp hsupp w x y hw, ← Finset.coe_union]

/-- The middle step with the witness family computed by the innermost loop is `LFInner`, with no
    hypothesis on the family. The bridge the middle loop takes. -/
theorem coe_lmid (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y x : Finset S) : (↑(lmid supp b y x) : Set S) = C.LFInner ↑b ↑y ↑x := by
  unfold lmid
  rw [coe_LFInner_apply C supp hsupp b y x (lw supp x y)
    (fun s => LW_eq_coe_lw C supp hsupp x y s)]

/-- The middle loop lands on `LFInner`'s least fixed point. -/
theorem coe_lfInner (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y : Finset S) : (↑(lfInner supp b y) : Set S) = (C.LFInner ↑b ↑y).lfp :=
  (lfp_eq_coe_fixFrom_empty _ _ (coe_lmid C supp hsupp b y)).symm

/-- `LFOuter` is that least fixed point, so the middle loop is the outer loop's bridge. -/
theorem coe_lfInner_outer
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y : Finset S) : (↑(lfInner supp b y) : Set S) = C.LFOuter ↑b ↑y :=
  coe_lfInner C supp hsupp b y

/-- **Where the three nested loops stop is `LF b`**, the value-1 set for reaching `b`. -/
theorem LF_eq_coe_lfRegion
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b : Finset S) : C.LF ↑b = (↑(lfRegion supp b) : Set S) :=
  gfp_eq_coe_fixFrom_univ _ _ (coe_lfInner_outer C supp hsupp b)

/-- One counted middle step: from a lower bound `x` on the `μX` fixed point, the next region is
    still a lower bound. -/
theorem le_lfInner_of_step
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y x c : Finset S) (w : S → Finset A1)
    (hw : ∀ s, C.LW ↑x ↑y s = (↑(w s) : Set A1))
    (hle : (↑x : Set S) ≤ (C.LFInner ↑b ↑y).lfp) (hc : c = lpre1 supp w x ∪ b) :
    (↑c : Set S) ≤ (C.LFInner ↑b ↑y).lfp := by
  subst hc
  exact OrderHom.le_lfp_of_step _ hle (coe_LFInner_apply C supp hsupp b y x w hw).symm

/-- The counted form: a region the middle chain reached and that the middle step leaves fixed is
    the `μX` fixed point at `y`. -/
theorem lfInner_eq_coe_of_fixed
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y c : Finset S) (w : S → Finset A1)
    (hw : ∀ s, C.LW ↑c ↑y s = (↑(w s) : Set A1)) (hfix : c = lpre1 supp w c ∪ b)
    (hle : (↑c : Set S) ≤ (C.LFInner ↑b ↑y).lfp) :
    (C.LFInner ↑b ↑y).lfp = (↑c : Set S) := by
  have hfixS : C.LFInner (↑b : Set S) ↑y ↑c = (↑c : Set S) := by
    rw [coe_LFInner_apply C supp hsupp b y c w hw, ← hfix]
  exact (OrderHom.eq_lfp_of_fixed_of_le _ hfixS hle).symm

/-! ## Counted outer steps, packaged

One outer step of a descent together with the middle chain that justifies it, and the closing
step. Each hypothesis is an equation between computed `Finset`s; the limit-sure ones also ask that
`k` steps of the innermost climb reach a fixed point at every region the middle chain can
visit. -/

/-- One outer almost-sure step, from a middle chain run for `m` steps and seen to stop. -/
theorem AF_le_of_iter (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y c : Finset S) (m : ℕ) (hiter : (afStep supp b y)^[m] ∅ = c)
    (hfix : afStep supp b y c = c) (hy : C.AF ↑b ≤ (↑y : Set S)) :
    C.AF ↑b ≤ (↑c : Set S) :=
  AF_le_of_step C b y c (afInner_eq_coe_of_fixed C supp hsupp b y c m hiter hfix) hy

/-- The closing almost-sure step: the middle chain at `y` returns `y`. -/
theorem AF_eq_coe_of_iter (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (b y : Finset S) (m : ℕ) (hiter : (afStep supp b y)^[m] ∅ = y)
    (hfix : afStep supp b y y = y) (hy : C.AF ↑b ≤ (↑y : Set S)) :
    C.AF ↑b = (↑y : Set S) :=
  AF_eq_coe_of_fixed C b y (afInner_eq_coe_of_fixed C supp hsupp b y y m hiter hfix) hy

/-- `LW`, from `k` steps of the innermost climb seen to stop. -/
theorem LW_eq_coe_iter (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (k : ℕ) (x y : Finset S) (s : S)
    (hfix : lStep supp x y s ((lStep supp x y s)^[k] ∅) = (lStep supp x y s)^[k] ∅) :
    C.LW ↑x ↑y s = (↑((lStep supp x y s)^[k] ∅) : Set A1) :=
  LW_eq_coe_of_fixed C supp hsupp x y s _ k rfl hfix

/-- Every stage of the counted middle climb bounds the `μX` fixed point from below, given that
    `k` innermost steps suffice at every region. -/
theorem coe_iter_mid_le (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (k : ℕ) (b y : Finset S) (m : ℕ)
    (hlw : ∀ x s, lStep supp x y s ((lStep supp x y s)^[k] ∅) = (lStep supp x y s)^[k] ∅) :
    (↑((mid supp k b y)^[m] ∅) : Set S) ≤ (C.LFInner ↑b ↑y).lfp := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      set x := (mid supp k b y)^[m] ∅
      exact le_lfInner_of_step C supp hsupp b y x (mid supp k b y x)
        (fun s => (lStep supp x y s)^[k] ∅)
        (fun s => LW_eq_coe_iter C supp hsupp k x y s (hlw x s)) ih rfl

/-- A counted middle chain run for `m` steps and seen to stop is the `μX` fixed point at `y`. -/
theorem lfInner_eq_coe_of_mid_fixed
    (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (k : ℕ) (b y c : Finset S) (m : ℕ)
    (hlw : ∀ x s, lStep supp x y s ((lStep supp x y s)^[k] ∅) = (lStep supp x y s)^[k] ∅)
    (hiter : (mid supp k b y)^[m] ∅ = c) (hfix : mid supp k b y c = c) :
    (C.LFInner ↑b ↑y).lfp = (↑c : Set S) := by
  have hle : (↑c : Set S) ≤ (C.LFInner ↑b ↑y).lfp := by
    have hm := coe_iter_mid_le C supp hsupp k b y m hlw
    rwa [hiter] at hm
  exact lfInner_eq_coe_of_fixed C supp hsupp b y c (fun s => (lStep supp c y s)^[k] ∅)
    (fun s => LW_eq_coe_iter C supp hsupp k c y s (hlw c s)) hfix.symm hle

/-- One outer limit-sure step, from a counted middle chain. -/
theorem LF_le_of_iter (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (k : ℕ) (b y c : Finset S) (m : ℕ)
    (hlw : ∀ x s, lStep supp x y s ((lStep supp x y s)^[k] ∅) = (lStep supp x y s)^[k] ∅)
    (hiter : (mid supp k b y)^[m] ∅ = c) (hfix : mid supp k b y c = c)
    (hy : C.LF ↑b ≤ (↑y : Set S)) : C.LF ↑b ≤ (↑c : Set S) :=
  LF_le_of_step C b y c (lfInner_eq_coe_of_mid_fixed C supp hsupp k b y c m hlw hiter hfix) hy

/-- The closing limit-sure step: the counted middle chain at `y` returns `y`. -/
theorem LF_eq_coe_of_iter (hsupp : ∀ s a1 a2, (C.K s a1 a2).support = (↑(supp s a1 a2) : Set S))
    (k : ℕ) (b y : Finset S) (m : ℕ)
    (hlw : ∀ x s, lStep supp x y s ((lStep supp x y s)^[k] ∅) = (lStep supp x y s)^[k] ∅)
    (hiter : (mid supp k b y)^[m] ∅ = y) (hfix : mid supp k b y y = y)
    (hy : C.LF ↑b ≤ (↑y : Set S)) : C.LF ↑b = (↑y : Set S) :=
  LF_eq_coe_of_fixed C b y (lfInner_eq_coe_of_mid_fixed C supp hsupp k b y y m hlw hiter hfix) hy

end Bridge

end Qual

end Comp
