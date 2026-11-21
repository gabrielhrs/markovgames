/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelData
import Comp.QualBridge

/-!
# The qualitative line, for a model given as data

**Status: confirmed by a clean `lake build`.**

`Comp/QualOps.lean` has the qualitative operators over an arbitrary support function, and
`Comp/QualBridge.lean` proves them correct for any support function that is the kernel's. This file
connects a `ModelData` to both, and it does three things.

**It supplies the support.** `support_toCSG` says that `supportOf` -- a transition's successors,
read off the keys of its sparse distribution -- is the support of the game the model denotes. That
is the one hypothesis `Comp/QualBridge.lean` asks for, so every operator and every loop of
`Comp/QualOps.lean`, applied to `d.supportOf hs`, is the corresponding operator or fixed point of
the model's `CSG`. Nothing is restated per operator.

It is also where the rationals stop. `supportOf` is `ℕ` data, so the kernel reduces everything
built on it whatever the weights are; the three rational conditions (`Nonneg`, `Nonzero`,
`Stochastic`) are discharged once per model, by `norm_num`, and are used here and nowhere above.

**It narrows the action quantifiers.** The operators of `Comp/QualOps.lean` range over the whole
action types, which for a model are the global namespaces `Fin d.nAct1` and `Fin d.nAct2`. A state
enables only the actions its transitions name, and the `*Tr` family -- `pre1Tr`, `aTr`, `bTr`,
`lStepTr`, `apre1Tr`, `lpre1Tr`, and the loops over them -- ranges over those instead. The two are
related by `∩ enabled`, under *pad-saturation* as the side condition, and the regions the loops
return are equal: `gRegionTr_eq`, `afRegionTr_eq`, `lfRegionTr_eq`. These are statements about the
data alone and need only `Shape`.

**It states the entry points.** Each `answers_*_of_fix` takes one equality, naming the region the
narrowed loop returned, and concludes `Comp/Objective.lean`'s `Answers`. Each `answers_*_of_data`
is the counted form: iteration counts and fixed-point observations over the dense operators, for
exhibiting a descent one step at a time. Single counted steps are `Comp/QualBridge.lean`'s
`_of_iter` lemmas, applied with `support_toCSG`.

**Not here:** the `ω`-regular shapes (`SF`, `SFG`, `SGF`, `AGF`, `LGF`, `AFG`, `LFG`), which are
the same operators at greater nesting depth.
-/

namespace Comp

namespace ModelData

variable (d : ModelData)

/-! ## The support -/

/-- **`supportOf` is the support of the game the model denotes.** The hypothesis every theorem of
    `Comp/QualBridge.lean` takes, and the only place the rational conditions are used: `Nonneg` and
    `Nonzero` make a support readable from a distribution's keys, and `Stochastic` makes the model
    a game at all. -/
theorem support_toCSG [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    ((d.toCsgQ.toCSG (d.wellFormed hs h2)).K s a1 a2).support
      = (↑(d.supportOf hs s a1 a2) : Set (Fin d.nStates)) := by
  rw [CsgQ.toCSG_support, d.supportF_eq hs h2.nonneg hnz]

/-! ## Pad-saturation

The invariant that makes the action quantifiers narrowable. A set of actions is *pad-saturated* at
`s` when it cannot tell an action from its padded representative -- equivalently, when it is the
preimage of its own enabled part under `pad`.

Why it is the right condition, and why `⊆ enabled` is not: narrowing `aSet`'s inner `∀ a2`
evaluates the disjunct `a2 ∈ v2` at the *raw* `a2`. A disabled `a2` is outside any
`v2 ⊆ enabled2`, but its representative may be inside, so the dense form demands a support
condition the narrowed form skips and the two disagree. Pad-saturation is exactly what rules that
out.

The two lemmas below make the invariant free: `aSet` and `bSet` both *produce* pad-saturated sets,
unconditionally, because the support cannot see either coordinate's padding. So along the chain
`∅ → bSet → aSet → bSet → …` the hypothesis is discharged at `∅` and carried by these two from then
on. -/

/-- A set of row actions that cannot distinguish an action from its padded representative. -/
def PadSat1 (hs : d.Shape) (s : Fin d.nStates) (v : Finset (Fin d.nAct1)) : Prop :=
  ∀ a1, a1 ∈ v ↔ d.padFin1 hs s a1 ∈ v

/-- The column player's. -/
def PadSat2 (hs : d.Shape) (s : Fin d.nStates) (v : Finset (Fin d.nAct2)) : Prop :=
  ∀ a2, a2 ∈ v ↔ d.padFin2 hs s a2 ∈ v

@[simp]
theorem padSat1_empty (hs : d.Shape) (s : Fin d.nStates) : d.PadSat1 hs s ∅ := by
  intro a1; simp

@[simp]
theorem padSat2_empty (hs : d.Shape) (s : Fin d.nStates) : d.PadSat2 hs s ∅ := by
  intro a2; simp

/-- **`aSet` produces pad-saturated sets**, for any `v2` at all. Only the support term mentions the
    row action, and the support does not see its padding. -/
theorem padSat1_aSet (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) : d.PadSat1 hs s (Qual.aSet (d.supportOf hs) v2 y s) := by
  intro a1
  simp only [Qual.mem_aSet, d.supportOf_padFin1 hs s]

/-- **And `bSet` does too**, for any `v1`. Same reason, on the other coordinate. -/
theorem padSat2_bSet (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) : d.PadSat2 hs s (Qual.bSet (d.supportOf hs) v1 x s) := by
  intro a2
  simp only [Qual.mem_bSet, d.supportOf_padFin2 hs s]

/-! ## `A` and `B` over a state's transitions

The narrowed counterparts of `aSet`/`bSet`: they range over the actions the state enables, so their
cost is `|enabled1 s| · |enabled2 s|` rather than `|A1| · |A2|`.

Each is the dense operator restricted to the enabled set, but the two restrictions are not
symmetric, and the asymmetry is the whole content of this section. `bTr` quantifies over the *same*
`v1` as `bSet`, so the correspondence is unconditional. `aTr` narrows its inner `∀ a2`, and that is
sound exactly when `v2` is pad-saturated -- which `padSat2_bSet` supplies wherever `v2` comes from
a `bSet`, and `padSat2_empty` at the base of the chain. -/

/-- `aSet` over the state's own actions. -/
def aTr (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) : Finset (Fin d.nAct1) :=
  (d.enabled1 hs s).filter fun a1 =>
    ∀ a2 ∈ d.enabled2 hs s, a2 ∈ v2 ∨ d.supportOf hs s a1 a2 ⊆ y

/-- `bSet` over the state's own actions. -/
def bTr (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) : Finset (Fin d.nAct2) :=
  (d.enabled2 hs s).filter fun a2 => ∃ a1 ∈ v1, (d.supportOf hs s a1 a2 ∩ x).Nonempty

@[simp]
theorem mem_aTr (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) (a1 : Fin d.nAct1) :
    a1 ∈ d.aTr hs v2 y s ↔
      a1 ∈ d.enabled1 hs s ∧ ∀ a2 ∈ d.enabled2 hs s, a2 ∈ v2 ∨ d.supportOf hs s a1 a2 ⊆ y := by
  simp only [aTr, Finset.mem_filter]

@[simp]
theorem mem_bTr (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) (a2 : Fin d.nAct2) :
    a2 ∈ d.bTr hs v1 x s ↔
      a2 ∈ d.enabled2 hs s ∧ ∃ a1 ∈ v1, (d.supportOf hs s a1 a2 ∩ x).Nonempty := by
  simp only [bTr, Finset.mem_filter]

/-- **`bTr` is `bSet` restricted to the enabled columns.** Unconditional: the `∃ a1 ∈ v1` is the
    same on both sides. -/
theorem bTr_eq (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) :
    d.bTr hs v1 x s = Qual.bSet (d.supportOf hs) v1 x s ∩ d.enabled2 hs s := by
  ext a2
  simp only [mem_bTr, Finset.mem_inter, Qual.mem_bSet]
  tauto

/-- **`aTr` is `aSet` restricted to the enabled rows**, given a pad-saturated `v2`. The inner
    `∀ a2` is narrowed to the enabled columns, which needs `v2` unable to tell a column action
    from its representative: otherwise the dense form demands a support condition at a disabled
    `a2` that the narrowed form never asks about. -/
theorem aTr_eq (hs : d.Shape) (s : Fin d.nStates) (v2 : Finset (Fin d.nAct2))
    (hv2 : d.PadSat2 hs s v2) (y : Finset (Fin d.nStates)) :
    d.aTr hs v2 y s = Qual.aSet (d.supportOf hs) v2 y s ∩ d.enabled1 hs s := by
  ext a1
  simp only [mem_aTr, Finset.mem_inter, Qual.mem_aSet]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨fun a2 => ?_, hm⟩
    rcases h (d.padFin2 hs s a2) (d.padFin2_mem hs s a2) with hv | hsub
    · exact Or.inl ((hv2 a2).mpr hv)
    · rw [d.supportOf_padFin2 hs s a1 a2] at hsub
      exact Or.inr hsub
  · rintro ⟨h, hm⟩
    exact ⟨hm, fun a2 _ => h a2⟩

/-- **`bTr` sees its argument only through its enabled part**, which is what keeps the chain
    narrow: the row-action sets the iteration carries are subsets of `enabled1`, while the dense
    chain's are pad-saturated. Needs pad-saturation, since a disabled row action in `v1` mirrors
    its representative and pad-saturation is the guarantee that the representative is there too. -/
theorem bTr_inter_enabled1 (hs : d.Shape) (s : Fin d.nStates) (v1 : Finset (Fin d.nAct1))
    (hv1 : d.PadSat1 hs s v1) (x : Finset (Fin d.nStates)) :
    d.bTr hs (v1 ∩ d.enabled1 hs s) x s = d.bTr hs v1 x s := by
  ext a2
  simp only [mem_bTr, Finset.mem_inter]
  constructor
  · rintro ⟨hm, a1, ⟨h1, -⟩, hne⟩
    exact ⟨hm, a1, h1, hne⟩
  · rintro ⟨hm, a1, h1, hne⟩
    refine ⟨hm, d.padFin1 hs s a1, ⟨(hv1 a1).mp h1, d.padFin1_mem hs s a1⟩, ?_⟩
    rwa [d.supportOf_padFin1 hs s a1 a2]

/-- **The test the operators consume.** `apre1` and `lpre1` ask whether every column action is
    answered; over transitions that becomes whether every *enabled* one is. The two agree because
    `bSet`'s output is pad-saturated, so a disabled column action is in it exactly when its
    representative is. -/
theorem bSet_eq_univ_iff (hs : d.Shape) (s : Fin d.nStates) (v1 : Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) :
    Qual.bSet (d.supportOf hs) v1 x s = Finset.univ ↔ d.bTr hs v1 x s = d.enabled2 hs s := by
  rw [d.bTr_eq hs v1 x s]
  constructor
  · intro h
    rw [h, Finset.univ_inter]
  · intro h
    ext a2
    simp only [Finset.mem_univ, iff_true]
    rw [d.padSat2_bSet hs v1 x s a2]
    have hmem : d.padFin2 hs s a2 ∈ Qual.bSet (d.supportOf hs) v1 x s ∩ d.enabled2 hs s := by
      rw [h]
      exact d.padFin2_mem hs s a2
    exact (Finset.mem_inter.mp hmem).1

/-- **`aTr` sees its `v2` only through the enabled columns.** No hypothesis needed, and the
    contrast with `bTr_inter_enabled1` is the point: restricting a `∀` range that is already
    restricted to `enabled2` is free, whereas restricting an `∃` witness set can lose a witness
    unless pad-saturation guarantees its representative is also there. -/
theorem aTr_inter_enabled2 (hs : d.Shape) (s : Fin d.nStates) (v2 : Finset (Fin d.nAct2))
    (y : Finset (Fin d.nStates)) :
    d.aTr hs (v2 ∩ d.enabled2 hs s) y s = d.aTr hs v2 y s := by
  ext a1
  simp only [mem_aTr, Finset.mem_inter]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, fun a2 ha2 => ?_⟩
    rcases h a2 ha2 with ⟨hv, -⟩ | hsub
    · exact Or.inl hv
    · exact Or.inr hsub
  · rintro ⟨hm, h⟩
    refine ⟨hm, fun a2 ha2 => ?_⟩
    rcases h a2 ha2 with hv | hsub
    · exact Or.inl ⟨hv, ha2⟩
    · exact Or.inr hsub

/-! ## The innermost `μW` climb over a state's transitions

`LW` is the one place the narrowing has to survive a fixed point rather than a single step, and the
two chains do not climb through the same sets: the dense one carries pad-saturated sets of row
actions, the narrowed one carries subsets of `enabled1 s`. They correspond under `∩ enabled1` at
every stage (`lStepTr_iterate_eq`), and hence where the loops stop (`lwTr_eq`).

The dense side's invariant is free, since `lStep` is an `aSet` and `padSat1_aSet` is
unconditional. -/

/-- One turn of the innermost climb, over the state's own actions. -/
def lStepTr (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (w : Finset (Fin d.nAct1)) : Finset (Fin d.nAct1) :=
  d.aTr hs (d.bTr hs w x s) y s

/-- Every stage of the dense climb is pad-saturated: each stage is an `aSet`. -/
theorem padSat1_lStep_iterate (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (k : ℕ) : d.PadSat1 hs s ((Qual.lStep (d.supportOf hs) x y s)^[k] ∅) := by
  induction k with
  | zero =>
      rw [Function.iterate_zero_apply]
      exact d.padSat1_empty hs s
  | succ k _ =>
      rw [Function.iterate_succ_apply']
      exact d.padSat1_aSet hs _ y s

/-- **The two innermost climbs correspond, stage by stage.** One step of the chain: `bTr` drops
    the disabled rows (`bTr_inter_enabled1`, on the dense stage's pad-saturation), `aTr` ignores
    the disabled columns it is handed (`aTr_inter_enabled2`), and `aTr_eq` then identifies the
    result with the dense step restricted -- its pad-saturation hypothesis discharged by
    `padSat2_bSet`. -/
theorem lStepTr_iterate_eq (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (k : ℕ) :
    (d.lStepTr hs x y s)^[k] ∅
      = (Qual.lStep (d.supportOf hs) x y s)^[k] ∅ ∩ d.enabled1 hs s := by
  induction k with
  | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply, Finset.empty_inter]
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      unfold lStepTr
      rw [d.bTr_inter_enabled1 hs s _ (d.padSat1_lStep_iterate hs x y s k) x,
        d.bTr_eq hs _ x s, d.aTr_inter_enabled2 hs s _ y,
        d.aTr_eq hs s _ (d.padSat2_bSet hs _ x s) y]
      rfl

/-- The innermost `μW` fixed point at `(x, y, s)`, over the state's own actions. -/
def lwTr (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    Finset (Fin d.nAct1) :=
  fixFrom (d.lStepTr hs x y s) ∅

/-- **Where the narrowed climb stops is the enabled part of where the dense one does.** Both loops
    are iterates of the same length (`fixAux_eq_iterate`), and the iterates correspond stage by
    stage. -/
theorem lwTr_eq (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    d.lwTr hs x y s = Qual.lw (d.supportOf hs) x y s ∩ d.enabled1 hs s := by
  unfold lwTr Qual.lw fixFrom
  rw [fixAux_eq_iterate, fixAux_eq_iterate, d.lStepTr_iterate_eq hs x y s]

/-- The dense witness set is pad-saturated, being a stage of the dense climb. -/
theorem padSat1_lw (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    d.PadSat1 hs s (Qual.lw (d.supportOf hs) x y s) := by
  unfold Qual.lw fixFrom
  rw [fixAux_eq_iterate]
  exact d.padSat1_lStep_iterate hs x y s _

/-! ## `Pre1`, `Apre1` and `Lpre1` over a state's transitions

`pre1` has the shape `∃ a1, ∀ a2, P a1 a2` with `P` factoring through the support, so it narrows by
`Comp/ModelData.lean`'s `exists_forall_enabled_iff` alone. The other two ask "is every column
action answered?", which over transitions becomes "is every *enabled* column action answered?";
`bSet_eq_univ_iff` is what makes the two the same question. -/

/-- `pre1` over the state's own actions. -/
def pre1Tr (hs : d.Shape) (x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s =>
    ∃ a1 ∈ d.enabled1 hs s, ∀ a2 ∈ d.enabled2 hs s, d.supportOf hs s a1 a2 ⊆ x

@[simp]
theorem mem_pre1Tr (hs : d.Shape) (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.pre1Tr hs x ↔
      ∃ a1 ∈ d.enabled1 hs s, ∀ a2 ∈ d.enabled2 hs s, d.supportOf hs s a1 a2 ⊆ x := by
  simp only [pre1Tr, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **`pre1`, narrowed.** A disabled witness is replaced by its padded representative, and a
    disabled response is answered through its own. -/
theorem pre1Tr_eq (hs : d.Shape) (x : Finset (Fin d.nStates)) :
    d.pre1Tr hs x = Qual.pre1 (d.supportOf hs) x := by
  ext s
  have hP : ∀ a1 a2, d.supportOf hs s (d.padFin1 hs s a1) (d.padFin2 hs s a2) ⊆ x ↔
      d.supportOf hs s a1 a2 ⊆ x := fun a1 a2 => by rw [d.supportOf_padFin hs s a1 a2]
  rw [mem_pre1Tr, Qual.mem_pre1]
  exact (d.exists_forall_enabled_iff hs s (fun a1 a2 => d.supportOf hs s a1 a2 ⊆ x) hP).symm

/-- `apre1` over the state's own actions. -/
def apre1Tr (hs : d.Shape) (x y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bTr hs (d.aTr hs ∅ y s) x s = d.enabled2 hs s

@[simp]
theorem mem_apre1Tr (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.apre1Tr hs x y ↔ d.bTr hs (d.aTr hs ∅ y s) x s = d.enabled2 hs s := by
  simp only [apre1Tr, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **`apre1`, narrowed.** Three steps and every side condition is free: `aTr_eq` at `v2 = ∅`
    (pad-saturated by `padSat2_empty`), `bTr_inter_enabled1` on the pad-saturation of an `aSet`
    output, and `bSet_eq_univ_iff` to trade `= Finset.univ` for `= enabled2 s`. -/
theorem apre1Tr_eq (hs : d.Shape) (x y : Finset (Fin d.nStates)) :
    d.apre1Tr hs x y = Qual.apre1 (d.supportOf hs) x y := by
  ext s
  rw [mem_apre1Tr, Qual.mem_apre1,
    d.aTr_eq hs s ∅ (d.padSat2_empty hs s) y,
    d.bTr_inter_enabled1 hs s _ (d.padSat1_aSet hs ∅ y s) x]
  exact (d.bSet_eq_univ_iff hs s _ x).symm

/-- `lpre1` over the state's own actions, given a narrowed witness family. -/
def lpre1Tr (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bTr hs (w s) x s = d.enabled2 hs s

@[simp]
theorem mem_lpre1Tr (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.lpre1Tr hs w x ↔ d.bTr hs (w s) x s = d.enabled2 hs s := by
  simp only [lpre1Tr, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **`lpre1`, narrowed.** The witness family is given twice -- the dense one and the narrow one
    the computation carries -- related by `∩ enabled1` at every state. The dense family must be
    pad-saturated, which `padSat1_lw` supplies for the family that arises. -/
theorem lpre1Tr_eq (hs : d.Shape) (wF wTr : Fin d.nStates → Finset (Fin d.nAct1))
    (hw : ∀ s, wTr s = wF s ∩ d.enabled1 hs s) (hpad : ∀ s, d.PadSat1 hs s (wF s))
    (x : Finset (Fin d.nStates)) :
    d.lpre1Tr hs wTr x = Qual.lpre1 (d.supportOf hs) wF x := by
  ext s
  rw [mem_lpre1Tr, Qual.mem_lpre1, hw s, d.bTr_inter_enabled1 hs s _ (hpad s) x]
  exact (d.bSet_eq_univ_iff hs s _ x).symm

/-! ## The loops over a state's transitions

The steps above are equal to the dense ones as functions, so the loops built on them return the
same regions. What differs is the cost of a step. -/

/-- One turn of the sure-safety descent, over the state's own actions. -/
def gStepTr (hs : d.Shape) (safe x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.pre1Tr hs x ∩ safe

theorem gStepTr_eq_fun (hs : d.Shape) (safe : Finset (Fin d.nStates)) :
    d.gStepTr hs safe = Qual.gStep (d.supportOf hs) safe := by
  funext x
  unfold gStepTr Qual.gStep
  rw [d.pre1Tr_eq hs x]

/-- **The sure-safety region, computed over each state's own actions.** -/
def gRegionTr (hs : d.Shape) (safe : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.gStepTr hs safe) Finset.univ

theorem gRegionTr_eq (hs : d.Shape) (safe : Finset (Fin d.nStates)) :
    d.gRegionTr hs safe = Qual.gRegion (d.supportOf hs) safe := by
  unfold gRegionTr Qual.gRegion
  rw [d.gStepTr_eq_fun hs safe]

/-- One turn of the almost-sure middle chain, over the state's own actions. -/
def afStepTr (hs : d.Shape) (b y x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.apre1Tr hs x y ∪ b

theorem afStepTr_eq_fun (hs : d.Shape) (b y : Finset (Fin d.nStates)) :
    d.afStepTr hs b y = Qual.afStep (d.supportOf hs) b y := by
  funext x
  unfold afStepTr Qual.afStep
  rw [d.apre1Tr_eq hs x y]

/-- The middle `μX` fixed point at `y`, over the state's own actions. -/
def afInnerTr (hs : d.Shape) (b y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.afStepTr hs b y) ∅

theorem afInnerTr_eq_fun (hs : d.Shape) (b : Finset (Fin d.nStates)) :
    d.afInnerTr hs b = Qual.afInner (d.supportOf hs) b := by
  funext y
  unfold afInnerTr Qual.afInner
  rw [d.afStepTr_eq_fun hs b y]

/-- **The almost-sure reachability region, computed over each state's own actions.** -/
def afRegionTr (hs : d.Shape) (b : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.afInnerTr hs b) Finset.univ

theorem afRegionTr_eq (hs : d.Shape) (b : Finset (Fin d.nStates)) :
    d.afRegionTr hs b = Qual.afRegion (d.supportOf hs) b := by
  unfold afRegionTr Qual.afRegion
  rw [d.afInnerTr_eq_fun hs b]

/-- One turn of the limit-sure middle chain, over the state's own actions. -/
def lmidTr (hs : d.Shape) (b y x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.lpre1Tr hs (d.lwTr hs x y) x ∪ b

/-- The two middle steps are one function: `lpre1Tr_eq`, at the witness families the two
    innermost loops compute. -/
theorem lmidTr_eq_fun (hs : d.Shape) (b y : Finset (Fin d.nStates)) :
    d.lmidTr hs b y = Qual.lmid (d.supportOf hs) b y := by
  funext x
  unfold lmidTr Qual.lmid
  rw [d.lpre1Tr_eq hs (Qual.lw (d.supportOf hs) x y) (d.lwTr hs x y)
    (fun s => d.lwTr_eq hs x y s) (fun s => d.padSat1_lw hs x y s) x]

/-- The middle `μX` fixed point at `y`, over the state's own actions. -/
def lfInnerTr (hs : d.Shape) (b y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.lmidTr hs b y) ∅

theorem lfInnerTr_eq_fun (hs : d.Shape) (b : Finset (Fin d.nStates)) :
    d.lfInnerTr hs b = Qual.lfInner (d.supportOf hs) b := by
  funext y
  unfold lfInnerTr Qual.lfInner
  rw [d.lmidTr_eq_fun hs b y]

/-- **The value-1 set, computed over each state's own actions.** -/
def lfRegionTr (hs : d.Shape) (b : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.lfInnerTr hs b) Finset.univ

theorem lfRegionTr_eq (hs : d.Shape) (b : Finset (Fin d.nStates)) :
    d.lfRegionTr hs b = Qual.lfRegion (d.supportOf hs) b := by
  unfold lfRegionTr Qual.lfRegion
  rw [d.lfInnerTr_eq_fun hs b]

/-! ## The entry points

A model, an objective and a computed region, in one term. The caller names the region and says, by
one decidable check, that it is what the loop returned; no iteration count and no fixed-point
check, because the loops stop on their own and are proved to. The loops are the narrowed ones, and
the `*_eq` lemmas above identify what they return with the regions `Comp/QualBridge.lean` proves
correct. -/

/-- **Sure safety from a model.** -/
theorem answers_sureSafe_of_fix [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (safe c : Finset (Fin d.nStates))
    (hc : d.gRegionTr hs safe = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.sureSafe safe) (Answer.region c) := by
  subst hc
  rw [d.gRegionTr_eq hs safe]
  exact .sureSafe (Qual.G_eq_coe_gRegion (d.toCsgQ.toCSG (d.wellFormed hs h2)) (d.supportOf hs)
    (d.support_toCSG hs h2 hnz) safe)

/-- **Almost-sure reachability from a model.** -/
theorem answers_almostReach_of_fix [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b c : Finset (Fin d.nStates))
    (hc : d.afRegionTr hs b = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.almostReach b) (Answer.region c) := by
  subst hc
  rw [d.afRegionTr_eq hs b]
  exact .almostReach (Qual.AF_eq_coe_afRegion (d.toCsgQ.toCSG (d.wellFormed hs h2))
    (d.supportOf hs) (d.support_toCSG hs h2 hnz) b)

/-- **The value-1 set of a model**: the states from which the row player reaches `b` with
    probability arbitrarily close to one. -/
theorem answers_limitReach_of_fix [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b c : Finset (Fin d.nStates))
    (hc : d.lfRegionTr hs b = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.limitReach b) (Answer.region c) := by
  subst hc
  rw [d.lfRegionTr_eq hs b]
  exact .limitReach (Qual.LF_eq_coe_lfRegion (d.toCsgQ.toCSG (d.wellFormed hs h2))
    (d.supportOf hs) (d.support_toCSG hs h2 hnz) b)

/-! ## The counted entry points

The same three answers from iteration counts and fixed-point observations over the dense
operators, which is how a descent is exhibited one step at a time. `hy` in the two reachability
forms is the outer descent, built from `Qual.AF_le_univ` or `Qual.LF_le_univ` by one
`Qual.AF_le_of_iter` or `Qual.LF_le_of_iter` per step. -/

/-- Sure safety, counted: `n` steps of the descent reach `c`, and `c` is fixed. -/
theorem answers_sureSafe_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (safe c : Finset (Fin d.nStates)) (n : ℕ)
    (hiter : (Qual.gStep (d.supportOf hs) safe)^[n] Finset.univ = c)
    (hfix : Qual.gStep (d.supportOf hs) safe c = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.sureSafe safe) (Answer.region c) :=
  .sureSafe (Qual.G_eq_coe_of_fixed (d.toCsgQ.toCSG (d.wellFormed hs h2)) (d.supportOf hs)
    (d.support_toCSG hs h2 hnz) safe c n hiter hfix)

/-- Almost-sure reachability, counted: the middle chain at `y` returns `y` in `m` steps, and the
    outer descent has reached `y`. -/
theorem answers_almostReach_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (Qual.afStep (d.supportOf hs) b y)^[m] ∅ = y)
    (hfix : Qual.afStep (d.supportOf hs) b y y = y)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.almostReach b) (Answer.region y) :=
  .almostReach (Qual.AF_eq_coe_of_iter (d.toCsgQ.toCSG (d.wellFormed hs h2)) (d.supportOf hs)
    (d.support_toCSG hs h2 hnz) b y m hiter hfix hy)

/-- Limit-sure reachability, counted. `hlw` says `k` steps of the innermost climb reach a fixed
    point at every region and state, which over all regions is `2 ^ |S| · |S|` instances; the loop
    form asks for none of it. -/
theorem answers_limitReach_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (k : ℕ) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, Qual.lStep (d.supportOf hs) x y s ((Qual.lStep (d.supportOf hs) x y s)^[k] ∅)
      = (Qual.lStep (d.supportOf hs) x y s)^[k] ∅)
    (hiter : (Qual.mid (d.supportOf hs) k b y)^[m] ∅ = y)
    (hfix : Qual.mid (d.supportOf hs) k b y y = y)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.limitReach b) (Answer.region y) :=
  .limitReach (Qual.LF_eq_coe_of_iter (d.toCsgQ.toCSG (d.wellFormed hs h2)) (d.supportOf hs)
    (d.support_toCSG hs h2 hnz) k b y m hlw hiter hfix hy)

end ModelData

end Comp
