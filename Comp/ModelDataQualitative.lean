/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelData
import Comp.FixLoop

/-!
# The qualitative operators, computed from sparse data

**Status: confirmed by a clean `lake build`.**

Two families of operators live here. The `*Of` ones quantify over the whole action namespace and
are what the `answers_*` entry points still use. The `*Tr` ones -- `aTr`, `bTr`, `lStepTr`,
`apre1Tr`, `lpre1Tr` -- quantify over a state's enabled actions instead, and are related to the
dense ones by `∩ enabled`, with pad-saturation as the side condition. The transfer lemmas are
proved; rewiring the entry points to use them is not done, so the narrowing is not yet realised in
anything a model actually runs.

`Comp/ModelData.lean` ends with `supportF_eq`: a model's support, read off its sparse row instead of
found by scanning the states. That lemma is where the cost goes away, but on its own it changes
nothing, because every operator above it is still *defined* through `supportF`. This file carries
the substitution upward for the sure-safety line -- `Pre1` and the `G`-step -- so that a model given
as data computes through its own rows from end to end.

**The pattern, once, for every model.** `Comp/HideOrRunQ.lean` does this by hand for one game: it
defines `aC`, `bC`, `lStepC` with its own support table substituted and proves each equal to the
general operator. Those definitions are per-game and have to be rewritten for the next one. Here
the same work is done against `ModelData`, so it is done for every model at once, and an instance
supplies nothing but the two decidable validity checks.

**What that buys, concretely.** `pre1Of` and `gStepOf` are computable functions of the sparse rows,
so `(d.gStepOf hs safe)^[n] Finset.univ` is something `#eval` prints and `decide` can check. Two
things had been blocking the latter. One is the state scan, now gone. The other is that the kernel
cannot do rational arithmetic -- which, with the weights written as fractions, means it cannot even
*evaluate* a weight, since `(1/2 : ℚ)` is a division. `supportOf` sidesteps both by being built from
`keysNat`, which is `ℕ` data: a support is read off the row's keys and the weights are never
inspected. So the operators here reduce in the kernel for a model with any weights at all, and the
three rational side conditions (`Nonneg`, `Nonzero`, `Stochastic`) are discharged once per model by
`norm_num`, outside the computation.

**The entry point is `answers_sureSafe_of_data`.** It takes the two validity checks and the two
fixed-point observations, all four decidable, and returns an `Answers` -- the specification relation
of `Comp/Objective.lean`. So a model, an objective and a computed region meet in one term, and the
`Csg/` side of it is `CSG.G` exactly, by `Comp/QualitativeFinset.lean`'s `G_eq_coe_of_fixed`.

Note which hypothesis is needed where. The transfer lemmas want `Nonneg` and `Nonzero` -- the two
conditions that make a support readable from the keys -- while `Stochastic` is needed once, at the
end, to make the data a well-formed game. Keeping them apart is what lets the first two be stated as
facts about rows rather than about distributions.

**Two lines reach a computed answer here**, the sure-safety one (`Pre1`, `G`) and the almost-sure
one (`A`, `B`, `Apre1`, `AF`). The second is the interesting case: `Apre1` reads its row-action pool
straight off `A ∅ y s` with no inner fixed point, so `afStepOf` is a function of `x` alone and the
`μX` chain is an honest `Function.iterate`. That is what lets `answers_almostReach_of_data` ask the
caller for nothing but `decide`-able facts about the rows.

**All three modes reach a computed answer here**: sure safety (`Pre1`, `G`), almost-sure
reachability (`A`, `B`, `Apre1`, `AF`) and limit-sure reachability (`LW`, `Lpre1`, `LF`) -- the last
being the value-1 set, which is the one a probabilistic reachability precomputation actually needs.
The three differ only in how much structure sits between the rows and the answer: none for sure
safety, a middle `μX` chain for almost-sure, and a fixed point inside that chain for limit-sure.

**Two interfaces per mode.** Each `answers_*_of_data` takes an iteration count and the observation
that that many steps land on the answer. Each `answers_*_of_fix` takes neither: it runs
`Comp/FixLoop.lean`'s apply-compare-stop loop, which is proved to terminate at a fixed point, so the
caller supplies one equality -- the region the loop returned. `gRegion` is one such loop, `afRegion`
two nested (the outer `νY` descent over the inner `μX` climb), and `lfRegion` three.

**Not here:** the `ω`-regular shapes (`SF`, `SFG`, `SGF`, `AGF`, `LGF`, `AFG`, `LFG`), which are the
same substitutions again at greater nesting depth.
-/

namespace Comp

namespace ModelData

variable (d : ModelData)

/-! ## `Pre1`, from the rows -/

/-- `Comp/QualitativeFinset.lean`'s `pre1F` with the support read off the sparse row: the states
    from which some row action keeps every column response inside `x`.

    Needs only `Shape`, which `supportOf` needs anyway -- no `NeZero`, because this is a
    computation on the data and never mentions the game it denotes. -/
def pre1Of (hs : d.Shape) (x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => ∃ a1, ∀ a2, d.supportOf hs s a1 a2 ⊆ x

@[simp]
theorem mem_pre1Of (hs : d.Shape) (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.pre1Of hs x ↔ ∃ a1, ∀ a2, d.supportOf hs s a1 a2 ⊆ x := by
  simp only [pre1Of, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The transfer lemma: the general operator and the row-based one agree. `supportF_eq` rewritten
    under the two quantifiers, which is all there is to it -- both have the same shape.

    Note what this does *not* do: narrow the action quantifiers to the state's enabled actions.
    That is sound for this operator but not piecewise for `aOf`/`bOf`, so all three modes are left
    with the same shape; see `Comp/ModelData.lean`'s `exists_forall_enabled_iff`. -/
theorem pre1F_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x : Finset (Fin d.nStates)) :
    d.toCsgQ.pre1F x = d.pre1Of hs x := by
  ext s
  simp only [CsgQ.mem_pre1F, mem_pre1Of, d.supportF_eq hs hnn hnz]

/-! ## The sure-safety step, from the rows -/

/-- `gStepF`'s shape, over the rows: `pre1Of x ∩ safe`. A computable `Finset → Finset`, so
    `Function.iterate` drives it and `#eval` prints it. -/
def gStepOf (hs : d.Shape) (safe x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.pre1Of hs x ∩ safe

theorem gStepF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (safe x : Finset (Fin d.nStates)) :
    d.toCsgQ.gStepF safe x = d.gStepOf hs safe x := by
  unfold CsgQ.gStepF gStepOf
  rw [d.pre1F_eq hs hnn hnz x]

/-- The same, as an equality of *functions*, which is the form a rewrite inside
    `Function.iterate` needs. -/
theorem gStepF_eq_fun [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (safe : Finset (Fin d.nStates)) :
    d.toCsgQ.gStepF safe = d.gStepOf hs safe :=
  funext fun x => d.gStepF_eq hs hnn hnz safe x

/-! ## The entry point -/

/-- **A model, an objective, and a computed answer, in one term.** The descent is run over the
    sparse rows; `hiter` records that it reached `c` and `hfix` that it stopped there; and the
    conclusion is `Comp/Objective.lean`'s specification relation, whose sure-safety constructor is
    `CSG.G` on the nose.

    All four hypotheses are decidable statements about concrete data, and three of the four involve
    no rational arithmetic at all. `Stochastic` is the exception and is needed only here, to make
    the model a well-formed game. -/
theorem answers_sureSafe_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (safe c : Finset (Fin d.nStates)) (n : ℕ)
    (hiter : (d.gStepOf hs safe)^[n] Finset.univ = c)
    (hfix : d.gStepOf hs safe c = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.sureSafe safe) (Answer.region c) := by
  refine CsgQ.answers_sureSafe d.toCsgQ (d.wellFormed hs h2) safe c n ?_ ?_
  · rw [d.gStepF_eq_fun hs h2.nonneg hnz safe]
    exact hiter
  · rw [d.gStepF_eq hs h2.nonneg hnz safe c]
    exact hfix

/-! ## The same, without an iteration count

`answers_sureSafe_of_data` above asks for `n` and for the observation that `n` steps land on `c`.
Nobody can anticipate `n`, and the algorithm does not need to be told: `Comp/FixLoop.lean`'s loop
applies the step, compares, and stops when nothing changes -- and, by `fixFrom_univ_fixed`, is
proved to stop. So the fixed-point check goes too, and the caller supplies one equality: the region
the loop returned. -/

/-- **The sure-safety region, computed.** Run the descent from `Finset.univ` until it stops. No
    iteration count: `#eval d.gRegion hs safe` prints the answer, and `decide` checks it. -/
def gRegion (hs : d.Shape) (safe : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.gStepOf hs safe) Finset.univ

/-- The step over the rows is the specification's own `GOrderHom`, under `Finset.coe`. This is the
    `hf` that `Comp/FixLoop.lean`'s lemmas take -- the single bridge between the loop and the
    real-valued game, and the only place the three transfer lemmas are needed. -/
theorem coe_gStepOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (safe x : Finset (Fin d.nStates)) :
    (↑(d.gStepOf hs safe x) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).GOrderHom ↑safe ↑x := by
  rw [← d.gStepF_eq hs h2.nonneg hnz safe x, CsgQ.coe_gStepF, CsgQ.GOrderHom_toCSG]

/-- **Where the loop stops *is* the sure-safety region.** Unconditionally: the downward half comes
    from `Comp/FixLoop.lean`'s `gfp_le_coe_fixAux`, one `OrderHom.gfp_le_of_step` per level of fuel,
    and the upward half from `fixFrom_univ_fixed`, which proves that `Fintype.card S` steps always
    reach a fixed point. Nothing is counted and nothing is checked -- `coe_gStepOf` is the only
    input, and even the monotonicity `fixFrom_univ_fixed` needs comes out of it. -/
theorem G_eq_coe_gRegion [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (safe : Finset (Fin d.nStates)) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).G (↑safe : Set (Fin d.nStates))
      = (↑(d.gRegion hs safe) : Set (Fin d.nStates)) :=
  gfp_eq_coe_fixFrom_univ _ _ (d.coe_gStepOf hs h2 hnz safe)

/-- **A model, an objective, and a computed answer -- with nothing counted and nothing certified.**
    The caller names the region and says, by one decidable check, that it is what the loop returned.

    Compare `answers_sureSafe_of_data`, which wants an iteration count *and* a fixed-point check.
    Both are gone: the count because the loop stops on its own, the check because the loop is proved
    to stop. What is left is the one thing a caller genuinely has to say -- which `Finset` it is
    claiming the answer to be. -/
theorem answers_sureSafe_of_fix [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (safe c : Finset (Fin d.nStates))
    (hc : d.gRegion hs safe = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.sureSafe safe) (Answer.region c) := by
  subst hc
  exact .sureSafe (d.G_eq_coe_gRegion hs h2 hnz safe)

/-! ## Pad-saturation

The invariant that makes the action quantifiers narrowable. A set of actions is *pad-saturated* at
`s` when it cannot tell an action from its padded representative -- equivalently, when it is the
preimage of its own enabled part under `pad`.

Why it is the right condition, and why `⊆ enabled` is not: narrowing `aF`'s inner `∀ a2` evaluates
the disjunct `a2 ∈ v2` at the *raw* `a2`. A disabled `a2` is outside any `v2 ⊆ enabled2`, but its
representative may be inside, so the dense form demands a support condition the narrowed form skips
and the two disagree. Pad-saturation is exactly what rules that out.

The two lemmas below are what make the invariant free rather than a burden: `aF` and `bF` both
*produce* pad-saturated sets, unconditionally, because the support cannot see either coordinate's
padding. So along the chain `∅ → bF → aF → bF → …` the hypothesis is discharged at `∅` and carried
by these two from then on. -/

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

/-- **`aF` produces pad-saturated sets**, for any `v2` at all. Only the support term mentions the
    row action, and the support does not see its padding. -/
theorem padSat1_aF [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) : d.PadSat1 hs s (d.toCsgQ.aF v2 y s) := by
  intro a1
  simp only [CsgQ.mem_aF, d.supportF_eq hs hnn hnz, d.supportOf_padFin1 hs s]

/-- **And `bF` does too**, for any `v1`. Same reason, on the other coordinate. -/
theorem padSat2_bF [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) : d.PadSat2 hs s (d.toCsgQ.bF v1 x s) := by
  intro a2
  simp only [CsgQ.mem_bF, d.supportF_eq hs hnn hnz, d.supportOf_padFin2 hs s]

/-! ## `A` and `B` over a state's transitions

The narrowed counterparts of `aOf`/`bOf`: they range over the actions the state enables, so their
cost is `|enabled1 s| · |enabled2 s|` rather than `|A1| · |A2|`.

Each is the dense operator restricted to the enabled set, but the two restrictions are not
symmetric, and the asymmetry is the whole content of this section. `bTr` quantifies over the *same*
`v1` as `bF`, so the correspondence is unconditional. `aTr` narrows its inner `∀ a2`, and that is
sound exactly when `v2` is pad-saturated -- which `padSat2_bF` supplies wherever `v2` comes from a
`bF`, and `padSat2_empty` at the base of the chain. -/

/-- `aF` over the state's own actions. -/
def aTr (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) : Finset (Fin d.nAct1) :=
  (d.enabled1 hs s).filter fun a1 =>
    ∀ a2 ∈ d.enabled2 hs s, a2 ∈ v2 ∨ d.supportOf hs s a1 a2 ⊆ y

/-- `bF` over the state's own actions. -/
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

/-- **`bTr` is `bF` restricted to the enabled columns.** Unconditional: the `∃ a1 ∈ v1` is the
    same on both sides, so only the support substitution is involved. -/
theorem bTr_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) :
    d.bTr hs v1 x s = d.toCsgQ.bF v1 x s ∩ d.enabled2 hs s := by
  ext a2
  simp only [mem_bTr, Finset.mem_inter, CsgQ.mem_bF, d.supportF_eq hs hnn hnz]
  tauto

/-- **`aTr` is `aF` restricted to the enabled rows** -- and here pad-saturation earns its keep. The
    inner `∀ a2` is narrowed to the enabled columns, which needs `v2` unable to tell a column
    action from its representative: otherwise the dense form demands a support condition at a
    disabled `a2` that the narrowed form never asks about. -/
theorem aTr_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (s : Fin d.nStates) (v2 : Finset (Fin d.nAct2))
    (hv2 : d.PadSat2 hs s v2) (y : Finset (Fin d.nStates)) :
    d.aTr hs v2 y s = d.toCsgQ.aF v2 y s ∩ d.enabled1 hs s := by
  ext a1
  simp only [mem_aTr, Finset.mem_inter, CsgQ.mem_aF, d.supportF_eq hs hnn hnz]
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

/-- **The test the operators actually consume.** `apre1Of` and `lpre1Of` ask whether every column
    action is answered; over transitions that becomes whether every *enabled* one is. The two agree
    because `bF`'s output is pad-saturated, so a disabled column action is in it exactly when its
    representative is. -/
theorem bF_eq_univ_iff [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (s : Fin d.nStates) (v1 : Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) :
    d.toCsgQ.bF v1 x s = Finset.univ ↔ d.bTr hs v1 x s = d.enabled2 hs s := by
  rw [d.bTr_eq hs hnn hnz v1 x s]
  constructor
  · intro h
    rw [h, Finset.univ_inter]
  · intro h
    ext a2
    simp only [Finset.mem_univ, iff_true]
    rw [d.padSat2_bF hs hnn hnz v1 x s a2]
    have hmem : d.padFin2 hs s a2 ∈ d.toCsgQ.bF v1 x s ∩ d.enabled2 hs s := by
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

/-! ## The inner `μW` climb over a state's transitions

`LW` is the one place the narrowing has to survive a fixed point rather than a single step, and the
two chains do not climb through the same sets: the dense one carries pad-saturated sets of row
actions, the narrowed one carries subsets of `enabled1 s`. They correspond under `∩ enabled1` at
every stage, which is what `lStepTr_iterate_eq` says.

The dense side's invariant is free, since `lStepF` is an `aF` and `padSat1_aF` is unconditional. -/

/-- One turn of the inner climb, over the state's own actions. -/
def lStepTr (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (w : Finset (Fin d.nAct1)) : Finset (Fin d.nAct1) :=
  d.aTr hs (d.bTr hs w x s) y s

/-- Every stage of the dense climb is pad-saturated -- the invariant the correspondence needs,
    and it costs nothing because each stage is an `aF`. -/
theorem padSat1_lStepF_iterate [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) (k : ℕ) :
    d.PadSat1 hs s ((d.toCsgQ.lStepF x y s)^[k] ∅) := by
  induction k with
  | zero =>
      rw [Function.iterate_zero_apply]
      exact d.padSat1_empty hs s
  | succ k _ =>
      rw [Function.iterate_succ_apply']
      exact d.padSat1_aF hs hnn hnz _ y s

/-- **The two inner climbs correspond, stage by stage.** One step of the chain: `bTr` drops the
    disabled rows (`bTr_inter_enabled1`, on the dense stage's pad-saturation), `aTr` ignores the
    disabled columns it is handed (`aTr_inter_enabled2`), and `aTr_eq` then identifies the result
    with the dense step restricted -- its pad-saturation hypothesis discharged by `padSat2_bF`. -/
theorem lStepTr_iterate_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) (k : ℕ) :
    (d.lStepTr hs x y s)^[k] ∅
      = (d.toCsgQ.lStepF x y s)^[k] ∅ ∩ d.enabled1 hs s := by
  induction k with
  | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply, Finset.empty_inter]
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      unfold lStepTr
      rw [d.bTr_inter_enabled1 hs s _ (d.padSat1_lStepF_iterate hs hnn hnz x y s k) x,
        d.bTr_eq hs hnn hnz _ x s, d.aTr_inter_enabled2 hs s _ y,
        d.aTr_eq hs hnn hnz s _ (d.padSat2_bF hs hnn hnz _ x s) y]
      rfl

/-! ## `Apre1` and `Lpre1` over a state's transitions

The two places the operators ask "is every column action answered?". Over transitions that becomes
"is every *enabled* column action answered?", and `bF_eq_univ_iff` is what makes the two the same
question. -/

/-- `Apre1` over the state's own actions. -/
def apre1Tr (hs : d.Shape) (x y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bTr hs (d.aTr hs ∅ y s) x s = d.enabled2 hs s

@[simp]
theorem mem_apre1Tr (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.apre1Tr hs x y ↔ d.bTr hs (d.aTr hs ∅ y s) x s = d.enabled2 hs s := by
  simp only [apre1Tr, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **`Apre1`, narrowed.** Three steps and every side condition is free: `aTr_eq` at `v2 = ∅`
    (pad-saturated by `padSat2_empty`), `bTr_inter_enabled1` on the pad-saturation of an `aF`
    output, and `bF_eq_univ_iff` to trade `= Finset.univ` for `= enabled2 s`. -/
theorem apre1Tr_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) :
    d.apre1Tr hs x y = d.toCsgQ.apre1F x y := by
  ext s
  rw [mem_apre1Tr, CsgQ.mem_apre1F,
    d.aTr_eq hs hnn hnz s ∅ (d.padSat2_empty hs s) y,
    d.bTr_inter_enabled1 hs s _ (d.padSat1_aF hs hnn hnz ∅ y s) x]
  exact (d.bF_eq_univ_iff hs hnn hnz s _ x).symm

/-- `Lpre1` over the state's own actions, given a narrowed witness family. -/
def lpre1Tr (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bTr hs (w s) x s = d.enabled2 hs s

@[simp]
theorem mem_lpre1Tr (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.lpre1Tr hs w x ↔ d.bTr hs (w s) x s = d.enabled2 hs s := by
  simp only [lpre1Tr, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **`Lpre1`, narrowed.** The witness family is given twice -- the dense one the specification
    talks about and the narrow one the computation carries -- related by `∩ enabled1` at every
    state. The dense family must be pad-saturated, which `padSat1_lStepF_iterate` supplies for the
    family that actually arises. -/
theorem lpre1Tr_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (wF wTr : Fin d.nStates → Finset (Fin d.nAct1))
    (hw : ∀ s, wTr s = wF s ∩ d.enabled1 hs s) (hpad : ∀ s, d.PadSat1 hs s (wF s))
    (x : Finset (Fin d.nStates)) :
    d.lpre1Tr hs wTr x = d.toCsgQ.lpre1F wF x := by
  ext s
  rw [mem_lpre1Tr, CsgQ.mem_lpre1F, hw s, d.bTr_inter_enabled1 hs s _ (hpad s) x]
  exact (d.bF_eq_univ_iff hs hnn hnz s _ x).symm

/-! ## `A` and `B`, from the rows

The two one-step combinators `Csg/QualitativeAlmostSure.lean` builds everything above `Pre1` out of.
Same pattern as `pre1Of`: `supportOf` in place of `supportF`, and one `ext`-plus-`simp only`. -/

/-- `Comp/QualitativeLimitFinset.lean`'s `aF` over the rows: the row actions at `s` that keep every
    unexcused column response inside `y`. -/
def aOf (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) : Finset (Fin d.nAct1) :=
  Finset.univ.filter fun a1 => ∀ a2, a2 ∈ v2 ∨ d.supportOf hs s a1 a2 ⊆ y

@[simp]
theorem mem_aOf (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) (a1 : Fin d.nAct1) :
    a1 ∈ d.aOf hs v2 y s ↔ ∀ a2, a2 ∈ v2 ∨ d.supportOf hs s a1 a2 ⊆ y := by
  simp only [aOf, Finset.mem_filter, Finset.mem_univ, true_and]

theorem aF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) :
    d.toCsgQ.aF v2 y s = d.aOf hs v2 y s := by
  ext a1
  simp only [CsgQ.mem_aF, mem_aOf, d.supportF_eq hs hnn hnz]

/-- `bF` over the rows: the column actions at `s` against which some row action in `v1` can reach
    `x`. -/
def bOf (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) : Finset (Fin d.nAct2) :=
  Finset.univ.filter fun a2 => ∃ a1 ∈ v1, (d.supportOf hs s a1 a2 ∩ x).Nonempty

@[simp]
theorem mem_bOf (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) (a2 : Fin d.nAct2) :
    a2 ∈ d.bOf hs v1 x s ↔ ∃ a1 ∈ v1, (d.supportOf hs s a1 a2 ∩ x).Nonempty := by
  simp only [bOf, Finset.mem_filter, Finset.mem_univ, true_and]

theorem bF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) :
    d.toCsgQ.bF v1 x s = d.bOf hs v1 x s := by
  ext a2
  simp only [CsgQ.mem_bF, mem_bOf, d.supportF_eq hs hnn hnz]

/-- `lStepF` over the rows: one turn of `lpreXY`'s inner loop. Not used below -- the limit-sure
    line needs the witness-family machinery that `Comp/QualitativeLimitReach.lean` states per
    step -- but it is the same two lines as the rest, and it is what that line will be built on. -/
def lStepOf (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (w : Finset (Fin d.nAct1)) : Finset (Fin d.nAct1) :=
  d.aOf hs (d.bOf hs w x s) y s

theorem lStepF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    d.toCsgQ.lStepF x y s = d.lStepOf hs x y s := by
  funext w
  unfold CsgQ.lStepF lStepOf
  rw [d.bF_eq hs hnn hnz, d.aF_eq hs hnn hnz]

/-! ## `Apre1` and the almost-sure step, from the rows

Where the almost-sure line gets cheap. `Apre1` reads its row-action pool straight off `A ∅ y s`
with no inner fixed point, so `afStepOf` is a function of `x` alone and the middle chain is an
honest `Function.iterate` -- which is why `AF` reaches a computed answer in this file while `LF`
waits for the next. -/

/-- `apre1F` over the rows. -/
def apre1Of (hs : d.Shape) (x y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bOf hs (d.aOf hs ∅ y s) x s = Finset.univ

@[simp]
theorem mem_apre1Of (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.apre1Of hs x y ↔ d.bOf hs (d.aOf hs ∅ y s) x s = Finset.univ := by
  simp only [apre1Of, Finset.mem_filter, Finset.mem_univ, true_and]

theorem apre1F_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) :
    d.toCsgQ.apre1F x y = d.apre1Of hs x y := by
  ext s
  simp only [CsgQ.mem_apre1F, mem_apre1Of, d.bF_eq hs hnn hnz, d.aF_eq hs hnn hnz]

/-- One turn of the almost-sure middle chain, over the rows: `Apre1(x,y) ∪ b`. -/
def afStepOf (hs : d.Shape) (b y x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.apre1Of hs x y ∪ b

theorem afStepF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (b y x : Finset (Fin d.nStates)) :
    d.toCsgQ.afStepF b y x = d.afStepOf hs b y x := by
  unfold CsgQ.afStepF afStepOf
  rw [d.apre1F_eq hs hnn hnz x y]

theorem afStepF_eq_fun [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    d.toCsgQ.afStepF b y = d.afStepOf hs b y :=
  funext fun x => d.afStepF_eq hs hnn hnz b y x

/-! ## Almost-sure reachability, end to end from a model

Three wrappers, matching the three things an `AF` run does: settle one `νY`-step's inner `μX` fixed
point, descend one outer step, and stop. Each takes decidable facts about the rows; none asks the
caller for anything about the real-valued operators. -/

/-- One outer step's inner `μX` fixed point, from a chain run over the rows. -/
theorem afInner_eq_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (d.afStepOf hs b y)^[m] ∅ = c) (hfix : d.afStepOf hs b y c = c) :
    ((d.toCsgQ.toCSG (d.wellFormed hs h2)).AFInner ↑b ↑y).lfp =
      (↑c : Set (Fin d.nStates)) := by
  refine CsgQ.afInner_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) b y c m ?_ ?_
  · rw [d.afStepF_eq_fun hs h2.nonneg hnz b y]
    exact hiter
  · rw [d.afStepF_eq hs h2.nonneg hnz b y c]
    exact hfix

/-- One outer step of the `νY` descent. Chained from `CsgQ.AF_le_univ`, once per step. -/
theorem AF_le_of_data_step [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (d.afStepOf hs b y)^[m] ∅ = c) (hfix : d.afStepOf hs b y c = c)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑c : Set (Fin d.nStates)) :=
  CsgQ.AF_le_of_step d.toCsgQ (d.wellFormed hs h2) b y c
    (d.afInner_eq_of_data hs h2 hnz b y c m hiter hfix) hy

/-- **Almost-sure reachability of `b`, as an answer to an objective.** The outer chain has stopped
    at `y`: it is its own inner `μX` fixed point, and the descent has reached it. Everything the
    caller supplies is a `decide` away -- `hiter` and `hfix` are `Finset` equalities over the rows,
    and `hy` is the chain, one `AF_le_of_data_step` per outer step from `CsgQ.AF_le_univ`. -/
theorem answers_almostReach_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (d.afStepOf hs b y)^[m] ∅ = y) (hfix : d.afStepOf hs b y y = y)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.almostReach b) (Answer.region y) :=
  .almostReach (CsgQ.AF_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) b y
    (d.afInner_eq_of_data hs h2 hnz b y y m hiter hfix) hy)

/-! ## The same, as a loop inside a loop

`answers_almostReach_of_data` asks the caller to walk the outer `νY` descent by hand, one
`AF_le_of_data_step` per step, each carrying its own inner `μX` count and check. Two nested
`Comp/FixLoop.lean` loops replace the whole of that.

What makes the nesting work is that the inner loop is *proved* to stop, at every `y`. So
`afInnerOf hs b` is a total `Finset → Finset` function whose `Finset.coe` is `AFOuter ↑b` on the
nose, which is exactly the bridge the outer loop wants -- and the outer loop then supplies its own
termination the same way. Had the inner fixed point stayed a caller obligation it would have had to
be certified for every `y` the outer descent visits, which is not something anyone can enumerate in
advance; stated over all `y` at once it is a `2 ^ |S|`-way `decide`, the cost that still burdens the
limit-sure line below. Here that cost does not arise. -/

/-- The inner `μX` fixed point at `y`, computed: climb from `∅` until nothing changes. -/
def afInnerOf (hs : d.Shape) (b y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.afStepOf hs b y) ∅

/-- **The almost-sure reachability set, computed.** The outer `νY` descent from `Finset.univ`, each
    of whose steps runs the inner loop. No counts anywhere. -/
def afRegion (hs : d.Shape) (b : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.afInnerOf hs b) Finset.univ

/-- The inner step over the rows is `AFInner`, under `Finset.coe`: the bridge for the inner loop. -/
theorem coe_afStepOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y x : Finset (Fin d.nStates)) :
    (↑(d.afStepOf hs b y x) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).AFInner ↑b ↑y ↑x := by
  rw [← d.afStepF_eq hs h2.nonneg hnz b y x, CsgQ.coe_AFInner_apply]

/-- The inner loop lands on `AFInner`'s least fixed point -- unconditionally, by
    `lfp_eq_coe_fixFrom_empty`. This is the step that makes the nesting possible. -/
theorem coe_afInnerOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.afInnerOf hs b y) : Set (Fin d.nStates))
      = ((d.toCsgQ.toCSG (d.wellFormed hs h2)).AFInner ↑b ↑y).lfp :=
  (lfp_eq_coe_fixFrom_empty _ _ (d.coe_afStepOf hs h2 hnz b y)).symm

/-- …and `AFOuter` *is* that least fixed point, so the inner loop is the outer loop's bridge. The
    restatement is one `rfl`; it is separate only to keep the definitional step in one place. -/
theorem coe_afInnerOf_outer [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.afInnerOf hs b y) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).AFOuter ↑b ↑y :=
  d.coe_afInnerOf hs h2 hnz b y

/-- **Where the nested loops stop *is* the almost-sure reachability set.** Unconditionally: the
    outer descent's upper-bound chain from `gfp_le_coe_fixAux`, its termination from
    `fixFrom_univ_fixed`, and the inner fixed point from `coe_afInnerOf`. -/
theorem AF_eq_coe_afRegion [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b : Finset (Fin d.nStates)) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b
      = (↑(d.afRegion hs b) : Set (Fin d.nStates)) :=
  gfp_eq_coe_fixFrom_univ _ _ (d.coe_afInnerOf_outer hs h2 hnz b)

/-- **Almost-sure reachability from a model, with nothing to supply but the answer.** Compare
    `answers_almostReach_of_data`, which wants an inner count, an inner check, and the outer descent
    assembled by hand. -/
theorem answers_almostReach_of_fix [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b c : Finset (Fin d.nStates))
    (hc : d.afRegion hs b = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.almostReach b) (Answer.region c) := by
  subst hc
  exact .almostReach (d.AF_eq_coe_afRegion hs h2 hnz b)

/-! ## `Lpre1` and the limit-sure middle step, from the rows

Where the almost-sure line was cheap, this one is not: `Lpre1` calls the `μW` fixed point `LW` once
per state, so there is a fixed point *inside* the middle chain.
`Comp/QualitativeLimitReach.lean` therefore takes the witness family as data and states the middle
and outer levels one step at a time. Over a `ModelData` the family can be computed -- it is
`lStepOf` iterated from `∅` -- so the middle chain becomes a function of `x` alone again, at the
price of one hypothesis: that the inner iteration has stopped at each `x` the chain visits.

That hypothesis is written `∀ x s, lStepOf … ((lStepOf …)^[k] ∅) = (lStepOf …)^[k] ∅` below. Over
all `x` it is a `2 ^ |S|`-way check -- affordable at four or six states, not at thirty -- and the
per-step route of `Comp/QualitativeLimitReach.lean` remains available for anything larger. It is
the same lever `Comp/HideOrRunQ.lean` pulls by hand with `lw_fixed`, generalised.

The `(lStepOf …)^[k] ∅` spelling is written out rather than named, deliberately: a named
abbreviation would be a plain `def`, and `rw` does not unfold those when closing a goal by `rfl`. -/

/-- `lpre1F` over the rows, given a family of row-action witness sets. -/
def lpre1Of (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bOf hs (w s) x s = Finset.univ

@[simp]
theorem mem_lpre1Of (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.lpre1Of hs w x ↔ d.bOf hs (w s) x s = Finset.univ := by
  simp only [lpre1Of, Finset.mem_filter, Finset.mem_univ, true_and]

theorem lpre1F_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (w : Fin d.nStates → Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates)) :
    d.toCsgQ.lpre1F w x = d.lpre1Of hs w x := by
  ext s
  simp only [CsgQ.mem_lpre1F, mem_lpre1Of, d.bF_eq hs hnn hnz]

/-- The row-action witness set at `s`, once the inner iteration has been seen to stop: `LW`, from
    the rows. -/
theorem LW_eq_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (hfix : d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅) = (d.lStepOf hs x y s)^[k] ∅) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LW ↑x ↑y s
      = (↑((d.lStepOf hs x y s)^[k] ∅) : Set (Fin d.nAct1)) :=
  CsgQ.LW_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) x y s _ k
    (by rw [d.lStepF_eq hs h2.nonneg hnz])
    (by rw [d.lStepF_eq hs h2.nonneg hnz]; exact hfix)

/-- One turn of the limit-sure middle chain, over the rows: the witness family is `lStepOf`
    iterated, which is what makes this a function of `x` alone. -/
def midOf (hs : d.Shape) (k : ℕ) (b y x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.lpre1Of hs (fun s => (d.lStepOf hs x y s)^[k] ∅) x ∪ b

theorem coe_LFInner_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y x : Finset (Fin d.nStates))
    (hlw : ∀ s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅) = (d.lStepOf hs x y s)^[k] ∅) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y ↑x
      = (↑(d.midOf hs k b y x) : Set (Fin d.nStates)) := by
  rw [CsgQ.coe_LFInner_apply d.toCsgQ (d.wellFormed hs h2) b y x
      (fun s => (d.lStepOf hs x y s)^[k] ∅)
      (fun s => d.LW_eq_of_data hs h2 hnz k x y s (hlw s)),
    d.lpre1F_eq hs h2.nonneg hnz]
  rfl

/-- Every stage of the middle climb is a lower bound on the `μX` fixed point. -/
theorem mid_le_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅) :
    (↑((d.midOf hs k b y)^[m] ∅) : Set (Fin d.nStates))
      ≤ ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      set x := (d.midOf hs k b y)^[m] ∅ with hx
      refine CsgQ.le_lfInner_of_step d.toCsgQ (d.wellFormed hs h2) b y x (d.midOf hs k b y x)
        (fun s => (d.lStepOf hs x y s)^[k] ∅)
        (fun s => d.LW_eq_of_data hs h2 hnz k x y s (hlw x s)) ih ?_
      unfold midOf
      rw [d.lpre1F_eq hs h2.nonneg hnz]

/-- A middle chain run and seen to stop pins the `μX` fixed point at `y`, exactly. -/
theorem mid_eq_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅)
    (hiter : (d.midOf hs k b y)^[m] ∅ = c) (hfix : d.midOf hs k b y c = c) :
    ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp =
      (↑c : Set (Fin d.nStates)) := by
  have hle : (↑c : Set (Fin d.nStates))
      ≤ ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp := by
    have hm := d.mid_le_of_data hs h2 hnz k b y m hlw
    rwa [hiter] at hm
  refine CsgQ.lfInner_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) b y c
    (fun s => (d.lStepOf hs c y s)^[k] ∅)
    (fun s => d.LW_eq_of_data hs h2 hnz k c y s (hlw c s)) ?_ hle
  rw [d.lpre1F_eq hs h2.nonneg hnz]
  exact hfix.symm

/-! ## Limit-sure reachability, end to end from a model -/

/-- One outer step of the `νY` descent. Chained from `CsgQ.LF_le_univ`, once per step. -/
theorem LF_le_of_data_step [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅)
    (hiter : (d.midOf hs k b y)^[m] ∅ = c) (hfix : d.midOf hs k b y c = c)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑c : Set (Fin d.nStates)) :=
  CsgQ.LF_le_of_step d.toCsgQ (d.wellFormed hs h2) b y c
    (d.mid_eq_of_data hs h2 hnz k b y c m hlw hiter hfix) hy

/-- **The value-1 set of a model, as an answer to an objective.** `y` is its own certified `μX`
    fixed point and the outer descent has reached it, so it *is* `CSG.LF b` -- the states from which
    the row player can reach `b` with probability arbitrarily close to one.

    Four hypotheses, all decidable over the rows: the inner iteration has stopped (`hlw`), the
    middle chain reached `y` and stays (`hiter`, `hfix`), and the descent got there (`hy`, one
    `LF_le_of_data_step` per outer step from `CsgQ.LF_le_univ`). Nothing about the real-valued
    operators is asked of the caller, and nothing in any of it evaluates a weight. -/
theorem answers_limitReach_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (k : ℕ) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅)
    (hiter : (d.midOf hs k b y)^[m] ∅ = y) (hfix : d.midOf hs k b y y = y)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.limitReach b) (Answer.region y) :=
  .limitReach (CsgQ.LF_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) b y
    (d.mid_eq_of_data hs h2 hnz k b y y m hlw hiter hfix) hy)

/-! ## The same, as three nested loops

`answers_limitReach_of_data` above needs `hlw`: that the innermost `μW` iteration has stopped, at
every `x` the middle chain visits. Since which `x` those are is not known in advance, the
hypothesis has to be stated over all of them, making it a `2 ^ |S| · |S|`-way `decide` -- 192
instances at three states.

The loop removes the hypothesis rather than the cost of checking it.
`Comp/FixLoop.lean`'s `lfp_eq_coe_fixFrom_empty` makes the innermost loop a total function of
`(x, y, s)` that *is* `CSG.LW` at every `x`, so the witness family is something the middle step
computes and the middle step is a function of `x` alone with no side condition. The same holds one
level up. Three loops, three bridges, and the caller names the region that came back. -/

/-- The innermost `μW` climb at `(x, y, s)`, computed over `Finset (Fin d.nAct1)`: the row actions
    that stay good against every column response the opponent is not excused from. -/
def lwOf (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    Finset (Fin d.nAct1) :=
  fixFrom (d.lStepOf hs x y s) ∅

/-- The innermost step over the rows is `CSG.LStep`, under `Finset.coe`. -/
theorem coe_lStepOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (w : Finset (Fin d.nAct1)) :
    (↑(d.lStepOf hs x y s w) : Set (Fin d.nAct1))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).LStep ↑x ↑y s ↑w := by
  rw [← d.lStepF_eq hs h2.nonneg hnz x y s, CsgQ.coe_lStepF]

/-- **`LW`, with no check at all.** Compare `LW_eq_of_data`, which wants `hfix` at this `(x, y, s)`;
    over all `x` that hypothesis is what made the limit-sure line exponential. -/
theorem LW_eq_coe_lwOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LW ↑x ↑y s
      = (↑(d.lwOf hs x y s) : Set (Fin d.nAct1)) :=
  lfp_eq_coe_fixFrom_empty _ _ (d.coe_lStepOf hs h2 hnz x y s)

/-- One turn of the limit-sure middle chain, with the witness family computed rather than counted.
    Compare `midOf`, which takes `k` and leaves the caller to certify it. -/
def lmidOf (hs : d.Shape) (b y x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.lpre1Of hs (d.lwOf hs x y) x ∪ b

/-- The middle step is `LFInner`, under `Finset.coe`, unconditionally -- the bridge for the middle
    loop, and the place where `hlw`'s disappearance is cashed in. -/
theorem coe_lmidOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y x : Finset (Fin d.nStates)) :
    (↑(d.lmidOf hs b y x) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y ↑x := by
  unfold lmidOf
  rw [CsgQ.coe_LFInner_apply d.toCsgQ (d.wellFormed hs h2) b y x (d.lwOf hs x y)
      (fun s => d.LW_eq_coe_lwOf hs h2 hnz x y s), d.lpre1F_eq hs h2.nonneg hnz]

/-- The middle `μX` fixed point at `y`, computed. -/
def lfInnerOf (hs : d.Shape) (b y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.lmidOf hs b y) ∅

/-- The middle loop lands on `LFInner`'s least fixed point. -/
theorem coe_lfInnerOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.lfInnerOf hs b y) : Set (Fin d.nStates))
      = ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp :=
  (lfp_eq_coe_fixFrom_empty _ _ (d.coe_lmidOf hs h2 hnz b y)).symm

/-- …and `LFOuter` *is* that least fixed point, so the middle loop is the outer loop's bridge. One
    `rfl`, kept separate so the definitional step sits in one place. -/
theorem coe_lfInnerOf_outer [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.lfInnerOf hs b y) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).LFOuter ↑b ↑y :=
  d.coe_lfInnerOf hs h2 hnz b y

/-- **The value-1 set, computed.** The outer `νY` descent from `Finset.univ`, over the middle `μX`
    climb, over the innermost `μW` climb at every state. -/
def lfRegion (hs : d.Shape) (b : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.lfInnerOf hs b) Finset.univ

/-- **Where the three loops stop *is* `CSG.LF b`.** Unconditionally. -/
theorem LF_eq_coe_lfRegion [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b : Finset (Fin d.nStates)) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b
      = (↑(d.lfRegion hs b) : Set (Fin d.nStates)) :=
  gfp_eq_coe_fixFrom_univ _ _ (d.coe_lfInnerOf_outer hs h2 hnz b)

/-- **The value-1 set of a model, as an answer to an objective, from one equality.** The states from
    which the row player reaches `b` with probability arbitrarily close to one -- computed by three
    nested loops, each proved to terminate, with no count and no fixed-point check anywhere.

    Compare `answers_limitReach_of_data`: four hypotheses, one of them exponential in `|S|`. -/
theorem answers_limitReach_of_fix [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b c : Finset (Fin d.nStates))
    (hc : d.lfRegion hs b = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.limitReach b) (Answer.region c) := by
  subst hc
  exact .limitReach (d.LF_eq_coe_lfRegion hs h2 hnz b)

end ModelData

end Comp
