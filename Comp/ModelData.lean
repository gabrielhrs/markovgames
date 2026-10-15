/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Objective

/-!
# A model as data: sparse adjacency in, a `CsgQ` out

**Status: confirmed by a clean `lake build`.**

The other half of separating the model from the question. `Comp/Objective.lean` made the objective
a first-class datum; this file does the same for the game, so that a model can arrive as literal
tables -- parsed from a file, generated, or written out by hand -- rather than as a Lean definition
with one `match` arm per state. `Comp/HideOrRunQ.lean`'s `kernel`-style pattern match stays
perfectly good Lean, but it is a *program*, not data: nothing outside Lean can produce it.

**Why the kernel is sparse.** A dense kernel -- `List (List (List (List ℚ)))` indexed
`[s][a1][a2][s']` -- is `|S|·|A1|·|A2|·|S|` entries, so the `|S|²` factor dominates: a model with a
thousand states and four actions each would need sixteen million entries to record a few thousand
transitions. A transition row here is instead a *sparse distribution*, `List (ℕ × ℚ)` -- only the
successors that actually occur -- and the states are a list, each carrying its own rows, which is
the adjacency form PRISM
itself uses. Storage is now proportional to the number of real transitions.

**Two shapes, because models come in two shapes.** `ModelData` carries sparse rational
distributions, which is what a genuinely probabilistic model needs. `DetModelData` carries a
successor table, one next state per `[s][a1][a2]`, which is what the graph structure of most PRISM
models is before probabilities are attached. The second is not just a special case to be tidy
about: its validity check involves no `ℚ` at all (see below), and that has consequences.

**State rewards and action rewards, separately.** `Csg.CSG`'s reward is `r : S → A1 → A2 → ℝ`, an
*action* reward, which already subsumes a state reward -- a state reward is one that happens not to
vary with the action pair. So nothing was missing from the theory; what was missing was a way to
*say* it, since writing a state reward through an action-indexed table means repeating the same
number across every action pair of that state. A `StateEntry` therefore carries its own `rew` and a
`TransRow` carries the action's, and `toCsgQ` sums them. `r_eq` records the decomposition. (The
qualitative operators read neither, and `CsgQ.RewardFree` asks that both vanish.)

**Lookup is total, and validation is separate.** Every index goes through `List.getD` with a
default, so a malformed table yields a total function rather than an error: a missing state, row or
reward reads as empty or zero. That is the same discipline `Comp/Basic.lean` already follows -- the
structure carries no proof obligations, and `WellFormed`, decidable, is the validation step. Note
also that `nStates` is *derived* from `states.length` rather than stored, so the count can never
disagree with the data, and that a successor index is never reduced modulo `nStates`: clamping
would make every table valid and every typo silent.

**Validity splits in two, and the split matters.** `InRange` says every successor index is a real
state -- a finite conjunction of `ℕ` comparisons, so `decide` settles it. `Stochastic` says every
row is nonnegative and sums to one -- genuine `ℚ` arithmetic, so `decide` runs into the `Nat.gcd`
obstruction recorded in `Comp/RockPaperScissorsQ.lean` and a caller discharges it with `norm_num`
instead (or `#eval decide` to *check* rather than prove). `Nonneg` and `Nonzero` are the other two
conditions, and what they buy is explained at `keysNat`: together they let a support be read off a
row's keys without the weights being inspected, which is what keeps the kernel in play above the
bridge. None of the three `ℚ` conditions is reachable by `decide` once a weight is written as a
fraction -- `(1/2 : ℚ)` is a division -- so each is proved once per model by `norm_num`, and
*nothing above them* needs rational arithmetic again. `DetModelData` needs only the first half:
its rows are point masses, so `sum_ite_coe_eq` proves the stochastic part once and for all, with no
`ℚ` reasoning left for the caller. That is why `Comp/HideOrRunQ.lean`'s data section can close its
whole computation with a bare `decide`, quarantine lemma and all.

**Why `NeZero` appears, and one practical note.** `Comp/Basic.lean`'s `CsgQ` requires
`[Nonempty A1] [Nonempty A2]`, and `Fin d.nRow` is nonempty only when `d.nRow ≠ 0`. So both
`toCsgQ`s take `[NeZero d.nRow]` and `[NeZero d.nCol]`. At a concrete model these are found from
the numerals, *provided* the model is declared `abbrev` rather than `def`: the game's type is
`CsgQ (Fin d.nStates) ..`, so instance search has to see through the projection to reach the
numeral. Declaring the three `NeZero`s by hand beside the model works too, and does not depend on
that.

**The support, read off the row.** Sparse storage fixes the size of the *model*, but
`Comp/QualitativeFinset.lean`'s `supportF` is `Finset.univ.filter (· ≠ 0)`, so computing a
two-element support still costs a scan of every state. `supportOf` reads it straight off the row
instead, at a cost proportional to the row's length, and `supportF_eq` is the bridge. That one lemma
does two jobs, which is the pleasing part: it is also exactly the per-instance arithmetic quarantine
(`supportF_eq_supp` in `Comp/HideOrRunQ.lean`, `supportF_eq_chainSupp` in
`Comp/SafetyChainQ.lean`) proved once for every model at once. Above the bridge there is no `ℚ`
arithmetic, only comparison of a weight with zero -- so `decide` is available even for a
*probabilistic* model, which the hand-written instances could not manage.

The step after that is to make the operators above `supportF` go through it, the way
`Comp/HideOrRunQ.lean`'s `aC`/`bC`/`lStepC` go through its own table. That is a transfer lemma per
operator and it is not here yet.

**Also not here:** parsing, which is ordinary programming and belongs outside the proof
development; `Array` in place of `List`, which is what a lookup-*time* fix would need and which
makes proofs harder, so it waits until the shape is settled; and labels, which belong in a
presentation layer beside the data.
-/

namespace Comp

/-! ## Sparse distributions, densified

The one piece of arithmetic the sparse form needs: what vector a list of weighted successors
denotes, and that its entries are nonnegative and sum to the list's total. -/

/-- The dense vector a sparse distribution denotes: the weight of `s'` is the sum of the entries
    keyed to it. Defined by recursion on the list rather than by `List.filter` so that the two
    lemmas below are plain inductions, and so that *duplicate* keys add rather than shadow. -/
def denseOf (n : ℕ) : List (ℕ × ℚ) → Fin n → ℚ
  | [], _ => 0
  | (t, q) :: rest, s' => (if (s' : ℕ) = t then q else 0) + denseOf n rest s'

/-- A single weighted index in range contributes its weight to the sum and nothing elsewhere. The
    arithmetic core of this file: `sum_denseOf` is this plus an induction, and `DetModelData`'s
    well-formedness is this at `q = 1`.

    `Fin.ext` is the fact that a `Fin` is determined by its value; it has gone under other names
    (`Fin.eq_of_val_eq`, `Fin.val_injective`) in other versions. -/
theorem sum_ite_coe_eq {n t : ℕ} (ht : t < n) (q : ℚ) :
    ∑ s' : Fin n, (if (s' : ℕ) = t then q else 0) = q := by
  have hcond : ∀ s' : Fin n, ((s' : ℕ) = t) ↔ (s' = (⟨t, ht⟩ : Fin n)) := by
    intro s'
    constructor
    · intro hv
      exact Fin.ext hv
    · intro he
      rw [he]
  calc ∑ s' : Fin n, (if (s' : ℕ) = t then q else 0)
      = ∑ s' : Fin n, (if s' = (⟨t, ht⟩ : Fin n) then q else 0) := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        simp only [hcond s']
    _ = q := by simp

/-- The `q = 1` case, which is what a point-mass kernel needs. -/
theorem sum_ite_coe_eq_one {n t : ℕ} (ht : t < n) :
    ∑ s' : Fin n, (if (s' : ℕ) = t then (1 : ℚ) else 0) = 1 :=
  sum_ite_coe_eq ht 1

/-- A sparse distribution with nonnegative weights densifies to a nonnegative vector. -/
theorem denseOf_nonneg (n : ℕ) (dist : List (ℕ × ℚ)) (s' : Fin n) :
    (∀ p ∈ dist, 0 ≤ p.2) → 0 ≤ denseOf n dist s' := by
  induction dist with
  | nil => intro _; simp [denseOf]
  | cons p rest ih =>
      intro h
      obtain ⟨t, q⟩ := p
      have hq : (0 : ℚ) ≤ q := h (t, q) (by simp)
      have hrest : 0 ≤ denseOf n rest s' := ih fun p hp => h p (List.mem_cons_of_mem _ hp)
      simp only [denseOf]
      split_ifs <;> linarith

/-- **The payoff of the sparse form.** The densified vector sums to the list's own total, provided
    every key is a real state. An induction on the list, with `sum_ite_coe_eq` at each step. -/
theorem sum_denseOf (n : ℕ) (dist : List (ℕ × ℚ)) :
    (∀ p ∈ dist, p.1 < n) →
      ∑ s' : Fin n, denseOf n dist s' = (dist.map Prod.snd).sum := by
  induction dist with
  | nil => intro _; simp [denseOf]
  | cons p rest ih =>
      intro h
      obtain ⟨t, q⟩ := p
      have ht : t < n := h (t, q) (by simp)
      have hrest : ∀ p ∈ rest, p.1 < n := fun p hp => h p (List.mem_cons_of_mem _ hp)
      simp only [denseOf, List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, sum_ite_coe_eq ht q, ih hrest]

/-! ## Supports, read off the row

The second thing sparsity buys, and the more valuable one: a support that costs the row's length
rather than the state count -- and, as a side effect, no rational arithmetic above this line. -/

/-- A sum of two nonnegative rationals vanishes only if both do, so it is nonzero exactly when one
    of them is. The only arithmetic `denseOf_ne_zero_iff` needs, and the reason nonnegativity is a
    hypothesis there: with cancellation allowed, a support could not be read off the keys.
    (`Comp/HideOrRunQ.lean`'s `half_add_half_ne_zero` is this fact with explicit `1/2`s.) -/
theorem add_ne_zero_iff_of_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  constructor
  · intro hab
    rcases eq_or_ne a 0 with ha0 | ha0
    · rcases eq_or_ne b 0 with hb0 | hb0
      · rw [ha0, hb0, add_zero] at hab
        exact absurd rfl hab
      · exact Or.inr hb0
    · exact Or.inl ha0
  · rintro (h | h)
    · intro hab
      have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
      linarith
    · intro hab
      have hpos : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
      linarith

/-- The indices a sparse row mentions, as a `Finset ℕ`. Read off the row, so the cost is the row's
    length -- and, more importantly, **without looking at the weights at all**. That is what makes
    everything above this definition reducible by the kernel: a weight like `1/2` is a *division*,
    which `Nat.gcd` puts beyond the kernel's reach (`Comp/RockPaperScissorsQ.lean` works the case
    through), so a
    support that had to compare weights with zero would be no more `decide`-able than one that had
    to add them. The price is a validity condition -- `Nonzero` below -- and it is the right price:
    a row that lists a successor with weight zero is a row with a redundant entry. -/
def keysNat (dist : List (ℕ × ℚ)) : Finset ℕ :=
  (dist.map Prod.fst).toFinset

@[simp]
theorem mem_keysNat (dist : List (ℕ × ℚ)) (m : ℕ) :
    m ∈ keysNat dist ↔ ∃ p ∈ dist, p.1 = m := by
  simp only [keysNat, List.mem_toFinset, List.mem_map]

/-- An in-range row's keys are all real states -- the side condition `Finset.attachFin` wants. -/
theorem keysNat_lt {n : ℕ} (dist : List (ℕ × ℚ)) (h : ∀ p ∈ dist, p.1 < n) :
    ∀ m ∈ keysNat dist, m < n := by
  intro m hm
  rw [mem_keysNat] at hm
  obtain ⟨p, hp, rfl⟩ := hm
  exact h p hp

/-- **The support of a sparse row.** With no negative weights there is nothing to cancel and with
    no zero weights nothing to discount, so the densified vector is nonzero at `s'` exactly when
    some entry mentions `s'` -- a statement about the row's *keys*, with the weights gone.

    Both hypotheses earn their place. Drop nonnegativity and two entries could cancel; drop
    nonzero-ness and a listed successor could carry no mass. An induction, with
    `add_ne_zero_iff_of_nonneg` at each step. -/
theorem denseOf_ne_zero_iff (n : ℕ) (dist : List (ℕ × ℚ)) (s' : Fin n) :
    (∀ p ∈ dist, 0 ≤ p.2) → (∀ p ∈ dist, p.2 ≠ 0) →
      (denseOf n dist s' ≠ 0 ↔ ∃ p ∈ dist, p.1 = (s' : ℕ)) := by
  induction dist with
  | nil => intro _ _; simp [denseOf]
  | cons p rest ih =>
      intro h hz
      obtain ⟨t, q⟩ := p
      have hq : (0 : ℚ) ≤ q := h (t, q) (by simp)
      have hqz : q ≠ 0 := hz (t, q) (by simp)
      have hrest : ∀ p ∈ rest, 0 ≤ p.2 := fun p hp => h p (List.mem_cons_of_mem _ hp)
      have hrestz : ∀ p ∈ rest, p.2 ≠ 0 := fun p hp => hz p (List.mem_cons_of_mem _ hp)
      have hB : (0 : ℚ) ≤ denseOf n rest s' := denseOf_nonneg n rest s' hrest
      have hA : (0 : ℚ) ≤ (if (s' : ℕ) = t then q else 0) := by
        split_ifs
        · exact hq
        · exact le_refl 0
      simp only [denseOf, List.mem_cons]
      rw [add_ne_zero_iff_of_nonneg hA hB, ih hrest hrestz]
      constructor
      · rintro (hne | ⟨p, hp, h1⟩)
        · refine ⟨(t, q), Or.inl rfl, ?_⟩
          split_ifs at hne with hc
          · exact hc.symm
          · exact absurd rfl hne
        · exact ⟨p, Or.inr hp, h1⟩
      · rintro ⟨p, hp, h1⟩
        rcases hp with rfl | hp
        · refine Or.inl ?_
          split_ifs with hc
          · exact hqz
          · exact absurd h1.symm hc
        · exact Or.inr ⟨p, hp, h1⟩

/-! ## The sparse shape -/

/-- One cell of a state's transition table: the sparse distribution over successors for a joint
    action, together with that action's reward. -/
structure TransRow where
  /-- Successors with their weights. Only the ones that occur. -/
  dist : List (ℕ × ℚ)
  /-- Reward for taking this joint action in this state. -/
  rew : ℚ

instance : Inhabited TransRow := ⟨⟨[], 0⟩⟩

/-- One state: its own reward, and its transition table indexed `[a1][a2]`. -/
structure StateEntry where
  /-- Reward for being in this state. -/
  rew : ℚ
  /-- Transition rows, indexed `[a1][a2]`. -/
  rows : List (List TransRow)

instance : Inhabited StateEntry := ⟨⟨0, []⟩⟩

/-- A model as data, in adjacency form: a list of states, each carrying its own transitions. The
    state count is derived from the list, so it cannot disagree with it. -/
structure ModelData where
  /-- Number of row-player actions. -/
  nRow : ℕ
  /-- Number of column-player actions. -/
  nCol : ℕ
  /-- The states, in index order. -/
  states : List StateEntry

/-- The number of states -- derived, not stored. -/
def ModelData.nStates (d : ModelData) : ℕ := d.states.length

/-- The state at an index, or an empty state. -/
def ModelData.stateAt (d : ModelData) (s : ℕ) : StateEntry := d.states.getD s default

/-- The transition row at a state/action triple, or an empty row. -/
def ModelData.rowAt (d : ModelData) (s a1 a2 : ℕ) : TransRow :=
  ((d.stateAt s).rows.getD a1 []).getD a2 default

/-- Every successor index is a real state. Pure `ℕ`, so `decide` settles it. -/
def ModelData.InRange (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ a1 : Fin d.nRow, ∀ a2 : Fin d.nCol,
    ∀ p ∈ (d.rowAt s a1 a2).dist, p.1 < d.nStates

instance (d : ModelData) : Decidable d.InRange := by
  unfold ModelData.InRange
  infer_instance

/-- Every row is a probability distribution. Genuine `ℚ` arithmetic, so a caller proves this with
    `norm_num` rather than `decide`. -/
def ModelData.Stochastic (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ a1 : Fin d.nRow, ∀ a2 : Fin d.nCol,
    (∀ p ∈ (d.rowAt s a1 a2).dist, 0 ≤ p.2) ∧
      ((d.rowAt s a1 a2).dist.map Prod.snd).sum = 1

instance (d : ModelData) : Decidable d.Stochastic := by
  unfold ModelData.Stochastic
  infer_instance

/-- Every weight is nonnegative: the half of `Stochastic` that the support bridge actually needs,
    and the cheap half. It is a conjunction of rational *comparisons* with no addition in it, so
    `decide` settles it where a row sum would not. -/
def ModelData.Nonneg (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ a1 : Fin d.nRow, ∀ a2 : Fin d.nCol,
    ∀ p ∈ (d.rowAt s a1 a2).dist, 0 ≤ p.2

instance (d : ModelData) : Decidable d.Nonneg := by
  unfold ModelData.Nonneg
  infer_instance

theorem ModelData.Stochastic.nonneg {d : ModelData} (h : d.Stochastic) : d.Nonneg :=
  fun s a1 a2 => (h s a1 a2).1

/-- No weight is zero. The condition that lets a support be read off the *keys* of a row, with the
    weights never inspected -- see `keysNat`. It is not an extra burden on a model so much as a
    normalisation of it: a successor listed with probability zero is a successor not listed.

    Decidable, but not by `decide` for a model with fractional weights, since `(1/2 : ℚ)` is a
    division the kernel cannot evaluate. One `norm_num` per model, and everything above it is
    `ℕ`. -/
def ModelData.Nonzero (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ a1 : Fin d.nRow, ∀ a2 : Fin d.nCol,
    ∀ p ∈ (d.rowAt s a1 a2).dist, p.2 ≠ 0

instance (d : ModelData) : Decidable d.Nonzero := by
  unfold ModelData.Nonzero
  infer_instance

/-- The rational game a `ModelData` denotes. Total by construction; whether it is a *game* is
    `WellFormed`'s business. -/
def ModelData.toCsgQ (d : ModelData) [NeZero d.nRow] [NeZero d.nCol] :
    CsgQ (Fin d.nStates) (Fin d.nRow) (Fin d.nCol) where
  K s a1 a2 := denseOf d.nStates (d.rowAt s a1 a2).dist
  r s a1 a2 := (d.stateAt s).rew + (d.rowAt s a1 a2).rew

/-- The kernel entry, unfolded. `rfl`, recorded so later proofs can rewrite with it instead of
    relying on the structure projection reducing at the right moment. -/
@[simp]
theorem ModelData.toCsgQ_K (d : ModelData) [NeZero d.nRow] [NeZero d.nCol]
    (s : Fin d.nStates) (a1 : Fin d.nRow) (a2 : Fin d.nCol) (s' : Fin d.nStates) :
    d.toCsgQ.K s a1 a2 s' = denseOf d.nStates (d.rowAt s a1 a2).dist s' := rfl

/-- The reward decomposition, by definition: what `CSG.r` folds into one number. -/
theorem ModelData.r_eq (d : ModelData) [NeZero d.nRow] [NeZero d.nCol]
    (s : Fin d.nStates) (a1 : Fin d.nRow) (a2 : Fin d.nCol) :
    d.toCsgQ.r s a1 a2 = (d.stateAt s).rew + (d.rowAt s a1 a2).rew := rfl

/-- **The payoff.** The two halves of validity give well-formedness. Split deliberately: the caller
    discharges `InRange` by `decide` in `ℕ`, and only `Stochastic` costs rational arithmetic. -/
theorem ModelData.wellFormed (d : ModelData) [NeZero d.nRow] [NeZero d.nCol]
    (h1 : d.InRange) (h2 : d.Stochastic) : d.toCsgQ.WellFormed := by
  refine ⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩
  · exact denseOf_nonneg _ _ s' (h2 s a1 a2).1
  · change ∑ s' : Fin d.nStates, denseOf d.nStates (d.rowAt s a1 a2).dist s' = 1
    rw [sum_denseOf d.nStates _ (h1 s a1 a2)]
    exact (h2 s a1 a2).2

/-- **The fast support.** The successors of a state/action triple, read off the row rather than
    found by scanning the states. `Finset.attachFin` is what turns the row's `ℕ` keys into states,
    and `InRange` is exactly its side condition -- so the validity check the model needed anyway is
    also what makes this well defined. -/
def ModelData.supportOf (d : ModelData) (h1 : d.InRange) (s : Fin d.nStates) (a1 : Fin d.nRow)
    (a2 : Fin d.nCol) : Finset (Fin d.nStates) :=
  Finset.attachFin (keysNat (d.rowAt s a1 a2).dist) (keysNat_lt _ (h1 s a1 a2))

/-- **The bridge, and the quarantine.** `Comp/QualitativeFinset.lean`'s `supportF` -- a filter over
    every state, with a rational disequality in it -- is the row's own key set.

    Two consequences, and the second is the one that matters for proofs. Computing a support now
    costs the row's length instead of the state count; and nothing above this line touches a weight
    at all -- `supportOf` is built from `keysNat`, which is `ℕ` data. So the kernel can reduce every
    operator above it even when the weights are fractions it could not so much as evaluate. That is
    the job `Comp/HideOrRunQ.lean` and `Comp/SafetyChainQ.lean` each do by hand for their own game,
    except that those tables only work because their kernels are `0`/`1`; this one works for any
    model, and the three `ℚ` conditions it rests on are proved once per model rather than reproved
    inside every fixed-point check. -/
theorem ModelData.supportF_eq (d : ModelData) [NeZero d.nRow] [NeZero d.nCol]
    (h1 : d.InRange) (hnn : d.Nonneg) (hnz : d.Nonzero) (s : Fin d.nStates) (a1 : Fin d.nRow)
    (a2 : Fin d.nCol) :
    d.toCsgQ.supportF s a1 a2 = d.supportOf h1 s a1 a2 := by
  ext s'
  rw [CsgQ.mem_supportF, ModelData.toCsgQ_K,
    denseOf_ne_zero_iff d.nStates _ s' (hnn s a1 a2) (hnz s a1 a2)]
  simp [ModelData.supportOf]

/-! ## The deterministic shape

A successor table, with no probabilities to validate. Kept as its own structure rather than folded
into the sparse form because the difference is not cosmetic: a point-mass kernel's rows are
`if _ then 1 else 0`, so `wellFormed` needs nothing from the caller beyond an `ℕ` range check, and
nothing downstream ever performs a rational addition. That is what lets a model in this form run the
qualitative engine end to end under `decide`. -/

/-- A deterministic model as data: `succ` is indexed `[s][a1][a2]` and gives the next state's
    index. -/
structure DetModelData where
  /-- Number of states. -/
  nStates : ℕ
  /-- Number of row-player actions. -/
  nRow : ℕ
  /-- Number of column-player actions. -/
  nCol : ℕ
  /-- Successor index, `[s][a1][a2]`. Missing entries read as `0`, and an out-of-range entry is
      *not* clamped -- it is caught by `InRange`. -/
  succ : List (List (List ℕ))
  /-- Reward for being in a state, `[s]`. Missing entries read as `0`. -/
  stateReward : List ℚ
  /-- Reward for a joint action in a state, `[s][a1][a2]`. Missing entries read as `0`. -/
  actionReward : List (List (List ℚ))

/-- The successor index at a state/action triple. -/
def DetModelData.next (d : DetModelData) (s a1 a2 : ℕ) : ℕ :=
  ((d.succ.getD s []).getD a1 []).getD a2 0

/-- The state component of the reward. -/
def DetModelData.stateRew (d : DetModelData) (s : ℕ) : ℚ := d.stateReward.getD s 0

/-- The action component of the reward. -/
def DetModelData.actionRew (d : DetModelData) (s a1 a2 : ℕ) : ℚ :=
  ((d.actionReward.getD s []).getD a1 []).getD a2 0

/-- Every successor index is a real state. The one thing a deterministic model has to satisfy, and
    a finite conjunction of `ℕ` comparisons -- so `decide` settles it. -/
def DetModelData.InRange (d : DetModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ a1 : Fin d.nRow, ∀ a2 : Fin d.nCol, d.next s a1 a2 < d.nStates

instance (d : DetModelData) : Decidable d.InRange := by
  unfold DetModelData.InRange
  infer_instance

/-- The rational game a `DetModelData` denotes: a point mass on the successor. Note the shape of the
    entries -- `if _ then 1 else 0` -- which is what makes everything downstream `decide`-friendly,
    since no `ℚ` addition or division ever appears in the kernel. -/
def DetModelData.toCsgQ (d : DetModelData) [NeZero d.nRow] [NeZero d.nCol] :
    CsgQ (Fin d.nStates) (Fin d.nRow) (Fin d.nCol) where
  K s a1 a2 s' := if (s' : ℕ) = d.next s a1 a2 then 1 else 0
  r s a1 a2 := d.stateRew s + d.actionRew s a1 a2

/-- The reward decomposition, by definition. -/
theorem DetModelData.r_eq (d : DetModelData) [NeZero d.nRow] [NeZero d.nCol]
    (s : Fin d.nStates) (a1 : Fin d.nRow) (a2 : Fin d.nCol) :
    d.toCsgQ.r s a1 a2 = d.stateRew s + d.actionRew s a1 a2 := rfl

/-- **The payoff of the deterministic shape.** An in-range successor table is a well-formed game,
    with no `ℚ` reasoning required of the caller: `InRange` is `decide`-able in `ℕ`, and everything
    else is `sum_ite_coe_eq_one`. The rewards play no part -- `WellFormed` constrains only the
    kernel. -/
theorem DetModelData.wellFormed (d : DetModelData) [NeZero d.nRow] [NeZero d.nCol]
    (h : d.InRange) : d.toCsgQ.WellFormed := by
  refine ⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩
  · change (0 : ℚ) ≤ if (s' : ℕ) = d.next s a1 a2 then 1 else 0
    split_ifs <;> norm_num
  · change ∑ s' : Fin d.nStates, (if (s' : ℕ) = d.next s a1 a2 then (1 : ℚ) else 0) = 1
    exact sum_ite_coe_eq_one (h s a1 a2)

end Comp
