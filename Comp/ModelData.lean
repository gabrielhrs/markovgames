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
successors that actually occur -- and the states are a list, each carrying its own transitions,
which is the adjacency form PRISM itself uses. Storage is proportional to the number of real
transitions.

**Sparse in the actions too, and for the same reason.** A `Transition` carries the joint action it
belongs to, so a state stores exactly the transitions it has rather than a dense `[a1][a2]` matrix.
The enabled action sets are then read off the transitions, and the operators above this file
quantify over a state's own actions instead of the global namespace -- which matters because PRISM
names actions globally and enables a handful per state, so the dense form spends almost all of its
work on pairs that are not available where it is looking. A deterministic model needs no separate
shape: it is one whose distributions are singletons.

**State rewards and action rewards, separately.** `Csg.CSG`'s reward is `r : S → A1 → A2 → ℝ`, an
*action* reward, which already subsumes a state reward -- a state reward is one that happens not to
vary with the action pair. So nothing was missing from the theory; what was missing was a way to
*say* it, since writing a state reward through an action-indexed table means repeating the same
number across every action pair of that state. A `StateEntry` therefore carries its own `rew` and a
`Transition` carries the action's, and `toCsgQ` sums them. `r_eq` records the decomposition. (The
qualitative operators read neither, and `CsgQ.RewardFree` asks that both vanish.)

**Lookup is total, and validation is separate.** Every index goes through `List.getD` with a
default, so a malformed table yields a total function rather than an error: a missing state, row or
reward reads as empty or zero. That is the same discipline `Comp/Basic.lean` already follows -- the
structure carries no proof obligations, and `WellFormed`, decidable, is the validation step. Note
also that `nStates` is *derived* from `states.length` rather than stored, so the count can never
disagree with the data, and that a successor index is never reduced modulo `nStates`: clamping
would make every table valid and every typo silent.

**Every condition is a property of transitions that exist.** Each one quantifies over `transOf`,
so a model can be validated one transition at a time as it is built rather than over the whole
`|S| × |A1| × |A2|` grid -- and the pairs a model does *not* declare need no condition of their
own, since padding sends each to a declared transition and a terminal state's self-loop carries
weight `1`. That is why there is no populatedness condition: an empty state is terminal, not
invalid, and `transOf_ne_nil` is a theorem.

**Validity splits in two, and the split matters.** `InRange` says every successor index is a real
state -- a finite conjunction of `ℕ` comparisons, so `decide` settles it. `Stochastic` says every
row is nonnegative and sums to one -- genuine `ℚ` arithmetic, so `decide` runs into the `Nat.gcd`
obstruction recorded in `Comp/RockPaperScissorsQ.lean` and a caller discharges it with `norm_num`
instead (or `#eval decide` to *check* rather than prove). `Nonneg` and `Nonzero` are the other two
conditions, and what they buy is explained at `keysNat`: together they let a support be read off a
row's keys without the weights being inspected, which is what keeps the kernel in play above the
bridge. None of the three `ℚ` conditions is reachable by `decide` once a weight is written as a
fraction -- `(1/2 : ℚ)` is a division -- so each is proved once per model by `norm_num`, and
*nothing above them* needs rational arithmetic again. A model whose weights are all `0` or `1` is
the exception in practice: those are not divisions, so its three rational conditions should fall to
`decide` like the structural ones.

**Why `NeZero` appears, and one practical note.** `Comp/Basic.lean`'s `CsgQ` requires
`[Nonempty A1] [Nonempty A2]`, and `Fin d.nAct1` is nonempty only when `d.nAct1 ≠ 0`. So `toCsgQ`
takes `[NeZero d.nAct1]` and `[NeZero d.nAct2]`. At a concrete model these are found from
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
    arithmetic core of this file: `sum_denseOf` is this plus an induction, and a point-mass
    kernel's well-formedness is this at `q = 1`.

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

/-! ## The sparse shape

A transition carries its own joint action, so a state stores exactly the transitions it has. Two
consequences: the enabled action sets are read off the transitions rather than declared, and the
operators above this file quantify over a state's own actions instead of the global namespace. -/

/-- One transition: the joint action it belongs to, where it leads, and what it pays.

    `act1` and `act2` are indices into the *global* action namespaces, which is how PRISM names
    actions -- distinct names, not enabled everywhere. A state's enabled sets are whichever of
    those its transitions mention. -/
structure Transition where
  /-- The row player's action, as a global index. -/
  act1 : ℕ
  /-- The column player's action, as a global index. -/
  act2 : ℕ
  /-- Successors with their weights. Only the ones that occur. -/
  dist : List (ℕ × ℚ)
  /-- Reward for taking this joint action in this state. -/
  rew : ℚ

instance : Inhabited Transition := ⟨⟨0, 0, [], 0⟩⟩

/-- One state: its own reward, and its transitions. -/
structure StateEntry where
  /-- Reward for being in this state. -/
  rew : ℚ
  /-- The transitions available here, each carrying its joint action. -/
  trans : List Transition

instance : Inhabited StateEntry := ⟨⟨0, []⟩⟩

/-- A model as data, in adjacency form: a list of states, each carrying its own transitions. The
    state count is derived from the list, so it cannot disagree with it.

    `nAct1`/`nAct2` bound the *global* action namespaces. They are not per-state matrix dimensions:
    the stage game a state denotes is `enabled1 × enabled2`, which `Comp/Shapley.lean` builds, and
    "row" and "column" are reserved for that. -/
structure ModelData where
  /-- Size of the row player's global action namespace. -/
  nAct1 : ℕ
  /-- Size of the column player's global action namespace. -/
  nAct2 : ℕ
  /-- The states, in index order. -/
  states : List StateEntry

/-- The number of states -- derived, not stored. -/
def ModelData.nStates (d : ModelData) : ℕ := d.states.length

/-- The state at an index, or an empty state. -/
def ModelData.stateAt (d : ModelData) (s : ℕ) : StateEntry := d.states.getD s default

/-! ### Transitions, with a terminal state's self-loop

A state with no declared outgoing transition is terminal, and a terminal state in a `CSG` still has
to do something; the convention is to stay put. The denotation supplies that self-loop rather than
asking the modeller to, which is why there is no "every state is populated" validity condition:
`transOf_ne_nil` is a theorem, and the three rational conditions hold of the synthesized transition
for free, its one weight being a literal `1`.

**This is not the padding convention of `pad1`/`pad2` below, and the two must not be confused.** A
self-loop here is a terminal state's only transition and offers nobody a choice. A self-loop
standing in for a *disabled action* in a populated state would hand a player a safe move they do
not have, and could only enlarge `Pre1`; that is why padding duplicates an enabled action instead.

Everything downstream reads a state's transitions through `transOf`, never through
`(stateAt s).trans` directly, so the self-loop is not something a later definition can forget. -/

/-- The transitions of state `s`, with a terminal state's self-loop supplied. -/
def ModelData.transOf (d : ModelData) (s : ℕ) : List Transition :=
  match (d.stateAt s).trans with
  | [] => [{ act1 := 0, act2 := 0, dist := [(s, 1)], rew := 0 }]
  | t :: ts => t :: ts

/-- Every state has somewhere to go. A theorem, not a hypothesis. -/
theorem ModelData.transOf_ne_nil (d : ModelData) (s : ℕ) : d.transOf s ≠ [] := by
  unfold ModelData.transOf
  split <;> simp

/-- The head of a state's transitions is one of them -- the fallback `pad1`/`pad2` use. -/
theorem ModelData.headD_mem (d : ModelData) (s : ℕ) :
    (d.transOf s).headD default ∈ d.transOf s := by
  cases h : d.transOf s with
  | nil => exact absurd h (d.transOf_ne_nil s)
  | cons u rest => simp

/-! ### Enabled actions, read off the transitions -/

/-- The row actions this state's transitions mention, as `ℕ` keys. -/
def ModelData.keys1 (d : ModelData) (s : ℕ) : Finset ℕ :=
  ((d.transOf s).map Transition.act1).toFinset

/-- The column actions this state's transitions mention. -/
def ModelData.keys2 (d : ModelData) (s : ℕ) : Finset ℕ :=
  ((d.transOf s).map Transition.act2).toFinset

@[simp]
theorem ModelData.mem_keys1 (d : ModelData) (s m : ℕ) :
    m ∈ d.keys1 s ↔ ∃ t ∈ d.transOf s, t.act1 = m := by
  simp only [ModelData.keys1, List.mem_toFinset, List.mem_map]

@[simp]
theorem ModelData.mem_keys2 (d : ModelData) (s m : ℕ) :
    m ∈ d.keys2 s ↔ ∃ t ∈ d.transOf s, t.act2 = m := by
  simp only [ModelData.keys2, List.mem_toFinset, List.mem_map]

/-! ### Padding, so the denotation is total

`Csg.CSG`'s kernel is total in both action types, which is the right shape: enabledness is a
property of a concrete model, and the game it denotes resolves it, exactly as PRISM resolves guards
into a transition function. The resolution is *duplication*: a row action not enabled at `s`
denotes the same transition as a fixed enabled one.

Both the qualitative operators and `MatrixGame.value` are invariant under that -- the former
because they quantify `∃ a1 ∀ a2` over the action index and a retraction onto the enabled set
leaves such a quantifier unchanged, the latter because a duplicated row adds no new mixed
strategy. -/

/-- The row action `a1` denotes at `s`: itself when enabled, and otherwise a fixed enabled one. -/
def ModelData.pad1 (d : ModelData) (s a1 : ℕ) : ℕ :=
  if a1 ∈ d.keys1 s then a1 else ((d.transOf s).headD default).act1

/-- The column-side mirror. -/
def ModelData.pad2 (d : ModelData) (s a2 : ℕ) : ℕ :=
  if a2 ∈ d.keys2 s then a2 else ((d.transOf s).headD default).act2

/-- The transition for a joint action, after padding. Total; `transAt_mem` says the fall-through to
    `default` is unreachable for a model of valid shape. -/
def ModelData.transAt (d : ModelData) (s a1 a2 : ℕ) : Transition :=
  ((d.transOf s).find? fun t => t.act1 == d.pad1 s a1 && t.act2 == d.pad2 s a2).getD default

/-- `pad1` lands in the state's row-action keys. -/
theorem ModelData.pad1_mem_keys1 (d : ModelData) (s a1 : ℕ) : d.pad1 s a1 ∈ d.keys1 s := by
  unfold ModelData.pad1
  split_ifs with hmem
  · exact hmem
  · rw [ModelData.mem_keys1]
    exact ⟨(d.transOf s).headD default, d.headD_mem s, rfl⟩

/-- The column-side mirror. -/
theorem ModelData.pad2_mem_keys2 (d : ModelData) (s a2 : ℕ) : d.pad2 s a2 ∈ d.keys2 s := by
  unfold ModelData.pad2
  split_ifs with hmem
  · exact hmem
  · rw [ModelData.mem_keys2]
    exact ⟨(d.transOf s).headD default, d.headD_mem s, rfl⟩

/-- An enabled action denotes itself. `split_ifs` leaves one goal, not two: the `if` condition is
    `h` itself, so the negative branch closes on the spot. -/
theorem ModelData.pad1_eq_self (d : ModelData) {s a1 : ℕ} (h : a1 ∈ d.keys1 s) :
    d.pad1 s a1 = a1 := by
  unfold ModelData.pad1
  split_ifs
  rfl

/-- The column-side mirror. -/
theorem ModelData.pad2_eq_self (d : ModelData) {s a2 : ℕ} (h : a2 ∈ d.keys2 s) :
    d.pad2 s a2 = a2 := by
  unfold ModelData.pad2
  split_ifs
  rfl

/-- Padding twice is padding once -- it lands in the enabled set, where it is the identity. -/
theorem ModelData.pad1_idem (d : ModelData) (s a1 : ℕ) : d.pad1 s (d.pad1 s a1) = d.pad1 s a1 :=
  d.pad1_eq_self (d.pad1_mem_keys1 s a1)

/-- The column-side mirror. -/
theorem ModelData.pad2_idem (d : ModelData) (s a2 : ℕ) : d.pad2 s (d.pad2 s a2) = d.pad2 s a2 :=
  d.pad2_eq_self (d.pad2_mem_keys2 s a2)

/-- **Padding invariance.** The transition a joint action denotes is the one its padded
    representative denotes -- the padding map is a retraction onto the enabled set and the kernel
    factors through it. -/
theorem ModelData.transAt_pad (d : ModelData) (s a1 a2 : ℕ) :
    d.transAt s (d.pad1 s a1) (d.pad2 s a2) = d.transAt s a1 a2 := by
  unfold ModelData.transAt
  rw [d.pad1_idem s a1, d.pad2_idem s a2]

/-! ### Validity

Five conditions in `ℕ`, bundled as `Shape` so a caller discharges them with one `decide`, and three
in `ℚ`. All of them quantify over `transOf`, so each is a property of transitions that exist --
checkable as a model is built, one transition at a time. -/

/-- Every transition's actions are in the global namespaces. -/
def ModelData.ActInRange (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s, t.act1 < d.nAct1 ∧ t.act2 < d.nAct2

instance (d : ModelData) : Decidable d.ActInRange := by
  unfold ModelData.ActInRange; infer_instance

/-- Every successor index is a real state. -/
def ModelData.InRange (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s, ∀ p ∈ t.dist, p.1 < d.nStates

instance (d : ModelData) : Decidable d.InRange := by
  unfold ModelData.InRange; infer_instance

/-- **No two transitions in a state share a joint action.** Once both players have chosen there is
    nothing left to resolve, so a second transition for the same pair would be nondeterminism a
    `CSG` cannot express.

    Stated as `Nodup` on the list of joint actions rather than as an implication ending in `t = u`.
    That keeps it in `ℕ`: comparing two `Transition`s would compare their `ℚ` fields, and a model
    with fractional weights would then put `Shape` itself beyond `decide`. -/
def ModelData.Functional (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ((d.transOf s).map fun t => (t.act1, t.act2)).Nodup

instance (d : ModelData) : Decidable d.Functional := by
  unfold ModelData.Functional; infer_instance

/-- **The enabled set is a product.** The players choose independently, so every pair in
    `keys1 × keys2` must have a transition: a state offering `(0,0)`, `(0,1)` and `(1,0)` but not
    `(1,1)` denotes no `CSG`, since both players picking `1` is a legal pair of independent choices
    with nowhere to go.

    A count (`(transOf s).length = (keys1 s).card * (keys2 s).card`) is equivalent given
    `Functional` and cheaper to check, but needs a pigeonhole argument to be usable; this is the
    form `transAt_mem` consumes. -/
def ModelData.Total (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ a1 ∈ d.keys1 s, ∀ a2 ∈ d.keys2 s,
    ∃ t ∈ d.transOf s, t.act1 = a1 ∧ t.act2 = a2

instance (d : ModelData) : Decidable d.Total := by
  unfold ModelData.Total; infer_instance

/-- The structural conditions, bundled. Pure `ℕ`, so one `decide` settles all of them. -/
def ModelData.Shape (d : ModelData) : Prop :=
  d.ActInRange ∧ d.InRange ∧ d.Functional ∧ d.Total

instance (d : ModelData) : Decidable d.Shape := by
  unfold ModelData.Shape; infer_instance

theorem ModelData.Shape.actInRange {d : ModelData} (hs : d.Shape) : d.ActInRange := hs.1

theorem ModelData.Shape.inRange {d : ModelData} (hs : d.Shape) : d.InRange := hs.2.1

theorem ModelData.Shape.functional {d : ModelData} (hs : d.Shape) : d.Functional := hs.2.2.1

theorem ModelData.Shape.total {d : ModelData} (hs : d.Shape) : d.Total := hs.2.2.2

/-- Every weight is nonnegative: the half of `Stochastic` the support bridge needs, and the cheap
    half -- rational *comparisons* with no addition, so `decide` settles it where a row sum would
    not. -/
def ModelData.Nonneg (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s, ∀ p ∈ t.dist, 0 ≤ p.2

instance (d : ModelData) : Decidable d.Nonneg := by
  unfold ModelData.Nonneg; infer_instance

/-- No weight is zero -- what lets a support be read off a row's *keys*, with the weights never
    inspected. See `keysNat`. A successor listed with probability zero is a successor not listed,
    so this is a normalisation rather than a burden. -/
def ModelData.Nonzero (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s, ∀ p ∈ t.dist, p.2 ≠ 0

instance (d : ModelData) : Decidable d.Nonzero := by
  unfold ModelData.Nonzero; infer_instance

/-- Every transition's distribution is a probability distribution. Genuine `ℚ` arithmetic, so a
    caller discharges it with `norm_num` rather than `decide` once any weight is a fraction. -/
def ModelData.Stochastic (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s,
    (∀ p ∈ t.dist, 0 ≤ p.2) ∧ (t.dist.map Prod.snd).sum = 1

instance (d : ModelData) : Decidable d.Stochastic := by
  unfold ModelData.Stochastic; infer_instance

theorem ModelData.Stochastic.nonneg {d : ModelData} (h : d.Stochastic) : d.Nonneg :=
  fun s t ht => (h s t ht).1

/-! ### The transition a padded pair selects really is one of the state's -/

/-- **Padding is faithful.** For a model of valid shape the padded pair always matches one of the
    state's own transitions, so `transAt` never falls through to `default`. This connects the
    validity conditions, which quantify over `transOf`, to `transAt`. -/
theorem ModelData.transAt_mem (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a1 a2 : ℕ) :
    d.transAt s a1 a2 ∈ d.transOf s := by
  obtain ⟨t, ht, h1, h2⟩ := hs.total s _ (d.pad1_mem_keys1 s a1) _ (d.pad2_mem_keys2 s a2)
  have hne : ((d.transOf s).find? fun u =>
      u.act1 == d.pad1 s a1 && u.act2 == d.pad2 s a2) ≠ none := by
    intro hnone
    have hcontra := List.find?_eq_none.mp hnone t ht
    simp only [h1, h2, beq_self_eq_true, Bool.and_self] at hcontra
    exact hcontra trivial
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hne
  unfold ModelData.transAt
  rw [hu]
  exact List.mem_of_find?_eq_some hu

/-- Hence the padded transition's successors are all real states -- `Finset.attachFin`'s side
    condition. -/
theorem ModelData.inRange_transAt (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a1 a2 : ℕ) :
    ∀ p ∈ (d.transAt s a1 a2).dist, p.1 < d.nStates :=
  hs.inRange s _ (d.transAt_mem hs s a1 a2)

/-! ## The enabled action sets, and padding invariance in `Fin`

What the operators above this file quantify over, and the facts that let a quantifier over a
state's own actions stand in for one over the global namespace. -/

/-- A state's row-action keys are all in the global namespace. -/
theorem ModelData.keys1_lt (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    ∀ m ∈ d.keys1 s, m < d.nAct1 := by
  intro m hm
  rw [ModelData.mem_keys1] at hm
  obtain ⟨t, ht, rfl⟩ := hm
  exact (hs.actInRange s t ht).1

/-- The column-side mirror. -/
theorem ModelData.keys2_lt (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    ∀ m ∈ d.keys2 s, m < d.nAct2 := by
  intro m hm
  rw [ModelData.mem_keys2] at hm
  obtain ⟨t, ht, rfl⟩ := hm
  exact (hs.actInRange s t ht).2

/-- **The row actions enabled at `s`.** A `Finset (Fin d.nAct1)`, so the operators can quantify
    over it in place of `Finset.univ`. -/
def ModelData.enabled1 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    Finset (Fin d.nAct1) :=
  Finset.attachFin (d.keys1 s) (d.keys1_lt hs s)

/-- The column player's. -/
def ModelData.enabled2 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    Finset (Fin d.nAct2) :=
  Finset.attachFin (d.keys2 s) (d.keys2_lt hs s)

@[simp]
theorem ModelData.mem_enabled1 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) : a1 ∈ d.enabled1 hs s ↔ (a1 : ℕ) ∈ d.keys1 s := by
  simp only [ModelData.enabled1, Finset.mem_attachFin]

@[simp]
theorem ModelData.mem_enabled2 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a2 : Fin d.nAct2) : a2 ∈ d.enabled2 hs s ↔ (a2 : ℕ) ∈ d.keys2 s := by
  simp only [ModelData.enabled2, Finset.mem_attachFin]

/-- The padded representative of `a1`, back in `Fin d.nAct1`. -/
def ModelData.padFin1 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a1 : Fin d.nAct1) :
    Fin d.nAct1 :=
  ⟨d.pad1 s a1, d.keys1_lt hs s _ (d.pad1_mem_keys1 s a1)⟩

/-- The column player's. -/
def ModelData.padFin2 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a2 : Fin d.nAct2) :
    Fin d.nAct2 :=
  ⟨d.pad2 s a2, d.keys2_lt hs s _ (d.pad2_mem_keys2 s a2)⟩

@[simp]
theorem ModelData.padFin1_mem (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) : d.padFin1 hs s a1 ∈ d.enabled1 hs s := by
  rw [ModelData.mem_enabled1]
  exact d.pad1_mem_keys1 s a1

@[simp]
theorem ModelData.padFin2_mem (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a2 : Fin d.nAct2) : d.padFin2 hs s a2 ∈ d.enabled2 hs s := by
  rw [ModelData.mem_enabled2]
  exact d.pad2_mem_keys2 s a2

/-- Neither enabled set is empty, since every state has a transition and it names an action. -/
theorem ModelData.enabled1_nonempty (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    (d.enabled1 hs s).Nonempty := by
  refine ⟨⟨d.pad1 s 0, d.keys1_lt hs s _ (d.pad1_mem_keys1 s 0)⟩, ?_⟩
  rw [ModelData.mem_enabled1]
  exact d.pad1_mem_keys1 s 0

/-- The column player's. -/
theorem ModelData.enabled2_nonempty (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    (d.enabled2 hs s).Nonempty := by
  refine ⟨⟨d.pad2 s 0, d.keys2_lt hs s _ (d.pad2_mem_keys2 s 0)⟩, ?_⟩
  rw [ModelData.mem_enabled2]
  exact d.pad2_mem_keys2 s 0

/-- `padFin1` is the identity on enabled actions. -/
theorem ModelData.padFin1_eq_self (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    {a1 : Fin d.nAct1} (h : a1 ∈ d.enabled1 hs s) : d.padFin1 hs s a1 = a1 := by
  rw [ModelData.mem_enabled1] at h
  exact Fin.ext (d.pad1_eq_self h)

/-- The column-side mirror. -/
theorem ModelData.padFin2_eq_self (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    {a2 : Fin d.nAct2} (h : a2 ∈ d.enabled2 hs s) : d.padFin2 hs s a2 = a2 := by
  rw [ModelData.mem_enabled2] at h
  exact Fin.ext (d.pad2_eq_self h)

/-- Padding invariance at the `Fin` level, which is the form the transfer lemmas use. -/
theorem ModelData.transAt_padFin (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.transAt s (d.padFin1 hs s a1) (d.padFin2 hs s a2) = d.transAt s a1 a2 :=
  d.transAt_pad s a1 a2

/-! ### Padding one coordinate at a time

`transAt_pad` pads both coordinates. The qualitative operators need each separately, because `aF`
varies its row action with the column action fixed and `bF` does the reverse. Both hold because
`transAt` pads the two coordinates independently and each padding is idempotent. The support-level
versions, `supportOf_padFin1` and `supportOf_padFin2`, are with `supportOf` below. -/

/-- Padding the row action alone leaves the transition alone. -/
theorem ModelData.transAt_pad1 (d : ModelData) (s a1 a2 : ℕ) :
    d.transAt s (d.pad1 s a1) a2 = d.transAt s a1 a2 := by
  unfold ModelData.transAt
  rw [d.pad1_idem s a1]

/-- And the column action alone. -/
theorem ModelData.transAt_pad2 (d : ModelData) (s a1 a2 : ℕ) :
    d.transAt s a1 (d.pad2 s a2) = d.transAt s a1 a2 := by
  unfold ModelData.transAt
  rw [d.pad2_idem s a2]


/-! ### The quantifier swap

**The payoff of carrying actions on transitions.** Every qualitative operator in this library has
the shape `∃ a1, ∀ a2, P a1 a2` over the *global* action namespaces. This says such a quantifier may
be restricted to a state's own enabled actions, provided `P` cannot tell a joint action from its
padded representative -- which `supportOf_padFin` supplies, since `P` always factors through the
support.

The argument is that `pad` is a retraction onto the enabled set. Forwards, a witness `a1` is
replaced by `padFin1 a1`, which is enabled and which `P` cannot distinguish from it, and an enabled
`a2` is its own representative. Backwards, an enabled witness serves unchanged, and an arbitrary
`a2` is handled by its representative, which is enabled. Nothing here is specific to `Pre1`; the
other five operators instantiate the same lemma. -/

/-- Restricting `∃ a1, ∀ a2` to the actions a state actually enables. -/
theorem ModelData.exists_forall_enabled_iff (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (P : Fin d.nAct1 → Fin d.nAct2 → Prop)
    (hP : ∀ a1 a2, P (d.padFin1 hs s a1) (d.padFin2 hs s a2) ↔ P a1 a2) :
    (∃ a1, ∀ a2, P a1 a2) ↔ (∃ a1 ∈ d.enabled1 hs s, ∀ a2 ∈ d.enabled2 hs s, P a1 a2) := by
  constructor
  · rintro ⟨a1, ha1⟩
    refine ⟨d.padFin1 hs s a1, d.padFin1_mem hs s a1, fun a2 ha2 => ?_⟩
    have h2 := d.padFin2_eq_self hs s ha2
    have hgot := (hP a1 a2).mpr (ha1 a2)
    rwa [h2] at hgot
  · rintro ⟨a1, hm1, ha1⟩
    refine ⟨a1, fun a2 => ?_⟩
    have hgot := ha1 (d.padFin2 hs s a2) (d.padFin2_mem hs s a2)
    have hiff := hP a1 a2
    rw [d.padFin1_eq_self hs s hm1] at hiff
    exact hiff.mp hgot

/-! ## The game a model denotes -/

/-- The rational game a `ModelData` denotes. Total by construction; whether it is a *game* is
    `WellFormed`'s business. Terminal states self-loop and disabled actions are padded, both inside
    `transAt`. -/
def ModelData.toCsgQ (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] :
    CsgQ (Fin d.nStates) (Fin d.nAct1) (Fin d.nAct2) where
  K s a1 a2 := denseOf d.nStates (d.transAt s a1 a2).dist
  r s a1 a2 := (d.stateAt s).rew + (d.transAt s a1 a2).rew

/-- The kernel entry, unfolded. -/
@[simp]
theorem ModelData.toCsgQ_K (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) (s' : Fin d.nStates) :
    d.toCsgQ.K s a1 a2 s' = denseOf d.nStates (d.transAt s a1 a2).dist s' := rfl

/-- The reward decomposition, by definition: what `CSG.r` folds into one number. -/
theorem ModelData.r_eq (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.toCsgQ.r s a1 a2 = (d.stateAt s).rew + (d.transAt s a1 a2).rew := rfl

/-! ## The fast support -/

/-- **The successors of a state/action triple**, read off the padded transition's row rather than
    found by scanning the states. -/
def ModelData.supportOf (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a1 : Fin d.nAct1)
    (a2 : Fin d.nAct2) : Finset (Fin d.nStates) :=
  Finset.attachFin (keysNat (d.transAt s a1 a2).dist)
    (keysNat_lt _ (d.inRange_transAt hs s a1 a2))

/-- The support is padding-invariant -- the statement the quantifier swap consumes. -/
theorem ModelData.supportOf_padFin (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.supportOf hs s (d.padFin1 hs s a1) (d.padFin2 hs s a2) = d.supportOf hs s a1 a2 := by
  unfold ModelData.supportOf
  simp only [ModelData.transAt_padFin]
/-- The support does not see a row action's padding. Stated with `padFin1` on the left so that it
    rewrites in the direction the operator proofs need. -/
theorem ModelData.supportOf_padFin1 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.supportOf hs s (d.padFin1 hs s a1) a2 = d.supportOf hs s a1 a2 := by
  unfold ModelData.supportOf
  simp only [ModelData.padFin1, ModelData.transAt_pad1]

/-- Nor a column action's. -/
theorem ModelData.supportOf_padFin2 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.supportOf hs s a1 (d.padFin2 hs s a2) = d.supportOf hs s a1 a2 := by
  unfold ModelData.supportOf
  simp only [ModelData.padFin2, ModelData.transAt_pad2]

/-- **The bridge, and the quarantine.** `Comp/QualitativeFinset.lean`'s `supportF` -- a filter over
    every state, with a rational disequality in it -- is the padded transition's own key set.

    Computing a support costs the row's length instead of the state count; and nothing above this
    line touches a weight at all, since `supportOf` is built from `keysNat`, which is `ℕ` data. So
    the kernel reduces every operator above it even when the weights are fractions it could not so
    much as evaluate. That is the job `Comp/HideOrRunQ.lean` and `Comp/SafetyChainQ.lean` each do by
    hand for their own game, except that those tables rely on their kernels being `0`/`1`; this one
    holds for any model, and the three `ℚ` conditions it rests on are proved once per model rather
    than reproved inside every fixed-point check. -/
theorem ModelData.supportF_eq (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (hs : d.Shape) (hnn : d.Nonneg) (hnz : d.Nonzero) (s : Fin d.nStates) (a1 : Fin d.nAct1)
    (a2 : Fin d.nAct2) :
    d.toCsgQ.supportF s a1 a2 = d.supportOf hs s a1 a2 := by
  have hmem := d.transAt_mem hs s a1 a2
  ext s'
  rw [CsgQ.mem_supportF, ModelData.toCsgQ_K,
    denseOf_ne_zero_iff d.nStates _ s' (hnn s _ hmem) (hnz s _ hmem)]
  simp [ModelData.supportOf]

/-! ## Well-formedness -/

/-- **The payoff.** The structural conditions and the stochastic one give a well-formed game. Split
    deliberately: `Shape` is pure `ℕ` and goes by `decide`, and only `Stochastic` costs rational
    arithmetic.

    Note how little the totality of the kernel costs here. `Stochastic` is a property of the
    transitions a model declares -- checkable one at a time as it is built -- and the pairs the
    model does *not* declare inherit it, because padding sends each of them to a declared
    transition (`transAt_mem`) and a terminal state's self-loop carries weight `1`. -/
theorem ModelData.wellFormed (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (hs : d.Shape) (h2 : d.Stochastic) : d.toCsgQ.WellFormed := by
  refine ⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩
  · exact denseOf_nonneg _ _ s' (h2 s _ (d.transAt_mem hs s a1 a2)).1
  · change ∑ s' : Fin d.nStates, denseOf d.nStates (d.transAt s a1 a2).dist s' = 1
    rw [sum_denseOf d.nStates _ (d.inRange_transAt hs s a1 a2)]
    exact (h2 s _ (d.transAt_mem hs s a1 a2)).2

end Comp
