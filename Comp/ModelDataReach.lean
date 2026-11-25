/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelDataQualitative
import Comp.ModelDataStage
import Comp.ReachTrace
import Comp.ReachBounds
import Comp.Search

/-!
# Probabilistic reachability for a model given as data

**Status: confirmed by a clean `lake build`.** `Comp/ReachTrace.lean` turns a checked trace into
an answer to `Objective.reach` for any `CsgQ`. This file supplies the two things a `ModelData`
needs to use it: a plain-data shape for a trace, and a search that produces one.

**The data.** A `ReachRun` is three tables: the vectors, and for each step the row and column
strategies at each state. A strategy is sparse: a list of pairs of an action index and its weight,
every action it does not list having weight `0`. `ReachRun.val`, `row` and `col` read the tables
with total lookups, so a table that is too short reads as `0` instead of failing; a wrong or
missing entry makes a step's check false, never unsound.

**Finding a run.** `ModelData.reachRun d target start n` iterates the operator `n` times from the
vector `start`, solving each state's stage game with `MatrixGameQ.findValueCert`. It is for
`#eval`: its output is printed, pasted into the instance file as a literal `ReachRun`, and
forgotten. Nothing is proved about it.

**Checking a run.** `ModelData.answers_reach_of_runs` takes a literal run from `0` and one from
`1` and asks for four closed decidable facts: the two starting vectors, and the checked steps of
each run. `decide +kernel` settles them, by having the kernel evaluate the game's rational
arithmetic directly. The conclusion is an `Answers` statement about the real-valued game the model
denotes.

**A tighter upper run.** `ModelData.answers_reach_of_runs_avoiding` lets the upper run start at `0`
on a set `z` of states and `1` elsewhere. It asks that `z` avoid the target and that
`z ⊆ Qual.pre1 (d.supportOf hs) z`, which plain `decide` settles since no weight is involved. The
sure-safety region `d.gRegionTr hs (Finset.univ \ target)` is the largest such `z`, and `#eval`
prints it.

**One-sided runs.** `Comp/ReachBounds.lean` checks a lower run with column strategies alone and
an upper vector with row strategies alone. `ModelData.reachLowerRun d target den n` searches for
the first, rounding each value down to a multiple of `1 / den` before the next step.
`ModelData.reachUpperRun d target u` prints, for a candidate upper vector `u`, one step of the
operator from `u` and the row strategies of that step; `u` passes the check when the step is
nowhere above `u`. `ModelData.answers_reach_of_bounds` takes the two as literal `ReachRun`s: a
lower run leaves `rows` empty, and an upper one is read at index `0` and leaves `cols` empty.

**Enabled actions.** Every check here is on a state's enabled actions. A strategy in a run may
give weight to enabled actions only, and is tested against the other player's enabled actions
only (`ReachStepEn`, `ReachLowerEn`, `ReachUpperEn`). Each of these
implies the corresponding check on the game the model denotes, because a disabled action
duplicates an enabled one there (`reachGameQ_dupRow`, `reachGameQ_dupCol`). The searches
enumerate supports over the enabled actions, so the strategies they print are of that form.
-/

namespace Comp

/-- A reachability run, as plain data. -/
structure ReachRun where
  /-- `vals[k][s]`: the `k`-th vector at state `s`. -/
  vals : List (List ℚ)
  /-- `rows[k][s]`: the row strategy at state `s` that certifies step `k`, as pairs of an action
      index and its weight. -/
  rows : List (List (List (ℕ × ℚ)))
  /-- `cols[k][s]`: the column strategy at state `s` that certifies step `k`, in the same form. -/
  cols : List (List (List (ℕ × ℚ)))
  deriving Repr

/-- The weight a sparse strategy gives to the action `a`: that of the first pair listing `a`, and
    `0` when none does. -/
def sparseAt (l : List (ℕ × ℚ)) (a : ℕ) : ℚ :=
  match l.find? (fun p => p.1 == a) with
  | some p => p.2
  | none => 0

/-- The nonzero entries of `p` on the listed actions, as pairs of an action index and its weight.
    For `#eval`. -/
def sparseOf {n : ℕ} (acts : List (Fin n)) (p : Fin n → ℚ) : List (ℕ × ℚ) :=
  acts.filterMap fun a => if p a = 0 then none else some (a.val, p a)

namespace ReachRun

/-- The `k`-th vector at state `s`, or `0` where the table has no entry. -/
def val (r : ReachRun) {n : ℕ} (k : ℕ) (s : Fin n) : ℚ :=
  (r.vals.getD k []).getD s.val 0

/-- The weight of the action `a` in the row strategy at state `s` for step `k`; `0` where the
    table has no entry. -/
def row (r : ReachRun) {n n1 : ℕ} (k : ℕ) (s : Fin n) (a : Fin n1) : ℚ :=
  sparseAt ((r.rows.getD k []).getD s.val []) a.val

/-- The weight of the action `a` in the column strategy at state `s` for step `k`; `0` where the
    table has no entry. -/
def col (r : ReachRun) {n n2 : ℕ} (k : ℕ) (s : Fin n) (a : Fin n2) : ℚ :=
  sparseAt ((r.cols.getD k []).getD s.val []) a.val

end ReachRun

/-- `x` rounded down to a multiple of `1 / den`, for `x ≥ 0`. With `den = 0` it returns `x`. For
    `#eval`. -/
def floorTo (den : ℕ) (x : ℚ) : ℚ :=
  if den = 0 then x else (((x * den).num.toNat / (x * den).den : ℕ) : ℚ) / den

/-- `x` rounded up to a multiple of `1 / den`, for `x ≥ 0`. With `den = 0` it returns `x`. For
    `#eval`. -/
def ceilTo (den : ℕ) (x : ℚ) : ℚ :=
  if den = 0 then x
  else ((((x * den).num.toNat + (x * den).den - 1) / (x * den).den : ℕ) : ℚ) / den

namespace ModelData

/-! ## Finding a run -/

/-- The row actions enabled at `s`, as a list in index order. -/
def rowList (d : ModelData) (s : Fin d.nStates) : List (Fin d.nAct1) :=
  (List.finRange d.nAct1).filter fun a => decide ((a : ℕ) ∈ d.keys1 s)

/-- The column actions enabled at `s`, as a list in index order. -/
def colList (d : ModelData) (s : Fin d.nStates) : List (Fin d.nAct2) :=
  (List.finRange d.nAct2).filter fun a => decide ((a : ℕ) ∈ d.keys2 s)

/-- One step of the search, tabulated by state: the next value and the two strategies. A target
    state gets `1` and no strategies; a state where the search finds nothing gets `0` and no
    strategies, which the check will reject. Supports are enumerated over the state's enabled
    actions, and each strategy is printed as the pairs of an action and its nonzero weight. For
    `#eval`. -/
def reachStepRun (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (target : Finset (Fin d.nStates)) (v : Fin d.nStates → ℚ) :
    List (ℚ × List (ℕ × ℚ) × List (ℕ × ℚ)) :=
  (List.finRange d.nStates).map fun s =>
    if s ∈ target then (1, [], [])
    else
      match (d.toCsgQ.reachGameQ s v).findValueCert (d.rowList s) (d.colList s) with
      | some c => (c.1, sparseOf (d.rowList s) c.2.1, sparseOf (d.colList s) c.2.2)
      | none => (0, [], [])

/-- `n` steps of the search from the vector `start`, as a `ReachRun` to print. `start` is the
    constant `0` for a lower run and the constant `1`, or a tightened start, for an upper one. For
    `#eval`. -/
def reachRun (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (target : Finset (Fin d.nStates)) (start : Fin d.nStates → ℚ) : ℕ → ReachRun
  | 0 => ⟨[(List.finRange d.nStates).map start], [], []⟩
  | n + 1 =>
    let r := reachRun d target start n
    let st := d.reachStepRun target (r.val n)
    ⟨r.vals ++ [st.map fun x => x.1], r.rows ++ [st.map fun x => x.2.1],
      r.cols ++ [st.map fun x => x.2.2]⟩

/-- `n` lower steps of the search from the constant `0`, each value rounded down to a multiple of
    `1 / den` before the next step, with the column strategies the search found. Rounding keeps the
    numbers small, and a rounded value is still certified by the column strategy of the exact one.
    For `#eval`. -/
def reachLowerRun (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (target : Finset (Fin d.nStates)) (den : ℕ) : ℕ → ReachRun
  | 0 => ⟨[(List.finRange d.nStates).map (fun _ => (0 : ℚ))], [], []⟩
  | n + 1 =>
    let r := reachLowerRun d target den n
    let st := d.reachStepRun target (r.val n)
    ⟨r.vals ++ [st.map fun x => floorTo den x.1], [], r.cols ++ [st.map fun x => x.2.2]⟩

/-- A candidate upper vector `u`, one step of the operator from it, and the row strategies of
    that step. Where the second vector is nowhere above the first, `u` is a pre-fixed point and
    these row strategies certify it. For `#eval`. -/
def reachUpperRun (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (target : Finset (Fin d.nStates)) (u : Fin d.nStates → ℚ) : ReachRun :=
  let st := d.reachStepRun target u
  ⟨[(List.finRange d.nStates).map u, st.map fun x => x.1], [st.map fun x => x.2.1], []⟩

/-! ## Checks on enabled actions -/

/-- The reachability stage game does not see a row action's padding. -/
theorem reachGameQ_A_padFin1 (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (s : Fin d.nStates) (v : Fin d.nStates → ℚ) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    (d.toCsgQ.reachGameQ s v).A (d.padFin1 hs s a1) a2 = (d.toCsgQ.reachGameQ s v).A a1 a2 := by
  change d.toCsgQ.expectQ s (d.padFin1 hs s a1) a2 v = d.toCsgQ.expectQ s a1 a2 v
  unfold CsgQ.expectQ
  rw [d.toCsgQ_K_padFin1 hs s a1 a2]

/-- Nor a column action's. -/
theorem reachGameQ_A_padFin2 (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (s : Fin d.nStates) (v : Fin d.nStates → ℚ) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    (d.toCsgQ.reachGameQ s v).A a1 (d.padFin2 hs s a2) = (d.toCsgQ.reachGameQ s v).A a1 a2 := by
  change d.toCsgQ.expectQ s a1 (d.padFin2 hs s a2) v = d.toCsgQ.expectQ s a1 a2 v
  unfold CsgQ.expectQ
  rw [d.toCsgQ_K_padFin2 hs s a1 a2]

/-- Every row of the reachability stage game duplicates an enabled row. -/
theorem reachGameQ_dupRow (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (s : Fin d.nStates) (v : Fin d.nStates → ℚ) :
    ∀ a1, ∃ a1' ∈ d.enabled1 hs s, ∀ a2,
      (d.toCsgQ.reachGameQ s v).A a1 a2 = (d.toCsgQ.reachGameQ s v).A a1' a2 :=
  fun a1 => ⟨d.padFin1 hs s a1, d.padFin1_mem hs s a1,
    fun a2 => (d.reachGameQ_A_padFin1 hs s v a1 a2).symm⟩

/-- Every column of the reachability stage game duplicates an enabled column. -/
theorem reachGameQ_dupCol (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (s : Fin d.nStates) (v : Fin d.nStates → ℚ) :
    ∀ a2, ∃ a2' ∈ d.enabled2 hs s, ∀ a1,
      (d.toCsgQ.reachGameQ s v).A a1 a2 = (d.toCsgQ.reachGameQ s v).A a1 a2' :=
  fun a2 => ⟨d.padFin2 hs s a2, d.padFin2_mem hs s a2,
    fun a1 => (d.reachGameQ_A_padFin2 hs s v a1 a2).symm⟩

/-- **One exact step, on enabled actions.** As `CsgQ.ReachStep`, with the value certificate at
    each state taken on that state's enabled row and column actions. -/
def ReachStepEn (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (target : Finset (Fin d.nStates)) (v w : Fin d.nStates → ℚ)
    (p : Fin d.nStates → Fin d.nAct1 → ℚ) (q : Fin d.nStates → Fin d.nAct2 → ℚ) : Prop :=
  ∀ s, (s ∈ target → w s = 1) ∧
    (s ∉ target → (d.toCsgQ.reachGameQ s v).ValueCertOn (d.enabled1 hs s) (d.enabled2 hs s)
      (w s) (p s) (q s))

instance (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (target : Finset (Fin d.nStates)) (v w : Fin d.nStates → ℚ)
    (p : Fin d.nStates → Fin d.nAct1 → ℚ) (q : Fin d.nStates → Fin d.nAct2 → ℚ) :
    Decidable (d.ReachStepEn hs target v w p q) := by
  unfold ReachStepEn
  infer_instance

/-- **A lower step, on enabled actions.** As `CsgQ.ReachLower`, with the lower certificate taken
    on the state's enabled actions. -/
def ReachLowerEn (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (target : Finset (Fin d.nStates)) (v w : Fin d.nStates → ℚ)
    (q : Fin d.nStates → Fin d.nAct2 → ℚ) : Prop :=
  ∀ s, 0 ≤ w s ∧ w s ≤ 1 ∧
    (s ∉ target → (d.toCsgQ.reachGameQ s v).LowerCertOn (d.enabled1 hs s) (d.enabled2 hs s)
      (w s) (q s))

instance (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (target : Finset (Fin d.nStates)) (v w : Fin d.nStates → ℚ)
    (q : Fin d.nStates → Fin d.nAct2 → ℚ) : Decidable (d.ReachLowerEn hs target v w q) := by
  unfold ReachLowerEn
  infer_instance

/-- **An upper step, on enabled actions.** As `CsgQ.ReachUpper`, with the upper certificate taken
    on the state's enabled actions. -/
def ReachUpperEn (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (target : Finset (Fin d.nStates)) (v w : Fin d.nStates → ℚ)
    (p : Fin d.nStates → Fin d.nAct1 → ℚ) : Prop :=
  ∀ s, 0 ≤ w s ∧ w s ≤ 1 ∧ (s ∈ target → w s = 1) ∧
    (s ∉ target → (d.toCsgQ.reachGameQ s v).UpperCertOn (d.enabled1 hs s) (d.enabled2 hs s)
      (w s) (p s))

instance (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (target : Finset (Fin d.nStates)) (v w : Fin d.nStates → ℚ)
    (p : Fin d.nStates → Fin d.nAct1 → ℚ) : Decidable (d.ReachUpperEn hs target v w p) := by
  unfold ReachUpperEn
  infer_instance

/-- An exact step on enabled actions is an exact step of the denoted game. -/
theorem reachStep_of_en (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    {target : Finset (Fin d.nStates)} {v w : Fin d.nStates → ℚ}
    {p : Fin d.nStates → Fin d.nAct1 → ℚ} {q : Fin d.nStates → Fin d.nAct2 → ℚ}
    (h : d.ReachStepEn hs target v w p q) : d.toCsgQ.ReachStep target v w p q := by
  intro s
  exact And.intro (h s).1 fun hst =>
    MatrixGameQ.valueCert_of_on ((h s).2 hst) (d.reachGameQ_dupCol hs s v)
      (d.reachGameQ_dupRow hs s v)

/-- A lower step on enabled actions is a lower step of the denoted game. -/
theorem reachLower_of_en (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    {target : Finset (Fin d.nStates)} {v w : Fin d.nStates → ℚ}
    {q : Fin d.nStates → Fin d.nAct2 → ℚ}
    (h : d.ReachLowerEn hs target v w q) : d.toCsgQ.ReachLower target v w q := by
  intro s
  exact And.intro (h s).1 (And.intro (h s).2.1 fun hst =>
    MatrixGameQ.lowerCert_of_on ((h s).2.2 hst) (d.reachGameQ_dupRow hs s v))

/-- An upper step on enabled actions is an upper step of the denoted game. -/
theorem reachUpper_of_en (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    {target : Finset (Fin d.nStates)} {v w : Fin d.nStates → ℚ}
    {p : Fin d.nStates → Fin d.nAct1 → ℚ}
    (h : d.ReachUpperEn hs target v w p) : d.toCsgQ.ReachUpper target v w p := by
  intro s
  exact And.intro (h s).1 (And.intro (h s).2.1 (And.intro (h s).2.2.1 fun hst =>
    MatrixGameQ.upperCert_of_on ((h s).2.2.2 hst) (d.reachGameQ_dupCol hs s v)))

/-! ## Checking a run -/

/-- **Reachability, from two literal runs.** `lo` is a run of `n` steps from `0` and `hi` a run of
    `m` steps from `1`, each step exact on the enabled actions. The four hypotheses are closed
    and decidable. The conclusion: at every state, the real reachability value of the game `d`
    denotes lies in `[lo.val n s, hi.val m s]`. `CsgQ.answers_reach_of_steps` at the tables'
    reading functions. -/
theorem answers_reach_of_runs (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (hs : d.Shape) (h2 : d.Stochastic) (hrf : d.toCsgQ.RewardFree)
    (target : Finset (Fin d.nStates)) (lo hi : ReachRun) (n m : ℕ)
    (hlo0 : ∀ s : Fin d.nStates, lo.val 0 s = 0)
    (hlo : ∀ k < n, d.ReachStepEn hs target (lo.val k) (lo.val (k + 1)) (lo.row k) (lo.col k))
    (hhi0 : ∀ s : Fin d.nStates, hi.val 0 s = 1)
    (hhi : ∀ k < m, d.ReachStepEn hs target (hi.val k) (hi.val (k + 1)) (hi.row k) (hi.col k)) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.reach target)
      (Answer.interval (lo.val n) (hi.val m)) :=
  CsgQ.answers_reach_of_steps d.toCsgQ (d.wellFormed hs h2) hrf target
    lo.val lo.row lo.col n hi.val hi.row hi.col m hlo0
    (fun k hk => d.reachStep_of_en hs (hlo k hk)) hhi0
    (fun k hk => d.reachStep_of_en hs (hhi k hk))

/-- **Reachability, with the upper run started on a sure-avoid set.** As
    `answers_reach_of_runs`, except that `hi` starts at `0` on `z` and `1` elsewhere. The two
    conditions on `z` are closed and decidable without arithmetic; `Nonzero` is what lets the
    model's supports be read off its transition keys. -/
theorem answers_reach_of_runs_avoiding (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (hs : d.Shape) (h2 : d.Stochastic) (hnz : d.Nonzero) (hrf : d.toCsgQ.RewardFree)
    (target z : Finset (Fin d.nStates))
    (hz : z ⊆ Qual.pre1 (d.supportOf hs) z) (hdisj : ∀ s ∈ z, s ∉ target)
    (lo hi : ReachRun) (n m : ℕ)
    (hlo0 : ∀ s : Fin d.nStates, lo.val 0 s = 0)
    (hlo : ∀ k < n, d.ReachStepEn hs target (lo.val k) (lo.val (k + 1)) (lo.row k) (lo.col k))
    (hhi0 : ∀ s : Fin d.nStates, hi.val 0 s = if s ∈ z then 0 else 1)
    (hhi : ∀ k < m, d.ReachStepEn hs target (hi.val k) (hi.val (k + 1)) (hi.row k) (hi.col k)) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.reach target)
      (Answer.interval (lo.val n) (hi.val m)) :=
  CsgQ.answers_reach_of_steps_avoiding d.toCsgQ (d.wellFormed hs h2) hrf target
    (d.supportOf hs) (d.support_toCSG hs h2 hnz) z hz hdisj
    lo.val lo.row lo.col n hi.val hi.row hi.col m hlo0
    (fun k hk => d.reachStep_of_en hs (hlo k hk)) hhi0
    (fun k hk => d.reachStep_of_en hs (hhi k hk))

/-- **Reachability, from a one-sided lower run and a pre-fixed upper vector.** `lo` is a run of
    `n` lower steps from `0`, read with its column strategies, and `hi.val 0` is an upper vector
    that passes `ReachUpperEn` against itself with the row strategies `hi.row 0`. The three
    hypotheses are closed and decidable. `CsgQ.answers_reach_of_bounds` at the tables' reading
    functions. -/
theorem answers_reach_of_bounds (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (hs : d.Shape) (h2 : d.Stochastic) (hrf : d.toCsgQ.RewardFree)
    (target : Finset (Fin d.nStates)) (lo hi : ReachRun) (n : ℕ)
    (hlo0 : ∀ s : Fin d.nStates, lo.val 0 s = 0)
    (hlo : ∀ k < n, d.ReachLowerEn hs target (lo.val k) (lo.val (k + 1)) (lo.col k))
    (hhi : d.ReachUpperEn hs target (hi.val 0) (hi.val 0) (hi.row 0)) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.reach target)
      (Answer.interval (lo.val n) (hi.val 0)) :=
  CsgQ.answers_reach_of_bounds d.toCsgQ (d.wellFormed hs h2) hrf target
    lo.val lo.col n (hi.val 0) (hi.row 0) hlo0
    (fun k hk => d.reachLower_of_en hs (hlo k hk)) (d.reachUpper_of_en hs hhi)

end ModelData

end Comp
