/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelData
import Comp.ReachTrace
import Comp.Search

/-!
# Probabilistic reachability for a model given as data

**Status: confirmed by a clean `lake build`.** `Comp/ReachTrace.lean` turns a checked trace into
an answer to `Objective.reach` for any `CsgQ`. This file supplies the two things a `ModelData`
needs to use it: a plain-data shape for a trace, and a search that produces one.

**The data.** A `ReachRun` is three tables of rationals: the vectors, and for each step the row
and column strategies at each state. `ReachRun.val`, `row` and `col` read them with `List.getD`,
so a table that is too short reads as `0` instead of failing; a wrong or missing entry makes a
step's check false, never unsound.

**Finding a run.** `ModelData.reachRun d target start n` iterates the operator `n` times from the
constant `start`, solving each state's stage game with `MatrixGameQ.findValueCert`. It is for
`#eval`: its output is printed, pasted into the instance file as a literal `ReachRun`, and
forgotten. Nothing is proved about it.

**Checking a run.** `ModelData.answers_reach_of_runs` takes a literal run from `0` and one from
`1` and asks for four closed decidable facts: the two starting vectors, and the checked steps of
each run. `decide +kernel` settles them, by having the kernel evaluate the game's rational
arithmetic directly. The conclusion is an `Answers` statement about the real-valued game the model
denotes.

The stage games here are over the global action namespaces, with disabled actions padded as
`ModelData.toCsgQ` pads them, so a strategy in a run has one entry per global action.
-/

namespace Comp

/-- A reachability run, as plain data. -/
structure ReachRun where
  /-- `vals[k][s]`: the `k`-th vector at state `s`. -/
  vals : List (List ℚ)
  /-- `rows[k][s][a1]`: the row strategy at state `s` that certifies step `k`. -/
  rows : List (List (List ℚ))
  /-- `cols[k][s][a2]`: the column strategy at state `s` that certifies step `k`. -/
  cols : List (List (List ℚ))
  deriving Repr

namespace ReachRun

/-- The `k`-th vector at state `s`, or `0` where the table has no entry. -/
def val (r : ReachRun) {n : ℕ} (k : ℕ) (s : Fin n) : ℚ :=
  (r.vals.getD k []).getD s.val 0

/-- The row strategy at state `s` for step `k`, or `0` where the table has no entry. -/
def row (r : ReachRun) {n n1 : ℕ} (k : ℕ) (s : Fin n) (a : Fin n1) : ℚ :=
  ((r.rows.getD k []).getD s.val []).getD a.val 0

/-- The column strategy at state `s` for step `k`, or `0` where the table has no entry. -/
def col (r : ReachRun) {n n2 : ℕ} (k : ℕ) (s : Fin n) (a : Fin n2) : ℚ :=
  ((r.cols.getD k []).getD s.val []).getD a.val 0

end ReachRun

namespace ModelData

/-! ## Finding a run -/

/-- One step of the search, tabulated by state: the next value and the two strategies. A target
    state gets `1` and no strategies; a state where the search finds nothing gets `0` and no
    strategies, which the check will reject. For `#eval`. -/
def reachStepRun (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (target : Finset (Fin d.nStates)) (v : Fin d.nStates → ℚ) : List (ℚ × List ℚ × List ℚ) :=
  (List.finRange d.nStates).map fun s =>
    if s ∈ target then (1, [], [])
    else
      match (d.toCsgQ.reachGameQ s v).findValueCert (List.finRange d.nAct1)
          (List.finRange d.nAct2) with
      | some c => (c.1, (List.finRange d.nAct1).map c.2.1, (List.finRange d.nAct2).map c.2.2)
      | none => (0, [], [])

/-- `n` steps of the search from the constant vector `start`, as a `ReachRun` to print. `start` is
    `0` for a lower run and `1` for an upper one. For `#eval`. -/
def reachRun (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (target : Finset (Fin d.nStates)) (start : ℚ) : ℕ → ReachRun
  | 0 => ⟨[(List.finRange d.nStates).map fun _ => start], [], []⟩
  | n + 1 =>
    let r := reachRun d target start n
    let st := d.reachStepRun target (r.val n)
    ⟨r.vals ++ [st.map fun x => x.1], r.rows ++ [st.map fun x => x.2.1],
      r.cols ++ [st.map fun x => x.2.2]⟩

/-! ## Checking a run -/

/-- **Reachability, from two literal runs.** `lo` is a run of `n` steps from `0` and `hi` a run of
    `m` steps from `1`. The four hypotheses are closed and decidable. The conclusion: at every
    state, the real reachability value of the game `d` denotes lies in `[lo.val n s, hi.val m s]`.
    `CsgQ.answers_reach_of_steps` at the tables' reading functions. -/
theorem answers_reach_of_runs (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (hs : d.Shape) (h2 : d.Stochastic) (hrf : d.toCsgQ.RewardFree)
    (target : Finset (Fin d.nStates)) (lo hi : ReachRun) (n m : ℕ)
    (hlo0 : ∀ s : Fin d.nStates, lo.val 0 s = 0)
    (hlo : ∀ k < n, d.toCsgQ.ReachStep target (lo.val k) (lo.val (k + 1)) (lo.row k) (lo.col k))
    (hhi0 : ∀ s : Fin d.nStates, hi.val 0 s = 1)
    (hhi : ∀ k < m,
      d.toCsgQ.ReachStep target (hi.val k) (hi.val (k + 1)) (hi.row k) (hi.col k)) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.reach target)
      (Answer.interval (lo.val n) (hi.val m)) :=
  CsgQ.answers_reach_of_steps d.toCsgQ (d.wellFormed hs h2) hrf target
    lo.val lo.row lo.col n hi.val hi.row hi.col m hlo0 hlo hhi0 hhi

end ModelData

end Comp
