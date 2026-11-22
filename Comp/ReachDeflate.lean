/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelDataReach

/-!
# A search for a pre-fixed upper vector: deflation

**Status: confirmed by a clean `lake build`.** `Comp/ReachBounds.lean` accepts any vector that the
reachability operator maps below itself as an upper bound on the reachability value. This file
proposes one. It is a search, for `#eval`: nothing here is proved, and nothing needs to be, since
`CsgQ.ReachUpper` decides whether to believe what it returns.

**The method.** Start from the vector that is `0` where the row player can surely avoid the
target and `1` elsewhere. Repeat: apply the operator once, then *deflate* sets of states. To
deflate a set `x` of non-target states against a vector `u` is to cap `u` on `x` at the best exit
value of `x`, the largest over its states of the exit value defined next.

**The exit value** of a state `s` of `x`. For a nonempty set `T` of row actions, let `L(T)` be the
column actions that leave `x` against some action of `T`. The exit value is the least, over `T`,
of the value of the stage game against `u` restricted to the rows `T` and the columns `L(T)`, read
as `0` when `L(T)` is empty. A row strategy on `T` attaining it holds every column that can leave
to at most that value, and no other column leaves at all.

**Which sets.** Deflation is applied to the *closed components* of the states that are neither
target nor sure-avoid: the sets that are strongly connected through joint actions keeping the play
inside them. Every end component among those states lies in one. After a component is capped, the
states attaining its best exit are removed and the closed components of the remainder are
deflated in turn.

**Why the result passes the check.** Let `u` be pre-fixed and `w` be `u` capped at `c` on `x`,
where at every state of `x` some row strategy `σ` and set `L` of columns are such that each column
outside `L` keeps the play inside `x` against `σ`, and each column in `L` pays at most `c` against
`σ` under `u`. Then `w` is pre-fixed. Where `w = u`, the operator at `w` is below the operator at
`u`, which is below `u`. At a capped state, `σ` holds a column outside `L` to at most `c` because
all its successors are in `x`, where `w ≤ c`, and a column in `L` to at most `c` because `w ≤ u`.
A step of the operator also takes pre-fixed vectors to pre-fixed vectors, and the starting vector
is pre-fixed (`Csg/ReachZero.lean`). For the real-valued game the argument is
`Csg/ReachCap.lean`'s `reachOp_cap_le`. This search is not proved to meet that theorem's
hypotheses, and the check does not depend on it.

**Relation to the literature.** Capping an end component by its best exit is deflation as in
Kelmendi, Krämer, Křetínský and Weininger for turn-based games, and in Grobelna, Křetínský and
Weininger for concurrent ones (arXiv:2505.21087). The exit value above is defined from what the
pre-fixed-point check needs. For a turn-based game it is the largest value of a leaving action at
a state of the maximiser, and `0` at a state where the minimiser can stay.

**Rounding.** With `den ≠ 0`, every value the search writes is rounded up to a multiple of
`1 / den`: the result of a step of the operator, and each cap. The vectors then stay on that grid.
Rounding up keeps a pre-fixed vector pre-fixed in both places. A vector `w` with `F u ≤ w ≤ u`,
for the operator `F`, satisfies `F w ≤ F u ≤ w` (`CSG.reachOp_le_of_between`). And the argument
for capping holds for any cap at or above the best exit value. With `den = 0` nothing is rounded
and the values are exact; a mixed stage game multiplies denominators, so they can grow very fast,
and on the model of `Comp/HideTwiceQ.lean` they pass thirty digits in four rounds.

**Cost.** The exit value enumerates the subsets of a state's enabled row actions and solves one
restricted game for each, by the support enumeration of `Comp/Search.lean`.
-/

namespace Comp

/-- The value of the matrix `A` restricted to the rows `Is` and the columns `Js`, or `none` when
    either list is empty or the search finds no certificate. For `#eval`. -/
def subValue {I J : Type*} (A : I → J → ℚ) : List I → List J → Option ℚ
  | i :: it, j :: jt =>
    let G : MatrixGameQ (Fin (it.length + 1)) (Fin (jt.length + 1)) :=
      { A := fun a b => A ((i :: it).getD a.val i) ((j :: jt).getD b.val j) }
    (G.findValueCert (List.finRange (it.length + 1)) (List.finRange (jt.length + 1))).map
      fun c => c.1
  | _, _ => none

namespace ModelData

/-! ## Closed components -/

/-- The row actions enabled at `s`, as a list. -/
def rowList (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) : List (Fin d.nAct1) :=
  (List.finRange d.nAct1).filter fun a => decide (a ∈ d.enabled1 hs s)

/-- The column actions enabled at `s`, as a list. -/
def colList (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) : List (Fin d.nAct2) :=
  (List.finRange d.nAct2).filter fun a => decide (a ∈ d.enabled2 hs s)

/-- The successors of `s` under the enabled joint actions that keep the play inside `x`. -/
def staySucc (d : ModelData) (hs : d.Shape) (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    Finset (Fin d.nStates) :=
  (d.rowList hs s).foldl (fun acc a1 =>
    (d.colList hs s).foldl (fun acc' a2 =>
      if d.supportOf hs s a1 a2 ⊆ x then acc' ∪ d.supportOf hs s a1 a2 else acc') acc)
    (∅ : Finset (Fin d.nStates))

/-- The states reachable from the set `r` in at most `k` further steps of `staySucc`. -/
def reachIn (d : ModelData) (hs : d.Shape) (x : Finset (Fin d.nStates)) :
    ℕ → Finset (Fin d.nStates) → Finset (Fin d.nStates)
  | 0, r => r
  | k + 1, r => reachIn d hs x k (r ∪ r.biUnion (d.staySucc hs x))

/-- The states on a common cycle with `s` through joint actions that keep the play inside `x`.
    Empty when `s` is on no such cycle. -/
def cycleOf (d : ModelData) (hs : d.Shape) (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    Finset (Fin d.nStates) :=
  (d.reachIn hs x d.nStates (d.staySucc hs x s)).filter fun t =>
    s ∈ d.reachIn hs x d.nStates (d.staySucc hs x t)

/-- The distinct nonempty sets `cycleOf hs x s`, for `s` in `x`. -/
def cycleClasses (d : ModelData) (hs : d.Shape) (x : Finset (Fin d.nStates)) :
    List (Finset (Fin d.nStates)) :=
  ((List.finRange d.nStates).filter fun s => decide (s ∈ x)).foldl (fun acc s =>
    let c := d.cycleOf hs x s
    if c = ∅ ∨ c ∈ acc then acc else acc ++ [c]) []

/-- **The closed components inside `x`**: the sets strongly connected through joint actions that
    keep the play inside them, found by splitting `x` into cycle classes until a class is the
    whole of its set. The first argument is fuel, and one more than the number of states is
    enough. -/
def closedComps (d : ModelData) (hs : d.Shape) :
    ℕ → Finset (Fin d.nStates) → List (Finset (Fin d.nStates))
  | 0, _ => []
  | k + 1, x =>
    (d.cycleClasses hs x).flatMap fun c => if c = x then [x] else closedComps d hs k c

/-! ## Exit values and deflation -/

/-- **The exit value of `s` from `x` against `v`**: the least, over the nonempty sets `T` of
    enabled row actions, of the value of the stage game restricted to `T` and to the columns that
    leave `x` against some action of `T`. -/
def exitValue (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (x : Finset (Fin d.nStates)) (v : Fin d.nStates → ℚ) (s : Fin d.nStates) : ℚ :=
  let cols := d.colList hs s
  let cands : List ℚ := (d.rowList hs s).sublists.filterMap fun T =>
    if T.isEmpty then none
    else
      let L := cols.filter fun a2 => T.any fun a1 => !decide (d.supportOf hs s a1 a2 ⊆ x)
      if L.isEmpty then some (0 : ℚ) else subValue (d.toCsgQ.reachGameQ s v).A T L
  cands.foldl min 1

/-- **Deflate `x`.** Cap the vector on `x` at the best exit value, rounded up by `ceilTo den`, then
    deflate the closed components of `x` without the states attaining it. The vector is a list,
    one entry per state. The first argument after `den` is fuel. -/
def deflate (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (den : ℕ) :
    ℕ → Finset (Fin d.nStates) → List ℚ → List ℚ
  | 0, _, l => l
  | k + 1, x, l =>
    let v : Fin d.nStates → ℚ := fun s => l.getD s.val 0
    let es : List (Fin d.nStates × ℚ) :=
      ((List.finRange d.nStates).filter fun s => decide (s ∈ x)).map fun s =>
        (s, d.exitValue hs x v s)
    let m : ℚ := (es.map fun p => p.2).foldl max 0
    let u : ℚ := ceilTo den m
    let l' : List ℚ := (List.finRange d.nStates).map fun s =>
      if s ∈ x then min (v s) u else v s
    let best : List (Fin d.nStates) := (es.filter fun p => p.2 == m).map fun p => p.1
    let rest : Finset (Fin d.nStates) := x.filter fun s => s ∉ best
    (d.closedComps hs (d.nStates + 1) rest).foldl (fun acc c => deflate d hs den k c acc) l'

/-! ## The search -/

/-- **`n` rounds of a step of the operator followed by deflation**, from the vector that is `0`
    on the sure-avoid region of the target and `1` elsewhere, with every value rounded up to a
    multiple of `1 / den` (`den = 0` for none). The result is printed as `reachUpperRun` prints a
    candidate: the vector, one step of the operator from it, and the row strategies of that step,
    ready for `ModelData.answers_reach_of_bounds`. For `#eval`. -/
def reachDeflateRun (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (target : Finset (Fin d.nStates)) (den n : ℕ) : ReachRun :=
  let z := d.gRegionTr hs (Finset.univ \ target)
  let comps := d.closedComps hs (d.nStates + 1) ((Finset.univ \ target) \ z)
  let start : List ℚ := (List.finRange d.nStates).map fun s => if s ∈ z then 0 else 1
  let l : List ℚ := (List.range n).foldl (fun acc _ =>
    let b : List ℚ := (d.reachStepRun target (fun s => acc.getD s.val 0)).map fun y => y.1
    let stepped : List ℚ := (List.finRange d.nStates).map fun s =>
      min (acc.getD s.val 0) (ceilTo den (b.getD s.val 0))
    comps.foldl (fun acc' c => d.deflate hs den (d.nStates + 1) c acc') stepped) start
  d.reachUpperRun target (fun s => l.getD s.val 0)

end ModelData

end Comp
