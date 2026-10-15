/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.MatrixGameQ

/-!
# Finding a value certificate: support enumeration with exact rational elimination

**Status: confirmed by a clean `lake build`.**

The search half of `Comp/`. Everything here is ordinary computation -- no theorem in this file says
that any of it is correct, and none needs to. `Comp/MatrixGameQ.lean`'s `ValueCert` is decidable, so
whatever comes out is checked before it is believed; a bug here produces a rejected candidate, never
a false theorem. That is what makes it reasonable to write a solver in Lean without verifying it.

**Why support enumeration rather than simplex.** By the Shapley-Snow characterisation an optimal
pair can be found on supports of equal size, where the equalising conditions become *equalities*: a
square rational linear system per support pair, solvable exactly by elimination. This is where the
complementarity view from `MatrixGameQ.lean` earns its keep -- it is what turns the problem into
finitely many exactly-solvable systems rather than an optimisation. The cost is that the number of
support pairs is exponential in the action counts, which is fine at the sizes this project's worked
instances use (2x2 and 3x3) and would not be at scale; a simplex pass could later replace
`findValueCert` behind the same signature, since nothing outside this file depends on how the
witness was found.

**What is solved.** For supports `Rs ⊆ I` and `Cs ⊆ J` of equal size `k`, the unknowns are the `k`
weights on `Rs` together with the value `t`, and the equations are that every column in `Cs` pays
exactly `t` against `p`, plus `∑ p = 1`. That is `k + 1` equations in `k + 1` unknowns. The mirror
system gives `q`. Both systems contain `t`; the two solutions are not forced to agree here, and
nothing tries to make them -- if they disagree the resulting candidate simply fails `ValueCert`.

**Degeneracy is not handled, deliberately.** A singular system returns `none` and the enumeration
moves on, and supports whose solution has negative weights are rejected by `ValueCert`'s
`IsStratQ` clause. Neither case needs special treatment, because the check is downstream of the
search.

**Two things this file had to learn the hard way**, recorded as standing rules. First, there is no
computable enumeration of a `Fintype`: `Finset.powerset` is fine, but `Finset.toList` is
`noncomputable` because it picks a representative out of a `Multiset` quotient, so any `def` that
tries to list a type's elements fails to compile. Hence the action lists below are parameters and
`sublistsOf` is rolled by hand. Second, `List.find?_some` needs its predicate supplied by name
(`(p := G.certOK)`, with `certOK` a real definition rather than a lambda), or higher-order
unification cannot tell whether `decide (G.ValueCert t p q)` is the predicate itself or the
predicate applied to a triple.

Everything else is deliberately built from `List.foldr`, `List.filterMap`, `List.zipWith` and
explicit `zip`-then-`find?` lookups rather than from library functions whose names have moved
between toolchains.
-/

namespace Comp

open Csg

namespace MatrixGameQ

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

/-! ## Exact rational elimination -/

/-- One elimination step on an augmented matrix: pick a row with a nonzero leading entry, scale it
    to a leading `1`, clear that column from every other row, and drop the column. Returns the
    normalised pivot row together with the reduced system, or `none` when the whole leading column
    is zero.

    Rows are removed by index (`List.eraseIdx`) rather than by value, so a system with two identical
    rows loses exactly one of them. -/
private def elimStep (rows : List (List ℚ)) : Option (List ℚ × List (List ℚ)) :=
  match rows.findIdx? (fun r => r.headD 0 != 0) with
  | none => none
  | some k =>
    match rows[k]? with
    | none => none
    | some piv =>
      let a := piv.headD 0
      let pivN := piv.map (fun x => x / a)
      let rest := (rows.eraseIdx k).map fun r =>
        let c := r.headD 0
        (List.zipWith (fun x y => x - c * y) r pivN).tail
      some (pivN, rest)

/-- Solve a square rational system by Gaussian elimination, exactly. `n` is the number of unknowns
    and each row of `rows` is `n + 1` long (coefficients then right-hand side). Returns `none` if
    the system is singular or the shape is wrong.

    The recursion is structural in `n`, so there is no termination obligation and no `partial`. The
    result is deliberately unverified; `ValueCert` is what decides whether to believe it. -/
def solveQ : Nat → List (List ℚ) → Option (List ℚ)
  | 0, _ => some []
  | n + 1, rows => do
    let (piv, rest) ← elimStep rows
    let xs ← solveQ n rest
    -- `piv` is `[1, c₁, …, cₙ, b]`: back-substitute `x = b - ∑ cᵢ xᵢ`.
    let coeffs := piv.tail.dropLast
    let b := (piv.getLast?).getD 0
    some ((b - (List.zipWith (fun c x => c * x) coeffs xs).sum) :: xs)

/-! ## The two systems a support pair induces -/

/-- The row player's system for supports `Rs`/`Cs`: unknowns are the weights on `Rs` followed by the
    value `t`. One equation per column of `Cs` saying that column pays exactly `t`
    (`∑ᵢ pᵢ A i j - t = 0`), then `∑ᵢ pᵢ = 1`. -/
def rowSystem (G : MatrixGameQ I J) (Rs : List I) (Cs : List J) : List (List ℚ) :=
  (Cs.map fun j => (Rs.map fun i => G.A i j) ++ [-1, 0])
    ++ [(Rs.map fun _ => (1 : ℚ)) ++ [0, 1]]

/-- The column player's mirror system: unknowns are the weights on `Cs` followed by `t`, with one
    equation per row of `Rs` (`∑ⱼ A i j qⱼ - t = 0`) and then `∑ⱼ qⱼ = 1`. -/
def colSystem (G : MatrixGameQ I J) (Rs : List I) (Cs : List J) : List (List ℚ) :=
  (Rs.map fun i => (Cs.map fun j => G.A i j) ++ [-1, 0])
    ++ [(Cs.map fun _ => (1 : ℚ)) ++ [0, 1]]

/-- Read a solved weight back out by position: `xs` lists the weights in the order `support` lists
    the actions, and everything off the support is zero. Written as an explicit `zip`-then-`find?`
    rather than through an index-of function, whose name has moved between toolchains. -/
private def weightOf {α : Type*} [DecidableEq α] (support : List α) (xs : List ℚ) (a : α) : ℚ :=
  match (support.zip xs).find? (fun pr => pr.1 == a) with
  | some pr => pr.2
  | none => 0

/-- The candidate a single support pair yields, if both systems are solvable: the value `t` taken
    from the row system, and the two strategies extended by zero off their supports. Nothing is
    checked here. -/
def candidateFor (G : MatrixGameQ I J) (Rs : List I) (Cs : List J) :
    Option (ℚ × (I → ℚ) × (J → ℚ)) :=
  if Rs.length != Cs.length then none
  else if Rs.length == 0 then none
  else
    match solveQ (Rs.length + 1) (G.rowSystem Rs Cs),
          solveQ (Cs.length + 1) (G.colSystem Rs Cs) with
    | some sp, some sq =>
      some ((sp.getLast?).getD 0, weightOf Rs sp.dropLast, weightOf Cs sq.dropLast)
    | _, _ => none

/-! ## Enumeration -/

/-- Every sublist of a list. Rolled by hand rather than taken from the library because the obvious
    route, `Finset.powerset` followed by `Finset.toList`, does not compile: `Finset.toList` is
    `noncomputable`, picking a representative out of a `Multiset` quotient. Structural, so no
    termination obligation. -/
private def sublistsOf {α : Type*} : List α → List (List α)
  | [] => [[]]
  | a :: as => let r := sublistsOf as; r ++ r.map (fun t => a :: t)

/-- Every equal-sized, nonempty pair of supports drawn from the supplied action lists.

    The enumerations are *parameters* rather than derived from `Fintype`, for the reason in the
    module docstring: there is no computable way to get a `List I` from `Fintype I` alone. Asking
    the caller is honest about what the search needs, and at a concrete instance the lists are
    written out literally. -/
def supportPairs (Is : List I) (Js : List J) : List (List I × List J) :=
  let css := sublistsOf Js
  (sublistsOf Is).foldr (fun Rs acc =>
    (css.filterMap fun Cs =>
      if Rs.length == Cs.length && Rs.length != 0 then some (Rs, Cs) else none) ++ acc) []

/-- The test the search filters by, as a named definition rather than an inline lambda. This is not
    cosmetic: with the predicate a single head symbol, `List.find?_some`'s unification is
    first-order, whereas against a lambda Lean cannot tell whether `decide (G.ValueCert t p q)` is
    the predicate or the predicate applied to a triple. -/
def certOK (G : MatrixGameQ I J) (c : ℚ × (I → ℚ) × (J → ℚ)) : Bool :=
  decide (G.ValueCert c.1 c.2.1 c.2.2)

/-- **The search.** Walk the support pairs, solve each one's two systems, and return the first
    candidate that passes `ValueCert` -- which is where every soundness question is settled, since
    the predicate is decidable and is checked here rather than assumed. -/
def findValueCert (G : MatrixGameQ I J) (Is : List I) (Js : List J) :
    Option (ℚ × (I → ℚ) × (J → ℚ)) :=
  ((supportPairs Is Js).filterMap fun pr => G.candidateFor pr.1 pr.2).find? G.certOK

/-- Whatever the search returns really is a value certificate. This is the only place the search and
    the proofs meet, and it says nothing about the search being *complete* -- only that it does not
    lie. -/
theorem valueCert_of_find {G : MatrixGameQ I J} {Is : List I} {Js : List J}
    {t : ℚ} {p : I → ℚ} {q : J → ℚ}
    (h : G.findValueCert Is Js = some (t, p, q)) : G.ValueCert t p q := by
  unfold findValueCert at h
  have hb := List.find?_some (p := G.certOK) h
  simp only [certOK] at hb
  exact of_decide_eq_true hb

/-- **The payoff.** A successful search pins the real-valued game value exactly. Composition of
    `valueCert_of_find` with `MatrixGameQ.value_eq_of_valueCert`; no new mathematics, and in
    particular no appeal to the solver being right. -/
theorem value_eq_of_find {G : MatrixGameQ I J} {Is : List I} {Js : List J}
    {t : ℚ} {p : I → ℚ} {q : J → ℚ}
    (h : G.findValueCert Is Js = some (t, p, q)) : G.toMatrixGame.value = ((t : ℚ) : ℝ) :=
  value_eq_of_valueCert (valueCert_of_find h)

/-! ## Exercising the solver: `#eval`, not `decide`

The two are not interchangeable here, and the difference shapes how the search is used. `#eval`
runs compiled code; `decide` asks the *kernel* to reduce a `Decidable` instance, and kernel
reduction gets stuck on `solveQ` -- it will not unfold the recursion and the `Option` plumbing far
enough to yield a literal. So

    #eval solveQ 2 [[1, 1, 3], [1, -1, 1]]   -- some [2, 1]
    #eval solveQ 2 [[1, 1, 2], [2, 2, 4]]    -- none

answer immediately, while the same two statements written as `example ... := by decide` do not
elaborate at all.

At the game level, `findValueCert` returns the following on the standard small instances, which is
what to expect when wiring up a new one:

    matching pennies  `!![0, 1; 1, 0]`-style `[[1,-1],[-1,1]]`  ->  `t = 0`, both uniform
    rock-paper-scissors `[[0,-1,1],[1,0,-1],[-1,1,0]]`          ->  `t = 0`, both uniform
    a pure saddle `[[1,2],[3,4]]`                               ->  `t = 2`, both pure
    a mixed 2x2 `[[2,-1],[-1,1]]`                               ->  `t = 1/5`, both `(2/5, 3/5)`
    a constant game `[[3,3],[3,3]]`                             ->  `t = 3`, both pure

The last two are the cases worth noting: the mixed one is the `(ad - bc)/(a + d - b - c)` formula,
and the constant game is degenerate -- every support pair solves it, and the first one enumerated
wins, which is harmless because `ValueCert` does not care which optimal pair it is handed.

The constraint is a feature rather than a nuisance. `#eval` is for *finding* a witness; `decide` is
for *checking* one, and checking only has to chew through `ValueCert` at explicit rational literals
-- finitely many comparisons, no recursion -- which it does happily. Verifying a whole computed run
inside the kernel would need `native_decide` and its trust axiom; taking the witness out of `#eval`
and checking it with `decide` needs neither. -/

end MatrixGameQ

end Comp
