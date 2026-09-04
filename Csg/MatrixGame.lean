/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Finite two-player zero-sum matrix games

**Status: confirmed by a clean `lake build`, including Update 2's four-satellite-file consolidation
below -- no fix round needed.** This is the first artifact for Goal 02
(concurrent stochastic games), and plays the same role for the CSG line of work that
`RecyclingRobot.lean` played for the discounted-MDP line: a small, self-contained, hands-on
exercise that checks a genuinely nontrivial piece of Mathlib before any downstream theory gets
built on top of it. Here the load-bearing dependency is `Mathlib.Topology.Sion`
(`Sion.exists_isSaddlePointOn`), a 2025 formalisation of Sion's minimax theorem, which that file's
own docstring notes specialises to von Neumann's minimax theorem in the finite bilinear case —
exactly the finite zero-sum matrix game below.

Why this matters for the project as a whole (see `PHASE0-NOTES.md`, "Heavy debrief" section): the
per-state value computation of a *concurrent* stochastic game, at every stage of a
`Backward_Induction.thy`-style bounded computation, is not a plain `Finset.sup'` over actions the
way it is for MDPs (`DiscountedMDP.bellman` in `Basic.lean`) — it's the value of a one-shot finite
zero-sum matrix game between the two players, since both choose actions simultaneously at a
state. Existence of that value (as a mixed-strategy saddle point) was, before this file, the
single biggest unconfirmed dependency in the CSG roadmap. `exists_optimal_strategies` below closes
it: it exists in Mathlib, and it is usable directly, without reproving von Neumann from scratch the
way the rest of this project avoids reproving Banach from scratch for the MDP case.

**Update.** `value` and its supporting API
(`optimalRow`, `optimalCol`, `value_row_optimal`, `value_col_optimal`, `value_unique`) used to live
in `Basic.lean`, added there only because this file "deliberately stopped at bare existence" when
first written and the packaging step came later. On reflection (prompted by a design discussion
about `MatrixGame`/`MatrixGameCongr`/`MatrixGameLP` being split across files for no reason beyond
avoiding reopening a confirmed one) that placement was never right: none of that content is about
`CSG`, all of it is about `MatrixGame` alone, and it belongs beside `exists_optimal_strategies`
itself, not smuggled into the file that happens to define `CSG` on top of it. Moved here verbatim
(statements and proofs unchanged from `Basic.lean`'s copy) as the first step of a staged
consolidation. `Basic.lean` now only defines `CSG`/`stageGame`/`stageValue`, importing `value` from
here like any other consumer.

**Update 2 (confirmed by a clean `lake build`).** Step two of that same consolidation:
`MatrixGameMonotone.lean`, `MatrixGameCongr.lean`, `MatrixGameCongrCol.lean`, and
`MatrixGameLP.lean` -- each a pure `MatrixGame` fact with no `CSG` content (checked before Update 1
above, re-checked now: still true of all four) -- are folded in below as four further sections,
each keeping its own original module docstring's design rationale and fix-round history verbatim
(as a section note rather than a top-of-file docstring), rather than losing that record. The four
satellite files are deleted; every downstream file that imported one of them now gets the same
content transitively through `Csg.Basic`/`Csg.Coalition`/`Csg.SkirmishFeint` (whichever it already
imported) importing `Csg.MatrixGame` in turn, so most needed no new import at all -- only
`BoundedReachability.lean`, `CsgMonotone.lean`, and `SkirmishFeint.lean`, which imported a satellite
file *directly* rather than through `Csg.Basic`, needed their import line repointed to `Csg.Basic`.
No statement or proof below changed from its original file's copy; only `variable` declarations
were deduplicated against the ones already active from Update 1 above (each satellite's own
`{I J} [Fintype I]...`/`(G : MatrixGame I J)` was identical to what this file already declares, so
only genuinely new variables -- `MatrixGameCongr`'s `I'`, `MatrixGameCongrCol`'s `J'` -- needed
restating).

Convention: the row player picks `i : I` and *minimizes* the payoff `A i j`; the column player
picks `j : J` and *maximizes* it. This matches `Sion.exists_isSaddlePointOn`'s own `X`/`Y`
convention exactly (`X` is the minimizing side, `Y` the maximizing side), so no sign flip is
needed anywhere below — a deliberate choice, not the more common "row player maximizes" textbook
convention.
-/

namespace Csg

/-- A finite two-player zero-sum matrix game: row player picks `i : I` (minimizing), column
    player picks `j : J` (maximizing), `A i j` is the payoff from row to column. `DecidableEq` on
    both index types is needed downstream only to exhibit a nonempty mixed strategy
    (`single_mem_stdSimplex`) -- a mild hypothesis, true of every concrete finite action set this
    project actually uses (`Fin n`, hand-rolled enums with `deriving DecidableEq`, as in
    `RecyclingRobot.lean`). -/
structure MatrixGame (I J : Type*) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] where
  /-- The payoff matrix: `A i j` is paid by the row player to the column player. -/
  A : I → J → ℝ

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

namespace MatrixGame

variable (G : MatrixGame I J)

/-- Expected payoff of a pair of mixed strategies `x : I → ℝ`, `y : J → ℝ` -- the bilinear
    extension of `A` to the mixed extension of the game. No claim that `x`/`y` are themselves
    mixed strategies (i.e. lie in `stdSimplex ℝ I`/`stdSimplex ℝ J`) is baked in here; that's
    imposed where needed by the theorems below, matching how `DiscountedMDP.expect` in
    `Basic.lean` is stated for a bare `v : S → ℝ` with no side conditions. -/
noncomputable def payoff (x : I → ℝ) (y : J → ℝ) : ℝ := ∑ i, ∑ j, x i * G.A i j * y j

/-- `payoff`, regrouped so the row player's mixed strategy is pulled out as an outer sum of
    single factors -- the shape linearity-in-`x` and continuity-in-`x` arguments below actually
    want. -/
theorem payoff_eq_sum_mul (x : I → ℝ) (y : J → ℝ) :
    G.payoff x y = ∑ i, x i * ∑ j, G.A i j * y j := by
  unfold payoff
  congr 1
  funext i
  rw [Finset.mul_sum]
  congr 1
  funext j
  ring

/-- `payoff`, regrouped the other way: the column player's mixed strategy pulled out as an outer
    sum -- the shape linearity-in-`y` and continuity-in-`y` want. -/
theorem payoff_eq_sum_mul' (x : I → ℝ) (y : J → ℝ) :
    G.payoff x y = ∑ j, (∑ i, x i * G.A i j) * y j := by
  unfold payoff
  rw [Finset.sum_comm]
  congr 1
  funext j
  rw [Finset.sum_mul]

/-- `payoff` is linear (not just convex/concave) in its row argument, for fixed column strategy --
    the bilinear extension of a matrix is exactly linear in each argument separately. This is the
    one fact `convexOn_payoff_left` and `continuous_payoff_left` both reduce to. -/
theorem payoff_smul_add_smul_left (p₁ p₂ : I → ℝ) (q : J → ℝ) (a b : ℝ) :
    G.payoff (a • p₁ + b • p₂) q = a * G.payoff p₁ q + b * G.payoff p₂ q := by
  simp only [payoff_eq_sum_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  funext i
  ring

/-- `payoff` is linear in its column argument, for fixed row strategy. Symmetric counterpart of
    `payoff_smul_add_smul_left`. -/
theorem payoff_smul_add_smul_right (p : I → ℝ) (q₁ q₂ : J → ℝ) (a b : ℝ) :
    G.payoff p (a • q₁ + b • q₂) = a * G.payoff p q₁ + b * G.payoff p q₂ := by
  simp only [payoff_eq_sum_mul', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  funext j
  ring

/-- `payoff` is continuous in the row player's strategy, for a fixed column strategy: a finite sum
    of `x ↦ x i * (constant)` terms, each continuous since coordinate projection is. -/
theorem continuous_payoff_left (y : J → ℝ) :
    Continuous (fun x : I → ℝ => G.payoff x y) := by
  simp only [payoff_eq_sum_mul]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

/-- `payoff` is continuous in the column player's strategy, for a fixed row strategy. Symmetric
    counterpart of `continuous_payoff_left`. -/
theorem continuous_payoff_right (x : I → ℝ) :
    Continuous (fun y : J → ℝ => G.payoff x y) := by
  simp only [payoff_eq_sum_mul']
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

/-- `payoff`, as a function of the row player's mixed strategy on the simplex, is convex --
    trivially, since (`payoff_smul_add_smul_left`) it is exactly linear, and linear functions are
    convex with equality rather than strict inequality. This is the hypothesis
    `Sion.exists_isSaddlePointOn` calls `hfy'`. -/
theorem convexOn_payoff_left (y : J → ℝ) :
    ConvexOn ℝ (stdSimplex ℝ I) (fun x => G.payoff x y) := by
  refine ⟨convex_stdSimplex ℝ I, ?_⟩
  intro p _ p' _ a b _ _ _
  simp only [smul_eq_mul]
  exact (G.payoff_smul_add_smul_left p p' y a b).le

/-- `payoff`, as a function of the column player's mixed strategy on the simplex, is concave --
    symmetric counterpart of `convexOn_payoff_left`, using `payoff_smul_add_smul_right`. This is
    the hypothesis `Sion.exists_isSaddlePointOn` calls `hfx'`. -/
theorem concaveOn_payoff_right (x : I → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ J) (fun y => G.payoff x y) := by
  refine ⟨convex_stdSimplex ℝ J, ?_⟩
  intro q _ q' _ a b _ _ _
  simp only [smul_eq_mul]
  exact (G.payoff_smul_add_smul_right x q q' a b).ge

/-- **The payoff.** The matrix game has a pair of optimal mixed strategies: a row strategy `p`
    that minimizes the payoff against the worst-case response, and a column strategy `q` that
    maximizes it against the worst-case response, with neither player able to improve by
    unilaterally deviating while the other holds still. This is von Neumann's minimax theorem for
    finite two-player zero-sum games, obtained here as a direct instance of Mathlib's
    `Sion.exists_isSaddlePointOn` -- every hypothesis it asks for (nonemptiness, convexity,
    compactness of the two simplices; continuity and quasiconvexity/quasiconcavity of the
    bilinear payoff in each argument) is supplied by the lemmas above, with no extra work beyond
    bilinearity of `payoff`. The one thing this proof leans on that hasn't been exercised
    elsewhere in this project yet: that Mathlib's ambient
    `IsTopologicalAddGroup`/`ContinuousSMul ℝ`-style instances for the Pi type `I → ℝ` (a
    finite-dimensional real vector space) resolve automatically -- expected to be routine, but
    genuinely unconfirmed until `lake build` says so. -/
theorem exists_optimal_strategies :
    ∃ p ∈ stdSimplex ℝ I, ∃ q ∈ stdSimplex ℝ J,
      (∀ p' ∈ stdSimplex ℝ I, G.payoff p q ≤ G.payoff p' q) ∧
      (∀ q' ∈ stdSimplex ℝ J, G.payoff p q' ≤ G.payoff p q) := by
  obtain ⟨p, hp, q, hq, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn
      (X := stdSimplex ℝ I) (Y := stdSimplex ℝ J) (f := G.payoff)
      (ne_X := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary I)⟩)
      (cX := convex_stdSimplex ℝ I) (kX := isCompact_stdSimplex ℝ I)
      (hfy := fun y _ => (G.continuous_payoff_left y).continuousOn.lowerSemicontinuousOn)
      (hfy' := fun y _ => G.convexOn_payoff_left y |>.quasiconvexOn)
      (cY := convex_stdSimplex ℝ J)
      (ne_Y := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary J)⟩)
      (kY := isCompact_stdSimplex ℝ J)
      (hfx := fun x _ => (G.continuous_payoff_right x).continuousOn.upperSemicontinuousOn)
      (hfx' := fun x _ => G.concaveOn_payoff_right x |>.quasiconcaveOn)
  exact ⟨p, hp, q, hq, fun p' hp' => hsaddle p' hp' q hq, fun q' hq' => hsaddle p hp q' hq'⟩

/-- A row (minimizing player's) mixed strategy witnessing `exists_optimal_strategies` -- one
    specific choice among possibly several, extracted via `Classical.choose` since Mathlib's
    saddle-point existence doesn't come with a canonical one. -/
noncomputable def optimalRow : I → ℝ := G.exists_optimal_strategies.choose

/-- A column (maximizing player's) mixed strategy witnessing `exists_optimal_strategies`,
    optimal against `optimalRow`. -/
noncomputable def optimalCol : J → ℝ := G.exists_optimal_strategies.choose_spec.2.choose

/-- **The game's value.** The payoff at the optimal strategy pair -- what neither player can do
    better than, given the other holds still (`value_row_optimal`/`value_col_optimal` below). -/
noncomputable def value : ℝ := G.payoff G.optimalRow G.optimalCol

theorem optimalRow_mem : G.optimalRow ∈ stdSimplex ℝ I := by
  unfold optimalRow
  exact G.exists_optimal_strategies.choose_spec.1

theorem optimalCol_mem : G.optimalCol ∈ stdSimplex ℝ J := by
  unfold optimalCol
  exact G.exists_optimal_strategies.choose_spec.2.choose_spec.1

/-- The row player cannot lower the payoff below `value` by unilaterally deviating from
    `optimalRow`, while the column player holds `optimalCol` fixed. -/
theorem value_row_optimal : ∀ p' ∈ stdSimplex ℝ I, G.value ≤ G.payoff p' G.optimalCol := by
  unfold value
  exact G.exists_optimal_strategies.choose_spec.2.choose_spec.2.1

/-- The column player cannot raise the payoff above `value` by unilaterally deviating from
    `optimalCol`, while the row player holds `optimalRow` fixed. -/
theorem value_col_optimal : ∀ q' ∈ stdSimplex ℝ J, G.payoff G.optimalRow q' ≤ G.value := by
  unfold value
  exact G.exists_optimal_strategies.choose_spec.2.choose_spec.2.2

/-- The game's value doesn't depend on which saddle point exhibits it: *any* mixed-strategy pair
    `p, q` satisfying the two no-unilateral-improvement conditions relative to each other has
    `payoff p q = value`, not just the particular pair `value` was built from via
    `Classical.choose`. Standard minimax fact (the *value* of a zero-sum game is unique even when
    optimal strategies are not), proved directly from `value_row_optimal`/`value_col_optimal` by
    chaining both pairs' optimality conditions against each other.

    **Relocated here from `Basic.lean`**, which had itself relocated it from `MatchingPennies.lean`
    once `MatrixGameMonotone.lean`'s `value_add_const` needed it too: a general fact about `value`
    that doesn't depend on anything `CSG`- or worked-example-specific belongs beside `value` and
    `exists_optimal_strategies` themselves, in the file that owns `MatrixGame`, not in a file about
    a different structure built on top of it. Pure relocation, second hop -- the statement and
    proof are unchanged from `Basic.lean`'s copy, which was itself unchanged from
    `MatchingPennies.lean`'s original. -/
theorem value_unique {p : I → ℝ} {q : J → ℝ} (hp : p ∈ stdSimplex ℝ I) (hq : q ∈ stdSimplex ℝ J)
    (hrow : ∀ p' ∈ stdSimplex ℝ I, G.payoff p q ≤ G.payoff p' q)
    (hcol : ∀ q' ∈ stdSimplex ℝ J, G.payoff p q' ≤ G.payoff p q) :
    G.payoff p q = G.value := by
  apply le_antisymm
  · calc G.payoff p q ≤ G.payoff G.optimalRow q := hrow G.optimalRow G.optimalRow_mem
      _ ≤ G.value := G.value_col_optimal q hq
  · calc G.value ≤ G.payoff p G.optimalCol := G.value_row_optimal p hp
      _ ≤ G.payoff p q := hcol G.optimalCol G.optimalCol_mem

/-! ## Monotonicity and boundedness of `value`

Folded in from `MatrixGameMonotone.lean` (Update 2 above); original module docstring, verbatim:

**Original status: done, confirmed by a clean `lake build`, including the later addition
(`payoff_add_const` through `abs_value_sub_le`, Lipschitz continuity of `value` in the payoff
matrix) -- see `PHASE0-NOTES.md`'s "reachability iterate" section for the plan this feeds, and its
one fix round (a missing-dependency error, `value_unique` relocated to `Basic.lean`).** First
building block for the infinite-horizon half of Phase 3
(`until`/reachability), scoped in the "Heavy debrief" section of `PHASE0-NOTES.md` but not built
until now. Builds on the now-confirmed `Csg/Basic.lean`, adding lemmas to the existing `MatrixGame`
namespace rather than reopening anything else -- the same pattern `MatchingPennies.lean` used for
`value_unique`.

Why this file, and why now: reachability/until values for CSGs, unlike the bounded objectives
`BackwardInduction.lean` already covers, aren't computed by a fixed number of recursion steps --
they're the least fixed point of a per-state Bellman-style operator (Knaster-Tarski, not plain
structural recursion), per the reachcert architecture scoped in the debrief. Existence of that
fixed point needs the operator to be *monotone* on a *complete lattice*, neither of which
`BackwardInduction.lean` needed (`bwInd` never compares two different reward functions against
each other). This section supplies the two facts about `MatrixGame.value` that argument is built on:

1. `value_mono`: if one payoff matrix dominates another entrywise, its value is at least as large.
   Needed so the per-state stage-game step (`CSG.stageValue`, `Basic.lean`) is monotone in the
   continuation value -- exactly the hypothesis Knaster-Tarski asks for.
2. `value_le_of_forall_le`/`le_value_of_forall_le`: the value is sandwiched between any two
   constants bounding all matrix entries. Needed to show the reachability operator maps `[0, 1]`
   into itself, so the fixed point can be found inside `Set.Icc (0:ℝ) 1` rather than needing all of
   `ℝ` to be a complete lattice (it isn't -- `ℝ` has no top or bottom element).

Confirmed directly against the cached Mathlib source before writing this file (not guessed):
`Set.Icc a b` in a `ConditionallyCompleteLattice` (`ℝ` qualifies) gets a `CompleteLattice` instance
for free (`Set.Icc.completeLattice`, `Mathlib/Order/CompleteLatticeIntervals.lean`), and `Pi` types
of complete lattices are complete lattices (`Pi.instCompleteLattice`,
`Mathlib/Order/CompleteLattice/Basic.lean`). So `S → Set.Icc (0:ℝ) 1` is a complete lattice, and
Mathlib's Knaster-Tarski (`OrderHom.lfp`/`gfp`, `Mathlib/Order/FixedPoints.lean`) applies to any
bundled monotone self-map of it directly -- no need to redo the whole `MatrixGame`/`Sion`-based
value-existence layer over `ℝ≥0∞` the way reachcert's own `F_inf`/`F_sup` do it for plain MDPs
(Sion's theorem needs genuine real-vector-space structure `ℝ≥0∞` doesn't have, so that detour would
have meant a second, from-scratch saddle-point existence proof). The entire real-valued stack built
so far can be reused as-is; only the two facts below needed adding before the reachability operator
itself, its boundedness, and its fixed point can be stated.

Neither lemma is deep -- both are direct consequences of `value_row_optimal`/`value_col_optimal`
(the same two facts `value_unique` in `MatchingPennies.lean` chains) plus the nonnegativity half of
`stdSimplex` membership. What's new is that nothing built so far needed them: `bwInd` never compares
two reward functions, and the worked example fixed one concrete matrix rather than reasoning about
matrices in general.
-/

/-- `payoff` is monotone in the payoff matrix, for any fixed pair of nonnegative (not necessarily
    normalised, not necessarily optimal) strategies -- a direct term-by-term comparison of the
    bilinear extension. Not needed by anything built so far; `value_mono` below is the only
    consumer, comparing two different games' values via a shared pair of strategies belonging to
    neither game in particular. -/
theorem payoff_mono {G G' : MatrixGame I J} (h : ∀ i j, G.A i j ≤ G'.A i j) {x : I → ℝ}
    {y : J → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) :
    G.payoff x y ≤ G'.payoff x y := by
  unfold payoff
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h i j) (hx i)) (hy j)

/-- **The payoff.** The game's value is monotone in the payoff matrix: if row pays column at least
    as much everywhere in `G'` as in `G`, then `G'`'s value is at least `G`'s. Proved by sandwiching
    `G.value` between the two games evaluated at the *same* pair of strategies
    (`G'.optimalRow, G.optimalCol`, belonging to neither game exclusively): `G`'s own saddle
    condition bounds it above by that payoff (`value_row_optimal`), `payoff_mono` carries that bound
    across to `G'`, and `G'`'s own saddle condition bounds the result above by `G'.value`
    (`value_col_optimal`). Neither game's optimal strategies need to relate to the other's. -/
theorem value_mono {G G' : MatrixGame I J} (h : ∀ i j, G.A i j ≤ G'.A i j) :
    G.value ≤ G'.value :=
  calc G.value ≤ G.payoff G'.optimalRow G.optimalCol :=
        G.value_row_optimal G'.optimalRow G'.optimalRow_mem
    _ ≤ G'.payoff G'.optimalRow G.optimalCol :=
        payoff_mono h G'.optimalRow_mem.1 G.optimalCol_mem.1
    _ ≤ G'.value := G'.value_col_optimal G.optimalCol G.optimalCol_mem

/-- The payoff at any pair of mixed strategies is at most any constant bounding every matrix entry
    -- a weighted average (nonnegative weights, each side's weights summing to `1`) of numbers `≤ c`
    is itself `≤ c`. No optimality needed; `value_le_of_forall_le` below is a one-line corollary at
    the optimal strategy pair. -/
theorem payoff_le_of_forall_le {x : I → ℝ} {y : J → ℝ} (hx : x ∈ stdSimplex ℝ I)
    (hy : y ∈ stdSimplex ℝ J) {c : ℝ} (h : ∀ i j, G.A i j ≤ c) :
    G.payoff x y ≤ c := by
  rw [payoff_eq_sum_mul]
  have hinner : ∀ i, ∑ j, G.A i j * y j ≤ c := fun i =>
    calc ∑ j, G.A i j * y j ≤ ∑ j, c * y j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h i j) (hy.1 j)
      _ = c := by rw [← Finset.mul_sum, hy.2, mul_one]
  calc ∑ i, x i * ∑ j, G.A i j * y j ≤ ∑ i, x i * c :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hinner i) (hx.1 i)
    _ = c := by rw [← Finset.sum_mul, hx.2, one_mul]

/-- Symmetric counterpart of `payoff_le_of_forall_le`: the payoff is at least any constant bounded
    above by every matrix entry. -/
theorem le_payoff_of_forall_le {x : I → ℝ} {y : J → ℝ} (hx : x ∈ stdSimplex ℝ I)
    (hy : y ∈ stdSimplex ℝ J) {c : ℝ} (h : ∀ i j, c ≤ G.A i j) :
    c ≤ G.payoff x y := by
  rw [payoff_eq_sum_mul]
  have hinner : ∀ i, c ≤ ∑ j, G.A i j * y j := fun i =>
    calc c = ∑ j, c * y j := by rw [← Finset.mul_sum, hy.2, mul_one]
      _ ≤ ∑ j, G.A i j * y j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h i j) (hy.1 j)
  calc c = ∑ i, x i * c := by rw [← Finset.sum_mul, hx.2, one_mul]
    _ ≤ ∑ i, x i * ∑ j, G.A i j * y j :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hinner i) (hx.1 i)

/-- **The payoff.** The game's value lies between any two constants bounding all its matrix
    entries -- both halves of the sandwich the reachability Bellman operator will need to stay
    inside `[0, 1]`. Direct corollaries of `payoff_le_of_forall_le`/`le_payoff_of_forall_le` at the
    optimal strategy pair, since `value` is *defined* as `payoff optimalRow optimalCol`. -/
theorem value_le_of_forall_le {c : ℝ} (h : ∀ i j, G.A i j ≤ c) : G.value ≤ c := by
  unfold value
  exact G.payoff_le_of_forall_le G.optimalRow_mem G.optimalCol_mem h

theorem le_value_of_forall_le {c : ℝ} (h : ∀ i j, c ≤ G.A i j) : c ≤ G.value := by
  unfold value
  exact G.le_payoff_of_forall_le G.optimalRow_mem G.optimalCol_mem h

/-- **Added for the reachability-iterate convergence plan (see `PHASE0-NOTES.md`).** Shifting
    every entry of a payoff matrix by the same constant shifts the payoff at any fixed strategy
    pair by that constant -- both players' weights sum to `1`, so the shift factors straight out.
    The per-state building block `value_add_const` below chains against. -/
theorem payoff_add_const {G G' : MatrixGame I J} (c : ℝ) (h : ∀ i j, G'.A i j = G.A i j + c)
    {x : I → ℝ} {y : J → ℝ} (hx : x ∈ stdSimplex ℝ I) (hy : y ∈ stdSimplex ℝ J) :
    G'.payoff x y = G.payoff x y + c := by
  rw [payoff_eq_sum_mul, payoff_eq_sum_mul]
  have hinner : ∀ i, ∑ j, G'.A i j * y j = (∑ j, G.A i j * y j) + c := by
    intro i
    calc ∑ j, G'.A i j * y j = ∑ j, (G.A i j * y j + c * y j) :=
          Finset.sum_congr rfl fun j _ => by rw [h i j]; ring
      _ = (∑ j, G.A i j * y j) + ∑ j, c * y j := Finset.sum_add_distrib
      _ = (∑ j, G.A i j * y j) + c := by rw [← Finset.mul_sum, hy.2, mul_one]
  calc ∑ i, x i * ∑ j, G'.A i j * y j
      = ∑ i, x i * ((∑ j, G.A i j * y j) + c) :=
        Finset.sum_congr rfl fun i _ => by rw [hinner i]
    _ = ∑ i, (x i * ∑ j, G.A i j * y j + x i * c) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = (∑ i, x i * ∑ j, G.A i j * y j) + ∑ i, x i * c := Finset.sum_add_distrib
    _ = (∑ i, x i * ∑ j, G.A i j * y j) + c := by rw [← Finset.sum_mul, hx.2, one_mul]

/-- **The payoff.** Shifting every entry of a payoff matrix by a constant shifts the *value* by
    that same constant -- `G`'s own optimal strategy pair still witnesses a saddle point of the
    shifted game `G'` (`payoff_add_const` turns each of `G`'s no-unilateral-improvement facts into
    `G'`'s), so `value_unique` pins `G'`'s value down to `G.value + c` on the nose, rather than
    just bounding it. Together with `value_mono`, this is what makes `MatrixGame.value` a genuine
    Lipschitz (not just monotone) function of the payoff matrix -- see `abs_value_sub_le` below. -/
theorem value_add_const {G G' : MatrixGame I J} (c : ℝ) (h : ∀ i j, G'.A i j = G.A i j + c) :
    G'.value = G.value + c := by
  have hpayoff : G'.payoff G.optimalRow G.optimalCol = G.value + c := by
    unfold value
    exact payoff_add_const c h G.optimalRow_mem G.optimalCol_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ I,
      G'.payoff G.optimalRow G.optimalCol ≤ G'.payoff p' G.optimalCol := by
    intro p' hp'
    rw [hpayoff, payoff_add_const c h hp' G.optimalCol_mem]
    linarith [G.value_row_optimal p' hp']
  have hcol : ∀ q' ∈ stdSimplex ℝ J,
      G'.payoff G.optimalRow q' ≤ G'.payoff G.optimalRow G.optimalCol := by
    intro q' hq'
    rw [hpayoff, payoff_add_const c h G.optimalRow_mem hq']
    linarith [G.value_col_optimal q' hq']
  have hunique := G'.value_unique G.optimalRow_mem G.optimalCol_mem hrow hcol
  rw [hpayoff] at hunique
  exact hunique.symm

/-- One direction of the Lipschitz bound: if `G'`'s entries never exceed `G`'s by more than `ε`,
    `G'`'s value doesn't either. Assembled from `value_mono` (comparing `G'` against the *shifted*
    game `fun i j => G.A i j + ε`) and `value_add_const` (identifying that shifted game's value as
    `G.value + ε`) -- monotonicity plus the shift fact together give continuity, which neither
    alone would. -/
theorem value_le_add_of_forall_le {G G' : MatrixGame I J} {ε : ℝ}
    (h : ∀ i j, G'.A i j ≤ G.A i j + ε) : G'.value ≤ G.value + ε := by
  have hmono : G'.value ≤ (⟨fun i j => G.A i j + ε⟩ : MatrixGame I J).value :=
    value_mono (G := G') (G' := (⟨fun i j => G.A i j + ε⟩ : MatrixGame I J)) h
  have hHeq : (⟨fun i j => G.A i j + ε⟩ : MatrixGame I J).value = G.value + ε :=
    value_add_const (G := G) (G' := (⟨fun i j => G.A i j + ε⟩ : MatrixGame I J)) ε
      (fun _ _ => rfl)
  linarith

/-- **The payoff.** `MatrixGame.value` is `1`-Lipschitz in the sup-norm on the payoff matrix --
    the fact the reachability-iterate convergence plan actually needs (see `PHASE0-NOTES.md`):
    once this lifts through `CSG.expect`/`stageValue` to the continuation `v`, it is exactly what
    `ωScottContinuous (C.reachOp goal hr)` requires. Both directions of `value_le_add_of_forall_le`
    (`G` against `G'`, then `G'` against `G`) assembled into one `abs`-valued statement via
    `abs_le`. -/
theorem abs_value_sub_le {G G' : MatrixGame I J} {ε : ℝ}
    (h : ∀ i j, |G'.A i j - G.A i j| ≤ ε) : |G'.value - G.value| ≤ ε := by
  have hub : ∀ i j, G'.A i j ≤ G.A i j + ε := fun i j => by linarith [(abs_le.mp (h i j)).2]
  have hlb : ∀ i j, G.A i j ≤ G'.A i j + ε := fun i j => by linarith [(abs_le.mp (h i j)).1]
  have h1 : G'.value ≤ G.value + ε := value_le_add_of_forall_le hub
  have h2 : G.value ≤ G'.value + ε := value_le_add_of_forall_le hlb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## `value` is invariant under relabelling the row player's action type

Folded in from `MatrixGameCongr.lean` (Update 2 above); original module docstring, verbatim:

**Original status: confirmed by a clean `lake build`, after two real fix rounds (see below) --
clean meaning no errors; two harmless unused-instance lint warnings remain, deliberately left in
rather than risk a third untested syntax fix for pure lint noise, see Round 2.** The one genuinely
new piece of infrastructure `Csg/Coalition.lean`'s own docstring flagged as missing: nothing in
`MatrixGame.lean`/`Csg/Basic.lean` states that a matrix game's value doesn't care how the row
player's action type is labelled, only what it's in bijection with.

Checked against the FMSD paper (Kwiatkowska, Norman, Parker, Santos, "Automatic verification of
concurrent stochastic systems") before drafting this, rather than assuming the shape needed: its
Definition 13 (the coalition-game construction reducing an `n`-player CSG to two-player form for a
coalition `C`) reduces to exactly this shape once its own `⊥`/idle-action machinery (Definition 7's
per-state *partial* action availability -- some players can have no enabled action at some states)
is set aside. This project's `CSG`/`NCSG` already make that simplification everywhere (`Basic.lean`
itself notes "every action available in every state", matching `DiscountedMDP`'s own MDP-side
simplification), so under it `Definition 13`'s `A_C1`/`A_C2` -- built there as
`(A_1 ∪ {⊥}) × ⋯ × (A_n' ∪ {⊥}) \ {(⊥,…,⊥)}` to handle a coalition whose members might all be
idling -- degenerate exactly to the plain product `Csg.Coalition.CoalitionAction`/`ComplementAction`
already built, with no exclusion needed (a coalition of players who always have a real action
available is never in the all-idle corner case). So nothing already built needs to change; the
simplification already standing throughout this project is consistent with the paper's own general
construction, just a special case of it. The paper also states the resulting zero-sum identity
`⟨⟨C⟩⟩P_max=?[ψ] ≡ ⟨⟨N∖C⟩⟩P_min=?[ψ]` without proof, "as a consequence of CSG determinacy" -- i.e.
exactly the free/relabelling-level fact this section exists to actually *prove*, not merely assert.
(As of `SkirmishFeintCoalition.lean`, this is no longer just anticipated: `reduceMax_ne_reduceMin`
there is a genuine worked instance of `⟨⟨C⟩⟩P_max ≠ ⟨⟨C⟩⟩P_min` built on exactly this and the
`value_relabelCol` section below.)

Only the row side was built first here; the column side follows in its own section below
(`value_relabelCol`, folded in from `MatrixGameCongrCol.lean`).

**The technique.** `value_unique` (above) already says any saddle point's payoff equals the
value, not just the one `Classical.choose` happened to pick. So: push `G.optimalRow` forward along
the relabelling equivalence `e : I' ≃ I` to get a strategy on `I'`, show it is still optimal for
the relabelled game (against the *same* `G.optimalCol`, since the column type is untouched), and
`value_unique` reads the relabelled game's value straight off as the same number -- no new
saddle-point existence argument needed. The only computation anywhere is reindexing a single
`Finset.sum` along a bijection (`Equiv.sum_comp`), both for `payoff` itself and for `stdSimplex`
membership.

**Round 1, from real `lake build` output:** two independent issues, both in `value_relabelRow`.
First, `hpayoff`'s closing `rw [payoff_relabelRow, hcomp]` left the goal
`G.payoff G.optimalRow G.optimalCol = G.value` unsolved -- true by `value`'s own definition, but
`rw`'s trailing automatic-`rfl` check apparently didn't unfold a plain `noncomputable def` far
enough to see it; fixed with an explicit `rfl` line, which does unfold that far. Second, the final
`(G.relabelRow e).value_unique hp'_mem G.optimalCol_mem hrow hcol` comes out stated as
`(G.relabelRow e).payoff _ _ = (G.relabelRow e).value`, so rewriting by `hpayoff` turns it into
`G.value = (G.relabelRow e).value` -- the mirror image of the theorem's own goal
`(G.relabelRow e).value = G.value` -- caught by a genuine type-mismatch error, fixed with `.symm`
rather than restating the chain in the other order.

**Round 2:** tried silencing two unused-section-variable linter warnings on
`mem_stdSimplex_comp`/`_symm` (correctly flagged: they don't need `Nonempty`/`DecidableEq` on
either action type, only `Fintype`) with an `omit [...] in` modifier placed after each theorem's
doc comment, copying the build output's own suggested fix verbatim. That broke parsing outright
("unexpected token `omit`; expected `lemma`") against this toolchain/Mathlib version, for reasons
not chased down (possibly `omit ... in` needing to sit with no preceding doc comment, or a
version-specific syntax difference from whatever produced the suggestion). Reverted rather than
guess at a second untested fix for a lint warning, not a correctness issue: the two theorems are
unchanged, the warnings are left in. Fixing linter noise is not worth spending a build round on.
-/

variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']

/-- Relabel the row player's action type along a bijection, leaving the column side untouched:
    `i'` plays exactly as `e i'` would have. -/
noncomputable def relabelRow (e : I' ≃ I) : MatrixGame I' J where
  A i' j := G.A (e i') j

/-- A strategy on the relabelled row type transports to one on the original, by pushing along
    `e.symm`. Needed below to check that a strategy is optimal for the *original* game once it's
    been pulled back from a candidate on `I'`.

    Pure `stdSimplex`-membership bookkeeping (a nonnegativity fact plus a reindexed sum), needing
    only `Fintype I`/`Fintype I'` for `Equiv.sum_comp` -- round 1's `lake build` flagged
    `Nonempty`/`DecidableEq` on both action types as unused here, correctly, but an `omit [...] in`
    modifier to silence it broke parsing against this toolchain (see the fix-round note above), so
    the warning is left in rather than risk a second untested syntax. -/
theorem mem_stdSimplex_comp_symm (e : I' ≃ I) {x' : I' → ℝ} (hx' : x' ∈ stdSimplex ℝ I') :
    x' ∘ ⇑e.symm ∈ stdSimplex ℝ I := by
  obtain ⟨hnonneg, hsum⟩ := hx'
  exact ⟨fun i => hnonneg (e.symm i), (Equiv.sum_comp e.symm x').trans hsum⟩

/-- The other direction of `mem_stdSimplex_comp_symm`: pushing a strategy on `I` forward along `e`
    lands back in `I'`'s own simplex. Needed below to turn `G.optimalRow` (a strategy on `I`) into
    a candidate strategy on `I'` in the first place. Same unused-instance warning, same reason. -/
theorem mem_stdSimplex_comp (e : I' ≃ I) {x : I → ℝ} (hx : x ∈ stdSimplex ℝ I) :
    x ∘ ⇑e ∈ stdSimplex ℝ I' := by
  obtain ⟨hnonneg, hsum⟩ := hx
  exact ⟨fun i' => hnonneg (e i'), (Equiv.sum_comp e x).trans hsum⟩

/-- The relabelled game's payoff at any strategy pair is the original game's payoff at the row
    strategy pulled back through `e.symm` -- the one computation everything else here reduces to,
    a single reindexed `Finset.sum` (`Equiv.sum_comp`) inside `payoff_eq_sum_mul`'s already-summed
    form. -/
theorem payoff_relabelRow (e : I' ≃ I) (x' : I' → ℝ) (y : J → ℝ) :
    (G.relabelRow e).payoff x' y = G.payoff (x' ∘ ⇑e.symm) y := by
  rw [payoff_eq_sum_mul, payoff_eq_sum_mul,
    ← Equiv.sum_comp e (fun i => (x' ∘ ⇑e.symm) i * ∑ j, G.A i j * y j)]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp only [relabelRow, Function.comp_apply, Equiv.symm_apply_apply]

/-- **The payoff.** `MatrixGame.value` doesn't change under a bijective relabelling of the row
    player's action type: `G.optimalRow` pushed forward along `e` is still an optimal row strategy
    for the relabelled game, against the very same `G.optimalCol`, so `value_unique` reads the
    relabelled value off directly. -/
theorem value_relabelRow (e : I' ≃ I) : (G.relabelRow e).value = G.value := by
  have hcomp : (fun i' => G.optimalRow (e i')) ∘ ⇑e.symm = G.optimalRow := by
    funext i
    simp
  have hp'_mem : (fun i' => G.optimalRow (e i')) ∈ stdSimplex ℝ I' :=
    mem_stdSimplex_comp e G.optimalRow_mem
  have hpayoff : (G.relabelRow e).payoff (fun i' => G.optimalRow (e i')) G.optimalCol =
      G.value := by
    rw [payoff_relabelRow, hcomp]
    rfl
  have hrow : ∀ p'' ∈ stdSimplex ℝ I', (G.relabelRow e).payoff
      (fun i' => G.optimalRow (e i')) G.optimalCol ≤ (G.relabelRow e).payoff p'' G.optimalCol := by
    intro p'' hp''
    rw [hpayoff, payoff_relabelRow]
    exact G.value_row_optimal _ (mem_stdSimplex_comp_symm e hp'')
  have hcol : ∀ q' ∈ stdSimplex ℝ J, (G.relabelRow e).payoff
      (fun i' => G.optimalRow (e i')) q' ≤
      (G.relabelRow e).payoff (fun i' => G.optimalRow (e i')) G.optimalCol := by
    intro q' hq'
    rw [payoff_relabelRow, hcomp, hpayoff]
    exact G.value_col_optimal q' hq'
  have hval := (G.relabelRow e).value_unique hp'_mem G.optimalCol_mem hrow hcol
  rw [hpayoff] at hval
  exact hval.symm

/-! ## `value` is invariant under relabelling the column player's action type

Folded in from `MatrixGameCongrCol.lean` (Update 2 above); original module docstring, verbatim:

**Original status: confirmed by a clean `lake build`, first attempt -- no fix round needed.** The
mirror image `MatrixGameCongr.lean`'s own docstring flagged as "not attempted here, would be a
direct mirror of everything below with `I`/`J` swapped" -- needed for the `Csg.Coalition` lift of
`Csg.SkirmishFeint` (`SkirmishFeintCoalition.lean`), which has to relabel *both* sides of a stage
game at once: the row and column index types coming out of `NCSG.reduceMin`/`reduceMax`
(`CoalitionAction`/`ComplementAction`, dependent products over a `Finset` subtype) are each only in
bijection with, not literally equal to, the bare per-player action types a hand-built `CSG` uses.
`value_relabelRow` above handles one side; this section supplies the other, so the two can be
composed (`relabelRow` then `relabelCol`, or either order -- they touch disjoint fields of
`MatrixGame.A`) to relabel a whole `MatrixGame` at once -- exactly how `SkirmishFeintCoalition.lean`
uses them.

Every theorem below is `value_relabelRow`'s own proof (above) with `I ↔ J`, row ↔ column,
`optimalRow`/`value_row_optimal` ↔ `optimalCol`/`value_col_optimal` swapped throughout -- same
technique (`value_unique` reads a pushed-forward saddle point's payoff off directly, `payoff`
reindexed along a single bijection via `Equiv.sum_comp`), same reason it works (`value_unique`
doesn't care which side of the saddle condition is being checked). No new mathematical content;
only `payoff_eq_sum_mul'` (the column-pulled-out regrouping of `payoff`) is used instead of
`payoff_eq_sum_mul`, matching which side is being relabelled.
-/

variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']

/-- Relabel the column player's action type along a bijection, leaving the row side untouched:
    `j'` plays exactly as `e j'` would have. Mirror of `relabelRow`. -/
noncomputable def relabelCol (e : J' ≃ J) : MatrixGame I J' where
  A i j' := G.A i (e j')

/-- Mirror of `mem_stdSimplex_comp_symm`, for the column side. -/
theorem mem_stdSimplex_comp_symm' (e : J' ≃ J) {y' : J' → ℝ} (hy' : y' ∈ stdSimplex ℝ J') :
    y' ∘ ⇑e.symm ∈ stdSimplex ℝ J := by
  obtain ⟨hnonneg, hsum⟩ := hy'
  exact ⟨fun j => hnonneg (e.symm j), (Equiv.sum_comp e.symm y').trans hsum⟩

/-- Mirror of `mem_stdSimplex_comp`, for the column side. -/
theorem mem_stdSimplex_comp' (e : J' ≃ J) {y : J → ℝ} (hy : y ∈ stdSimplex ℝ J) :
    y ∘ ⇑e ∈ stdSimplex ℝ J' := by
  obtain ⟨hnonneg, hsum⟩ := hy
  exact ⟨fun j' => hnonneg (e j'), (Equiv.sum_comp e y).trans hsum⟩

/-- The relabelled game's payoff at any strategy pair is the original game's payoff at the column
    strategy pulled back through `e.symm` -- mirror of `payoff_relabelRow`, via
    `payoff_eq_sum_mul'` instead of `payoff_eq_sum_mul`. -/
theorem payoff_relabelCol (e : J' ≃ J) (x : I → ℝ) (y' : J' → ℝ) :
    (G.relabelCol e).payoff x y' = G.payoff x (y' ∘ ⇑e.symm) := by
  rw [payoff_eq_sum_mul', payoff_eq_sum_mul',
    ← Equiv.sum_comp e (fun j => (∑ i, x i * G.A i j) * (y' ∘ ⇑e.symm) j)]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp only [relabelCol, Function.comp_apply, Equiv.symm_apply_apply]

/-- **The payoff.** `MatrixGame.value` doesn't change under a bijective relabelling of the column
    player's action type -- mirror of `value_relabelRow`, with `G.optimalRow` held fixed this time
    and `G.optimalCol` pushed forward along `e`. -/
theorem value_relabelCol (e : J' ≃ J) : (G.relabelCol e).value = G.value := by
  have hcomp : (fun j' => G.optimalCol (e j')) ∘ ⇑e.symm = G.optimalCol := by
    funext j
    simp
  have hq'_mem : (fun j' => G.optimalCol (e j')) ∈ stdSimplex ℝ J' :=
    mem_stdSimplex_comp' e G.optimalCol_mem
  have hpayoff : (G.relabelCol e).payoff G.optimalRow (fun j' => G.optimalCol (e j')) =
      G.value := by
    rw [payoff_relabelCol, hcomp]
    rfl
  have hrow : ∀ p' ∈ stdSimplex ℝ I, (G.relabelCol e).payoff
      G.optimalRow (fun j' => G.optimalCol (e j')) ≤
      (G.relabelCol e).payoff p' (fun j' => G.optimalCol (e j')) := by
    intro p' hp'
    rw [hpayoff, payoff_relabelCol, hcomp]
    exact G.value_row_optimal p' hp'
  have hcol : ∀ q'' ∈ stdSimplex ℝ J', (G.relabelCol e).payoff G.optimalRow q'' ≤
      (G.relabelCol e).payoff G.optimalRow (fun j' => G.optimalCol (e j')) := by
    intro q'' hq''
    rw [hpayoff, payoff_relabelCol]
    exact G.value_col_optimal _ (mem_stdSimplex_comp_symm' e hq'')
  have hval := (G.relabelCol e).value_unique G.optimalRow_mem hq'_mem hrow hcol
  rw [hpayoff] at hval
  exact hval.symm

/-! ## `value` as a linear program, for any action counts

Folded in from `MatrixGameLP.lean` (Update 2 above); original module docstring, verbatim:

**Original status: confirmed by a clean `lake build`, first attempt -- no fix round needed**,
unlike every other satellite file folded into this one in Update 2 (`MatrixGameCongr.lean`,
`CoalitionComplement.lean` each needed real fix rounds). Replaces an earlier draft of this section
(`MatrixGameExtreme.lean`, never shipped past a first cut, no `lake build` ever run against it) that
stopped at two bound lemmas motivated by one specific need -- certifying an explicit `value` for a
worked instance with three actions on one side, since `RockPaperScissorsLfp.lean`'s technique
(a uniform strategy optimal regardless of the continuation) is a lucky accident of that game's
cyclic symmetry, not something available in general. That need is still met here (see
`payoff_ge_of_row_ge`/`payoff_le_of_col_le` below, unchanged from the earlier draft), but it is no
longer the point: on reflection, a file motivated by "what does this one example need" is exactly
the kind of narrowly-triggered "core" file worth avoiding when the underlying fact is actually
general. What this section proves instead is a fact true of *every* `MatrixGame`, at *every*
action count, with no reference to any specific worked instance anywhere in a statement or proof:
`value` is not just *some* real number pinned down by `Classical.choose` over Sion's minimax
existence proof, it is *exactly* the optimal value of a genuine finite linear program, in the
textbook sense -- `value_isLeast_rowLPFeasible`/`value_isGreatest_colLPFeasible` below.

**The two characterizations, precisely.** Writing `colVal p j := ∑ i, p i * G.A i j` (a row
strategy `p`'s expected payoff against the *pure* column strategy `j`) and `rowVal q i := ∑ j, G.A
i j * q j` (symmetric, for a fixed column strategy `q` against pure row `i`):

* `rowLPFeasible G := {t | ∃ p ∈ stdSimplex ℝ I, ∀ j, colVal p j ≤ t}` -- the set of upper bounds
  the row (minimising) player can *guarantee* uniformly over the maximiser's pure responses, by
  committing to some mixed `p`. `value_isLeast_rowLPFeasible` says `G.value` is the *least* such
  guaranteeable bound -- i.e. `value = min` over `p ∈ stdSimplex ℝ I` of `max_j (colVal p j)`, the
  textbook primal LP for a zero-sum game's value (minimise `t` subject to `t ≥ colVal p j` for
  every pure `j`, `p` ranging over the simplex -- a genuine finite conjunction of linear
  inequalities in `p` and `t`, for any `I, J` whatsoever).
* `colLPFeasible G := {t | ∃ q ∈ stdSimplex ℝ J, ∀ i, t ≤ rowVal q i}` -- the dual: bounds the
  column player can guarantee from below. `value_isGreatest_colLPFeasible` says `G.value` is the
  *greatest* such bound, i.e. the mirror-image LP.

Neither theorem needs anything beyond what already exists: `payoff_single_left`/
`payoff_single_right` (below) reduce "payoff against a *pure* strategy" to the bare sum `colVal`/
`rowVal` already wants, and from there each characterization is exactly two of the four facts
already established above (`value_row_optimal`, `value_col_optimal`) plus one of the two bound
lemmas below, chained with `le_antisymm`'s two halves packaged as `IsLeast`/`IsGreatest` instead.

**Where this is meant to be reused, and what it doesn't do.** Any future worked instance needing an
explicit `value` (the very case that prompted this section, and later `SkirmishFeint.lean`'s own
worked instance) has a route besides `value_unique`: exhibit a `p`/`q` pair achieving the *same*
number as both an element of `rowLPFeasible`/`colLPFeasible` and a lower/upper bound of it, and
`le_antisymm` between the two `IsLeast`/`IsGreatest` facts pins the value directly, with the
LP-shaped bookkeeping handled once, here, rather than re-derived per example. It also gives the
cleanest possible hook for later, more ambitious infrastructure: the cached Mathlib source has both
`Sion.minimax`/`Sion.minimax'` (`Mathlib/Topology/Sion.lean`, a minimax *equality*, unused anywhere
in this project so far since `exists_optimal_strategies` only needed the saddle-point *existence*
half) and a genuine formalised Farkas' lemma (`ProperCone.hyperplane_separation`,
`Mathlib/Analysis/Convex/Cone/Dual.lean`) -- the classical route to LP strong duality. Neither is
used here; this section only states the characterization, it does not derive it from either of
those, and it does not attempt to *solve* the LP for an arbitrary matrix (Mathlib's own simplex
algorithm, `Tactic/Linarith/Oracle/SimplexAlgorithm`, is `linarith`'s internal certificate search,
not a reusable term-level "solve this LP" function) -- guessing the optimal `p`/`q` for a specific
instance remains exactly as much per-instance work as it was before this section.
-/

/-- The row player's payoff against the pure column strategy `j` collapses to the bare sum
    `∑ i, x i * G.A i j` -- `payoff_eq_sum_mul'` pulls the column strategy out as an outer sum,
    over which `Pi.single j 1` picks out exactly the `j`-th term. -/
theorem payoff_single_right (x : I → ℝ) (j : J) :
    G.payoff x (Pi.single j 1) = ∑ i, x i * G.A i j := by
  rw [payoff_eq_sum_mul']
  simp [Pi.single_apply, mul_ite, ite_mul, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ]

/-- The column player's payoff against the pure row strategy `i` collapses to the bare sum
    `∑ j, G.A i j * y j` -- symmetric counterpart of `payoff_single_right`, via
    `payoff_eq_sum_mul` instead. -/
theorem payoff_single_left (i : I) (y : J → ℝ) :
    G.payoff (Pi.single i 1) y = ∑ j, G.A i j * y j := by
  rw [payoff_eq_sum_mul]
  simp [Pi.single_apply, mul_ite, ite_mul, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ]

/-- **The row-side bound.** If every row's payoff against a fixed column strategy `y` is at least
    `m`, then *every* mixed row strategy's payoff against `y` is at least `m` too -- `payoff (·) y`
    is a weighted average of the per-row numbers `∑ j, G.A i j * y j`, and a weighted average
    (nonnegative weights summing to `1`) of numbers each `≥ m` is itself `≥ m`. The one half of
    `value_isGreatest_colLPFeasible`'s lower-bound direction that isn't already established
    above. -/
theorem payoff_ge_of_row_ge (y : J → ℝ) (m : ℝ) (h : ∀ i, m ≤ ∑ j, G.A i j * y j) :
    ∀ x ∈ stdSimplex ℝ I, m ≤ G.payoff x y := by
  intro x hx
  rw [payoff_eq_sum_mul]
  obtain ⟨hnonneg, hsum⟩ := hx
  calc m = m * ∑ i, x i := by rw [hsum, mul_one]
    _ = ∑ i, m * x i := by rw [Finset.mul_sum]
    _ ≤ ∑ i, x i * ∑ j, G.A i j * y j := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_comm m (x i)]
        exact mul_le_mul_of_nonneg_left (h i) (hnonneg i)

/-- **The column-side bound.** Mirror of `payoff_ge_of_row_ge`: if every column's payoff against a
    fixed row strategy `x` is at most `m`, so is every mixed column strategy's payoff against `x`.
    The one half of `value_isLeast_rowLPFeasible`'s upper-bound direction that isn't already
    established above. -/
theorem payoff_le_of_col_le (x : I → ℝ) (m : ℝ) (h : ∀ j, (∑ i, x i * G.A i j) ≤ m) :
    ∀ y ∈ stdSimplex ℝ J, G.payoff x y ≤ m := by
  intro y hy
  rw [payoff_eq_sum_mul']
  obtain ⟨hnonneg, hsum⟩ := hy
  calc ∑ j, (∑ i, x i * G.A i j) * y j
      ≤ ∑ j, m * y j := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h j) (hnonneg j)
    _ = m := by rw [← Finset.mul_sum, hsum, mul_one]

/-- The primal LP's feasible bounds: real numbers the row (minimising) player can guarantee not to
    exceed, uniformly over the column player's *pure* responses, by some fixed mixed strategy `p`.
    A genuine finite conjunction of linear inequalities in `p` (and `t`) for any `I`, `J` -- no
    reference to a continuum of column strategies, only the finitely many pure ones, `J` itself. -/
def rowLPFeasible (G : MatrixGame I J) : Set ℝ :=
  {t : ℝ | ∃ p ∈ stdSimplex ℝ I, ∀ j, (∑ i, p i * G.A i j) ≤ t}

/-- The dual LP's feasible bounds: real numbers the column (maximising) player can guarantee to
    reach, uniformly over the row player's *pure* responses, by some fixed mixed strategy `q`. -/
def colLPFeasible (G : MatrixGame I J) : Set ℝ :=
  {t : ℝ | ∃ q ∈ stdSimplex ℝ J, ∀ i, t ≤ (∑ j, G.A i j * q j)}

/-- **The payoff, primal side.** `G.value` is exactly the *least* element of `rowLPFeasible G` --
    the textbook LP for a zero-sum game's value, from the minimising player's side. Membership
    comes from `value_col_optimal` applied at each pure column strategy in turn (via
    `payoff_single_right`); the lower-bound half is `payoff_le_of_col_le` chained with
    `value_row_optimal`. -/
theorem value_isLeast_rowLPFeasible : IsLeast (G.rowLPFeasible) G.value := by
  constructor
  · refine ⟨G.optimalRow, G.optimalRow_mem, fun j => ?_⟩
    have h := G.value_col_optimal (Pi.single j 1) (single_mem_stdSimplex ℝ j)
    rwa [payoff_single_right] at h
  · rintro t ⟨p, hp, ht⟩
    calc G.value ≤ G.payoff p G.optimalCol := G.value_row_optimal p hp
      _ ≤ t := G.payoff_le_of_col_le p t ht G.optimalCol G.optimalCol_mem

/-- **The payoff, dual side.** `G.value` is exactly the *greatest* element of `colLPFeasible G` --
    the mirror-image LP, from the maximising player's side. Membership comes from
    `value_row_optimal` applied at each pure row strategy (via `payoff_single_left`); the
    upper-bound half is `payoff_ge_of_row_ge` chained with `value_col_optimal`. -/
theorem value_isGreatest_colLPFeasible : IsGreatest (G.colLPFeasible) G.value := by
  constructor
  · refine ⟨G.optimalCol, G.optimalCol_mem, fun i => ?_⟩
    have h := G.value_row_optimal (Pi.single i 1) (single_mem_stdSimplex ℝ i)
    rwa [payoff_single_left] at h
  · rintro t ⟨q, hq, ht⟩
    calc t ≤ G.payoff G.optimalRow q := G.payoff_ge_of_row_ge q t ht G.optimalRow G.optimalRow_mem
      _ ≤ G.value := G.value_col_optimal q hq

end MatrixGame

end Csg
