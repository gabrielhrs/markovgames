/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Finite two-player zero-sum matrix games

**Status: confirmed by a clean `lake build`.** Finite zero-sum matrix games and their value. The
load-bearing dependency is `Mathlib.Topology.Sion` (`Sion.exists_isSaddlePointOn`), a
formalisation of Sion's minimax theorem, which that file's own docstring notes specialises to von
Neumann's minimax theorem in the finite bilinear case -- exactly the finite zero-sum matrix game
below.

Why it matters here: the per-state value computation of a *concurrent* stochastic game is not a
plain `Finset.sup'` over actions the way it is for MDPs (`DiscountedMDP.bellman` in
`Mdp/Basic.lean`) -- it is the value of a one-shot finite zero-sum matrix game between the two
players, since both choose actions simultaneously at a state. `exists_optimal_strategies` below
gives existence of that value (as a mixed-strategy saddle point) from Mathlib directly, without
reproving von Neumann from scratch, the way `Mdp/` avoids reproving Banach.

`value` and its supporting API (`optimalRow`, `optimalCol`, `value_row_optimal`,
`value_col_optimal`, `value_unique`) live here rather than in `Basic.lean`: none of it is about
`CSG`, all of it is about `MatrixGame` alone, so it belongs beside `exists_optimal_strategies`
itself. `Basic.lean` only defines `CSG`/`stageGame`/`stageValue`, importing `value` from here like
any other consumer.

Three further sections below -- `value`'s monotonicity and boundedness in the payoff matrix,
`value` as a linear program together with the certificate lemmas that read a value off a pair of
strategies, and invariance of `value` under reindexing either player's action type along a
surjection -- likewise state facts about `MatrixGame` alone, with no `CSG` content, and so are
gathered here alongside the rest of the `MatrixGame` API. Each keeps its own section heading
below.

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
    chaining both pairs' optimality conditions against each other. -/
theorem value_unique {p : I → ℝ} {q : J → ℝ} (hp : p ∈ stdSimplex ℝ I) (hq : q ∈ stdSimplex ℝ J)
    (hrow : ∀ p' ∈ stdSimplex ℝ I, G.payoff p q ≤ G.payoff p' q)
    (hcol : ∀ q' ∈ stdSimplex ℝ J, G.payoff p q' ≤ G.payoff p q) :
    G.payoff p q = G.value := by
  apply le_antisymm
  · calc G.payoff p q ≤ G.payoff G.optimalRow q := hrow G.optimalRow G.optimalRow_mem
      _ ≤ G.value := G.value_col_optimal q hq
  · calc G.value ≤ G.payoff p G.optimalCol := G.value_row_optimal p hp
      _ ≤ G.payoff p q := hcol G.optimalCol G.optimalCol_mem

/-- One row strategy bounds the value from above: if `p` keeps the payoff at or below `t` against
    every column strategy, then `value ≤ t`. The upper half of `value_unique`, with no column
    strategy to exhibit. `value_le_of_col_le` below asks for the bound at pure columns only. -/
theorem value_le_of_forall_payoff_le {p : I → ℝ} (hp : p ∈ stdSimplex ℝ I) {t : ℝ}
    (h : ∀ q ∈ stdSimplex ℝ J, G.payoff p q ≤ t) : G.value ≤ t :=
  (G.value_row_optimal p hp).trans (h G.optimalCol G.optimalCol_mem)

/-- One column strategy bounds the value from below. Mirror of `value_le_of_forall_payoff_le`;
    `le_value_of_row_ge` below asks for the bound at pure rows only. -/
theorem le_value_of_forall_le_payoff {q : J → ℝ} (hq : q ∈ stdSimplex ℝ J) {t : ℝ}
    (h : ∀ p ∈ stdSimplex ℝ I, t ≤ G.payoff p q) : t ≤ G.value :=
  (h G.optimalRow G.optimalRow_mem).trans (G.value_col_optimal q hq)

/-! ## Monotonicity and boundedness of `value`

**Status: confirmed by a clean `lake build`.**

Reachability/until values for CSGs, unlike the bounded objectives `BackwardInduction.lean` covers,
are not computed by a fixed number of recursion steps -- they are the least fixed point of a
per-state Bellman-style operator (Knaster-Tarski, not structural recursion). Existence of that
fixed point needs the operator to be *monotone* on a *complete lattice*. This section supplies the
two facts about `MatrixGame.value` that argument is built on:

1. `value_mono`: if one payoff matrix dominates another entrywise, its value is at least as large.
   Needed so the per-state stage-game step (`CSG.stageValue`, `Basic.lean`) is monotone in the
   continuation value -- exactly the hypothesis Knaster-Tarski asks for.
2. `value_le_of_forall_le`/`le_value_of_forall_le`: the value is sandwiched between any two
   constants bounding all matrix entries. Needed to show the reachability operator maps `[0, 1]`
   into itself, so the fixed point can be found inside `Set.Icc (0:ℝ) 1` rather than needing all of
   `ℝ` to be a complete lattice (it isn't -- `ℝ` has no top or bottom element).

`Set.Icc a b` in a `ConditionallyCompleteLattice` (`ℝ` qualifies) has a `CompleteLattice` instance
(`Set.Icc.completeLattice`, `Mathlib/Order/CompleteLatticeIntervals.lean`), and `Pi` types of
complete lattices are complete lattices (`Pi.instCompleteLattice`). So `S → Set.Icc (0:ℝ) 1` is a
complete lattice, and Mathlib's Knaster-Tarski (`OrderHom.lfp`/`gfp`,
`Mathlib/Order/FixedPoints.lean`) applies to any bundled monotone self-map of it directly -- there
is no need to redo the `MatrixGame`/`Sion`-based value-existence layer over `ℝ≥0∞` (Sion's theorem
needs real-vector-space structure `ℝ≥0∞` does not have).

Both lemmas are direct consequences of `value_row_optimal`/`value_col_optimal` plus the
nonnegativity half of `stdSimplex` membership.
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

/-- A constant payoff matrix has that constant as its value: `value_le_of_forall_le` and
    `le_value_of_forall_le` at the same constant. This is the stage game of any state whose
    reward and transition ignore the joint action. -/
theorem value_eq_of_forall_eq {c : ℝ} (h : ∀ i j, G.A i j = c) : G.value = c :=
  le_antisymm (G.value_le_of_forall_le fun i j => (h i j).le)
    (G.le_value_of_forall_le fun i j => (h i j).ge)

/-- Shifting every entry of a payoff matrix by the same constant shifts the payoff at any fixed
    strategy pair by that constant -- both players' weights sum to `1`, so the shift factors
    straight out. The per-state building block `value_add_const` below chains against. -/
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
    that same constant. `G`'s optimal row strategy holds the shifted game `G'` to `G.value + c`
    against every column strategy, and `G`'s optimal column strategy secures `G.value + c` against
    every row strategy (`payoff_add_const` carries each of `G`'s two optimality facts across), so
    `G'.value` is bounded on both sides. Together with `value_mono`, this is what makes
    `MatrixGame.value` a genuine Lipschitz (not just monotone) function of the payoff matrix --
    see `abs_value_sub_le` below. -/
theorem value_add_const {G G' : MatrixGame I J} (c : ℝ) (h : ∀ i j, G'.A i j = G.A i j + c) :
    G'.value = G.value + c := by
  apply le_antisymm
  · refine G'.value_le_of_forall_payoff_le G.optimalRow_mem fun q hq => ?_
    rw [payoff_add_const c h G.optimalRow_mem hq]
    linarith [G.value_col_optimal q hq]
  · refine G'.le_value_of_forall_le_payoff G.optimalCol_mem fun p hp => ?_
    rw [payoff_add_const c h hp G.optimalCol_mem]
    linarith [G.value_row_optimal p hp]

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
    the fact `ReachConverge.lean` needs:
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

/-! ## `value` as a linear program, for any action counts

**Status: confirmed by a clean `lake build`.** `value` is not just *some* real number pinned down
by `Classical.choose` over Sion's minimax existence proof: it is *exactly* the optimal value of a
finite linear program, in the textbook sense -- `value_isLeast_rowLPFeasible`/
`value_isGreatest_colLPFeasible` below. This holds for *every* `MatrixGame`, at *every* action
count. `payoff_ge_of_row_ge`/`payoff_le_of_col_le` are the bound lemmas it rests on; they also
certify an explicit `value` for a worked instance whose optimal strategies are not uniform, where
`RockPaperScissorsLfp.lean`'s technique (a uniform strategy optimal regardless of the
continuation, by that game's cyclic symmetry) is not available.

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

**Where this is reused, and what it doesn't do.** A worked instance needing an explicit `value`
has a route besides `value_unique`: `value_eq_of_certificate` below takes a row strategy `p`, a
column strategy `q` and a number `t`, and asks for one inequality per pure column (`p` holds the
payoff to at most `t`) and one per pure row (`q` secures at least `t`). The payoff at the pair
`(p, q)` is not computed and no mixed deviation is quantified over. `value_le_of_col_le` and
`le_value_of_row_ge` are its two halves, and the two LP characterizations are restatements of
them. The characterization is also a hook for more ambitious infrastructure: Mathlib has both
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
  simp [Pi.single_apply, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ]

/-- The column player's payoff against the pure row strategy `i` collapses to the bare sum
    `∑ j, G.A i j * y j` -- symmetric counterpart of `payoff_single_right`, via
    `payoff_eq_sum_mul` instead. -/
theorem payoff_single_left (i : I) (y : J → ℝ) :
    G.payoff (Pi.single i 1) y = ∑ j, G.A i j * y j := by
  rw [payoff_eq_sum_mul]
  simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq', Finset.mem_univ]

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

/-- `optimalRow` holds the payoff to at most `value` against every pure column:
    `value_col_optimal` at the pure column strategy `j`, read through `payoff_single_right`. -/
theorem optimalRow_col_le (j : J) : ∑ i, G.optimalRow i * G.A i j ≤ G.value := by
  have h := G.value_col_optimal (Pi.single j 1) (single_mem_stdSimplex ℝ j)
  rwa [payoff_single_right] at h

/-- `optimalCol` secures at least `value` against every pure row. Mirror of
    `optimalRow_col_le`. -/
theorem le_optimalCol_row (i : I) : G.value ≤ ∑ j, G.A i j * G.optimalCol j := by
  have h := G.value_row_optimal (Pi.single i 1) (single_mem_stdSimplex ℝ i)
  rwa [payoff_single_left] at h

/-- **The certificate, upper half.** A row strategy whose payoff against each *pure* column is at
    most `t` bounds the value by `t`: one inequality per column, with no mixed column strategy
    quantified over (`payoff_le_of_col_le` extends the bound to those). -/
theorem value_le_of_col_le {p : I → ℝ} (hp : p ∈ stdSimplex ℝ I) {t : ℝ}
    (h : ∀ j, ∑ i, p i * G.A i j ≤ t) : G.value ≤ t :=
  G.value_le_of_forall_payoff_le hp (G.payoff_le_of_col_le p t h)

/-- **The certificate, lower half.** A column strategy whose payoff against each pure row is at
    least `t` bounds the value below by `t`. Mirror of `value_le_of_col_le`. -/
theorem le_value_of_row_ge {q : J → ℝ} (hq : q ∈ stdSimplex ℝ J) {t : ℝ}
    (h : ∀ i, t ≤ ∑ j, G.A i j * q j) : t ≤ G.value :=
  G.le_value_of_forall_le_payoff hq (G.payoff_ge_of_row_ge q t h)

/-- **The value certificate.** A row strategy `p`, a column strategy `q` and a number `t`, with
    `p` holding every pure column to at most `t` and `q` securing at least `t` against every pure
    row, determine the value: `value = t`. The hypotheses are `|J| + |I|` inequalities between
    finite sums, so for a concrete game each one is a computation; neither the payoff at `(p, q)`
    nor any mixed deviation appears. -/
theorem value_eq_of_certificate {p : I → ℝ} {q : J → ℝ} (hp : p ∈ stdSimplex ℝ I)
    (hq : q ∈ stdSimplex ℝ J) {t : ℝ} (hle : ∀ j, ∑ i, p i * G.A i j ≤ t)
    (hge : ∀ i, t ≤ ∑ j, G.A i j * q j) : G.value = t :=
  le_antisymm (G.value_le_of_col_le hp hle) (G.le_value_of_row_ge hq hge)

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
    the textbook LP for a zero-sum game's value, from the minimising player's side. Membership is
    `optimalRow_col_le`; the lower-bound half is `value_le_of_col_le`. -/
theorem value_isLeast_rowLPFeasible : IsLeast (G.rowLPFeasible) G.value := by
  constructor
  · exact ⟨G.optimalRow, G.optimalRow_mem, G.optimalRow_col_le⟩
  · rintro t ⟨p, hp, ht⟩
    exact G.value_le_of_col_le hp ht

/-- **The payoff, dual side.** `G.value` is exactly the *greatest* element of `colLPFeasible G` --
    the mirror-image LP, from the maximising player's side. Membership is `le_optimalCol_row`; the
    upper-bound half is `le_value_of_row_ge`. -/
theorem value_isGreatest_colLPFeasible : IsGreatest (G.colLPFeasible) G.value := by
  constructor
  · exact ⟨G.optimalCol, G.optimalCol_mem, G.le_optimalCol_row⟩
  · rintro t ⟨q, hq, ht⟩
    exact G.le_value_of_row_ge hq ht

/-! ## `value` under reindexing the action types

**Status: confirmed by a clean `lake build`.** `comapRow f` replaces the row player's action type
`I` by `I'` along a map `f : I' → I`: row `i'` plays as `f i'` would have. `comapCol` does the same
for the column player. Two facts hold on each side.

* For any `f`, the reindexed player can do no better than before. The row player minimises, so
  `G.value ≤ (G.comapRow f).value` (`value_le_value_comapRow`); the column player maximises, so
  `(G.comapCol f).value ≤ G.value` (`value_comapCol_le_value`). The certificate is the *other*
  player's optimal strategy for `G`, since every row of `G.comapRow f` is a row of `G`.
* When `f` is surjective the value is unchanged (`value_comapRow`, `value_comapCol`): duplicate
  actions change nothing. The certificate is `G`'s optimal strategy pushed forward along a section
  of `f` (`pushStrat`), which puts each action's weight on one chosen preimage.

A bijection is the special case `relabelRow`/`relabelCol`, with `value_relabelRow`/
`value_relabelCol` as corollaries. All four value theorems go through the certificate lemmas of
the previous section, so the only computation is `sum_pushStrat_mul`: pairing a pushed-forward
weight vector with `c` is pairing the original with `c ∘ g`.

In the FMSD paper (Kwiatkowska, Norman, Parker, Santos, "Automatic verification of concurrent
stochastic systems"), Definition 13 (the coalition-game construction reducing an `n`-player CSG to
two-player form for a coalition `C`) reduces to a relabelling of this shape once its `⊥`/idle-action
machinery (Definition 7's per-state *partial* action availability -- some players can have no
enabled action at some states) is set aside. `CSG`/`NCSG` make that simplification everywhere
(every action available in every state, as in `DiscountedMDP`), so under it Definition 13's
`A_C1`/`A_C2` -- built there as `(A_1 ∪ {⊥}) × ⋯ × (A_n' ∪ {⊥}) \ {(⊥,…,⊥)}` to handle a coalition
whose members might all be idling -- degenerate to the plain product
`Csg.Coalition.CoalitionAction`/`ComplementAction`, with no exclusion needed. The paper also
states the resulting zero-sum identity `⟨⟨C⟩⟩P_max=?[ψ] ≡ ⟨⟨N∖C⟩⟩P_min=?[ψ]` without proof, "as a
consequence of CSG determinacy"; the relabelling-level fact behind it is `value_relabelRow`.
`SkirmishFeintCoalition.lean` relabels *both* sides of a stage game at once: the row and column
index types coming out of `NCSG.reduceMin`/`reduceMax` (`CoalitionAction`/`ComplementAction`,
dependent products over a `Finset` subtype) are each only in bijection with, not literally equal
to, the bare per-player action types a hand-built `CSG` uses. `relabelRow` and `relabelCol` touch
disjoint arguments of `MatrixGame.A`, so they compose in either order.
-/

section Reindex

/-- Push a weight vector forward along `g`: `b` receives the total weight of the `a` with
    `g a = b`. -/
noncomputable def pushStrat {α β : Type*} [Fintype α] [DecidableEq β] (g : α → β) (x : α → ℝ) :
    β → ℝ :=
  fun b => ∑ a, if g a = b then x a else 0

/-- Pairing a pushed-forward weight vector with `c` is pairing the original with `c ∘ g`. -/
theorem sum_pushStrat_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (g : α → β)
    (x : α → ℝ) (c : β → ℝ) : ∑ b, pushStrat g x b * c b = ∑ a, x a * c (g a) := by
  simp only [pushStrat, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [ite_mul]

/-- `sum_pushStrat_mul` with the factors in the other order. -/
theorem sum_mul_pushStrat {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (g : α → β)
    (x : α → ℝ) (c : β → ℝ) : ∑ b, c b * pushStrat g x b = ∑ a, c (g a) * x a :=
  calc ∑ b, c b * pushStrat g x b = ∑ b, pushStrat g x b * c b :=
        Finset.sum_congr rfl fun b _ => mul_comm _ _
    _ = ∑ a, x a * c (g a) := sum_pushStrat_mul g x c
    _ = ∑ a, c (g a) * x a := Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The push-forward of a mixed strategy is a mixed strategy. -/
theorem pushStrat_mem {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (g : α → β)
    {x : α → ℝ} (hx : x ∈ stdSimplex ℝ α) : pushStrat g x ∈ stdSimplex ℝ β := by
  refine ⟨fun b => ?_, ?_⟩
  · show 0 ≤ ∑ a, if g a = b then x a else 0
    refine Finset.sum_nonneg fun a _ => ?_
    split_ifs
    · exact hx.1 a
    · exact le_rfl
  · calc ∑ b, pushStrat g x b = ∑ b, pushStrat g x b * 1 := by simp only [mul_one]
      _ = ∑ a, x a * 1 := sum_pushStrat_mul g x fun _ => 1
      _ = ∑ a, x a := by simp only [mul_one]
      _ = 1 := hx.2

variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']

/-- Reindex the row player's action type along `f`, leaving the column side untouched: `i'` plays
    exactly as `f i'` would have. `f` need not be injective (several `i'` may play the same row)
    or surjective (some rows of `G` may go unplayed). -/
noncomputable def comapRow (f : I' → I) : MatrixGame I' J where
  A i' j := G.A (f i') j

/-- Reindexing the rows can only raise the value: every row of `G.comapRow f` is a row of `G`, so
    `G.optimalCol` still secures `G.value` against each of them. -/
theorem value_le_value_comapRow (f : I' → I) : G.value ≤ (G.comapRow f).value := by
  refine (G.comapRow f).le_value_of_row_ge G.optimalCol_mem fun i' => ?_
  exact G.le_optimalCol_row (f i')

/-- **The payoff.** Reindexing the rows along a surjection leaves the value unchanged.
    `G.optimalRow`, pushed forward along a section `g` of `f`, holds every pure column of
    `G.comapRow f` to exactly what `G.optimalRow` holds it to in `G`. -/
theorem value_comapRow {f : I' → I} (hf : Function.Surjective f) :
    (G.comapRow f).value = G.value := by
  refine le_antisymm ?_ (G.value_le_value_comapRow f)
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  refine (G.comapRow f).value_le_of_col_le (pushStrat_mem g G.optimalRow_mem) fun j => ?_
  have hsum : ∑ i', pushStrat g G.optimalRow i' * (G.comapRow f).A i' j =
      ∑ i, G.optimalRow i * G.A i j := by
    refine (sum_pushStrat_mul g G.optimalRow fun i' => (G.comapRow f).A i' j).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    show G.optimalRow i * G.A (f (g i)) j = G.optimalRow i * G.A i j
    rw [hg i]
  exact hsum.le.trans (G.optimalRow_col_le j)

/-- Relabel the row player's action type along a bijection, leaving the column side untouched:
    `i'` plays exactly as `e i'` would have. This is `comapRow` at `e`. -/
noncomputable def relabelRow (e : I' ≃ I) : MatrixGame I' J where
  A i' j := G.A (e i') j

/-- **The payoff.** `MatrixGame.value` doesn't change under a bijective relabelling of the row
    player's action type: `value_comapRow` at the surjection `e`. -/
theorem value_relabelRow (e : I' ≃ I) : (G.relabelRow e).value = G.value :=
  G.value_comapRow e.surjective

variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']

/-- Reindex the column player's action type along `f`, leaving the row side untouched. Mirror of
    `comapRow`. -/
noncomputable def comapCol (f : J' → J) : MatrixGame I J' where
  A i j' := G.A i (f j')

/-- Reindexing the columns can only lower the value: every column of `G.comapCol f` is a column
    of `G`, so `G.optimalRow` still holds each of them to `G.value`. Mirror of
    `value_le_value_comapRow`. -/
theorem value_comapCol_le_value (f : J' → J) : (G.comapCol f).value ≤ G.value := by
  refine (G.comapCol f).value_le_of_col_le G.optimalRow_mem fun j' => ?_
  exact G.optimalRow_col_le (f j')

/-- **The payoff.** Reindexing the columns along a surjection leaves the value unchanged. Mirror
    of `value_comapRow`, with `G.optimalCol` pushed forward along a section of `f`. -/
theorem value_comapCol {f : J' → J} (hf : Function.Surjective f) :
    (G.comapCol f).value = G.value := by
  refine le_antisymm (G.value_comapCol_le_value f) ?_
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  refine (G.comapCol f).le_value_of_row_ge (pushStrat_mem g G.optimalCol_mem) fun i => ?_
  have hsum : ∑ j', (G.comapCol f).A i j' * pushStrat g G.optimalCol j' =
      ∑ j, G.A i j * G.optimalCol j := by
    refine (sum_mul_pushStrat g G.optimalCol fun j' => (G.comapCol f).A i j').trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    show G.A i (f (g j)) * G.optimalCol j = G.A i j * G.optimalCol j
    rw [hg j]
  exact (G.le_optimalCol_row i).trans hsum.ge

/-- Relabel the column player's action type along a bijection, leaving the row side untouched:
    `j'` plays exactly as `e j'` would have. Mirror of `relabelRow`. -/
noncomputable def relabelCol (e : J' ≃ J) : MatrixGame I J' where
  A i j' := G.A i (e j')

/-- **The payoff.** `MatrixGame.value` doesn't change under a bijective relabelling of the column
    player's action type: `value_comapCol` at the surjection `e`. -/
theorem value_relabelCol (e : J' ≃ J) : (G.relabelCol e).value = G.value :=
  G.value_comapCol e.surjective

end Reindex

end MatrixGame

end Csg
