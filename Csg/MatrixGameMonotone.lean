/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Basic

/-!
# Monotonicity and boundedness of the matrix-game value

**Status: done, confirmed by a clean `lake build`, including the later addition
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
each other). This file supplies the two facts about `MatrixGame.value` that argument is built on:

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

namespace Csg
namespace MatrixGame

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

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

variable (G : MatrixGame I J)

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

end MatrixGame
end Csg
