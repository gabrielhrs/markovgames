/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Shapley
import Csg.DiscountedValueIteration

/-!
# A computed run's error bound: value iteration, conditionally

**Status: confirmed by a clean `lake build`.**

What makes the `Comp/` line a *value iteration* rather than a one-step bridge. Given two successive
rational iterates and a rational bound `d` on how far the last step moved, this file concludes a
bound on the distance from the later iterate to `vOpt` -- and, under a *rational* stopping
condition, the `ε` guarantee itself. So a run performed by `#eval` comes with a theorem about the
numbers it produced.

**The two results.** `dist_vOpt_le_of_step` gives `dist w vOpt ≤ l * d / (1 - l)`, the standard a
posteriori bound: the error of the latest iterate is controlled by the last step's movement.
`two_dist_vOpt_lt_of_step` turns that into `2 * dist w vOpt < ε` under the hypothesis
`2 * l * d < ε * (1 - l)` -- which is a comparison between *rationals*, so `norm_num` discharges it
at a concrete instance. That hypothesis is deliberately the same shape as
`Csg/DiscountedValueIteration.lean`'s `stopCond`, which is the stopping test `numIters` searches
for; the difference is that this one is checkable, because it is over `ℚ` rather than `ℝ`.

**Why conditional on witnesses rather than a total `shapleyQ`.** A total function carrying a
once-and-for-all correctness theorem would need completeness of support enumeration -- Shapley-Snow
plus a proof that the elimination in `Comp/Search.lean` actually finds the pair, which is verifying
the solver, exactly what the architecture exists to avoid. Taking the per-step results as data and
the checks as hypotheses costs nothing by comparison: each run's bound is its own theorem, proved
about the computation actually performed.

**`shapley_eq_of_valueCert` is the usable per-state step**, and it supersedes
`Comp/Shapley.lean`'s `shapley_eq_of_find` in practice. The latter is conditional on
`findValueCert` having returned a value, and *proving* that needs the kernel to evaluate the search,
which `Comp/Search.lean` records it cannot do. So the route is: `#eval` the search to discover the
witnesses, write them as literals, and feed a `ValueCert` rather than a search result. The
`_of_find` variants in both files remain correct and remain the ones to reach for behind
`native_decide`, but nothing here depends on them.

**How a run is assembled**, concretely:

1. `#eval` the search once per state to get the next iterate, and repeat for as many steps as
   wanted -- all outside any proof;
2. write the final two iterates `v` and `w` into the file as literals, together with a `d` bounding
   `|v s - w s|` and the per-state optimal strategies;
3. prove one `ValueCert` per state by `norm_num` (not `decide` -- see
   `Comp/RockPaperScissorsQ.lean` on why rational arithmetic is out of the kernel's reach), and feed
   each to `shapley_eq_of_valueCert` to get `hstep`;
4. apply `two_dist_vOpt_lt_of_step` with the rational stopping condition discharged by `norm_num`.

The result is an `ε`-accuracy theorem about a vector that was genuinely computed, with no trust
axiom, no appeal to the solver, and no claim that the search is complete.

**Two notes on reaching into `Csg/`.** This file imports `Csg.DiscountedValueIteration` directly:
`vOpt`, `vOpt_fixedPoint` and `shapley_aposteriori_bound` live there, not in `Csg.Discounted`, and
the rest of `Comp/` only reaches the latter -- Lean 4 does not re-export a module's imports, the
same rule `Comp/Basic.lean` records for `PMF.ofFintype`. And unlike the `stdSimplex` membership in
`Comp/MatrixGameQ.lean`, `dist_pi_le_iff` hands back an already beta-reduced goal, so no `change`
is needed before `Real.dist_eq`; whether a lemma leaves the witness applied or reduced is worth
checking rather than assuming either way.

**Not here:** rational reconstruction of an exact fixed point. Continued fractions on the iterates
plus the decidable fixed-point check would, where it fires, upgrade a bound to an equality via the
uniqueness in `Csg/Discounted.lean`'s `exists_unique_fixedPoint`. It fires rarely, since the fixed
point of a concurrent game is algebraic and usually irrational, and it is independent of everything
above.
-/

namespace Comp

open Csg

namespace DiscountedCsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

/-- **The usable per-state step.** A value certificate on the rational stage game at `s` pins the
    real Shapley operator's value there. Same conclusion as `Comp/Shapley.lean`'s
    `shapley_eq_of_find`, but conditional on a `ValueCert` at literals -- which `norm_num` can
    discharge -- rather than on the search having returned, which only `native_decide` could
    establish. -/
theorem shapley_eq_of_valueCert (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {v : S → ℚ} {s : S} {t : ℚ} {p : A1 → ℚ} {q : A2 → ℚ}
    (hc : (G.shapleyGameQ s v).ValueCert t p q) :
    (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s = ((t : ℚ) : ℝ) := by
  change ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).value = ((t : ℚ) : ℝ)
  rw [shapleyGameQ_value G h s v]
  exact MatrixGameQ.value_eq_of_valueCert hc

/-! ## Running a step

The only executable definitions in this file. Both need a `List S`, for the reason
`Comp/Search.lean` records about `Fintype` enumeration, and both are for `#eval` rather than for
proofs -- they are how the literals a certificate mentions get discovered in the first place. -/

/-- One Shapley step, tabulated: the value the search reports at each listed state, or `none` where
    it found nothing. `#eval` this to watch a run converge. -/
def stepValues (G : DiscountedCsgQ S A1 A2) (Ss : List S) (As1 : List A1) (As2 : List A2)
    (v : S → ℚ) : List (Option ℚ) :=
  Ss.map fun s => ((G.shapleyGameQ s v).findValueCert As1 As2).map fun c => c.1

/-- One Shapley step with its witnesses: the value and both optimal strategies at each listed
    state, the strategies tabulated over the action lists because `#eval` cannot print a function.
    This is the output to copy into a `ValueCert`. -/
def stepWitnesses (G : DiscountedCsgQ S A1 A2) (Ss : List S) (As1 : List A1) (As2 : List A2)
    (v : S → ℚ) : List (Option (ℚ × List ℚ × List ℚ)) :=
  Ss.map fun s => ((G.shapleyGameQ s v).findValueCert As1 As2).map fun c =>
    (c.1, As1.map c.2.1, As2.map c.2.2)

/-- **The exact route, when it is available.** A rational vector that the Shapley operator fixes
    *is* the game's value -- no error term. The operator is a contraction
    (`Csg/Discounted.lean`'s `contractingWith_shapley`), so its fixed point is unique, and
    exhibiting one therefore identifies `vOpt` outright.

    This fires only when the value happens to be rational, which for a concurrent game is luck
    rather than the rule -- the fixed point is algebraic and generally irrational. When it does
    fire it is strictly better than any `ε` bound, so it is worth trying before settling for one. -/
theorem eq_vOpt_of_fixed (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) {v : S → ℚ}
    (hfix : ∀ s, (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s
      = ((v s : ℚ) : ℝ)) :
    (fun s => ((v s : ℚ) : ℝ)) = (G.toDiscountedCSG h).vOpt :=
  (G.toDiscountedCSG h).contractingWith_shapley.fixedPoint_unique (funext hfix)

/-- A pointwise rational bound gives a bound on the sup distance between the casts. `0 ≤ d` is
    carried explicitly rather than recovered from `hd`, because `S` is not assumed `Nonempty` and so
    there need not be any state at which to read the sign off. -/
theorem dist_cast_le {v w : S → ℚ} {d : ℚ} (hd0 : 0 ≤ d) (hd : ∀ s, |v s - w s| ≤ d) :
    dist (fun s => ((v s : ℚ) : ℝ)) (fun s => ((w s : ℚ) : ℝ)) ≤ ((d : ℚ) : ℝ) := by
  refine (dist_pi_le_iff (by exact_mod_cast hd0)).mpr fun s => ?_
  rw [Real.dist_eq]
  have h1 : ((|v s - w s| : ℚ) : ℝ) ≤ ((d : ℚ) : ℝ) := by exact_mod_cast hd s
  push_cast at h1
  exact h1

/-- **The a posteriori bound for a computed step.** If `w` is the Shapley image of `v` and the two
    differ by at most `d` at every state, the distance from `w` to the game's value is at most
    `l * d / (1 - l)`.

    Assembled from three facts already in `Csg/`: `shapley_aposteriori_bound` at `n = 0` bounds
    `v`'s own error by the step it takes, `shapley_contracting` at `vOpt` (a fixed point, by
    `vOpt_fixedPoint`) transfers that bound to `w` with a factor `l`, and `dist_cast_le` gives the
    rational bound on the step. The arithmetic is cleared of denominators with `le_div_iff₀` before
    `nlinarith`, the same route `valueIteration_error` takes. -/
theorem dist_vOpt_le_of_step (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {v w : S → ℚ} {d : ℚ} (hd0 : 0 ≤ d) (hd : ∀ s, |v s - w s| ≤ d)
    (hstep : ∀ s, (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s
      = ((w s : ℚ) : ℝ)) :
    dist (fun s => ((w s : ℚ) : ℝ)) (G.toDiscountedCSG h).vOpt
      ≤ (G.toDiscountedCSG h).l * ((d : ℚ) : ℝ) / (1 - (G.toDiscountedCSG h).l) := by
  set D := G.toDiscountedCSG h with hD
  set V : S → ℝ := fun s => ((v s : ℚ) : ℝ) with hV
  set W : S → ℝ := fun s => ((w s : ℚ) : ℝ) with hW
  have hSV : D.shapley V = W := funext hstep
  have hap := D.shapley_aposteriori_bound V 0
  simp only [Function.iterate_zero_apply, zero_add, Function.iterate_one] at hap
  rw [hSV] at hap
  have hlcast : (D.lNN : ℝ) = D.l := rfl
  rw [hlcast] at hap
  have hc : dist W D.vOpt ≤ D.l * dist V D.vOpt := by
    have h1 := D.shapley_contracting V D.vOpt
    rwa [hSV, D.vOpt_fixedPoint] at h1
  have hVW : dist V W ≤ ((d : ℚ) : ℝ) := by
    rw [hV, hW]; exact dist_cast_le hd0 hd
  have hl0 : (0 : ℝ) ≤ D.l := D.l_nonneg
  have hl1 : (0 : ℝ) < 1 - D.l := by linarith [D.l_lt_one]
  rw [le_div_iff₀ hl1] at hap ⊢
  nlinarith [hap, hVW, hc, hl0, hl1, mul_le_mul_of_nonneg_left hap hl0,
    mul_le_mul_of_nonneg_left hVW hl0, mul_le_mul_of_nonneg_right hc hl1.le]

/-- **The payoff: a checkable stopping test.** Under the *rational* condition
    `2 * l * d < ε * (1 - l)`, the computed iterate `w` is within `ε / 2` of the game's value.

    The hypothesis is the rational twin of `Csg/DiscountedValueIteration.lean`'s `stopCond`, and
    that is the whole point: `stopCond` is a statement about real distances that `numIters` must
    search for, while this one is a comparison of rationals that `norm_num` settles on the spot. The
    conclusion is `valueIteration_error`'s, for one computed step rather than for an abstract
    iteration. -/
theorem two_dist_vOpt_lt_of_step (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {v w : S → ℚ} {d eps : ℚ} (hd0 : 0 ≤ d) (hd : ∀ s, |v s - w s| ≤ d)
    (hstep : ∀ s, (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s
      = ((w s : ℚ) : ℝ))
    (hstop : 2 * G.l * d < eps * (1 - G.l)) :
    2 * dist (fun s => ((w s : ℚ) : ℝ)) (G.toDiscountedCSG h).vOpt < ((eps : ℚ) : ℝ) := by
  have hDl : (G.toDiscountedCSG h).l = ((G.l : ℚ) : ℝ) := rfl
  have hb := dist_vOpt_le_of_step G h hd0 hd hstep
  rw [hDl] at hb
  have hl0 : (0 : ℝ) ≤ ((G.l : ℚ) : ℝ) := by exact_mod_cast h.2.1
  have hl1 : ((G.l : ℚ) : ℝ) < 1 := by exact_mod_cast h.2.2
  have hstopR : 2 * ((G.l : ℚ) : ℝ) * ((d : ℚ) : ℝ)
      < ((eps : ℚ) : ℝ) * (1 - ((G.l : ℚ) : ℝ)) := by exact_mod_cast hstop
  have hpos : (0 : ℝ) < 1 - ((G.l : ℚ) : ℝ) := by linarith
  rw [le_div_iff₀ hpos] at hb
  have h2 : (2 * dist (fun s => ((w s : ℚ) : ℝ)) (G.toDiscountedCSG h).vOpt)
      * (1 - ((G.l : ℚ) : ℝ)) < ((eps : ℚ) : ℝ) * (1 - ((G.l : ℚ) : ℝ)) := by
    nlinarith [hb, hstopR]
  exact lt_of_mul_lt_mul_right h2 (by linarith : (0 : ℝ) ≤ 1 - ((G.l : ℚ) : ℝ))

end DiscountedCsgQ

end Comp
