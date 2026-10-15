/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Discounted
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Rational concurrent stochastic games, and the bridge to the real-valued specification

**Status: confirmed by a clean `lake build`.** First file of the `Comp` library.

`Mdp/` and `Csg/` prove algorithms correct; `Comp/` runs them. Nothing in `Comp/` is imported by
either, so the specification side stays independent of anything done for the sake of computation.

This file supplies the data layer and the only bridge the rest of `Comp/` needs. A `CsgQ` is a
concurrent stochastic game whose kernel and rewards are *rational*, with no proof obligations
carried in the structure: being a genuine game (nonnegative kernel rows summing to one) is a
separate, **decidable** predicate `WellFormed`. That separation is the point of the design. Model
data can be written by hand, generated, or read from a file, and nothing upstream ever has to
produce a proof -- Lean checks the data instead, and a malformed model is rejected rather than
silently miscomputed.

The state and action types stay generic (`Fintype`, exactly `CSG`'s own binders) rather than being
fixed to `Fin n`. Two reasons: the existing worked instances already carry named inductive state
types with hand-written `Fintype` instances (`RPSState`, `RobotState`), so they can be reused
directly; and `Fin n` remains available simply by choosing it for `S`, with no loss. If a flat
indexed-and-arrayed representation is ever wanted for speed, it can be introduced as a separate
structure with an `Equiv` to this one, which is what `MatrixGame.value_relabelRow` and
`value_relabelCol` already exist to transport across.

**What the bridge does.** `toCSG`/`toDiscountedCSG` turn a well-formed `CsgQ`/`DiscountedCsgQ` into
the real-valued `CSG`/`DiscountedCSG` the whole specification side is stated over, by sending each
rational kernel row to a `PMF` via `PMF.ofFintype`. The two lemmas that matter downstream are
`toPMF_toReal` (the `PMF`'s mass at a state, back in `ℝ`, is exactly the cast of the rational
entry) and `expect_toCSG` (the real `CSG.expect` of a cast continuation is the cast of the rational
`expectQ`). Everything later in `Comp/` reaches the specification through those two and never
unfolds `PMF` again.

**Why `ℚ` and not `ℝ`, and why this cannot be avoided.** `ℝ` has no computable arithmetic or
order in Mathlib, so no restructuring makes the real-valued definitions run; `ℚ` is exact and
decidable, which is what both `#eval` and `decide` need. Note that exactness here is a property of
each *step*: given a rational continuation, every stage game has rational entries and hence a
rational value, so the iterates stay in `ℚ` throughout. It is emphatically not a claim about the
limit, which for a concurrent game is algebraic and in general irrational -- see
`Csg/DiscountedValueIteration.lean`'s docstring for why, and why `valueIteration_error` is
therefore the strongest statement available.

**One import note, because imports are not transitive.** `PMF.ofFintype` and
`PMF.ofFintype_apply` live in `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`,
which nothing in the `Csg/` chain imports -- `Csg/Basic.lean` takes only
`...ProbabilityMassFunction.Basic`, which is why `Mdp/RecyclingRobot.lean` can use `ofFintype`
(its `Mdp/Basic.lean` imports `Constructions`) and a `Csg/` file cannot. Lean 4 does not re-export
a module's own imports, so any `PMF` constructor beyond those `Basic` declares needs its own import
line here, exactly as `Csg/IntrusionDetection.lean` must import `...ProbabilityMassFunction.Monad`
directly to get `PMF.pure`.

**Not here:** anything about matrix games or equilibria (next checkpoint), any search procedure, and
any iteration. This file is data plus bridge, nothing else.
-/

namespace Comp

open Csg

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

/-- A concurrent stochastic game with rational data. Mirrors `Csg.CSG`'s binders exactly, with `ℚ`
    in place of `ℝ` and a bare rational kernel in place of a `PMF`.

    Deliberately carries no well-formedness proof: that is `WellFormed` below, a decidable
    predicate. A `CsgQ` on its own is just a table of numbers, which is what makes it safe to build
    one from any source. -/
structure CsgQ (S A1 A2 : Type*) [Fintype S] [Fintype A1] [Fintype A2]
    [Nonempty A1] [Nonempty A2] [DecidableEq A1] [DecidableEq A2] where
  /-- Transition weights: `K s a1 a2 s'` is the rational probability of moving to `s'`. Required to
      be a distribution by `WellFormed`, not by construction. -/
  K : S → A1 → A2 → S → ℚ
  /-- Reward for the joint action, paid by the row player to the column player, as in `CSG.r`. -/
  r : S → A1 → A2 → ℚ

/-- A `CsgQ` together with a rational discount factor. Mirrors `Csg.DiscountedCSG`'s relationship to
    `Csg.CSG`, including using `extends` so that nothing about the underlying game is duplicated. -/
structure DiscountedCsgQ (S A1 A2 : Type*) [Fintype S] [Fintype A1] [Fintype A2]
    [Nonempty A1] [Nonempty A2] [DecidableEq A1] [DecidableEq A2] extends CsgQ S A1 A2 where
  /-- Discount factor. Required to lie in `[0, 1)` by `WellFormed`. -/
  l : ℚ

namespace CsgQ

/-- Being a genuine game: every kernel row is nonnegative and sums to one. A `Prop`, but a
    decidable one (see the instance below) -- which is the whole reason the structure above carries
    no proofs. For a concrete model this is discharged by `decide`, and for a model obtained from
    outside Lean it is the validation step. -/
def WellFormed (G : CsgQ S A1 A2) : Prop :=
  (∀ s a1 a2 s', 0 ≤ G.K s a1 a2 s') ∧ (∀ s a1 a2, ∑ s', G.K s a1 a2 s' = 1)

/-- `WellFormed` is decidable: it is a finite conjunction of rational inequalities and equalities
    over `Fintype`s. Nothing here needs `DecidableEq S` -- `Fintype.decidableForallFintype` wants
    only a `DecidablePred`, and `ℚ`'s order and equality supply that. -/
instance (G : CsgQ S A1 A2) : Decidable G.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Each kernel entry, cast to `ℝ`, is nonnegative. The `ℝ`-side form of `WellFormed`'s first
    half, in the shape `PMF.ofFintype` and `ENNReal.toReal_ofReal` want it. -/
theorem K_cast_nonneg {G : CsgQ S A1 A2} (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) (s' : S) :
    (0 : ℝ) ≤ ((G.K s a1 a2 s' : ℚ) : ℝ) := by
  exact_mod_cast h.1 s a1 a2 s'

/-- Each kernel row, cast to `ℝ`, still sums to one. Proved by moving the cast across the finite
    sum with `push_cast` rather than by naming a specific `Rat.cast_sum`-style lemma. -/
theorem sum_K_cast_eq_one {G : CsgQ S A1 A2} (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    ∑ s' : S, ((G.K s a1 a2 s' : ℚ) : ℝ) = 1 := by
  have hq : ((∑ s' : S, G.K s a1 a2 s' : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by rw [h.2 s a1 a2]
  push_cast at hq
  exact hq

/-- One kernel row as a `PMF`, which is the form `CSG` wants its transitions in. Same
    `PMF.ofFintype` construction `Mdp/RecyclingRobot.lean`'s `searchPMF` uses, with the masses
    coming from the rational table instead of a literal. -/
noncomputable def toPMF (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    PMF S :=
  PMF.ofFintype (fun s' => ENNReal.ofReal ((G.K s a1 a2 s' : ℚ) : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun s' _ => K_cast_nonneg h s a1 a2 s',
      sum_K_cast_eq_one h s a1 a2, ENNReal.ofReal_one])

/-- **The first of the two bridge lemmas.** The mass `toPMF` assigns to `s'`, converted back to
    `ℝ`, is exactly the cast of the rational entry -- so the round trip through `ENNReal` loses
    nothing. Every later statement relating a rational computation to its real-valued specification
    goes through this, and none of them unfolds `PMF` again. -/
theorem toPMF_toReal (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) (s' : S) :
    (G.toPMF h s a1 a2 s').toReal = ((G.K s a1 a2 s' : ℚ) : ℝ) := by
  unfold toPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (K_cast_nonneg h s a1 a2 s')

/-- The real-valued `CSG` a well-formed rational game denotes. This is the object every theorem in
    `Csg/` is stated about; `Comp/` computes with the rational data and transports conclusions
    across this map. -/
noncomputable def toCSG (G : CsgQ S A1 A2) (h : G.WellFormed) : CSG S A1 A2 where
  K s a1 a2 := G.toPMF h s a1 a2
  r s a1 a2 := ((G.r s a1 a2 : ℚ) : ℝ)

/-- One-step expectation, rationally: the computable counterpart of `CSG.expect`. Written as a plain
    `Finset` sum over `ℚ`, so it is both `#eval`-able and usable inside `decide`. -/
def expectQ (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) (v : S → ℚ) : ℚ :=
  ∑ s', G.K s a1 a2 s' * v s'

/-- **The second of the two bridge lemmas.** `CSG.expect` of a cast continuation is the cast of
    `expectQ` -- the rational one-step computation agrees with the real-valued specification on the
    nose, with no error term. Together with `toPMF_toReal` this is everything the rest of `Comp/`
    needs about the transition structure. -/
theorem expect_toCSG (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2)
    (v : S → ℚ) :
    (G.toCSG h).expect s a1 a2 (fun s' => ((v s' : ℚ) : ℝ))
      = ((G.expectQ s a1 a2 v : ℚ) : ℝ) := by
  unfold CSG.expect expectQ
  push_cast
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [show (G.toCSG h).K s a1 a2 s' = G.toPMF h s a1 a2 s' from rfl, toPMF_toReal]

end CsgQ

namespace DiscountedCsgQ

/-- Being a genuine discounted game: the underlying game is well formed and the discount lies in
    `[0, 1)`. Decidable for the same reasons, with the two rational bounds on `l` adding only two
    more decidable comparisons. -/
def WellFormed (G : DiscountedCsgQ S A1 A2) : Prop :=
  G.toCsgQ.WellFormed ∧ 0 ≤ G.l ∧ G.l < 1

instance (G : DiscountedCsgQ S A1 A2) : Decidable G.WellFormed := by
  unfold WellFormed
  infer_instance

/-- The real-valued `DiscountedCSG` a well-formed rational discounted game denotes -- the object
    `Csg/Discounted.lean`'s `shapley` and `Csg/DiscountedValueIteration.lean`'s
    `valueIteration_error` are about. The two discount side conditions transfer by `exact_mod_cast`
    from their rational originals, since `Rat.cast` into `ℝ` is an order embedding. -/
noncomputable def toDiscountedCSG (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) :
    DiscountedCSG S A1 A2 where
  toCSG := G.toCsgQ.toCSG h.1
  l := ((G.l : ℚ) : ℝ)
  l_nonneg := by exact_mod_cast h.2.1
  l_lt_one := by exact_mod_cast h.2.2

/-- The underlying real-valued `CSG` of `toDiscountedCSG` is the one `CsgQ.toCSG` already built --
    `rfl`, recorded as a lemma so later files can rewrite with it instead of relying on `extends`
    unfolding at the right moment. -/
theorem toDiscountedCSG_toCSG (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) :
    (G.toDiscountedCSG h).toCSG = G.toCsgQ.toCSG h.1 := rfl

/-- The discount of `toDiscountedCSG` is the cast of the rational one. Also `rfl`, and recorded for
    the same reason: it is needed wherever a rational iteration's discount factor has to be matched
    against the real-valued operator's. -/
theorem toDiscountedCSG_l (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) :
    (G.toDiscountedCSG h).l = ((G.l : ℚ) : ℝ) := rfl

end DiscountedCsgQ

end Comp
