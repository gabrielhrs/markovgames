/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Iterate
import Comp.Reach
import Comp.QualitativeFinset
import Comp.QualitativeAlmostFinset
import Comp.QualitativeLimitReach

/-!
# The objective, as a separate object: what a model is asked, and what counts as an answer

**Status: confirmed by a clean `lake build`.**

Until now every worked instance in `Comp/` hard-wired its own question: `SafetyChainQ.lean` proves a
statement about `CSG.G` at one particular region, `HideOrRunQ.lean` two statements about `LF` and
`AF` at one particular target. The model was data, but the *question* was a theorem statement
written by hand, so nothing connected the instances to each other. This file separates the two, the
way a model checker does: a model is a `CsgQ`, a question is an `Objective`, and the two meet only
when something is proved about them.

**`Objective` is pure data, and the discount belongs to it.** No proofs, no side conditions, no
dependency on a particular game -- just `Finset`s and rationals, so an objective can be parsed,
compared, printed or stored. Putting the discount factor in the objective rather than in the model
is the same choice PRISM makes: `l` comes from the property being checked, not from the system being
checked, and `withDiscount` below assembles the `DiscountedCsgQ` on demand. (`Comp/Basic.lean`'s
`DiscountedCsgQ` remains what the discounted theory is stated about; it is now derived rather than
primary.)

**`Answers` is a relation, not a function.** This is the design decision the file turns on. A
`denote : Objective → (what it means)` function would have to be total, and the objectives do not
admit that: reachability needs the game to be reward-free, a discounted value needs `l ∈ [0,1)`, and
there is nothing sensible to return when those fail. Worse, the *kind* of answer differs by
objective -- a region for the qualitative shapes, an interval or an `ε`-ball for the quantitative
ones -- so a function would need a dependent result type and still could not express "this is a
bound" as opposed to "this is the value". As an indexed relation all of that is free: each
constructor carries exactly the side conditions its own objective needs, and the index pair
`(Objective, Answer)` makes a category error unprovable rather than merely false -- there is no
constructor producing a `region` for a `discounted` objective, which is
`not_answers_discounted_region` below.

**The two answer kinds are not a defect, they are the honest state of the two lines.** A
`region` answer is *exact*: `Comp/QualitativeFinset.lean` and its siblings identify a computed
`Finset` with the real-valued operator's fixed point on the nose. An `interval` or `approx` answer
is a bound, because the Shapley fixed point of a concurrent game is generally irrational and no
rational iterate equals it. The relation records which of the two a given result is, rather than
flattening both into "the answer".

**What this file does not do.** It does not solve anything. For `sureSafe` a generic solver-side
wrapper exists (`answers_sureSafe`, from `G_eq_coe_of_fixed`) because that operator's chain is a
plain `Function.iterate`; for `AF` and `LF` the chain length varies per instance and the outer steps
are given one at a time, so there is no single wrapper to write and the constructor itself is the
interface -- an instance supplies the equality however it obtained it. `Comp/SafetyChainQ.lean` and
`Comp/HideOrRunQ.lean` do exactly that, in one line each.

**Not here:** `until`, reward-until, Büchi and co-Büchi objectives, and the sure/almost-sure
variants of reachability and the two `ω`-regular shapes (`SF`, `SFG`, `SGF`, `AGF`, `LGF`, `AFG`,
`LFG`). Each is one more `Objective` constructor and one more `Answers` constructor naming the
operator it denotes; the ones here are the ones with computed results to point at. Also not here:
the list-based concrete syntax for a model -- a `CsgQ (Fin n) (Fin m1) (Fin m2)` built from nested
`List ℚ` data -- which is what would let a model come from outside Lean. That needs no transport
lemma, since every file in `Comp/` is already generic over the state and action types.
-/

namespace Comp

/-! ## The question -/

/-- A verification question, as data. Deliberately free of proofs and of any reference to a
    particular game, so that the same objective can be posed of several models. -/
inductive Objective (S : Type*) where
  /-- Sure safety: stay inside `region` forever, with certainty (`CSG.G`). -/
  | sureSafe (region : Finset S)
  /-- Almost-sure reachability of `target` (`CSG.AF`). -/
  | almostReach (target : Finset S)
  /-- Limit-sure reachability of `target` (`CSG.LF`) -- the value-1 set. -/
  | limitReach (target : Finset S)
  /-- Quantitative probability of reaching `target` (`CSG.reachOp`'s least fixed point). -/
  | reach (target : Finset S)
  /-- Optimal discounted value at discount `l` (`DiscountedCSG.vOpt`). The discount is part of the
      question, not of the model. -/
  | discounted (l : ℚ)

/-- What a result looks like. Three shapes, because the lines genuinely produce three: an exactly
    identified region, a sandwiched interval, and a vector with an `ε` guarantee. -/
inductive Answer (S : Type*) where
  /-- An exactly identified set of states. -/
  | region (c : Finset S)
  /-- A pair of sound bounds on a value vector, not claimed to be tight. -/
  | interval (lo hi : S → ℚ)
  /-- A vector within `eps` of the true value, in sup distance. -/
  | approx (v : S → ℚ) (eps : ℚ)

namespace CsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

/-! ## Two side conditions, as data-level predicates -/

/-- Reward-freeness, which `CSG.reachOp` requires. Decidable, like `WellFormed`, because the rewards
    are a rational table. -/
def RewardFree (G : CsgQ S A1 A2) : Prop := ∀ s a1 a2, G.r s a1 a2 = 0

instance (G : CsgQ S A1 A2) : Decidable G.RewardFree := by
  unfold RewardFree
  infer_instance

/-- The discounted game a model and a discount make between them. The model carries no discount;
    this is where the objective's `l` meets it. -/
def withDiscount (G : CsgQ S A1 A2) (l : ℚ) : DiscountedCsgQ S A1 A2 where
  toCsgQ := G
  l := l

/-- `withDiscount` is well formed exactly when the model is and the discount is in `[0, 1)`. -/
theorem withDiscount_wf (G : CsgQ S A1 A2) (h : G.WellFormed) {l : ℚ} (hl0 : 0 ≤ l)
    (hl1 : l < 1) : (G.withDiscount l).WellFormed :=
  ⟨h, hl0, hl1⟩

/-! ## The specification relation -/

/-- **What it means for `ans` to answer `obj` about `G`.** One constructor per objective shape, each
    carrying its own side conditions and naming the `Csg/` operator it is about. Nothing here is
    computed: this is the statement a run has to establish, and the files above are what establish
    it. -/
inductive Answers (G : CsgQ S A1 A2) (h : G.WellFormed) : Objective S → Answer S → Prop where
  /-- `c` is exactly the sure-safety region for `region`. -/
  | sureSafe {region c : Finset S} (hG : (G.toCSG h).G ↑region = (↑c : Set S)) :
      Answers G h (Objective.sureSafe region) (Answer.region c)
  /-- `c` is exactly the almost-sure reachability set for `target`. -/
  | almostReach {target c : Finset S} (hAF : (G.toCSG h).AF ↑target = (↑c : Set S)) :
      Answers G h (Objective.almostReach target) (Answer.region c)
  /-- `c` is exactly the limit-sure reachability set for `target` -- the value-1 set. -/
  | limitReach {target c : Finset S} (hLF : (G.toCSG h).LF ↑target = (↑c : Set S)) :
      Answers G h (Objective.limitReach target) (Answer.region c)
  /-- `lo` and `hi` sandwich the reachability value. Reward-freeness is a hypothesis of *this*
      constructor rather than of the objective, which is why `Answers` is a relation. -/
  | reach {target : Finset S} {lo hi : S → ℚ} (hrf : G.RewardFree)
      (h0 : ∀ s, 0 ≤ lo s) (h1 : ∀ s, lo s ≤ 1) (k0 : ∀ s, 0 ≤ hi s) (k1 : ∀ s, hi s ≤ 1)
      (hlo : castIcc lo h0 h1
        ≤ ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp)
      (hhi : ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp
        ≤ castIcc hi k0 k1) :
      Answers G h (Objective.reach target) (Answer.interval lo hi)
  /-- `v` is within `eps` of the optimal discounted value. The discount bounds are hypotheses here
      for the same reason reward-freeness is above. -/
  | discounted {l : ℚ} {v : S → ℚ} {eps : ℚ} (hl0 : 0 ≤ l) (hl1 : l < 1)
      (hd : 2 * dist (fun s => ((v s : ℚ) : ℝ))
          ((G.withDiscount l).toDiscountedCSG (withDiscount_wf G h hl0 hl1)).vOpt
        < ((eps : ℚ) : ℝ)) :
      Answers G h (Objective.discounted l) (Answer.approx v eps)

/-! ## Using it in both directions

An interface earns its keep only if nothing is lost on the way in and nothing has to be taken on
trust on the way out. The wrapper below goes in; the three extraction lemmas come back out. -/

/-- **In.** A `sureSafe` objective answered directly from a computed descent: the
    `Comp/QualitativeFinset.lean` payoff, phrased as an answer. This is the one objective with a
    generic wrapper, because its chain is a plain `Function.iterate` -- `AF` and `LF` take their
    outer steps one at a time, so their constructors are the interface instead. -/
theorem answers_sureSafe (G : CsgQ S A1 A2) (h : G.WellFormed) (region c : Finset S) (n : ℕ)
    (hiter : (G.gStepF region)^[n] Finset.univ = c) (hfix : G.gStepF region c = c) :
    G.Answers h (Objective.sureSafe region) (Answer.region c) :=
  .sureSafe (G_eq_coe_of_fixed G h region c n hiter hfix)

/-- **Out.** An answer to a `sureSafe` objective is the sure-safety region, with nothing else
    assumed. -/
theorem G_eq_of_answers (G : CsgQ S A1 A2) (h : G.WellFormed) {region c : Finset S}
    (ha : G.Answers h (Objective.sureSafe region) (Answer.region c)) :
    (G.toCSG h).G ↑region = (↑c : Set S) := by
  cases ha with
  | sureSafe hG => exact hG

/-- **Out.** Likewise for almost-sure reachability. -/
theorem AF_eq_of_answers (G : CsgQ S A1 A2) (h : G.WellFormed) {target c : Finset S}
    (ha : G.Answers h (Objective.almostReach target) (Answer.region c)) :
    (G.toCSG h).AF ↑target = (↑c : Set S) := by
  cases ha with
  | almostReach hAF => exact hAF

/-- **Out.** And for limit-sure reachability, the value-1 set. -/
theorem LF_eq_of_answers (G : CsgQ S A1 A2) (h : G.WellFormed) {target c : Finset S}
    (ha : G.Answers h (Objective.limitReach target) (Answer.region c)) :
    (G.toCSG h).LF ↑target = (↑c : Set S) := by
  cases ha with
  | limitReach hLF => exact hLF

/-- **The indices do work.** A region is not a possible answer to a discounted value, and the
    relation says so by having no constructor with those indices -- so this is unprovable rather
    than false, and the same holds of every other mismatched pair. That is the benefit of indexing
    the relation by both the question and the answer shape instead of by the question alone. -/
theorem not_answers_discounted_region (G : CsgQ S A1 A2) (h : G.WellFormed) (l : ℚ)
    (c : Finset S) : ¬ G.Answers h (Objective.discounted l) (Answer.region c) := by
  intro ha
  cases ha

end CsgQ

end Comp
