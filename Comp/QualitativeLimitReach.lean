/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.QualitativeLimitFinset

/-!
# `Lpre1` and `LF`: the value-1 set, from three nested computations

**Status: confirmed by a clean `lake build`.**

The last operator in the qualitative line and the one that matters most quantitatively:
`Csg/QualitativeLimitSure.lean`'s `LF b`, limit-sure reachability, which is the set of states from
which the row player can force reaching `b` with probability arbitrarily close to one -- the
*value-1 set* for probabilistic reachability. Limit-sure, not almost-sure, is the right notion
there: in a concurrent game the supremum over strategies need not be attained, so `AF b` can be
strictly smaller than the set of value-1 states while `LF b` is exactly it.

**Three levels, and no iteration count anywhere.** `LF b = νY.μX.(Lpre1(X,Y) ∪ b)`, and `Lpre1`
itself calls the `μW` fixed point `LW` once per state. So a run is three nested computations:

1. innermost, per state: `LW x y s`, climbing from `∅` on `Finset A1`
   (`Comp/QualitativeLimitFinset.lean`);
2. middle: the `μX` chain, climbing from `∅` on `Finset S`;
3. outermost: the `νY` chain, descending from `Finset.univ` on `Finset S`.

Each level's *exactness* is the next level's *hypothesis*, which is what lets every level stay free
of a termination theorem. `coe_lpre1F` takes the witness family `w` as data together with a proof
that it is `LW` -- a proof a worked instance gets from `LW_eq_coe_of_fixed`, one state at a time.
The middle and outer levels are then given as single-step lemmas rather than as `Function.iterate`
statements, deliberately: the witness family changes at every middle step, because `LW`'s first
argument is the middle chain's own variable, so a hypothesis quantified over all `x` would be an
exponential check. One step at a time keeps every hypothesis about one concrete `Finset`.

**The recipe**, following `Comp/Iterate.lean`'s:

1. `#eval` the whole nest to discover the chains and the witness families;
2. write the computed `Finset`s into the file as literals;
3. per state, `LW_eq_coe_of_fixed` turns an inner iterate into `hw`;
4. `le_lfInner_of_step` once per middle step, then `lfInner_eq_coe_of_fixed` when the middle chain
   stops -- that is one `νY`-step's inner `lfp`, exactly;
5. `LF_le_of_step` once per outer step, starting from `LF_le_univ`, then `LF_eq_coe_of_fixed` when
   the outer chain stops.

Every hypothesis along the way is a `Finset` equality over the game's support table, so with the
arithmetic quarantined the way `Comp/SafetyChainQ.lean` quarantines it, each one is a `decide`.

**Which side is cheap, at each level.** The middle chain climbs, so the fixed-point check gives its
*upper* half and the chain supplies the lower. The outer chain descends, so it is the other way
round. The two directions alternate as the nesting deepens, and `OrderHom.le_lfp_of_step` versus
`OrderHom.gfp_le_of_step` is the only thing that distinguishes them.
-/

namespace Comp

open Csg

namespace CsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

/-! ## `Lpre1`, with the witness family as data -/

/-- `CSG.Lpre1` as data, given a family `w` of row-action witness sets -- one per state, each
    intended to be `LW x y s`. The test itself is `bF (w s) x s = Finset.univ`: every column action
    can be driven to escape into `x`.

    `y` does not appear, because it enters only through `w`. That is the point of taking the family
    as data: the computed object depends on the witness sets, and `coe_lpre1F`'s hypothesis is what
    ties them to a particular `y`. -/
def lpre1F (G : CsgQ S A1 A2) (w : S → Finset A1) (x : Finset S) : Finset S :=
  Finset.univ.filter fun s => G.bF (w s) x s = Finset.univ

@[simp]
theorem mem_lpre1F (G : CsgQ S A1 A2) (w : S → Finset A1) (x : Finset S) (s : S) :
    s ∈ G.lpre1F w x ↔ G.bF (w s) x s = Finset.univ := by
  simp only [lpre1F, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `lpre1F` is `CSG.Lpre1`, provided the witness family really is `LW`. `coe_bF` inside, then
    `Finset.coe_eq_univ` to turn the `Set`-level `= Set.univ` test into the decidable `Finset`
    one. -/
theorem coe_lpre1F (G : CsgQ S A1 A2) (h : G.WellFormed) (w : S → Finset A1) (x y : Finset S)
    (hw : ∀ s, (G.toCSG h).LW ↑x ↑y s = (↑(w s) : Set A1)) :
    (↑(G.lpre1F w x) : Set S) = (G.toCSG h).Lpre1 ↑x ↑y := by
  ext s
  simp only [Finset.mem_coe, mem_lpre1F, CSG.Lpre1, Set.mem_setOf_eq, hw s, ← coe_bF G h,
    Finset.coe_eq_univ]

/-! ## The middle chain: `μX.(Lpre1(X,Y) ∪ b)` -/

/-- One turn of the middle chain, as data: `Lpre1(x,y) ∪ b`, matching `CSG.LFInnerFun`'s own
    shape. -/
theorem coe_LFInner_apply (G : CsgQ S A1 A2) (h : G.WellFormed) (b y x : Finset S)
    (w : S → Finset A1) (hw : ∀ s, (G.toCSG h).LW ↑x ↑y s = (↑(w s) : Set A1)) :
    (G.toCSG h).LFInner ↑b ↑y ↑x = (↑(G.lpre1F w x ∪ b) : Set S) := by
  change (G.toCSG h).Lpre1 (↑x : Set S) ↑y ∪ ↑b = (↑(G.lpre1F w x ∪ b) : Set S)
  rw [← coe_lpre1F G h w x y hw, ← Finset.coe_union]

/-- One middle step is sound: from a lower bound `x` on the `μX` fixed point, the next computed
    region is still a lower bound. `Comp/QualitativeLimitFinset.lean`'s climb, one level out. -/
theorem le_lfInner_of_step (G : CsgQ S A1 A2) (h : G.WellFormed) (b y x c : Finset S)
    (w : S → Finset A1) (hw : ∀ s, (G.toCSG h).LW ↑x ↑y s = (↑(w s) : Set A1))
    (hle : (↑x : Set S) ≤ ((G.toCSG h).LFInner ↑b ↑y).lfp)
    (hc : c = G.lpre1F w x ∪ b) :
    (↑c : Set S) ≤ ((G.toCSG h).LFInner ↑b ↑y).lfp := by
  subst hc
  exact OrderHom.le_lfp_of_step _ hle (coe_LFInner_apply G h b y x w hw).symm

/-- **The middle payoff.** A region the middle chain reached and that the middle step leaves fixed
    *is* the `μX` fixed point at `y`, exactly. That is one `νY`-step's worth of computation,
    certified. -/
theorem lfInner_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S)
    (w : S → Finset A1) (hw : ∀ s, (G.toCSG h).LW ↑c ↑y s = (↑(w s) : Set A1))
    (hfix : c = G.lpre1F w c ∪ b)
    (hle : (↑c : Set S) ≤ ((G.toCSG h).LFInner ↑b ↑y).lfp) :
    ((G.toCSG h).LFInner ↑b ↑y).lfp = (↑c : Set S) := by
  have hfixS : (G.toCSG h).LFInner (↑b : Set S) ↑y ↑c = (↑c : Set S) := by
    rw [coe_LFInner_apply G h b y c w hw, ← hfix]
  exact (OrderHom.eq_lfp_of_fixed_of_le _ hfixS hle).symm

/-! ## The outer chain: `νY` -/

/-- The outer chain's first link, free: `Finset.univ` bounds everything. -/
theorem LF_le_univ (G : CsgQ S A1 A2) (h : G.WellFormed) (b : Finset S) :
    (G.toCSG h).LF ↑b ≤ (↑(Finset.univ : Finset S) : Set S) := by
  rw [Finset.coe_univ]
  exact le_top

/-- One outer step is sound: if `c` is the certified `μX` fixed point at `y`, and `y` was an upper
    bound on `LF b`, then `c` is too. The descent, one `OrderHom.gfp_le_of_step` per step, with the
    middle chain's payoff supplying the step's identification. -/
theorem LF_le_of_step (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S)
    (hinner : ((G.toCSG h).LFInner ↑b ↑y).lfp = (↑c : Set S))
    (hy : (G.toCSG h).LF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).LF ↑b ≤ (↑c : Set S) := by
  have hLF : (G.toCSG h).LF (↑b : Set S) = ((G.toCSG h).LFOuter ↑b).gfp := rfl
  have hstep : (↑c : Set S) = (G.toCSG h).LFOuter (↑b : Set S) ↑y := hinner.symm
  rw [hLF] at hy ⊢
  exact OrderHom.gfp_le_of_step _ hy hstep

/-- **The value-1 set, exactly.** A region that is its own certified `μX` fixed point and that the
    outer descent has reached *is* `LF b` -- the limit-sure reachability set of the real-valued
    game, hence its set of value-1 states for reaching `b`.

    Nothing in the chain of hypotheses bounds any of the three iteration counts. Each level was run,
    seen to stop, and checked. -/
theorem LF_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (b y : Finset S)
    (hinner : ((G.toCSG h).LFInner ↑b ↑y).lfp = (↑y : Set S))
    (hy : (G.toCSG h).LF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).LF ↑b = (↑y : Set S) := by
  have hLF : (G.toCSG h).LF (↑b : Set S) = ((G.toCSG h).LFOuter ↑b).gfp := rfl
  have hfixS : (G.toCSG h).LFOuter (↑b : Set S) ↑y = (↑y : Set S) := hinner
  rw [hLF] at hy ⊢
  exact (OrderHom.eq_gfp_of_fixed_of_ge _ hfixS hy).symm

end CsgQ

end Comp
