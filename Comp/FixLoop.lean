/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Qualitative
import Comp.Reach

/-!
# The fixpoint loop: apply, compare, stop

**Status: confirmed by a clean `lake build`.**

A monotone operator on a finite lattice reaches its fixed point in finitely many steps, and the
iteration can detect that itself: apply the step, compare, return if nothing changed, recurse
otherwise. This file is that loop, together with the two facts that make its output usable inside a
proof -- that it never overshoots the fixed point, and that it always reaches one.

**Why there is a fuel at all, and why nobody has to see it.** "Loop until stable" is not
structurally recursive, so Lean wants a termination argument. The natural measure is the
cardinality, but `f x ⊆ x` is *not* a property of the step -- `Pre1(∅) ∩ safe` need not be empty, so
an arbitrary application does not shrink anything. The chain only descends because it starts at `⊤`
and the step is monotone. Carrying that invariant through a well-founded recursion is possible, but
well-founded recursion compiles to `Acc.rec`, which the kernel cannot reduce -- the same obstruction
that keeps `Nat.gcd`, and so every rational literal, out of `decide`'s reach. A loop defined that
way would run under `#eval` but could not appear in a `decide`.

So the recursion here is structural, on a fuel, and the fuel is `Fintype.card S` -- a bound derived
from the type rather than a number anyone chooses. The early exit is what keeps that cheap: once
`f x = x` the loop returns immediately and the remaining fuel is never unfolded, so the kernel does
the number of iterations the computation actually took, not the worst case. A static bound and
stopping early are not in tension.

**The two halves, and where each comes from.** `gfp_le_coe_fixAux` and `coe_fixAux_le_lfp` say the
loop never overshoots: whatever it returns is still on the correct side of the fixed point, by one
`OrderHom.gfp_le_of_step` (or `le_lfp_of_step`) per level of fuel. That is the half the iteration
has to supply, and it comes from the loop's shape rather than from a count. The other half is that
the returned region really is fixed -- and `fixFrom_univ_fixed` proves that outright, so the caller
supplies neither.

**That the fuel suffices.** `Fintype.card S` steps are enough for a monotone step, and the argument
is a cardinality one. The chain from `⊤` is nonincreasing, so each iteration either stops -- which
is the conclusion -- or is strict, and a strict step costs at least one from the cardinality. With
`x.card ≤ n` fuel in hand, a strict step leaves `(f x).card ≤ n - 1`, so the invariant is
maintained; and at `n = 0` the region is empty, where `f x ⊆ x` forces `f x = x`. Dually from `⊥`,
measuring `card S - x.card`. Both are `fixAux_fixed_of_card_le` and
`fixAux_fixed_of_compl_card_le` below, nine lines each.

That is the whole of it, and the payoff is `gfp_eq_coe_fixFrom_univ`: the greatest fixed point of
`F` equals a computed `Finset`, with one hypothesis -- the bridge `↑(f x) = F ↑x` -- and no
iteration count, no fixed-point check, and not even a monotonicity proof, since `mono_of_coe`
extracts that from the bridge too. The lemma does not appear to be in Mathlib, which has Kleene's
theorem via `ωScottContinuous` (used in `Csg/ReachConverge.lean`) but nothing for the finite-height
case.
-/

namespace Comp

/-! ## The loop

Note where the two instances enter. The loop itself needs only `DecidableEq S`, which is the
comparison; `Fintype S` is needed exactly once, to supply the fuel, and is declared below at the
point where it starts being used. -/

variable {S : Type*} [DecidableEq S]

/-- Apply, compare, stop if nothing changed, otherwise recurse with one less fuel. Structural on the
    fuel, so the kernel can reduce it; the comparison is `DecidableEq (Finset S)`. -/
def fixAux (f : Finset S → Finset S) : ℕ → Finset S → Finset S
  | 0, x => x
  | n + 1, x => if f x = x then x else fixAux f n (f x)

@[simp]
theorem fixAux_zero (f : Finset S → Finset S) (x : Finset S) : fixAux f 0 x = x := rfl

theorem fixAux_succ (f : Finset S → Finset S) (n : ℕ) (x : Finset S) :
    fixAux f (n + 1) x = if f x = x then x else fixAux f n (f x) := rfl

/-! ## The loop never overshoots

The two halves of a fixed-point identification are asymmetric: one comes from being an iterate, the
other from a decidable check (see `Comp/Qualitative.lean`). These are the iterate halves, and the
point is that the loop supplies them without a count -- induction on the fuel, applying the
corresponding one-step lemma whenever the loop decides to keep going. -/

/-- Running the loop from a region above the greatest fixed point leaves one above it. -/
theorem gfp_le_coe_fixAux (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (n : ℕ) (x : Finset S)
    (hx : F.gfp ≤ (↑x : Set S)) :
    F.gfp ≤ (↑(fixAux f n x) : Set S) := by
  induction n generalizing x hx with
  | zero =>
      rw [fixAux_zero]
      exact hx
  | succ n ih =>
      rw [fixAux_succ]
      split_ifs with h
      · exact hx
      · exact ih (f x) (OrderHom.gfp_le_of_step F hx (hf x))

/-- The dual: running the loop from a region below the least fixed point leaves one below it. -/
theorem coe_fixAux_le_lfp (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (n : ℕ) (x : Finset S)
    (hx : (↑x : Set S) ≤ F.lfp) :
    (↑(fixAux f n x) : Set S) ≤ F.lfp := by
  induction n generalizing x hx with
  | zero =>
      rw [fixAux_zero]
      exact hx
  | succ n ih =>
      rw [fixAux_succ]
      split_ifs with h
      · exact hx
      · exact ih (f x) (OrderHom.le_lfp_of_step F hx (hf x))

omit [DecidableEq S] in
/-- Monotonicity is not a separate assumption: the bridge gives it, because `Finset.coe` is an
    order embedding and `F` is an `OrderHom`. This is what keeps `gfp_eq_coe_fixFrom_univ` down to
    a single hypothesis. -/
theorem mono_of_coe (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) : Monotone f := by
  intro x y hxy
  have h : (↑(f x) : Set S) ⊆ (↑(f y) : Set S) := by
    rw [hf, hf]
    exact F.monotone (Finset.coe_subset.mpr hxy)
  exact Finset.coe_subset.mp h

/-! ## …and so pins the fixed point

`Fintype S` enters here and nowhere above: the fuel is the only thing it is for. -/

variable [Fintype S]

/-- The loop with the fuel filled in from the type. `Fintype.card S` is a bound, not a count: the
    early exit means it is never exhausted in practice, and the kernel unfolds only as far as the
    computation actually goes. -/
def fixFrom (f : Finset S → Finset S) (x : Finset S) : Finset S :=
  fixAux f (Fintype.card S) x

omit [DecidableEq S] in
/-- The usual starting point for a `gfp`: everything. -/
theorem gfp_le_coe_univ (F : Set S →o Set S) : F.gfp ≤ (↑(Finset.univ : Finset S) : Set S) := by
  rw [Finset.coe_univ]
  exact le_top

omit [Fintype S] [DecidableEq S] in
/-- The usual starting point for an `lfp`: nothing. -/
theorem coe_empty_le_lfp (F : Set S →o Set S) : (↑(∅ : Finset S) : Set S) ≤ F.lfp := by
  rw [Finset.coe_empty]
  exact bot_le

/-- **The greatest fixed point, from a loop and a check.** No iteration count: the loop ran until it
    stopped, `gfp_le_coe_fixAux` says it did not overshoot, and `hfix` says where it stopped is
    fixed. -/
theorem gfp_eq_coe_fixFrom (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (x : Finset S)
    (hx : F.gfp ≤ (↑x : Set S)) (hfix : f (fixFrom f x) = fixFrom f x) :
    F.gfp = (↑(fixFrom f x) : Set S) := by
  have hge : F.gfp ≤ (↑(fixFrom f x) : Set S) := gfp_le_coe_fixAux F f hf _ x hx
  have hfixS : F (↑(fixFrom f x) : Set S) = (↑(fixFrom f x) : Set S) := by
    rw [← hf, hfix]
  exact (OrderHom.eq_gfp_of_fixed_of_ge F hfixS hge).symm

/-- The dual, for a least fixed point. -/
theorem lfp_eq_coe_fixFrom (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (x : Finset S)
    (hx : (↑x : Set S) ≤ F.lfp) (hfix : f (fixFrom f x) = fixFrom f x) :
    F.lfp = (↑(fixFrom f x) : Set S) := by
  have hle : (↑(fixFrom f x) : Set S) ≤ F.lfp := coe_fixAux_le_lfp F f hf _ x hx
  have hfixS : F (↑(fixFrom f x) : Set S) = (↑(fixFrom f x) : Set S) := by
    rw [← hf, hfix]
  exact (OrderHom.eq_lfp_of_fixed_of_le F hfixS hle).symm

/-! ## The fuel always suffices

The caller's remaining obligation, discharged. Two inductions on the fuel, each carrying one
cardinality invariant: a nonincreasing chain spends `card` and a nondecreasing one spends its
complement, and in both cases running out of fuel means running out of room to move. -/

/-- **A descending chain stops within `x.card` steps.** The invariant is `x.card ≤ n`: a step that
    changes anything is strict, so it costs at least one from the cardinality, and at `n = 0` the
    region is empty, where `f x ⊆ x` leaves `f x = x` the only option. -/
theorem fixAux_fixed_of_card_le (f : Finset S → Finset S) (hmono : Monotone f) (n : ℕ)
    (x : Finset S) (hx : f x ≤ x) (hcard : x.card ≤ n) :
    f (fixAux f n x) = fixAux f n x := by
  induction n generalizing x with
  | zero =>
      rw [fixAux_zero]
      have hx0 : x = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hx0
      exact Finset.subset_empty.mp hx
  | succ n ih =>
      rw [fixAux_succ]
      split_ifs with h
      · exact h
      · refine ih (f x) (hmono hx) ?_
        have hss : f x ⊂ x := Finset.ssubset_iff_subset_ne.mpr ⟨hx, h⟩
        have hlt := Finset.card_lt_card hss
        omega

/-- **The dual: an ascending chain stops within `card S - x.card` steps.** Same argument against the
    complement, and at `n = 0` the region is everything. -/
theorem fixAux_fixed_of_compl_card_le (f : Finset S → Finset S) (hmono : Monotone f) (n : ℕ)
    (x : Finset S) (hx : x ≤ f x) (hcard : Fintype.card S - x.card ≤ n) :
    f (fixAux f n x) = fixAux f n x := by
  induction n generalizing x with
  | zero =>
      rw [fixAux_zero]
      have hle : x.card ≤ Fintype.card S := by
        simpa only [Finset.card_univ] using Finset.card_le_univ x
      have hxu : x = Finset.univ := Finset.eq_univ_of_card x (by omega)
      subst hxu
      exact le_antisymm (Finset.subset_univ _) hx
  | succ n ih =>
      rw [fixAux_succ]
      split_ifs with h
      · exact h
      · refine ih (f x) (hmono hx) ?_
        have hss : x ⊂ f x := Finset.ssubset_iff_subset_ne.mpr ⟨hx, fun he => h he.symm⟩
        have hlt := Finset.card_lt_card hss
        have hle : (f x).card ≤ Fintype.card S := by
          simpa only [Finset.card_univ] using Finset.card_le_univ (f x)
        omega

/-- The loop from `⊤` always stops at a fixed point. The fuel is `Fintype.card S`, which is exactly
    `Finset.univ.card`, so the invariant holds at the start and the previous lemma does the rest. -/
theorem fixFrom_univ_fixed (f : Finset S → Finset S) (hmono : Monotone f) :
    f (fixFrom f Finset.univ) = fixFrom f Finset.univ :=
  fixAux_fixed_of_card_le f hmono _ _ (Finset.subset_univ _) (le_of_eq Finset.card_univ)

/-- The loop from `⊥` always stops at a fixed point. -/
theorem fixFrom_empty_fixed (f : Finset S → Finset S) (hmono : Monotone f) :
    f (fixFrom f ∅) = fixFrom f ∅ :=
  fixAux_fixed_of_compl_card_le f hmono _ _ (Finset.empty_subset _) (by simp)

/-! ## The interface, with nothing left to supply

What a caller writes. One hypothesis: the bridge between the computed step and the specification's
operator. Not a count, not a fixed-point check, not a monotonicity proof. -/

/-- **The greatest fixed point of `F`, as a computed `Finset`.** `gfp_le_coe_fixAux` keeps the loop
    above `F.gfp`, `fixFrom_univ_fixed` says it stopped, and `mono_of_coe` gets the monotonicity the
    latter needs out of the bridge -- so `hf` is the whole of what this asks for. -/
theorem gfp_eq_coe_fixFrom_univ (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) :
    F.gfp = (↑(fixFrom f Finset.univ) : Set S) :=
  gfp_eq_coe_fixFrom F f hf Finset.univ (gfp_le_coe_univ F)
    (fixFrom_univ_fixed f (mono_of_coe F f hf))

/-- The dual, for a least fixed point computed from `∅`. -/
theorem lfp_eq_coe_fixFrom_empty (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) :
    F.lfp = (↑(fixFrom f ∅) : Set S) :=
  lfp_eq_coe_fixFrom F f hf ∅ (coe_empty_le_lfp F) (fixFrom_empty_fixed f (mono_of_coe F f hf))

end Comp
