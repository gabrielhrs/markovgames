/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Coalition

/-!
# `⟨⟨Cᶜ⟩⟩P_max`'s stage value equals `⟨⟨C⟩⟩P_min`'s

**Status: confirmed by a clean `lake build`, after one real fix round (see below) -- clean meaning
no errors; two harmless unused-instance lint warnings remain, deliberately left in rather than
risk an untested syntax fix for pure lint noise, same call as `MatrixGameCongr.lean`'s own Round
2.** Second and larger of the two pieces
`Csg/Coalition.lean`'s own docstring named as missing (`MatrixGameCongr.lean` was the first): the
complement bookkeeping, and the one place it actually needs `value_relabelRow` rather than pure
type-level rewriting. Stops at `stageValue` equality, one state and one continuation at a time --
lifting that to `reachOp`/`.lfp` equality (and so to the actual `⟨⟨C⟩⟩P_min = ⟨⟨Cᶜ⟩⟩P_max` theorem
promised in `Coalition.lean`'s "Not attempted here") is free once this holds (`reachOp`'s own type
doesn't mention the action types at all), but is deliberately not attempted in this file -- a
separate, smaller artifact once this one is confirmed clean, matching how `MatrixGameCongr.lean`
was kept to exactly the one lemma it needed to be.

**The shape of the argument**, all bookkeeping except one real step:

1. `mem_compl_compl`: `Cᶜᶜ` and `C` have the same members (`i ∈ Cᶜᶜ ↔ i ∈ C`, from
   `Finset.mem_compl` applied twice -- no `Finset.compl_compl` equality-of-`Finset`s needed at
   all).
2. `complCoalitionEquiv`: so `ComplementAction A Cᶜ` (`= Π i : Cᶜᶜ, A i`) and `CoalitionAction A C`
   (`= Π i : C, A i`) are in bijection via the identity on the underlying player, only the attached
   membership proof changing -- `left_inv`/`right_inv` both close by `rfl` alone, Lean's
   kernel-level proof irrelevance on the `Prop`-valued membership component doing all the work, no
   `Subtype.ext` needed explicitly.
3. `combine_compl`: `combine Cᶜ y x` and `combine C (complCoalitionEquiv C x) y` rebuild the exact
   same joint action -- a `by_cases i ∈ C` split, `Finset.mem_compl` deciding the other `dite`'s
   condition in each branch, same proof-irrelevance closing.
4. `reduceMin_stageValue_eq`: lifts (3) through `G.K`/`G.r` to show `(G.reduceMax Cᶜ).stageGame s
   v` is literally `((G.reduceMin C).stageGame s v).relabelRow (complCoalitionEquiv C)` (same
   payoff matrix, rows relabelled) -- the *only* place `MatrixGameCongr.value_relabelRow` gets
   used, and the one step that isn't pure bookkeeping: without it, there would be no reason the two
   reduced games' *values* (as opposed to their payoff matrices) agree.

The column side needs nothing from `MatrixGameCongr`: `ComplementAction A C` and
`CoalitionAction A Cᶜ` are the same `abbrev` unfolding already, exactly as `Csg/Coalition.lean`'s
own docstring noted.

**Round 1, from real `lake build` output:** two independent issues.

First, `combine_compl`'s original proof tried `show`-ing the goal past `combine`'s `dite` directly
to the two branches' bodies, then closing with `rfl` (the same idiom `MatrixGameCongr.lean`'s
`payoff_relabelRow` and this project's own `RockPaperScissorsLfp.lean` use for `ite`/`OrderHom`
packaging). It failed here: `RockPaperScissorsLfp.lean`'s concrete states (`RPSState.win1`, ...)
let their `ite` reduce by pure computation once the branch is fixed, but `combine`'s `dite` is on
`i ∈ C` for an arbitrary, uninstantiated `C : Finset Players` -- its `Decidable` instance has
nothing concrete to compute down to, so the kernel can't reduce the `dite` by `whnf` alone, and
`show` (which needs definitional equality, not just propositional) failed with a clear "not
definitionally equal to target" error rather than something silent. Fixed by going back to
`dif_pos`/`dif_neg` as rewrite *lemmas* (propositional, not relying on the instance computing) fed
to `simp`, which also unfolds `complCoalitionEquiv` and closes the resulting proof-irrelevance
equality automatically -- the approach the module docstring's own numbered list above already
described, restored here after a detour through `show`/`rfl` that this error correctly rejected.

Second, `reduceMin_stageValue_eq`'s `ext x y` step failed outright: "No applicable extensionality
theorem found for type `MatrixGame ...`" -- confirming the module docstring's own stated
uncertainty about whether `MatrixGame` has an auto-registered `@[ext]` lemma the `ext` *tactic*
(as opposed to a directly-named lemma) can find; it does not. Fixed without depending on any
`MatrixGame`-specific extensionality lemma at all: proved the two games' `.A` fields equal via
plain `funext`, then closed the actual `MatrixGame` equality with `congrArg MatrixGame.mk` against
that -- `G = MatrixGame.mk G.A` holds by Lean's own structure eta for the one-field structure, so
`congrArg MatrixGame.mk (hA : G1.A = G2.A) : MatrixGame.mk G1.A = MatrixGame.mk G2.A` already *is*
`G1 = G2` up to that eta, with no separate lemma name to get right.

Also dropped an unused `Finset.mem_compl` argument from two `simp` calls (real build feedback, a
one-line fix), and left in two remaining linter warnings (`combine_compl` not needing
`Fintype`/`DecidableEq` on the action types) rather than risk another untested `omit`/argument-list
fix for pure lint noise -- the same call `MatrixGameCongr.lean`'s own Round 2 made.
-/

namespace Csg
namespace NCSG

variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

variable (C : Finset Players)

/-- `Cᶜᶜ` and `C` have exactly the same members -- the propositional heart of
    `Finset.compl_compl`, from `Finset.mem_compl` applied twice rather than an equality of
    `Finset`s, so it can drive a `Subtype` reindexing directly with no `cast`/`Eq.rec` anywhere. -/
theorem mem_compl_compl (i : Players) : i ∈ (C : Finset Players)ᶜᶜ ↔ i ∈ C := by
  simp [Finset.mem_compl]

/-- A coalition's joint action and its complement-of-complement's joint action are the same thing,
    named two different ways: the identity on the underlying player, only the attached membership
    proof changes. `left_inv`/`right_inv` close by `rfl` alone -- Lean's kernel-level proof
    irrelevance on the `Prop`-valued membership component of the `Subtype` does all the work. -/
def complCoalitionEquiv : ComplementAction A Cᶜ ≃ CoalitionAction A C where
  toFun x i := x ⟨i.1, (mem_compl_compl C i.1).mpr i.2⟩
  invFun y i := y ⟨i.1, (mem_compl_compl C i.1).mp i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `combine`, run on `C` and on its complement, rebuilds the exact same joint action either way --
    the case split is on the same fact (`i ∈ C` versus `i ∈ Cᶜ`) either way, `Finset.mem_compl`
    deciding one `dite`'s condition from the other's in each branch, closing by the same
    proof-irrelevance `rfl` `complCoalitionEquiv` itself relies on. -/
theorem combine_compl (y : ComplementAction A C) (x : ComplementAction A Cᶜ) :
    combine Cᶜ y x = combine C (complCoalitionEquiv C x) y := by
  funext i
  by_cases h : i ∈ C
  · have h' : i ∉ Cᶜ := by simp [h]
    simp [combine, complCoalitionEquiv, dif_pos h, dif_neg h']
  · have h' : i ∈ Cᶜ := by simp [h]
    simp [combine, dif_neg h, dif_pos h']

variable (G : NCSG S Players A)

/-- A single `G.r ≡ 0` hypothesis on the underlying `n`-player game gives `reduceMin C`'s own
    `r ≡ 0` for free -- convenience for callers who'd otherwise have to restate the same fact
    twice, once per reduction. -/
theorem reduceMin_r_zero (hrG : ∀ s a, G.r s a = 0) :
    ∀ s a1 a2, (G.reduceMin C).r s a1 a2 = 0 := fun s _ _ => hrG s _

/-- The `reduceMax` counterpart of `reduceMin_r_zero`. -/
theorem reduceMax_r_zero (hrG : ∀ s a, G.r s a = 0) :
    ∀ s a1 a2, (G.reduceMax C).r s a1 a2 = 0 := fun s _ _ => hrG s _

/-- **The one real step.** `⟨⟨Cᶜ⟩⟩P_max`'s stage game at `s` against continuation `v` is literally
    `⟨⟨C⟩⟩P_min`'s own stage game, rows relabelled by `complCoalitionEquiv C` -- `combine_compl`
    lifted through `G.K`/`G.r`. `MatrixGameCongr.value_relabelRow` then reads the two stage
    *values* off as equal, not just the payoff matrices. -/
theorem reduceMin_stageValue_eq (s : S) (v : S → ℝ) :
    (G.reduceMax Cᶜ).stageValue s v = (G.reduceMin C).stageValue s v := by
  have hA : ((G.reduceMax Cᶜ).stageGame s v).A =
      (((G.reduceMin C).stageGame s v).relabelRow (complCoalitionEquiv C)).A := by
    funext x y
    show G.r s (combine Cᶜ y x) +
        ∑ s', (G.K s (combine Cᶜ y x) s').toReal * v s' =
      G.r s (combine C (complCoalitionEquiv C x) y) +
        ∑ s', (G.K s (combine C (complCoalitionEquiv C x) y) s').toReal * v s'
    rw [combine_compl C y x]
  have hgame : (G.reduceMax Cᶜ).stageGame s v =
      ((G.reduceMin C).stageGame s v).relabelRow (complCoalitionEquiv C) :=
    congrArg MatrixGame.mk hA
  unfold CSG.stageValue
  rw [hgame, MatrixGame.value_relabelRow]

end NCSG
end Csg
