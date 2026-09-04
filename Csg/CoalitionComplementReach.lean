/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.CoalitionComplement
import Csg.ReachOp

/-!
# `⟨⟨C⟩⟩P_min =?[F goal]` and `⟨⟨Cᶜ⟩⟩P_max =?[F goal]` agree

**Status: confirmed by a clean `lake build`, first attempt -- no fix round needed.** The lift
`CoalitionComplement.lean`'s own docstring named as "free once [`reduceMin_stageValue_eq`] holds
(`reachOp`'s own type doesn't mention the action types at all)": this file states and proves the
actual `n`-player identity `Csg/Coalition.lean` promised under "Not attempted here" --
`⟨⟨C⟩⟩P_min` and `⟨⟨Cᶜ⟩⟩P_max` are the *same* reachability fixed point, for any coalition `C`
and any reward-free `NCSG`.

**Why this is free, not a new argument.** `CSG.reachOp goal hr : (S → Set.Icc (0:ℝ) 1) →o
(S → Set.Icc (0:ℝ) 1)` is an `OrderHom` whose *type* depends only on `S`, never on the underlying
`CSG`'s action types `A1`/`A2` -- unlike `MatrixGame.value`, which lives at a different type for
every choice of row/column index type and needed `MatrixGameCongr`/`MatrixGameCongrCol`'s explicit
`Equiv` transport machinery to compare across index types at all. So `(G.reduceMax Cᶜ).reachOp` and
`(G.reduceMin C).reachOp` are two terms of the *literally same* `OrderHom` type, directly comparable
by plain equality with no relabelling step needed -- all the relabelling work
`reduceMin_stageValue_eq` already did (via `MatrixGameCongr.value_relabelRow`) stays entirely inside
the proof of the one pointwise fact this file needs, and never resurfaces at this level.

**The shape of the argument**, three steps:

1. `reduceMin_reachOpFun_eq`: the two operators' underlying functions agree pointwise, at every
   continuation `v` and state `s`. Case split on `goal s`: the `goal`-state branch is the constant
   `1` on both sides regardless of which reduced game it came from (`if_pos`/`if_neg` used as
   rewrite lemmas rather than relying on kernel reduction of an `ite` on the ambient, uninstantiated
   `[DecidablePred goal]` instance -- exactly the workaround `CoalitionComplement.lean`'s own
   `combine_compl` fix (Round 1) already established for the analogous `dite`-on-abstract-`Finset`
   problem); the other branch is `reduceMin_stageValue_eq` itself, transported across the
   `Set.Icc (0:ℝ) 1` `Subtype` wrapper via `Subtype.ext`.
2. `reduceMin_reachOp_eq`: the two `OrderHom`s themselves are equal, not just their values --
   `OrderHom.ext` (`Mathlib.Order.Hom.Basic`) reduces `OrderHom` equality to equality of the
   underlying functions, discarding the two (unequal-looking, but propositionally irrelevant since
   `Monotone` is a `Prop`) monotonicity proofs automatically; `funext` twice plus (1) closes it.
3. `reduceMin_reachOp_lfp_eq`: **the actual theorem.** `congrArg (fun f => f.lfp)` applied to (2) --
   equal `OrderHom`s have equal least fixed points by definition, no Knaster-Tarski-specific
   argument needed at all. This is `⟨⟨Cᶜ⟩⟩P_max =?[F goal] = ⟨⟨C⟩⟩P_min =?[F goal]`, the general
   `n`-player identity, for the first time at the reachability-fixed-point level rather than just
   one stage.
-/

namespace Csg
namespace NCSG

variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

variable (C : Finset Players) (G : NCSG S Players A)

/-- The two reduced games' reachability step functions agree pointwise, at every continuation and
    state -- the `goal`-state branch is trivially the same constant `1` on both sides, and the
    other branch is `reduceMin_stageValue_eq` itself, read through the `Set.Icc (0:ℝ) 1` wrapper
    via `Subtype.ext`. -/
theorem reduceMin_reachOpFun_eq (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a, G.r s a = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (G.reduceMax Cᶜ).reachOpFun goal (G.reduceMax_r_zero Cᶜ hr) v s =
      (G.reduceMin C).reachOpFun goal (G.reduceMin_r_zero C hr) v s := by
  by_cases h : goal s
  · simp only [CSG.reachOpFun, if_pos h]
  · simp only [CSG.reachOpFun, if_neg h]
    exact Subtype.ext (reduceMin_stageValue_eq C G s (fun s' => (v s' : ℝ)))

/-- **The payoff.** The two reduced games' reachability Bellman operators are the *same*
    `OrderHom` on `S → Set.Icc (0:ℝ) 1` -- not merely operators with equal values, but literally
    equal terms, via `OrderHom.ext` applied to `reduceMin_reachOpFun_eq`. -/
theorem reduceMin_reachOp_eq (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a, G.r s a = 0) :
    (G.reduceMax Cᶜ).reachOp goal (G.reduceMax_r_zero Cᶜ hr) =
      (G.reduceMin C).reachOp goal (G.reduceMin_r_zero C hr) := by
  apply OrderHom.ext
  funext v s
  exact reduceMin_reachOpFun_eq C G goal hr v s

/-- **The actual `n`-player theorem**, at the reachability fixed point: `⟨⟨C⟩⟩P_min =?[F goal]` and
    `⟨⟨Cᶜ⟩⟩P_max =?[F goal]` are the *same* least fixed point, for any coalition `C` of any
    `Players`-indexed game and any reward-free `NCSG` (`G.r ≡ 0`, the hypothesis every reachability
    instance in this project already satisfies). Immediate from `reduceMin_reachOp_eq`: equal
    `OrderHom`s have equal `.lfp`s by definition. -/
theorem reduceMin_reachOp_lfp_eq (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a, G.r s a = 0) :
    ((G.reduceMax Cᶜ).reachOp goal (G.reduceMax_r_zero Cᶜ hr)).lfp =
      ((G.reduceMin C).reachOp goal (G.reduceMin_r_zero C hr)).lfp :=
  congrArg (fun f => f.lfp) (reduceMin_reachOp_eq C G goal hr)

end NCSG
end Csg
