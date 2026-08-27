/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.ReachOp
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Stage 3: the reachability operator is `ωScottContinuous`, and the convergence theorem

**Status: done, confirmed by a clean `lake build`, first attempt, no fix round needed.** Stage 3 of
the infinite-horizon build order (`PHASE0-NOTES.md`): shows `C.reachOp goal hr` (`ReachOp.lean`) is
`ωScottContinuous`, using
`stageValue_lipschitz` (`CsgMonotone.lean`) to bridge pointwise monotone convergence of a chain to
convergence of the operator applied along it, then invokes Mathlib's Kleene fixed-point theorem
(`OrderHom.lfp_eq_sSup_iterate`) to conclude `(C.reachOp goal hr).lfp` -- the least fixed point
Knaster-Tarski already hands us for free, the moment `ReachOp.lean` typechecks -- equals
`⨆ n, (C.reachOp goal hr)^[n] ⊥`, the naive Kleene iterate sequence starting from `⊥`. That is
the actual convergence guarantee this build order has been working towards: unrolling the
reachability step finitely often, in the limit, reaches the same value Knaster-Tarski already
promised existed in the abstract.

`Set.Icc (0:ℝ) 1` needs `[Fact ((0:ℝ) ≤ 1)]` in scope to get Mathlib's `CompleteLattice`
instance (`Set.Icc.completeLattice`, `Mathlib/Order/CompleteLatticeIntervals.lean` -- confirmed
directly against the cached source, not guessed: it is stated with an explicit `[Fact (a ≤ b)]`
argument, not derived automatically from `a ≤ b` being true). `ReachOp.lean` never needed this
instance, since building an `OrderHom` needs no more than a `Preorder` on either side; this file is
the first to actually reason about `ωSup`/call `.lfp`, so the instance is registered here, once,
for every `CSG` at once (it does not depend on `S`/`A1`/`A2`/`C`).

The main lemma, `reachOp_ωScottContinuous`, goes through `ωScottContinuous_iff_map_ωSup_of_orderHom`
(`f (ωSup c) = ωSup (c.map f)` for every chain `c`) and `funext`, reducing to one state `s` at a
time:

- `goal s` holds: both sides are the constant `1` regardless of the chain -- `reachOpFun`'s own
  `if` branch, no continuity argument needed, just `le_antisymm` against `le_ωSup`/`ωSup_le`.
- `goal s` fails: both sides unfold to `stageValue s` applied to a continuation, and `ωSup`'s value
  at `s` is exactly the pointwise supremum of the chain at `s` (`Set.Icc.coe_iSup`, plus the
  Pi-type/`CompleteLattice` unfolding of `ωSup` itself, both by `rfl`). `S` being a `Fintype` lets
  `Filter.eventually_all` turn finitely many individual pointwise-convergence facts (one per state,
  from `tendsto_atTop_ciSup` applied to each monotone bounded real sequence `n ↦ (c n) s'`) into one
  bound uniform across every state at once, which `stageValue_lipschitz` then turns into a bound on
  `stageValue` itself. `le_of_forall_sub_le` closes the analytic direction (the limit's `stageValue`
  is at most the naive iterate's supremum, up to any `ε`); the reverse direction (the naive iterate
  never overshoots the limit) is a direct consequence of `stageValue_mono` alone, no analysis
  needed.
-/

namespace Csg

noncomputable instance : Fact ((0 : ℝ) ≤ 1) := ⟨by norm_num⟩

namespace CSG

open OmegaCompletePartialOrder Filter Topology

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- Finite-index "monotone convergence is eventually uniform": if `d n s'` tends to `g s'` for
    every `s'` ranging over a `Fintype`, there is a single `N` past which `d n` is within any given
    `δ` of `g` at *every* state at once, not just eventually at each state separately.
    `Filter.eventually_all` (needs `Finite S`, which `Fintype S` gives) is exactly the fact that
    lets finitely many individual `∀ᶠ` statements swap into one `∀ᶠ` of the conjunction -- the only
    place in this file `S`'s finiteness, rather than just its being a `Fintype`, earns its keep. -/
theorem exists_forall_le_add_of_tendsto {g : S → ℝ} {d : ℕ → S → ℝ}
    (htendsto : ∀ s', Tendsto (fun n => d n s') atTop (𝓝 (g s'))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ n ≥ N, ∀ s', g s' ≤ d n s' + δ := by
  have h1 : ∀ s', ∀ᶠ n in atTop, g s' - δ < d n s' := fun s' =>
    (tendsto_order.mp (htendsto s')).1 (g s' - δ) (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr h1)
  exact ⟨N, fun n hn s' => by linarith [hN n hn s']⟩

/-- **The payoff.** The reachability Bellman operator is `ωScottContinuous`: applying it to a
    chain's supremum gives the same answer as taking the supremum of applying it along the chain.
    Exactly Kleene's fixed-point theorem's hypothesis (`OrderHom.lfp_eq_sSup_iterate`). -/
theorem reachOp_ωScottContinuous (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    ωScottContinuous (C.reachOp goal hr) := by
  rw [ωScottContinuous_iff_map_ωSup_of_orderHom]
  intro c
  funext s
  by_cases hgoal : goal s
  · -- `goal s`: both sides are the constant `1`, regardless of the chain.
    have hterm : ∀ n, (c.map (C.reachOp goal hr)) n s
        = (⟨1, by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
      intro n
      show C.reachOpFun goal hr (c n) s = _
      simp only [reachOpFun, if_pos hgoal]
    have hLHS : C.reachOp goal hr (ωSup c) s
        = (⟨1, by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
      show C.reachOpFun goal hr (ωSup c) s = _
      simp only [reachOpFun, if_pos hgoal]
    have hRHS : ωSup (c.map (C.reachOp goal hr)) s
        = (⟨1, by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
      refine le_antisymm (ωSup_le _ _ fun n => (hterm n).le) ?_
      rw [← hterm 0]
      exact le_ωSup _ 0
    rw [hLHS, hRHS]
  · -- `¬ goal s`: reduces to `stageValue`'s continuity along the chain.
    apply Subtype.ext
    set g : S → ℝ := fun s' => ((ωSup c) s' : ℝ) with hg_def
    set d : ℕ → S → ℝ := fun n s' => ((c n) s' : ℝ) with hd_def
    have hle_g : ∀ n s', d n s' ≤ g s' := fun n s' => le_ωSup c n s'
    have hg_eq : ∀ s', g s' = ⨆ n, d n s' := by
      intro s'
      show ((ωSup c) s' : ℝ) = ⨆ n, d n s'
      have hpt : (ωSup c) s' = ⨆ n, (c n) s' := rfl
      rw [hpt, Set.Icc.coe_iSup (by norm_num : (0 : ℝ) ≤ 1)]
    have hmono : ∀ s', Monotone (fun n => d n s') := fun s' _ _ hnm =>
      OrderHomClass.mono c hnm s'
    have hbdd1 : ∀ s', BddAbove (Set.range (fun n => d n s')) :=
      fun s' => ⟨1, by rintro _ ⟨n, rfl⟩; exact (c n s').2.2⟩
    have htendsto : ∀ s', Tendsto (fun n => d n s') atTop (𝓝 (g s')) := fun s' => by
      rw [hg_eq s']
      exact tendsto_atTop_ciSup (hmono s') (hbdd1 s')
    have hstage_bdd : BddAbove (Set.range (fun n => C.stageValue s (d n))) :=
      ⟨1, by rintro _ ⟨n, rfl⟩; exact C.stageValue_le_one hr fun s' => (c n s').2.2⟩
    have hkey : C.stageValue s g = ⨆ n, C.stageValue s (d n) := by
      refine le_antisymm (le_of_forall_sub_le fun ε hε => ?_) (ciSup_le fun n => ?_)
      · obtain ⟨N, hN⟩ := exists_forall_le_add_of_tendsto htendsto hε
        have hbound : ∀ s', |g s' - d N s'| ≤ ε := fun s' =>
          abs_le.mpr ⟨by linarith [hle_g N s'], by linarith [hN N le_rfl s']⟩
        have hlip := abs_le.mp (C.stageValue_lipschitz hε.le hbound)
        have hNle : C.stageValue s (d N) ≤ ⨆ n, C.stageValue s (d n) := le_ciSup hstage_bdd N
        linarith [hlip.1]
      · exact C.stageValue_mono fun s' => hle_g n s'
    show (C.reachOp goal hr (ωSup c) s : ℝ) = (ωSup (c.map (C.reachOp goal hr)) s : ℝ)
    have hLHS_eq : (C.reachOp goal hr (ωSup c) s : ℝ) = C.stageValue s g := by
      show (C.reachOpFun goal hr (ωSup c) s : ℝ) = _
      simp only [reachOpFun, if_neg hgoal]
    have hRHS_eq : (ωSup (c.map (C.reachOp goal hr)) s : ℝ) = ⨆ n, C.stageValue s (d n) := by
      have hpt : (ωSup (c.map (C.reachOp goal hr)) s : Set.Icc (0 : ℝ) 1)
          = ⨆ n, (c.map (C.reachOp goal hr)) n s := rfl
      rw [hpt, Set.Icc.coe_iSup (by norm_num : (0 : ℝ) ≤ 1)]
      congr 1
      funext n
      show (C.reachOpFun goal hr (c n) s : ℝ) = _
      simp only [reachOpFun, if_neg hgoal]
    rw [hLHS_eq, hRHS_eq, hkey]

/-- **Stage 3, the payoff.** `(C.reachOp goal hr).lfp` -- Knaster-Tarski's least fixed point,
    already available for free the moment `ReachOp.lean` typechecks -- is genuinely the limit of
    the naive iterate sequence starting from `⊥`: Kleene's fixed-point theorem
    (`OrderHom.lfp_eq_sSup_iterate`), applicable now that `reachOp_ωScottContinuous` supplies its
    hypothesis. This upgrades `VERIFICATION-FRAMEWORK.md`'s "numeric iterate, undiscounted" row from
    open to done, with no computable convergence *rate* attached (Kleene's theorem gives none). -/
theorem reachOp_lfp_eq_sSup_iterate (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (C.reachOp goal hr).lfp = ⨆ n, (C.reachOp goal hr)^[n] ⊥ :=
  OrderHom.lfp_eq_sSup_iterate (C.reachOp_ωScottContinuous goal hr)

end CSG
end Csg
