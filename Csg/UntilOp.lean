/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.CsgMonotone
import Csg.ReachOp

/-!
# The until Bellman operator, bundled as an `OrderHom`

**Status: everything in this file done, confirmed by a clean `lake build`, including
`reachOp_eq_untilOp_true` after one small fix round (see its own note below).**

Generalises `ReachOp.lean`'s reachability-only operator to a genuine `φ U goal` ("stay in `φ`
until `goal`") operator, per
`VERIFICATION-FRAMEWORK.md`'s temporal-shape axis: unbounded reachability is the special case
`φ := fun _ => True`, but `until` is the more expressive primitive most model-checking treatments
actually start from. Written as a sibling of `ReachOp.lean`, importing `CsgMonotone.lean` directly,
rather than on top of it -- there is no reachability-specific content either file needs from the
other.

**The per-state Bellman step**, `untilOpFun`, is a three-way case split instead of `reachOpFun`'s
two-way one: a `goal` state is worth `1` regardless of `safe` (reaching the goal always succeeds,
even on the very step `safe` would otherwise have failed -- absorption at the goal takes priority);
a state that is neither `goal` nor `safe` is a dead end, worth `0` (the "stay in `safe` until
`goal`" requirement has already been violated, so no continuation can recover); and a state that is
`safe` but not yet `goal` plays the stage game against the continuation, exactly as `reachOpFun`'s
one non-goal case already does. Both `goal` and `safe` are abstract, universally-quantified
predicates throughout this file (never instantiated to a concrete decidable proposition), so the
`by_cases` + `simp only [defName, if_pos h]`/`if_neg h` idiom `reachOpFun_mono` already uses is
safe here too -- the pitfall diagnosed while debugging `RockPaperScissorsLfp.lean` (`simp`
pre-normalising a *concrete* ground `ite` condition before considering a supplied `if_pos`/`if_neg`
lemma) only bites when the condition is closed and decidable by `decide`, which neither `goal s`
nor `safe s` is here.

**`reachOp_eq_untilOp_true`**, added once the three-way split above and a concrete instance
(`RockPaperScissorsUntil.lean`) were both confirmed building: `reachOp goal hr = untilOp (fun _ =>
True) goal hr`, recovering plain reachability as `until`'s special case with a trivially-always-safe
predicate. This mixes an abstract condition (`goal`, safe via the `by_cases`/`if_pos`/`if_neg` idiom
above) with a concrete one (`safe := fun _ => True`, closed and decidable) in the same proof --
exactly the combination flagged as risky before any confirmed `until` instance existed. Handled by
splitting the two concerns rather than fighting them together: `change` first jumps past the
`OrderHom`/`FunLike` coercion layer down to `reachOpFun`/`untilOpFun` application (a pure defeq
step, unrelated to either condition's truth value); *then* `by_cases hg : goal s` plus
`simp only [reachOpFun, untilOpFun, if_pos/if_neg hg]` handles the abstract `goal` condition exactly
as `untilOpFun_mono` already does safely.

One real fix round, confirmed by a clean `lake build` after it, and a genuinely new wrinkle on the
ground-normalisation pitfall: in the `goal`-false branch, `simp only` *did* rewrite the concrete
condition `(fun _ => True) s` down to `True` (unopposed, exactly as expected, since no lemma about
it was supplied) -- but left the goal stuck as `... = if True then A else B` rather than also
collapsing the `ite` down to `A`, since `simp only`'s automatic closing check apparently doesn't
perform the further iota reduction on `True`'s own `Decidable` instance the way a bare `rfl` does.
So the earlier documented pitfall was one instance of a slightly broader fact worth generalising:
`simp only`'s built-in ground-condition normalisation rewrites the *condition*, but reaching the
literal branch value can still need an explicit follow-up (`rfl` here; `simp only [rpsVStar]` played
the same role for a different residual gap in `RockPaperScissorsLfp.lean`). Fixed with a trailing
`rfl` after the `simp only` in the `goal`-false case alone -- the `goal`-true case needed no such
follow-up, since `untilOpFun`'s `goal` branch is pinned to `1` without ever consulting `safe` at
all, so `if_pos hg` alone already leaves both sides at the same literal value.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-- The until Bellman step, on `S → Set.Icc (0 : ℝ) 1`: a `goal` state is worth `1` regardless of
    `safe` or the continuation (absorption at the goal takes priority over a `safe` violation at
    the same state); a state that is neither `goal` nor `safe` is a dead end, worth `0` (the "stay
    in `safe` until `goal`" requirement is already broken, no continuation can recover); any other
    state (`safe`, not yet `goal`) plays its stage game against the continuation, packaged back
    into `[0, 1]` via `stageValue_nonneg`/`_le_one` exactly as `reachOpFun`'s own non-goal case
    does. Named `untilOpFun` rather than `untilOp` itself so the monotonicity proof below
    (`untilOpFun_mono`) can refer to it by name before it's bundled into an `OrderHom`. -/
noncomputable def untilOpFun (safe goal : S → Prop) [DecidablePred safe] [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) : Set.Icc (0 : ℝ) 1 :=
  if goal s then ⟨1, by norm_num, by norm_num⟩
  else if safe s then ⟨C.stageValue s (fun s' => (v s' : ℝ)),
    C.stageValue_nonneg hr (fun s' => (v s').2.1), C.stageValue_le_one hr (fun s' => (v s').2.2)⟩
  else ⟨0, by norm_num, by norm_num⟩

/-- **The payoff.** `untilOpFun` is monotone in the continuation `v` -- `goal` states are pinned to
    the constant `1` regardless of `v` (trivially monotone), dead-end states (neither `goal` nor
    `safe`) are pinned to the constant `0` (also trivially monotone), and every remaining state's
    value is `stageValue_mono` applied to the pointwise hypothesis, unwrapped from
    `Set.Icc (0 : ℝ) 1`'s order back to `≤` on `ℝ` by definitional unfolding -- the same nested
    `by_cases` + `simp only [untilOpFun, if_pos h]`/`if_neg h` idiom `reachOpFun_mono` already uses,
    safe here since both `goal` and `safe` are abstract predicates, never concrete decidable
    propositions `simp` could ground-normalise out from under a supplied `if_pos`/`if_neg`. -/
theorem untilOpFun_mono (safe goal : S → Prop) [DecidablePred safe] [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    Monotone (C.untilOpFun safe goal hr) := by
  intro v w hvw s
  by_cases hg : goal s
  · have heq : C.untilOpFun safe goal hr v s = C.untilOpFun safe goal hr w s := by
      simp only [untilOpFun, if_pos hg]
    exact heq.le
  · by_cases hs : safe s
    · simp only [untilOpFun, if_neg hg, if_pos hs]
      exact C.stageValue_mono fun s' => hvw s'
    · have heq : C.untilOpFun safe goal hr v s = C.untilOpFun safe goal hr w s := by
        simp only [untilOpFun, if_neg hg, if_neg hs]
      exact heq.le

/-- **The payoff.** The until Bellman operator, bundled as an `OrderHom` on the complete lattice
    `S → Set.Icc (0 : ℝ) 1` -- `untilOpFun` plus its own monotonicity proof, mirroring `reachOp`'s
    structure exactly. Existence of a least (and greatest) fixed point is free the moment this
    definition typechecks, same as `reachOp`. Relating `(C.untilOp safe goal hr).lfp` to a bounded
    `until` sequence, and computing further concrete instances beyond `RockPaperScissorsUntil.lean`,
    are left for follow-up work; recovering `reachOp` as the special case `safe := fun _ => True` is
    `reachOp_eq_untilOp_true` below. -/
noncomputable def untilOp (safe goal : S → Prop) [DecidablePred safe] [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.untilOpFun safe goal hr
  monotone' := C.untilOpFun_mono safe goal hr

/-- **The payoff, fully general.** Plain reachability is `until`'s special case with a trivially
    always-safe predicate -- `reachOp` and `untilOp (fun _ => True)` are *the same operator*, not
    merely operators that happen to agree on one instance (`RockPaperScissorsUntil.lean`'s own
    `rpsCSG_untilOp_lfp_eq_reachOp_lfp` was exactly that weaker, instance-specific fact; this is the
    statement it was concrete evidence for). `change` jumps past the `OrderHom`/`FunLike` coercion
    to bare `reachOpFun`/`untilOpFun` application (pure defeq, independent of either condition's
    truth value); `by_cases hg : goal s` plus
    `simp only [reachOpFun, untilOpFun, if_pos/if_neg hg]` then handles the abstract `goal`
    condition, the same idiom `untilOpFun_mono` already uses safely.
    The concrete condition `(fun _ => True) s` is never named in a supplied lemma -- left for
    `simp`'s own ground-decidable normalisation to collapse unopposed, which is exactly what closes
    the `if_neg hg` branch once `goal`'s split is out of the way. -/
theorem reachOp_eq_untilOp_true (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    C.reachOp goal hr = C.untilOp (fun _ => True) goal hr := by
  apply OrderHom.ext
  funext v
  funext s
  apply Subtype.ext
  change (C.reachOpFun goal hr v s : ℝ) = (C.untilOpFun (fun _ => True) goal hr v s : ℝ)
  by_cases hg : goal s
  · simp only [reachOpFun, untilOpFun, if_pos hg]
  · simp only [reachOpFun, untilOpFun, if_neg hg]
    rfl

end CSG
end Csg
