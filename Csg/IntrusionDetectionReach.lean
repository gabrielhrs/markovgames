/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.IntrusionDetection
import Csg.ReachCertificate

/-!
# A genuine reachability instance on the IDS model, separate from `bwInd`'s reward question

**Status: done, confirmed by a clean `lake build`, after two real fix rounds** -- both
`MatrixGame.value_le_of_forall_le`/`le_value_of_forall_le` take their matrix game as an *explicit*
argument, not one inferred from the proof term, fixed with dot notation (the same pitfall
`RockPaperScissorsLfp.lean` hit with the analogous Knaster-Tarski lemmas); and, in `idsVStar_fixed`,
`simp only [idsVStar]` rewrote the goal's `fun s' => (idsVStar s' : ℝ)` down to `fun s' => 1` while
`hle`/`hge` still carried the un-rewritten form, leaving `linarith` looking at two syntactically
different `.value` atoms for the same real number -- fixed by pinning `idsVStar .compromised = 1`
as its own fact and rewriting only the goal's right-hand side, so the `.value` term itself stays
untouched and matches `hle`/`hge` exactly. A `show`-vs-`change` style-linter nit was also cleaned
up along the way (`show` was silently unfolding `reachOp`, which is exactly what `change` is for).

`IntrusionDetection.lean` asks a *reward* question of this model: how much cumulative damage does
optimal play produce (`bwInd`). This file asks a completely different, plain *reachability*
question about the exact same transition structure: ignoring damage entirely, can the defender
guarantee the system returns to `healthy`, no matter what the attacker does? That is squarely a
`P[F healthy]`-style property in rPATL's sense -- the same restricted, single-path-operator
fragment `ReachOp.lean`/`ReachCertificate.lean` already implement, just a new instance of it, not
new scope. (A genuinely stronger claim -- `healthy` recurs *infinitely often*, `P[G F healthy]` --
is full LTL, outside rPATL's syntax and this project's whole fixed-point architecture; it would
need an automata-theoretic model-checking technique this project doesn't have, and is deliberately
not attempted here. See `PHASE0-NOTES.md` for the fuller discussion of that boundary.)

`reachOp` needs a reward-free `CSG` (`hr : C.r ≡ 0`), so this file pairs `IntrusionDetection.lean`'s
`idsK` with a fresh, all-zero reward function, `idsGameCSG` -- the *same* transitions, a different
question about them.

**The key fact, worked out by hand first.** `idsK` is state-independent: the next state depends
only on the joint action, not on whether play started at `healthy` or `compromised`
(`IntrusionDetection.lean`'s own `idsNext`). If the defender fixes the *uniform* mixed strategy
(`defend1`/`defend2` each with probability `1/2`) every round, then regardless of the attacker's
response `q` (any mixed strategy at all, not just a fixed one), `P(next = healthy) = 1/2`: writing
out the four joint-action probabilities, the attacker's choice `q` cancels out completely, exactly
the same "uniform mixing decouples the opponent's move" phenomenon `unif3`
(`RockPaperScissors.lean`) and `unif2` (`MatchingPennies.lean`) already exploit elsewhere in this
project, rediscovered fresh for a structurally different (non-absorbing, cyclic) game. Reaching
`healthy` is therefore a sequence of independent fair coin flips under this fixed defender policy,
so the probability of never reaching it in `n` rounds is `(1/2)^n → 0` -- reachability probability
`1`, from either state.

**Turning that into an exact-pinning certificate**, the same technique
`RockPaperScissorsLfp.lean` uses: the constant candidate `idsVStar ≡ 1` is *trivially* a fixed point
of `reachOp` for *any* reward-free `CSG` at all (expected continuation value against the constant
`1` is always exactly `1`, since a `PMF`'s probabilities always sum to `1` -- no IDS-specific
argument needed for this half). The real content is in showing it is the *least* one: for an
arbitrary pre-fixed point `b`, `compromised`'s stage game against continuation `b` turns out to be
the symmetric matrix `[[b healthy, b compromised], [b compromised, b healthy]]` (from `idsNext`'s
own structure), and the *same* uniform strategy pins this matrix's value down to exactly
`(b healthy + b compromised) / 2` -- both players' own uniform strategies make the opponent's
response irrelevant, the same two-sided `value_unique` argument
`RockPaperScissors.lean`'s `rpsCSG_stageValue_initial` already uses. Combined with the pre-fixed-
point inequality and `b healthy = 1` (forced by goal absorption), this forces `b compromised ≥ 1`,
hence `= 1`.
-/

namespace Csg

/-- Reward-free companion to `idsCSG`, sharing its transition kernel `idsK`: used to ask a
    genuinely different question about the same model than `bwInd` does (see this file's own
    docstring), which needs a `hr : C.r ≡ 0` hypothesis `idsCSG` itself doesn't satisfy. -/
noncomputable def idsGameCSG : CSG IDSState PolicyAction AttackAction where
  K := idsK
  r := fun _ _ _ => 0

theorem idsGameCSG_r_zero (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction) :
    idsGameCSG.r s a1 a2 = 0 := rfl

/-- Reach `healthy`, from either state. `abbrev`, not `def` -- same `DecidablePred` typeclass-
    synthesis reason as `RockPaperScissors.lean`'s `rpsGoalWin2`. -/
abbrev idsGoalHealthy : IDSState → Prop := fun s => s = .healthy

/-- `idsGameCSG`'s stage-game payoff matrix against an arbitrary continuation `v`: identical in
    shape to `IntrusionDetection.lean`'s `idsCSG_stageGame_A'`, but without the reward term (`r`
    is identically `0` here), so it is exactly `v` evaluated at the deterministic next state. -/
theorem idsGameCSG_stageGame_A (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction)
    (v : IDSState → ℝ) :
    (idsGameCSG.stageGame s v).A a1 a2 = v (idsNext a1 a2) := by
  have hexpect : idsGameCSG.expect s a1 a2 v = v (idsNext a1 a2) := by
    change ∑ s' : IDSState, (idsK s a1 a2 s').toReal * v s' = v (idsNext a1 a2)
    cases a1 <;> cases a2 <;> simp [idsK, idsNext, PMF.pure_apply, apply_ite ENNReal.toReal]
  change idsGameCSG.r s a1 a2 + idsGameCSG.expect s a1 a2 v = v (idsNext a1 a2)
  rw [hexpect, idsGameCSG_r_zero s a1 a2, zero_add]

/-- The uniform defender strategy: `defend1`/`defend2` each with probability `1/2` -- the strategy
    that makes the attacker's response irrelevant (this file's docstring). -/
noncomputable def idsUnifP : PolicyAction → ℝ := fun _ => 1 / 2

theorem idsUnifP_mem : idsUnifP ∈ stdSimplex ℝ PolicyAction :=
  ⟨fun a => by cases a <;> norm_num [idsUnifP], by simp only [policyAction_sum, idsUnifP]; norm_num⟩

/-- Symmetric counterpart of `idsUnifP` for the attacker: `attack1`/`attack2` each with probability
    `1/2`. -/
noncomputable def idsUnifQ : AttackAction → ℝ := fun _ => 1 / 2

theorem idsUnifQ_mem : idsUnifQ ∈ stdSimplex ℝ AttackAction :=
  ⟨fun a => by cases a <;> norm_num [idsUnifQ], by simp only [attackAction_sum, idsUnifQ]; norm_num⟩

/-- Against `idsUnifQ`, *every* row strategy pays exactly `(b healthy + b compromised) / 2` at
    `compromised`'s stage game against continuation `b` -- `idsUnifQ` equalises the two pure row
    actions' payoffs (each is `(b healthy + b compromised) / 2`, checked directly by cases), so any
    weighted average of them is that same constant. Mirrors
    `RockPaperScissors.lean`'s `rpsCSG_stageGame_initial_payoff_row`. -/
theorem idsGameCSG_compromised_payoff_row (b : IDSState → Set.Icc (0 : ℝ) 1)
    {p' : PolicyAction → ℝ} (hp' : p' ∈ stdSimplex ℝ PolicyAction) :
    (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff p' idsUnifQ =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
  have hinner : ∀ a1, ∑ a2,
      (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).A a1 a2 * idsUnifQ a2 =
        ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
    intro a1
    rw [attackAction_sum]
    cases a1 <;> simp [idsGameCSG_stageGame_A, idsNext, idsUnifQ] <;> ring
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2,
        (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).A a1 a2 * idsUnifQ a2
      = ∑ a1, p' a1 * (((b .healthy : ℝ) + (b .compromised : ℝ)) / 2) :=
        Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * (((b .healthy : ℝ) + (b .compromised : ℝ)) / 2) := by
        rw [← Finset.sum_mul]
    _ = ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by rw [hp'.2, one_mul]

/-- Symmetric counterpart of `idsGameCSG_compromised_payoff_row` for the column player: fixing the
    row at `idsUnifP` makes *every* column strategy pay the same constant. -/
theorem idsGameCSG_compromised_payoff_col (b : IDSState → Set.Icc (0 : ℝ) 1)
    {q' : AttackAction → ℝ} (hq' : q' ∈ stdSimplex ℝ AttackAction) :
    (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP q' =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
  have hinner : ∀ a2, ∑ a1, idsUnifP a1 *
      (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).A a1 a2 =
        ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
    intro a2
    rw [policyAction_sum]
    cases a2 <;> simp [idsGameCSG_stageGame_A, idsNext, idsUnifP] <;> ring
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, idsUnifP a1 *
        (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).A a1 a2) * q' a2
      = ∑ a2, (((b .healthy : ℝ) + (b .compromised : ℝ)) / 2) * q' a2 :=
        Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = (((b .healthy : ℝ) + (b .compromised : ℝ)) / 2) * ∑ a2, q' a2 := by
        rw [← Finset.mul_sum]
    _ = ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by rw [hq'.2, mul_one]

/-- **The payoff.** `compromised`'s stage value against *any* continuation `b` is exactly the
    average of `b`'s two values -- the two payoff lemmas above, fed into `value_unique` the same
    way `RockPaperScissors.lean`'s `rpsCSG_stageValue_initial` uses `unif3` on both sides. -/
theorem idsGameCSG_compromised_stageValue (b : IDSState → Set.Icc (0 : ℝ) 1) :
    idsGameCSG.stageValue .compromised (fun s' => (b s' : ℝ)) =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
  have huu : (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP idsUnifQ =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 :=
    idsGameCSG_compromised_payoff_row b idsUnifP_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ PolicyAction,
      (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP idsUnifQ ≤
        (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff p' idsUnifQ :=
    fun p' hp' => le_of_eq (huu.trans (idsGameCSG_compromised_payoff_row b hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ AttackAction,
      (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP q' ≤
        (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP idsUnifQ :=
    fun q' hq' => le_of_eq ((idsGameCSG_compromised_payoff_col b hq').trans huu.symm)
  have hval := (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).value_unique
    idsUnifP_mem idsUnifQ_mem hrow hcol
  change (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).value =
    ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2
  rw [← hval]
  exact huu

/-- The guessed least-fixed-point candidate: `1` at *both* states -- `healthy` because it is the
    goal itself, `compromised` because the defender's uniform strategy guarantees reaching
    `healthy` eventually with probability `1` regardless of the attacker (this file's docstring).
    A single constant function, unlike `RockPaperScissorsLfp.lean`'s `rpsVStar` (which genuinely
    differs across states): this game has no dead end analogous to `win1`. -/
noncomputable def idsVStar : IDSState → Set.Icc (0 : ℝ) 1 := fun _ => ⟨1, by norm_num, by norm_num⟩

/-- **The payoff, part 1.** `idsVStar` is an exact fixed point of `reachOp`. `healthy` closes by
    `rfl` alone, exactly as `RockPaperScissorsLfp.lean`'s `win2` case does -- no stage game
    involved, just the structural `ite` on a concrete, decidable state comparison. `compromised`'s
    stage game against the *constant* continuation `1` has every entry equal to `1` regardless of
    the joint action (no strategic argument needed for this direction, unlike part 2 below: a
    `PMF`'s probabilities always sum to `1`), so its value is `1` by squeezing the payoff matrix
    between the same constant from both directions. -/
theorem idsVStar_fixed :
    idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero idsVStar = idsVStar := by
  funext s
  apply Subtype.ext
  cases s with
  | healthy => rfl
  | compromised =>
      change (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).value =
        (idsVStar .compromised : ℝ)
      have hconst : ∀ a1 a2,
          (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).A a1 a2 = 1 := by
        intro a1 a2
        rw [idsGameCSG_stageGame_A]
        simp [idsVStar]
      have hle : (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).value ≤ 1 :=
        (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).value_le_of_forall_le
          fun a1 a2 => (hconst a1 a2).le
      have hge :
          (1 : ℝ) ≤ (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).value :=
        (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).le_value_of_forall_le
          fun a1 a2 => (hconst a1 a2).ge
      have hVstar : (idsVStar .compromised : ℝ) = 1 := rfl
      rw [hVstar]
      linarith

/-- **The payoff, part 2.** `idsVStar` lower-bounds every pre-fixed point `b` of `reachOp`:
    `b healthy = 1` is forced by goal absorption (sandwiched between the pre-fixed-point inequality
    and `[0, 1]` membership, exactly `RockPaperScissorsLfp.lean`'s `hwin2`), and
    `idsGameCSG_compromised_stageValue` turns `compromised`'s own pre-fixed-point inequality into
    `(1 + b compromised) / 2 ≤ b compromised`, forcing `b compromised ≥ 1`. This is the one part of
    the argument doing genuine work -- the uniform-strategy computation is what makes the average
    formula exact rather than a mere bound. -/
theorem idsVStar_le_of_prefixed {b : IDSState → Set.Icc (0 : ℝ) 1}
    (hb : idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero b ≤ b) : idsVStar ≤ b := by
  have hhealthy : (b .healthy : ℝ) = 1 := by
    have hle : (1 : ℝ) ≤ (b .healthy : ℝ) := hb .healthy
    exact le_antisymm (b .healthy).2.2 hle
  have hcomp_le :
      idsGameCSG.stageValue .compromised (fun s' => (b s' : ℝ)) ≤ (b .compromised : ℝ) :=
    hb .compromised
  rw [idsGameCSG_compromised_stageValue, hhealthy] at hcomp_le
  have hcomp_ge : (1 : ℝ) ≤ (b .compromised : ℝ) := by linarith
  intro s
  cases s with
  | healthy =>
      change (idsVStar .healthy : ℝ) ≤ (b .healthy : ℝ)
      simp only [idsVStar]
      linarith
  | compromised =>
      change (idsVStar .compromised : ℝ) ≤ (b .compromised : ℝ)
      simp only [idsVStar]
      linarith

/-- **The headline result.** `idsVStar` (the constant `1`) *is* the least fixed point of `reachOp`
    for reaching `healthy`, on the nose -- no limiting argument, the two payoff lemmas above fed
    into `ReachCertificate.lean`'s reusable `CSG.reachOp_lfp_eq_of_certificate`. -/
theorem idsGameCSG_reachOp_lfp_eq :
    (idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero).lfp = idsVStar :=
  idsGameCSG.reachOp_lfp_eq_of_certificate idsGoalHealthy idsGameCSG_r_zero idsVStar idsVStar_fixed
    fun _ hb => idsVStar_le_of_prefixed hb

/-- The number the whole exercise was after: starting from `compromised`, the defender guarantees
    eventually returning to `healthy` with probability exactly `1`, regardless of the attacker --
    the plain-reachability fact behind the informal "visits `healthy` infinitely often" intuition
    this file's docstring is explicit about *not* formalising. -/
theorem idsGameCSG_reachOp_lfp_compromised :
    ((idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero).lfp .compromised : ℝ) = 1 := by
  rw [idsGameCSG_reachOp_lfp_eq]
  simp [idsVStar]

end Csg
