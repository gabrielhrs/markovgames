/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.Objective
import Comp.QualitativeFinset

/-!
# A worked qualitative instance: a surviving cycle and a decaying chain

**Status: confirmed by a clean `lake build`.**

The first place the qualitative line is pointed at an actual game, and the first `#eval` in it. A
six-state concurrent game whose sure-safety region is computed by iteration, observed to stabilise,
and then *identified exactly* with `Csg/QualitativeSure.lean`'s real-valued `CSG.G` -- no `ε`
anywhere, unlike the quantitative worked instances in `Comp/TwoStateQ.lean`.

**The game.** `safe` is everything but `bad`. Two regions:

* a **cycle** `c0`/`c1` the row player can keep the game inside forever. At `c0` the row action
  matters: `true` moves to a coin flip between `c0` and `c1`, `false` jumps straight to `bad`. At
  `c1` the *column* player picks instead -- `true` goes to `c0`, `false` to the same coin flip --
  and both responses stay inside the cycle, so the row player is safe there whatever it does.
* a **chain** `d0 → d1 → d2 → bad`, every state of which is in `safe` but none of which can stay
  there. At `d0` a wrong row action also jumps to `bad`.

Because the chain is three states deep, the iteration needs four steps rather than one: each pass
strips off the state that has just lost its last safe successor. That is the thing worth seeing in
the `#eval` output below -- the descending chain
`univ ⊇ safe ⊇ {c0,c1,d0,d1} ⊇ {c0,c1,d0} ⊇ {c0,c1}` -- and it is why the number of iterations is a
property of the graph rather than something to be bounded in advance.

**Why `decide` works here when `Comp/RockPaperScissorsQ.lean` records that it does not.** The coin
flip puts `1/2` in the kernel, and `1/2 : ℚ` normalises through `Nat.gcd`, which kernel reduction
cannot do -- exactly the obstruction that file hit. The fix is to confine every rational statement
to one lemma. `supportF_eq_chainSupp` replaces the kernel's rational supports by the explicit table
`chainSupp`, and it is proved by `rfl`-level unfolding plus `dirac_ne_zero_iff`/`coin_ne_zero_iff`,
never by `decide`. *After* that rewrite there is no `ℚ` left: `pre1C` is a `Finset` computation over
six states and two actions, and the kernel evaluates it happily. So the four descent steps and the
fixed-point check are each a one-word `decide`.

That split is the qualitative counterpart of the certificate methodology. In the quantitative line
an untrusted search proposes and a verified checker disposes; here the arithmetic is quarantined in
one bridge lemma and the combinatorics above it is checked outright.

**What is *not* assumed.** Nothing bounds the number of iterations, and no theorem says the descent
must finish within `|S|` steps. `chain_iter4` is the record of a computation that was run, and
`chain_fixed` the observation that it stopped; `CsgQ.G_eq_coe_of_fixed` needs no more than that.
-/

-- `#eval` runs compiled code, which is how this library computes; see `Comp/Search.lean`.
set_option linter.hashCommand false

namespace Comp

open Csg

/-! ## The state space -/

/-- Six states: the cycle `c0`/`c1`, the chain `d0`/`d1`/`d2`, and the unsafe sink `bad`. -/
inductive Chain
  | c0
  | c1
  | d0
  | d1
  | d2
  | bad
  deriving DecidableEq, Inhabited, Repr

/-- Same hand-written `Fintype` as `Csg/RockPaperScissors.lean`'s `RPSAction`, for the same
    toolchain reason: `deriving Fintype` is not available here. -/
instance : Fintype Chain where
  elems := {Chain.c0, Chain.c1, Chain.d0, Chain.d1, Chain.d2, Chain.bad}
  complete := by intro x; cases x <;> decide

/-! ## Distributions, and their supports

Two row shapes suffice: a point mass and a fair coin. Keeping them as named functions means the
support facts are proved once rather than per kernel clause. -/

/-- A point mass at `t`. -/
def dirac (t : Chain) : Chain → ℚ := fun s' => if s' = t then 1 else 0

theorem dirac_nonneg (t s' : Chain) : 0 ≤ dirac t s' := by
  unfold dirac
  split_ifs <;> norm_num

theorem sum_dirac (t : Chain) : ∑ s' : Chain, dirac t s' = 1 := by
  unfold dirac
  simp

/-- A point mass is nonzero exactly at its own point -- the support fact the qualitative operators
    actually consume. -/
theorem dirac_ne_zero_iff (t s' : Chain) : dirac t s' ≠ 0 ↔ s' = t := by
  unfold dirac
  split_ifs with h
  · simp [h]
  · simp [h]

/-- A fair coin between `t` and `u`, written as a combination of point masses so that both the row
    sum and the support follow from `dirac`'s own facts. -/
def coin (t u : Chain) : Chain → ℚ := fun s' => 1 / 2 * dirac t s' + 1 / 2 * dirac u s'

theorem coin_nonneg (t u s' : Chain) : 0 ≤ coin t u s' := by
  unfold coin
  have h1 := dirac_nonneg t s'
  have h2 := dirac_nonneg u s'
  linarith

theorem sum_coin (t u : Chain) : ∑ s' : Chain, coin t u s' = 1 := by
  unfold coin
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_dirac, sum_dirac]
  norm_num

/-- A nonnegative combination with positive weights vanishes only if both parts do. Isolated as its
    own arithmetic lemma because it is the only place the coin's *numbers* are reasoned about. -/
theorem half_add_half_ne_zero {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 / 2 * a + 1 / 2 * b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  constructor
  · intro h
    rcases eq_or_ne a 0 with ha0 | ha0
    · rcases eq_or_ne b 0 with hb0 | hb0
      · rw [ha0, hb0] at h
        norm_num at h
      · exact Or.inr hb0
    · exact Or.inl ha0
  · rintro (h | h)
    · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
      intro hzero
      linarith
    · have hpos : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
      intro hzero
      linarith

/-- The coin's support is the pair it mixes -- for the qualitative operators, the only thing about
    it that matters. Note that the *weights* are irrelevant to everything downstream: replacing
    `1/2` by any other pair of positive rationals changes nothing below. -/
theorem coin_ne_zero_iff (t u s' : Chain) : coin t u s' ≠ 0 ↔ s' = t ∨ s' = u := by
  unfold coin
  rw [half_add_half_ne_zero (dirac_nonneg t s') (dirac_nonneg u s'), dirac_ne_zero_iff,
    dirac_ne_zero_iff]

/-! ## The game -/

/-- The transition kernel, one row per state/action triple. The row player's action is what matters
    at `c0` and `d0`; the column player's is what matters at `c1`; the rest of the chain is
    forced. -/
def chainK : Chain → Bool → Bool → (Chain → ℚ)
  | .c0, true, _ => coin .c0 .c1
  | .c0, false, _ => dirac .bad
  | .c1, _, true => dirac .c0
  | .c1, _, false => coin .c0 .c1
  | .d0, true, _ => dirac .d1
  | .d0, false, _ => dirac .bad
  | .d1, _, _ => dirac .d2
  | .d2, _, _ => dirac .bad
  | .bad, _, _ => dirac .bad

/-- The game. Rewards are irrelevant to the qualitative operators -- they never read `r` -- so they
    are all zero. -/
def chainGame : CsgQ Chain Bool Bool where
  K := chainK
  r := fun _ _ _ => 0

/-- Every kernel row is a point mass or a coin. Stated once, by `rfl` in each of the twenty-four
    cases, so that both halves of `WellFormed` reduce to `dirac`'s and `coin`'s own facts instead of
    being re-derived clause by clause. -/
theorem chainK_cases (s : Chain) (a1 a2 : Bool) :
    (∃ t, chainGame.K s a1 a2 = dirac t) ∨ (∃ t u, chainGame.K s a1 a2 = coin t u) := by
  cases s <;> cases a1 <;> cases a2 <;>
    first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨_, _, rfl⟩

/-- `chainGame` really is a game: nonnegative kernel rows summing to one. -/
theorem chainGame_wf : chainGame.WellFormed := by
  refine ⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩
  · rcases chainK_cases s a1 a2 with ⟨t, ht⟩ | ⟨t, u, ht⟩
    · rw [ht]; exact dirac_nonneg t s'
    · rw [ht]; exact coin_nonneg t u s'
  · rcases chainK_cases s a1 a2 with ⟨t, ht⟩ | ⟨t, u, ht⟩
    · rw [ht]; exact sum_dirac t
    · rw [ht]; exact sum_coin t u

/-! ## Quarantining the arithmetic

Everything rational about this game ends at `supportF_eq_chainSupp`. Below that line there is a
kernel over `ℚ`; above it, a table of `Finset`s the kernel can reduce. -/

/-- The support table: `chainK`'s own case split, with each row replaced by the set of states it
    can reach. -/
def chainSupp : Chain → Bool → Bool → Finset Chain
  | .c0, true, _ => {.c0, .c1}
  | .c0, false, _ => {.bad}
  | .c1, _, true => {.c0}
  | .c1, _, false => {.c0, .c1}
  | .d0, true, _ => {.d1}
  | .d0, false, _ => {.bad}
  | .d1, _, _ => {.d2}
  | .d2, _, _ => {.bad}
  | .bad, _, _ => {.bad}

/-- A point-mass row's support is a singleton. -/
theorem supportF_dirac {s : Chain} {a1 a2 : Bool} {t : Chain}
    (hK : chainGame.K s a1 a2 = dirac t) : chainGame.supportF s a1 a2 = {t} := by
  ext s'
  simp only [CsgQ.mem_supportF, hK, dirac_ne_zero_iff, Finset.mem_singleton]

/-- A coin row's support is the pair. -/
theorem supportF_coin {s : Chain} {a1 a2 : Bool} {t u : Chain}
    (hK : chainGame.K s a1 a2 = coin t u) : chainGame.supportF s a1 a2 = {t, u} := by
  ext s'
  simp only [CsgQ.mem_supportF, hK, coin_ne_zero_iff, Finset.mem_insert, Finset.mem_singleton]

/-- **The bridge, and the last rational step in the file.** The game's own supports are exactly the
    table `chainSupp`. Twenty-four cases, each a point mass or a coin by `rfl`. -/
theorem supportF_eq_chainSupp (s : Chain) (a1 a2 : Bool) :
    chainGame.supportF s a1 a2 = chainSupp s a1 a2 := by
  cases s <;> cases a1 <;> cases a2 <;>
    first
      | exact supportF_dirac rfl
      | exact supportF_coin rfl

/-! ## The combinatorial layer, which `decide` can reduce -/

/-- The sure-safety region of interest: everything but the sink. -/
def chainSafe : Finset Chain := {.c0, .c1, .d0, .d1, .d2}

/-- `Pre1` with the support table substituted. No `ℚ` occurs in this definition, which is the whole
    reason the steps below are decidable. -/
def pre1C (x : Finset Chain) : Finset Chain :=
  Finset.univ.filter fun s => ∃ a1, ∀ a2, chainSupp s a1 a2 ⊆ x

/-- The game's `pre1F` is `pre1C`: `supportF_eq_chainSupp` rewritten inside the filter. -/
theorem pre1F_eq_pre1C (x : Finset Chain) : chainGame.pre1F x = pre1C x := by
  ext s
  simp only [CsgQ.mem_pre1F, pre1C, Finset.mem_filter, Finset.mem_univ, true_and,
    supportF_eq_chainSupp]

/-- And so the computable sure-safety step is a purely combinatorial one. -/
theorem gStepF_eq (x : Finset Chain) :
    chainGame.gStepF chainSafe x = pre1C x ∩ chainSafe := by
  unfold CsgQ.gStepF
  rw [pre1F_eq_pre1C]

/-! ## Running it

Compiled code, not kernel reduction -- see `Comp/Search.lean` on why that distinction matters. The
printed order follows this file's `Fintype.elems`. -/

#eval decide chainGame.WellFormed
-- expect: true

#eval chainGame.gStepF chainSafe Finset.univ
-- expect: {c0, c1, d0, d1, d2}  (all of `chainSafe`: one step cannot see past `bad`)

#eval (chainGame.gStepF chainSafe)^[2] Finset.univ
-- expect: {c0, c1, d0, d1}      (`d2`'s only successor is `bad`)

#eval (chainGame.gStepF chainSafe)^[3] Finset.univ
-- expect: {c0, c1, d0}          (`d1` has just lost `d2`)

#eval (chainGame.gStepF chainSafe)^[4] Finset.univ
-- expect: {c0, c1}              (`d0` has just lost `d1`)

#eval (chainGame.gStepF chainSafe)^[5] Finset.univ
-- expect: {c0, c1}              stabilised

/-! ## The descent, step by step

One `decide` each: after `gStepF_eq` these are finite set computations over six states and two
actions per player. -/

/-- The intermediate regions the `#eval`s above printed. -/
def chainR2 : Finset Chain := {.c0, .c1, .d0, .d1}

/-- One more step in. -/
def chainR3 : Finset Chain := {.c0, .c1, .d0}

/-- The answer: the cycle, and nothing else. -/
def chainGood : Finset Chain := {.c0, .c1}

theorem chain_step1 : chainGame.gStepF chainSafe Finset.univ = chainSafe := by
  rw [gStepF_eq]; decide

theorem chain_step2 : chainGame.gStepF chainSafe chainSafe = chainR2 := by
  rw [gStepF_eq]; decide

theorem chain_step3 : chainGame.gStepF chainSafe chainR2 = chainR3 := by
  rw [gStepF_eq]; decide

theorem chain_step4 : chainGame.gStepF chainSafe chainR3 = chainGood := by
  rw [gStepF_eq]; decide

/-- The stabilisation: `chainGood` is a fixed point of the step. This is the hypothesis that
    supplies the *lower* half of the identification for free, a greatest fixed point being above
    every post-fixed point. -/
theorem chain_fixed : chainGame.gStepF chainSafe chainGood = chainGood := by
  rw [gStepF_eq]; decide

/-- Four steps from `Finset.univ` reach `chainGood`. Chained from the single steps rather than
    evaluated in one go, so each `decide` stays small; the `(4 : ℕ) = 3 + 1` rewrites are only there
    to let `Function.iterate_succ_apply` see through the numeral. -/
theorem chain_iter4 : (chainGame.gStepF chainSafe)^[4] Finset.univ = chainGood := by
  have e4 : (4 : ℕ) = 3 + 1 := rfl
  have e3 : (3 : ℕ) = 2 + 1 := rfl
  have e2 : (2 : ℕ) = 1 + 1 := rfl
  rw [e4, Function.iterate_succ_apply, chain_step1, e3, Function.iterate_succ_apply, chain_step2,
    e2, Function.iterate_succ_apply, chain_step3, Function.iterate_one, chain_step4]

/-! ## The payoff -/

/-- **The sure-safety region of the real-valued game, exactly.** `CSG.G`, a greatest fixed point of
    an operator on `Set Chain` defined through `PMF.support`, is the cycle `{c0, c1}` -- established
    from a computation that was run and observed to stop, with no bound on the number of iterations
    and no appeal to any property of the search. -/
theorem chain_G :
    (chainGame.toCSG chainGame_wf).G (↑chainSafe : Set Chain) = (↑chainGood : Set Chain) :=
  CsgQ.G_eq_coe_of_fixed chainGame chainGame_wf chainSafe chainGood 4 chain_iter4 chain_fixed

/-- The same result as an answer to a `sureSafe` objective (`Comp/Objective.lean`), which is what
    connects this instance to the interface rather than to one hand-written statement. -/
theorem chain_answers :
    chainGame.Answers chainGame_wf (Objective.sureSafe chainSafe) (Answer.region chainGood) :=
  .sureSafe chain_G

end Comp
