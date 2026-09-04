/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.SkirmishFeint
import Csg.Coalition

/-!
# `⟨⟨hider⟩⟩ P_max ≠ ⟨⟨hider⟩⟩ P_min`, in `Csg.Coalition`'s own terms

**Status: confirmed by a clean `lake build`, after one real fix round.** Round 1: both real errors
were in `combine_hiderC_hider`/`combine_hiderC_thrower`.
The original proofs tried `simp [NCSG.combine, hiderSingletonEquiv/throwerComplementEquiv, dif_pos
.../dif_neg ...]`, mirroring `Csg.CoalitionComplement.combine_compl`'s own fix -- but there `C` was
a fully general, uninstantiated `Finset Players`, whereas `hiderC := {hider}` here is a *concrete*
literal, and simp's rewriting via an explicitly-applied `dif_pos`/`dif_neg` term didn't fire against
it (left the `dite` from `NCSG.combine` entirely unreduced; `dif_pos` is also deprecated in this
Mathlib snapshot, in favour of `dite_eq_left`, though that alone wasn't the failure). Since
`hiderC`/`hider`/`thrower` are all concrete, decidable data (no uninstantiated `Finset`/`Decidable`
standing in the way the way `combine_compl`'s general `C` did), both equalities are provable by
plain kernel computation -- replaced both proofs with a bare `rfl`. Also swapped two `show`s (in
`reduceMin_hiderC_stageGame_eq`/`reduceMax_hiderC_stageGame_eq`) for `change`, per this toolchain's
own style-linter suggestion (harmless, not a correctness issue, but free to fix). Clean on
resubmission, no further rounds needed.

`Csg.SkirmishFeint.skirmishMinCSG`/`skirmishMaxCSG` are the
plain two-player `CSG`s that `NCSG.reduceMin {hider}`/`reduceMax {hider}` *would* produce for a
genuine two-player `NCSG`, built by hand there to avoid paying for `CoalitionAction`/
`ComplementAction`'s dependent-product bookkeeping up front. This file pays for it: builds the
actual two-player `NCSG` (`skirmishNCSG`), the actual coalition `{hider}` (`hiderC`), and connects
`(skirmishNCSG.reduceMin hiderC).stageValue`/`(skirmishNCSG.reduceMax hiderC).stageValue` back to
the already-confirmed `4/5`/`1/2` -- the one piece of new, reusable infrastructure
`Csg.Coalition`'s own docstring flagged as missing ("Not attempted here: any worked instance"),
using `MatrixGameCongr.value_relabelRow`/`MatrixGameCongrCol.value_relabelCol` exactly as that
docstring anticipated.

**Why both a row and a column relabelling are needed.** `CoalitionAction SkirmishAction hiderC`
(`= ∀ i : ↥hiderC, SkirmishAction i`, a dependent product over a one-element `Finset` subtype) is
*in bijection with*, but not literally, `HiderAction` -- evaluating at the coalition's one member
is the bijection (`hiderSingletonEquiv`). Symmetrically `ComplementAction SkirmishAction hiderC`
(`= ∀ i : ↥hiderCᶜ, SkirmishAction i`) is in bijection with `ThrowerAction`
(`throwerComplementEquiv`). So `(skirmishNCSG.reduceMin hiderC).stageGame`'s payoff matrix is
literally `skirmishMinCSG.stageGame`'s own matrix with *both* its row and column index types
relabelled along these two bijections -- one `relabelRow`, one `relabelCol`, composed.

**The one real step**, `combine_hiderC_hider`/`combine_hiderC_thrower`: showing `NCSG.combine`
applied to `hiderC` and evaluated at the two concrete players `hider`/`thrower` literally reduces to
the two bijections above -- the exact role `Csg.CoalitionComplement.combine_compl` played there,
here for a concrete singleton coalition rather than a general complement pairing. Everything else
(`hGameEq`/`hGameEq2`, the `MatrixGame` equalities) is `Csg.CoalitionComplement.
reduceMin_stageValue_eq`'s own `funext`/`congrArg MatrixGame.mk` technique, reused verbatim.
-/

namespace Csg

/-! ## The two players, and the dependent action type over them -/

/-- The two players: the hider and the thrower. -/
inductive SkirmishPlayer
  | hider
  | thrower
  deriving DecidableEq, Inhabited

instance : Fintype SkirmishPlayer where
  elems := {SkirmishPlayer.hider, .thrower}
  complete := by intro p; cases p <;> decide

/-- `p ≠ hider` and `p = thrower` say the same thing, for the only other player there is --
    used to identify the one element of `hiderC`'s complement without ever computing
    `hiderCᶜ` as a `Finset` equality. -/
theorem skirmishPlayer_ne_hider_iff (p : SkirmishPlayer) :
    p ≠ SkirmishPlayer.hider ↔ p = SkirmishPlayer.thrower := by
  cases p <;> simp

/-- Each player's own action type, matching `Csg.SkirmishFeint`'s `HiderAction`/`ThrowerAction`
    exactly. -/
def SkirmishAction : SkirmishPlayer → Type
  | .hider => HiderAction
  | .thrower => ThrowerAction

instance : ∀ p, Fintype (SkirmishAction p)
  | .hider => inferInstanceAs (Fintype HiderAction)
  | .thrower => inferInstanceAs (Fintype ThrowerAction)

instance : ∀ p, Nonempty (SkirmishAction p)
  | .hider => inferInstanceAs (Nonempty HiderAction)
  | .thrower => inferInstanceAs (Nonempty ThrowerAction)

instance : ∀ p, DecidableEq (SkirmishAction p)
  | .hider => inferInstanceAs (DecidableEq HiderAction)
  | .thrower => inferInstanceAs (DecidableEq ThrowerAction)

/-! ## The genuine two-player `NCSG`, and the coalition `{hider}` -/

/-- The actual `NCSG`, built from the very same `jointK`/`jointR` as `Csg.SkirmishFeint`'s two
    hand-built `CSG`s -- one source of truth for the game mechanics, shared by both files. -/
noncomputable def skirmishNCSG : NCSG SkirmishState SkirmishPlayer SkirmishAction where
  K s a := jointK s (a .hider) (a .thrower)
  r s a := jointR s (a .hider) (a .thrower)

/-- The hider, as a coalition of one. -/
def hiderC : Finset SkirmishPlayer := {SkirmishPlayer.hider}

/-! ## Relabelling `CoalitionAction`/`ComplementAction` back to the bare action types -/

/-- `CoalitionAction SkirmishAction hiderC`, a dependent product over the one-element subtype
    `↥hiderC`, is in bijection with the bare `HiderAction`: evaluate at the coalition's one
    member. -/
def hiderSingletonEquiv : NCSG.CoalitionAction SkirmishAction hiderC ≃ HiderAction where
  toFun x := x ⟨SkirmishPlayer.hider, Finset.mem_singleton_self _⟩
  invFun h := fun i => by
    obtain ⟨val, prop⟩ := i
    have hval : val = SkirmishPlayer.hider := Finset.mem_singleton.mp prop
    subst hval
    exact h
  left_inv x := by
    funext i
    obtain ⟨val, prop⟩ := i
    have hval : val = SkirmishPlayer.hider := Finset.mem_singleton.mp prop
    subst hval
    rfl
  right_inv _ := rfl

/-- `ComplementAction SkirmishAction hiderC`, a dependent product over `↥hiderCᶜ`, is in bijection
    with the bare `ThrowerAction`: evaluate at the complement's one member, identified via
    `skirmishPlayer_ne_hider_iff` rather than any `Finset`-level complement computation. -/
def throwerComplementEquiv : NCSG.ComplementAction SkirmishAction hiderC ≃ ThrowerAction where
  toFun x := x ⟨SkirmishPlayer.thrower, by simp [hiderC, Finset.mem_compl]⟩
  invFun h := fun i => by
    obtain ⟨val, prop⟩ := i
    have hne : val ≠ SkirmishPlayer.hider := by simpa [hiderC, Finset.mem_compl] using prop
    have hval : val = SkirmishPlayer.thrower := (skirmishPlayer_ne_hider_iff val).mp hne
    subst hval
    exact h
  left_inv x := by
    funext i
    obtain ⟨val, prop⟩ := i
    have hne : val ≠ SkirmishPlayer.hider := by simpa [hiderC, Finset.mem_compl] using prop
    have hval : val = SkirmishPlayer.thrower := (skirmishPlayer_ne_hider_iff val).mp hne
    subst hval
    rfl
  right_inv _ := rfl

/-! ## `NCSG.combine`, evaluated at the two concrete players -/

/-- `NCSG.combine hiderC`, evaluated at `hider`, is exactly `hiderSingletonEquiv`'s own reading of
    the coalition's action -- the singleton-coalition analogue of
    `Csg.CoalitionComplement.combine_compl`. -/
theorem combine_hiderC_hider (aC : NCSG.CoalitionAction SkirmishAction hiderC)
    (aC' : NCSG.ComplementAction SkirmishAction hiderC) :
    NCSG.combine hiderC aC aC' SkirmishPlayer.hider = hiderSingletonEquiv aC := rfl

/-- `NCSG.combine hiderC`, evaluated at `thrower`, is exactly `throwerComplementEquiv`'s own
    reading of the complement's action. -/
theorem combine_hiderC_thrower (aC : NCSG.CoalitionAction SkirmishAction hiderC)
    (aC' : NCSG.ComplementAction SkirmishAction hiderC) :
    NCSG.combine hiderC aC aC' SkirmishPlayer.thrower = throwerComplementEquiv aC' := rfl

/-! ## The two stage games, related back to `Csg.SkirmishFeint`'s -/

/-- `⟨⟨hider⟩⟩ P_min`'s stage game at `s_hide` is literally `skirmishMinCSG`'s own stage game, both
    its row and column index types relabelled along `hiderSingletonEquiv`/`throwerComplementEquiv`
    -- `Csg.CoalitionComplement.reduceMin_stageValue_eq`'s own `funext`/`congrArg MatrixGame.mk`
    technique, reused verbatim. -/
theorem reduceMin_hiderC_stageGame_eq (v : SkirmishState → ℝ) :
    (skirmishNCSG.reduceMin hiderC).stageGame .hide v =
      ((skirmishMinCSG.stageGame .hide v).relabelRow hiderSingletonEquiv).relabelCol
        throwerComplementEquiv := by
  have hA : ((skirmishNCSG.reduceMin hiderC).stageGame .hide v).A =
      (((skirmishMinCSG.stageGame .hide v).relabelRow hiderSingletonEquiv).relabelCol
        throwerComplementEquiv).A := by
    funext aC aC'
    change jointR .hide (NCSG.combine hiderC aC aC' .hider) (NCSG.combine hiderC aC aC' .thrower) +
        ∑ s', (jointK .hide (NCSG.combine hiderC aC aC' .hider)
          (NCSG.combine hiderC aC aC' .thrower) s').toReal * v s' =
      jointR .hide (hiderSingletonEquiv aC) (throwerComplementEquiv aC') +
        ∑ s', (jointK .hide (hiderSingletonEquiv aC) (throwerComplementEquiv aC') s').toReal * v s'
    rw [combine_hiderC_hider, combine_hiderC_thrower]
  exact congrArg MatrixGame.mk hA

/-- **`⟨⟨hider⟩⟩ P_min`.** With `hider` reduced to the row/minimising side (`Csg.Coalition`'s own
    reading of `⟨⟨hider⟩⟩ P_min`), the stage value at `s_hide` is exactly `4/5` -- the same number
    `Csg.SkirmishFeint.stageValue_min_eq` already established for the hand-built two-player game,
    now transported through the genuine `NCSG`/`Coalition` reduction. -/
theorem reduceMin_hiderC_stageValue_eq (v : SkirmishState → ℝ) (vhide : v .hide = 4 / 5)
    (vhome : v .home = 1) (vwet : v .wet = 0) :
    (skirmishNCSG.reduceMin hiderC).stageValue .hide v = 4 / 5 := by
  unfold CSG.stageValue
  rw [reduceMin_hiderC_stageGame_eq, MatrixGame.value_relabelCol, MatrixGame.value_relabelRow]
  exact stageValue_min_eq v vhide vhome vwet

/-- `⟨⟨hider⟩⟩ P_max`'s stage game at `s_hide` is literally `skirmishMaxCSG`'s own stage game,
    row and column relabelled the other way round -- `throwerComplementEquiv` on the row side
    (`reduceMax`'s row slot is the complement), `hiderSingletonEquiv` on the column side. -/
theorem reduceMax_hiderC_stageGame_eq (v : SkirmishState → ℝ) :
    (skirmishNCSG.reduceMax hiderC).stageGame .hide v =
      ((skirmishMaxCSG.stageGame .hide v).relabelRow throwerComplementEquiv).relabelCol
        hiderSingletonEquiv := by
  have hA : ((skirmishNCSG.reduceMax hiderC).stageGame .hide v).A =
      (((skirmishMaxCSG.stageGame .hide v).relabelRow throwerComplementEquiv).relabelCol
        hiderSingletonEquiv).A := by
    funext aC' aC
    change jointR .hide (NCSG.combine hiderC aC aC' .hider) (NCSG.combine hiderC aC aC' .thrower) +
        ∑ s', (jointK .hide (NCSG.combine hiderC aC aC' .hider)
          (NCSG.combine hiderC aC aC' .thrower) s').toReal * v s' =
      jointR .hide (hiderSingletonEquiv aC) (throwerComplementEquiv aC') +
        ∑ s', (jointK .hide (hiderSingletonEquiv aC) (throwerComplementEquiv aC') s').toReal * v s'
    rw [combine_hiderC_hider, combine_hiderC_thrower]
  exact congrArg MatrixGame.mk hA

/-- **`⟨⟨hider⟩⟩ P_max`.** With `hider` reduced to the column/maximising side, the stage value at
    `s_hide` is exactly `1/2` -- transporting `Csg.SkirmishFeint.stageValue_max_eq` through the
    genuine reduction, mirror of `reduceMin_hiderC_stageValue_eq`. -/
theorem reduceMax_hiderC_stageValue_eq (v : SkirmishState → ℝ) (vhide : v .hide = 1 / 2)
    (vhome : v .home = 1) (vwet : v .wet = 0) :
    (skirmishNCSG.reduceMax hiderC).stageValue .hide v = 1 / 2 := by
  unfold CSG.stageValue
  rw [reduceMax_hiderC_stageGame_eq, MatrixGame.value_relabelCol, MatrixGame.value_relabelRow]
  exact stageValue_max_eq v vhide vhome vwet

/-- **The point of this file.** `⟨⟨hider⟩⟩ P_max ≠ ⟨⟨hider⟩⟩ P_min` at `s_hide`, in
    `Csg.Coalition`'s own `reduceMin`/`reduceMax` terms -- the FMSD-shaped statement
    `Csg.SkirmishFeint.value_ne` anticipated, now stated over the genuine coalition reduction
    rather than the two hand-built `CSG`s. -/
theorem reduceMax_ne_reduceMin (vMin vMax : SkirmishState → ℝ)
    (vMinHide : vMin .hide = 4 / 5) (vMinHome : vMin .home = 1) (vMinWet : vMin .wet = 0)
    (vMaxHide : vMax .hide = 1 / 2) (vMaxHome : vMax .home = 1) (vMaxWet : vMax .wet = 0) :
    (skirmishNCSG.reduceMax hiderC).stageValue .hide vMax ≠
      (skirmishNCSG.reduceMin hiderC).stageValue .hide vMin := by
  rw [reduceMax_hiderC_stageValue_eq vMax vMaxHide vMaxHome vMaxWet,
    reduceMin_hiderC_stageValue_eq vMin vMinHide vMinHome vMinWet]
  norm_num

end Csg
