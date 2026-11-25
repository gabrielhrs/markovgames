/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.ModelData
import Csg.MatrixGameRestrict

/-!
# The stage game of a model is the game on its enabled actions

**Status: confirmed by a clean `lake build`.** A `ModelData` lists, at each state, the joint
actions that state enables. The game it denotes, `ModelData.toCsgQ`, has a kernel that is total
over the two global action namespaces: a disabled action stands for an enabled one
(`ModelData.pad1`, `pad2`). Which enabled action it stands for is a choice the denotation makes
and the model does not.

This file shows that the choice has no effect on a stage value. At every state and against every
continuation, the stage game of the denoted game has the value of the matrix game whose rows are
the state's enabled row actions and whose columns are its enabled column actions
(`stageValue_eq_enabled`). The right-hand side does not mention padding.

`Comp/ModelDataQualitative.lean` does the same for the qualitative operators, which quantify over
actions where this file takes a value.

**The route.** The kernel and the reward of the denoted game are unchanged when a joint action is
replaced by its padded representative, because both are read off `transAt`
(`toCsgQ_K_padFin`, `toCsgQ_r_padFin`). So the stage game's entries are too
(`stageGame_A_padFin`), and `Csg/MatrixGameRestrict.lean`'s `value_eq_value_restrict` applies with
the two paddings as retractions.
-/

namespace Comp

open Csg

namespace CsgQ

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

/-- Two joint actions with the same rational kernel row and the same rational reward give the
    same entry of the real-valued stage game, against any continuation. -/
theorem stageGame_A_congr (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (v : S → ℝ)
    {a1 b1 : A1} {a2 b2 : A2} (hK : G.K s a1 a2 = G.K s b1 b2)
    (hr : G.r s a1 a2 = G.r s b1 b2) :
    ((G.toCSG h).stageGame s v).A a1 a2 = ((G.toCSG h).stageGame s v).A b1 b2 := by
  change (G.toCSG h).r s a1 a2 + (G.toCSG h).expect s a1 a2 v
    = (G.toCSG h).r s b1 b2 + (G.toCSG h).expect s b1 b2 v
  have hr' : (G.toCSG h).r s a1 a2 = (G.toCSG h).r s b1 b2 := by
    change ((G.r s a1 a2 : ℚ) : ℝ) = ((G.r s b1 b2 : ℚ) : ℝ)
    rw [hr]
  have hE : (G.toCSG h).expect s a1 a2 v = (G.toCSG h).expect s b1 b2 v := by
    unfold CSG.expect
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [show (G.toCSG h).K s a1 a2 s' = G.toPMF h s a1 a2 s' from rfl,
      show (G.toCSG h).K s b1 b2 s' = G.toPMF h s b1 b2 s' from rfl,
      toPMF_toReal, toPMF_toReal, hK]
  rw [hr', hE]

end CsgQ

namespace ModelData

/-! ## The enabled sets are nonempty, and padding retracts onto them -/

/-- Every state enables a row action: the one its first transition names. -/
instance enabled1_nonempty (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    Nonempty (d.enabled1 hs s) :=
  ⟨⟨⟨d.pad1 s 0, d.keys1_lt hs s _ (d.pad1_mem_keys1 s 0)⟩,
    (d.mem_enabled1 hs s _).mpr (d.pad1_mem_keys1 s 0)⟩⟩

/-- Every state enables a column action. -/
instance enabled2_nonempty (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    Nonempty (d.enabled2 hs s) :=
  ⟨⟨⟨d.pad2 s 0, d.keys2_lt hs s _ (d.pad2_mem_keys2 s 0)⟩,
    (d.mem_enabled2 hs s _).mpr (d.pad2_mem_keys2 s 0)⟩⟩

/-- Padding, as a map from the row namespace onto the state's enabled row actions. -/
def padTo1 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a1 : Fin d.nAct1) :
    d.enabled1 hs s :=
  ⟨d.padFin1 hs s a1, d.padFin1_mem hs s a1⟩

/-- The column player's. -/
def padTo2 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a2 : Fin d.nAct2) :
    d.enabled2 hs s :=
  ⟨d.padFin2 hs s a2, d.padFin2_mem hs s a2⟩

/-- Padding fixes an enabled row action. -/
theorem padTo1_coe (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : d.enabled1 hs s) : d.padTo1 hs s a1 = a1 :=
  Subtype.ext (d.padFin1_eq_self hs s a1.2)

/-- Padding fixes an enabled column action. -/
theorem padTo2_coe (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a2 : d.enabled2 hs s) : d.padTo2 hs s a2 = a2 :=
  Subtype.ext (d.padFin2_eq_self hs s a2.2)

/-! ## Padding is invisible to the denoted game -/

/-- The kernel row of a joint action is the kernel row of its padded representative. -/
theorem toCsgQ_K_padFin (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.toCsgQ.K s (d.padFin1 hs s a1) (d.padFin2 hs s a2) = d.toCsgQ.K s a1 a2 := by
  funext s'
  change denseOf d.nStates (d.transAt s (d.padFin1 hs s a1) (d.padFin2 hs s a2)).dist s'
    = denseOf d.nStates (d.transAt s a1 a2).dist s'
  rw [d.transAt_padFin hs s a1 a2]

/-- Padding the row action alone leaves the kernel row alone. -/
theorem toCsgQ_K_padFin1 (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.toCsgQ.K s (d.padFin1 hs s a1) a2 = d.toCsgQ.K s a1 a2 := by
  funext s'
  change denseOf d.nStates (d.transAt s (d.pad1 s a1) a2).dist s'
    = denseOf d.nStates (d.transAt s a1 a2).dist s'
  rw [d.transAt_pad1 s a1 a2]

/-- Padding the column action alone leaves the kernel row alone. -/
theorem toCsgQ_K_padFin2 (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.toCsgQ.K s a1 (d.padFin2 hs s a2) = d.toCsgQ.K s a1 a2 := by
  funext s'
  change denseOf d.nStates (d.transAt s a1 (d.pad2 s a2)).dist s'
    = denseOf d.nStates (d.transAt s a1 a2).dist s'
  rw [d.transAt_pad2 s a1 a2]

/-- The reward of a joint action is the reward of its padded representative. -/
theorem toCsgQ_r_padFin (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.toCsgQ.r s (d.padFin1 hs s a1) (d.padFin2 hs s a2) = d.toCsgQ.r s a1 a2 := by
  change (d.stateAt s).rew + (d.transAt s (d.padFin1 hs s a1) (d.padFin2 hs s a2)).rew
    = (d.stateAt s).rew + (d.transAt s a1 a2).rew
  rw [d.transAt_padFin hs s a1 a2]

/-- Hence so is every entry of the real-valued stage game, against any continuation. -/
theorem stageGame_A_padFin (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (s : Fin d.nStates) (v : Fin d.nStates → ℝ)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    ((d.toCsgQ.toCSG (d.wellFormed hs h2)).stageGame s v).A (d.padFin1 hs s a1)
        (d.padFin2 hs s a2)
      = ((d.toCsgQ.toCSG (d.wellFormed hs h2)).stageGame s v).A a1 a2 :=
  CsgQ.stageGame_A_congr d.toCsgQ (d.wellFormed hs h2) s v (d.toCsgQ_K_padFin hs s a1 a2)
    (d.toCsgQ_r_padFin hs s a1 a2)

/-! ## The value -/

/-- **The stage game a model denotes is the game on the enabled actions.** At every state and
    against every continuation, the stage value of the denoted game is the value of the stage
    game restricted to the state's enabled row and column actions. Nothing on the right depends
    on how disabled actions are padded. -/
theorem stageValue_eq_enabled (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (s : Fin d.nStates) (v : Fin d.nStates → ℝ) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).stageValue s v
      = (((d.toCsgQ.toCSG (d.wellFormed hs h2)).stageGame s v).restrict
          (d.enabled1 hs s) (d.enabled2 hs s)).value :=
  ((d.toCsgQ.toCSG (d.wellFormed hs h2)).stageGame s v).value_eq_value_restrict
    (d.enabled1 hs s) (d.enabled2 hs s) (d.padTo1 hs s) (d.padTo2 hs s)
    (d.padTo1_coe hs s) (d.padTo2_coe hs s)
    (fun a1 a2 => d.stageGame_A_padFin hs h2 s v a1 a2)

end ModelData

end Comp
