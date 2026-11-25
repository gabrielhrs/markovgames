/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.MatrixGame

/-!
# A matrix game restricted to sets of actions

**Status: confirmed by a clean `lake build`.** `G.restrict E1 E2` is the game `G` played on the
rows in `E1` and the columns in `E2` only. In general its value differs from `G`'s. This file
gives the case in which it does not: every action outside the two sets duplicates one inside.

**The statement.** Let `f` send each row to a row of `E1` and `g` each column to a column of
`E2`, both fixing the actions already in the set, and suppose `G` cannot tell an action from its
image: `G.A (f i) (g j) = G.A i j`. Then `G.value = (G.restrict E1 E2).value`
(`value_eq_value_restrict`).

**Why it is here.** A game whose players have fewer actions available in some situations than
their action types have elements can be written over the full types by letting each unavailable
action stand for an available one. The theorem says the value does not depend on which one, the
right-hand side making no mention of `f` or `g`.

**The proof.** `G` has the entries of `(G.restrict E1 E2)` reindexed along `f` and `g`, and
reindexing along a surjection preserves the value (`value_comapRow`, `value_comapCol`).
-/

namespace Csg
namespace MatrixGame

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
variable (G : MatrixGame I J)

/-- The game played on the rows in `E1` and the columns in `E2` only. -/
noncomputable def restrict (E1 : Finset I) (E2 : Finset J) [Nonempty E1] [Nonempty E2] :
    MatrixGame E1 E2 where
  A i j := G.A i.1 j.1

/-- **Duplicated actions do not change the value.** If `f` and `g` retract the rows onto `E1` and
    the columns onto `E2`, and `G` is unchanged when each action is replaced by its image, then
    `G` has the value of its restriction to `E1` and `E2`. -/
theorem value_eq_value_restrict (E1 : Finset I) (E2 : Finset J) [Nonempty E1] [Nonempty E2]
    (f : I → E1) (g : J → E2) (hf : ∀ i : E1, f i = i) (hg : ∀ j : E2, g j = j)
    (hA : ∀ i j, G.A (f i) (g j) = G.A i j) :
    G.value = (G.restrict E1 E2).value := by
  have hfs : Function.Surjective f := fun i => ⟨i, hf i⟩
  have hgs : Function.Surjective g := fun j => ⟨j, hg j⟩
  have h1 : (((G.restrict E1 E2).comapRow f).comapCol g).value = (G.restrict E1 E2).value :=
    (((G.restrict E1 E2).comapRow f).value_comapCol hgs).trans
      ((G.restrict E1 E2).value_comapRow hfs)
  have hb : |(((G.restrict E1 E2).comapRow f).comapCol g).value - G.value| ≤ 0 :=
    abs_value_sub_le (ε := 0) fun i j => by
      change |G.A (f i) (g j) - G.A i j| ≤ 0
      rw [hA i j]
      simp
  have hz : (((G.restrict E1 E2).comapRow f).comapCol g).value - G.value = 0 :=
    abs_nonpos_iff.mp hb
  linarith

end MatrixGame
end Csg
