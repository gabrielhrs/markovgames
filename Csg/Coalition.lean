/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Basic

/-!
# Coalitions: reducing an n-player game to the two-player `CSG` already built

**Status: confirmed by a clean `lake build`.** First cut
at the gap recorded in
`PHASE0-NOTES.md`'s "coalitions and direction are both missing, and it's one gap, not two":
`CSG S A1 A2` fixes, in its own type, both a coalition of size exactly two and a direction (`A1`
always minimises `r`, `A2` always maximises it). The FMSD/QEST papers' `⟨⟨C⟩⟩ P_max`/`⟨⟨C⟩⟩ P_min`
let both vary freely: `C` is any subset of any number of players, checked in either direction.
This file adds an n-player structure and a reduction to `CSG`, and touches nothing downstream:
`reachOp`, `untilOp`, `SafetyOp`, `BuchiOp`/`CoBuchiOp`, every certificate combinator all keep
working unchanged on whatever `CSG` the reduction below hands them.

**`NCSG`** mirrors `CSG`'s own `(S A1 A2 : Type*) [Fintype S] [Fintype A1] [Fintype A2]
[Nonempty A1] [Nonempty A2] [DecidableEq A1] [DecidableEq A2]` shape exactly, just replacing the
two fixed action types with one `Players`-indexed family `A : Players → Type*` carrying the same
three instances per player instead of per side.

**`CoalitionAction`/`ComplementAction`** are declared `abbrev`, not `def`, deliberately: a plain
`def` is semi-reducible by default and can block automatic typeclass synthesis on whatever it
unfolds to (as with a goal predicate defined via `def` blocking `DecidablePred` synthesis in
`RockPaperScissors.lean`) -- `abbrev` stays reducible, so instance search can see straight through
it to the underlying `∀ i, A i` shape it actually is.

**`combine`** rebuilds a full joint action from a coalition's and its complement's, by a decidable
case split on membership in `C` -- the one place this file is genuinely doing something; the rest
is packaging.

**`reduceMin`/`reduceMax`** are the actual payoff: `((G.reduceMax C).reachOp goal hr).lfp` is
`⟨⟨C⟩⟩ P_max=?[F goal]`, `((G.reduceMin C).reachOp goal hr).lfp` is `⟨⟨C⟩⟩ P_min=?[F goal]` -- the
same `reachOp`, no changes to it, just a different `CSG` built from the same `NCSG` and the same
`C`.

**A general Lean note:** an implicit argument that appears only in a bare return-type annotation
(as `A` does in `reduceMin`/`reduceMax` below, `CSG S (CoalitionAction C) (ComplementAction C)`)
has no value argument anywhere for Lean to read it off of, so nothing pins it down and synthesis
fails -- unlike `combine`, called with actual `aC`/`aC'` values whose types pin `A` down by
ordinary unification. `CoalitionAction`/`ComplementAction` therefore take `A` as an explicit
parameter (see each one's own docstring) rather than inferring it from the ambient section
variable.

**Still not thought through:** `r`'s sign convention across the coalition split (which side a
reward-until objective should be read as favouring once `C` moves between the `A1` and `A2` slots)
is included structurally, to match the `PHASE0-NOTES.md` write-up, but not actually thought through
yet -- only reachability-shaped properties (`r ≡ 0`, the convention every existing `reachOp`/
`untilOp` instance already uses) are anything close to exercised by what follows.

**Not attempted here:** any worked instance, and the `n = 2` identity from the scoping discussion
(`reduceMin {p1}` and `reduceMax {p2}` should be the same `CSG` up to which factor is named which,
whenever `Players` has exactly two elements `{p1, p2}`). A first attempt at stating this precisely
(prompted by a request to instantiate it against rock-paper-scissors) surfaced that it is not a
free corollary of what's here, even in the smallest possible case. `reduceMin {p1}` produces a
`CSG` whose action types are `CoalitionAction A {p1}`/`ComplementAction A {p1}` -- dependent
products over the subtype `↥({p1} : Finset Players)`, not the bare per-player type `A p1` --
so relating it back to a plain two-action-type `CSG` like `rpsCSG`, or to `reduceMax {p2}`'s own
differently-shaped action types, needs an explicit `Equiv` transport of the whole `CSG` (actions
relabelled, `K`/`r` pulled back along it) plus a proof that `reachOp`/`.lfp` is invariant under
that transport. That invariance proof bottoms out in comparing two `MatrixGame.value`s over
relabelled index types, and no lemma of that shape -- `MatrixGame.value` invariant under a
bijective (`Equiv`) relabelling of the row/column index types -- exists anywhere in
`MatrixGame.lean`/`MatrixGameMonotone.lean` yet (checked by grep). So the identity is real,
well-typed, and believed true (it is exactly the user's own `⟨⟨p1⟩⟩P_min = ⟨⟨p2⟩⟩P_max` claim), but
proving it -- for the general `n`-player theorem or even for one concrete two-player instance --
needs one genuine piece of new, reusable infrastructure first, not just bookkeeping. Not attempted
in this file; see `PHASE0-NOTES.md` for how this is being scoped.
-/

namespace Csg

/-- An `n`-player concurrent stochastic game: `Players`-many independently-acting sides instead of
    `CSG`'s fixed two, everything else the same shape (a transition kernel and a reward over the
    full joint action). Reduces to `CSG` via `NCSG.reduceMin`/`NCSG.reduceMax` below, one coalition
    and one direction at a time -- nothing here is solved or iterated on directly. -/
structure NCSG (S Players : Type*) (A : Players → Type*)
    [Fintype S] [Fintype Players] [DecidableEq Players]
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)] where
  /-- Transition kernel: `K s a` is the distribution over next states after every player
      simultaneously plays their component of the joint action `a`. -/
  K : S → (∀ i, A i) → PMF S
  /-- Reward for the joint action `a` in state `s`. Which side this favours, once a coalition is
      plugged into the maximising slot by `reduceMax`, is the "least certain part" flagged in the
      module docstring above -- not validated yet. -/
  r : S → (∀ i, A i) → ℝ

variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

namespace NCSG

variable (C : Finset Players)

/-- The joint action of everyone in `C`, playing as one decision-maker -- `CSG`'s `A1`/`A2` with
    `|C|` players folded into a single side instead of one. `abbrev`, not `def`: see the module
    docstring on why.

    `A` explicit here, unlike everywhere else in this file: it appears in `reduceMin`/`reduceMax`'s
    return type below, a bare type annotation with no value argument in sight for Lean to read `A`
    off of, so nothing would pin an implicit down there. Explicit instead of threading a value
    argument through just to fix inference. -/
abbrev CoalitionAction (A : Players → Type*) (C : Finset Players) : Type _ := ∀ i : C, A i

/-- The joint action of everyone outside `C`. Same reasoning as `CoalitionAction`, `A` explicit
    for the same reason. -/
abbrev ComplementAction (A : Players → Type*) (C : Finset Players) : Type _ :=
  ∀ i : (Cᶜ : Finset Players), A i

/-- Rebuild a full joint action from a coalition's and its complement's, by a decidable case split
    on membership in `C`. The one place this file does real work; everything around it is
    packaging. `A` stays implicit here (unlike the two `abbrev`s above): `aC`/`aC'` are actual
    value arguments whose types (`CoalitionAction A C`/`ComplementAction A C`, unfolded through
    the `abbrev`) pin `A` down by ordinary unification, so there is no inference gap to fix. -/
def combine (aC : CoalitionAction A C) (aC' : ComplementAction A C) : ∀ i, A i :=
  fun i => if h : i ∈ C then aC ⟨i, h⟩ else aC' ⟨i, Finset.mem_compl.mpr h⟩

variable (G : NCSG S Players A)

/-- Reduce to a two-player `CSG` with `C` as the row/minimising side and its complement as the
    column/maximising side -- i.e. `⟨⟨C⟩⟩ P_min`. -/
noncomputable def reduceMin : CSG S (CoalitionAction A C) (ComplementAction A C) where
  K s aC aC' := G.K s (combine C aC aC')
  r s aC aC' := G.r s (combine C aC aC')

/-- Reduce to a two-player `CSG` with `C` as the column/maximising side and its complement as the
    row/minimising side -- i.e. `⟨⟨C⟩⟩ P_max`. -/
noncomputable def reduceMax : CSG S (ComplementAction A C) (CoalitionAction A C) where
  K s aC' aC := G.K s (combine C aC aC')
  r s aC' aC := G.r s (combine C aC aC')

end NCSG

end Csg
