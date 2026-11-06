/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Mathlib.Order.FixedPoints

/-!
# Pinning a fixed point from one side

**Status: confirmed by a clean `lake build`.**

Five order-theoretic facts, with no game in sight. They are collected here because everything in
`Comp/` that identifies a fixed point uses them, and because the alternative is what this file
replaced: `Comp/FixLoop.lean` importing `Comp.Qualitative` and `Comp.Reach` -- and through them
`Csg.QualitativeSure`, `Csg.ReachOp`, `Csg.IntervalCertificate` and `Comp.Shapley` -- to reach four
lemmas about complete lattices.

**The asymmetry they encode**, which is the organising idea of the whole computational layer. A
candidate `a` is identified with `f.lfp` by two facts of unequal cost: that `f a = a`, a decidable
check on a finite lattice, and that `a ≤ f.lfp`, which has to come from `a` *being* an iterate from
`⊥`. The first is cheap and local; the second is the chain. For a `gfp` the roles swap and the chain
descends from `⊤`. Which of the two a given operator needs is fixed by whether its answer is a
least or a greatest fixed point, and it alternates with nesting depth -- so the two `_of_step`
lemmas below are the only thing distinguishing the two directions, and using the wrong one is the
easiest way to prove nothing of interest.

`lfp_le_of_step` is the odd one out: it is the *upper* bound on an `lfp`, sound from any starting
point above it and needing no end-component analysis. What such analysis buys is convergence, not
soundness -- see its own docstring.
-/

/-- A fixed point that is also below `f.lfp` *is* `f.lfp`. The second hypothesis is what an iterate
    from `⊥` supplies (`OrderHom.le_lfp_of_step`); the first is a decidable check on a finite
    lattice. Together they pin a least fixed point exactly, with no minimality argument and no
    bound on how many steps stabilisation takes. -/
theorem OrderHom.eq_lfp_of_fixed_of_le {α : Type*} [CompleteLattice α] (f : α →o α) {a : α}
    (hfix : f a = a) (hle : a ≤ f.lfp) : a = f.lfp :=
  le_antisymm hle (f.lfp_le hfix.le)

/-- The dual: a fixed point that is also above `f.gfp` *is* `f.gfp`, the second hypothesis coming
    from an iterate downward from `⊤`. -/
theorem OrderHom.eq_gfp_of_fixed_of_ge {α : Type*} [CompleteLattice α] (f : α →o α) {a : α}
    (hfix : f a = a) (hge : f.gfp ≤ a) : a = f.gfp :=
  le_antisymm (f.le_gfp hfix.ge) hge

/-- One step preserves being above the greatest fixed point, so iterating down from `⊤` gives a
    chain of upper bounds on a `gfp`. The mirror of `Comp/Reach.lean`'s `OrderHom.le_lfp_of_step`,
    and what supplies `eq_gfp_of_fixed_of_ge`'s second hypothesis. -/
theorem OrderHom.gfp_le_of_step {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : f.gfp ≤ a) (hb : b = f a) : f.gfp ≤ b := by
  subst hb
  calc f.gfp = f f.gfp := f.map_gfp.symm
    _ ≤ f a := f.monotone ha

/-- One step preserves being below the least fixed point: a monotone map sends anything `≤ f.lfp`
    to something `≤ f.lfp`, because `f.lfp` is a fixed point (`OrderHom.map_lfp`). Stated with the
    step as an equation `b = f a` so that it composes directly with a certified computation, which
    produces `b` and a proof that it is what `f` returned.

    Declared at top level in the `OrderHom` namespace, following
    `Csg/IntervalCertificate.lean`'s own lattice-level lemmas. -/
theorem OrderHom.le_lfp_of_step {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : a ≤ f.lfp) (hb : b = f a) : b ≤ f.lfp := by
  subst hb
  calc f a ≤ f f.lfp := f.monotone ha
    _ = f.lfp := f.map_lfp

/-- The dual: one step preserves being *above* the least fixed point, so iterating downward from
    anything above it gives sound upper bounds. For reachability the starting point costs nothing --
    `f.lfp ≤ ⊤` is `le_top` -- and with nonpositive rewards the constant `0` serves instead, being
    pre-fixed there.

    Soundness of an upper bound therefore needs no end-component analysis. What such analysis buys
    is *convergence*: iterating from `⊤` stalls above the value wherever the players can keep the
    play off the target forever, so the bound stays valid but stops improving. -/
theorem OrderHom.lfp_le_of_step {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : f.lfp ≤ a) (hb : b = f a) : f.lfp ≤ b := by
  subst hb
  calc f.lfp = f f.lfp := f.map_lfp.symm
    _ ≤ f a := f.monotone ha
