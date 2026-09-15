/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.QualitativeSure

/-!
# Qualitative winning regions: almost-sure mode

**Status: confirmed by a clean `lake build`.** `A_univ_v2` (a small general degeneracy fact about
`A`: its safety test always succeeds when every column is already excused, i.e. `v2 = univ`),
alongside `B_empty_x`/`B_empty_v1` (two degeneracy facts about `B`: its escape test always fails
when either argument -- the escape target or the row-action pool -- is `∅`), support
`Csg.SkirmishProperties`'s almost-sure co-Büchi (`AFG`) argument. Following L. de Alfaro and
T. Henzinger, "Concurrent Omega-Regular Games," LICS 2000, and
ported directly from the already-implemented, already-validated Java in `prism-games`'s
`explicit/CSGModelChecker.java` (methods `A`, `B`, `AF`, `AGF`, `AFG`).

**Why this file exists.** `Csg.QualitativeSure` and this file's sibling `Csg.QualitativeLimitSure`
split the qualitative line along the *mode* axis the paper itself uses -- sure, almost-sure,
limit-sure, each computing the same four objective shapes (safety `G`, reachability `F`, co-Büchi
`FG`, Büchi `GF`) -- rather than along the order the pieces happened to get built in. This file is
everything almost-sure mode needs and nothing else: `A`/`B` (the one-step combinators) and `Apre1`
were relocated from the old `QualitativeAlgorithms.lean`; `AF` from the old
`QualitativeReachability.lean`; `AFpre1`/`AFG` from the old `QualitativeRecurrence.lean`. `AGF` sits
between `AF` and `AFpre1`/`AFG` below, reordered from its original position (before `AF`, in the
old file split) to read in order of increasing complexity: `Apre1` (no fixed point of its own) →
`AF` (coupled `νY.μX`, no case split) → `AGF` (coupled `νY.μX`, with a case split on `b`) →
`AFpre1`/`AFG` (the 3-argument predecessor, and the `νZ.μX.νY` triple built on it).

`A_mono_v2` (monotonicity of `A` in its excused-columns argument) also moved here from the old
`QualitativeReachability.lean`, ahead of where it used to live: it is a plain fact about `A` itself,
needed by *both* `AFpre1` below (this file) and `Lpre1` (`Csg.QualitativeLimitSure`), so it belongs
with `A`/`B`'s other monotonicity lemmas rather than filed under whichever mode happened to need it
first historically.

**Scope**: every almost-sure operator (`A`, `B`, `Apre1`, `AF`, `AGF`, `AFpre1`, `AFG`). Every
`OrderHom` bundling step below reuses `OrderHom.lfp_mono_of_le`/`gfp_mono_of_le` from `Csg.BuchiOp`
unchanged, exactly as the sure-mode `SGF` (`Csg.QualitativeSure`) already does.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-! ## `A`/`B`, the one-step combinators -/

/-- The almost-sure one-step "which row actions are safe" combinator (`A` in the paper and in the
    Java): row action `a1` at state `s` qualifies against target `y`, columns in `v2` excused, if
    *every* other column response `a2` still forces the outcome's support into `y`. -/
noncomputable def A (v2 : Set A2) (y : Set S) (s : S) : Set A1 :=
  {a1 | ∀ a2, a2 ∈ v2 ∨ (C.K s a1 a2).support ⊆ y}

/-- **The payoff.** `A` is monotone in `y`, for fixed `v2`: a wider `y` only makes "support ⊆ y"
    easier for a row action already excused nowhere. -/
theorem A_mono_y (v2 : Set A2) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S) :
    C.A v2 y1 s ≤ C.A v2 y2 s := by
  intro a1 ha1 a2
  rcases ha1 a2 with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hy)

/-- The almost-sure one-step "which column actions can escape" combinator (`B` in the paper and in
    the Java): column action `a2` at state `s` can escape into `x` if *some* row action in `v1`
    gives an outcome whose support meets `x`. -/
noncomputable def B (v1 : Set A1) (x : Set S) (s : S) : Set A2 :=
  {a2 | ∃ a1 ∈ v1, ((C.K s a1 a2).support ∩ x).Nonempty}

/-- **The payoff.** `B` is monotone in `v1`, for fixed `x`: a wider row-action pool only adds more
    ways for a column action to escape. -/
theorem B_mono_v1 (x : Set S) {v1 v1' : Set A1} (hv : v1 ≤ v1') (s : S) :
    C.B v1 x s ≤ C.B v1' x s := by
  intro a2 ha2
  obtain ⟨a1, ha1, hne⟩ := ha2
  exact ⟨a1, hv ha1, hne⟩

/-- **The payoff.** `B` is monotone in `x`, for fixed `v1`: a wider escape target only makes
    "support meets `x`" easier. -/
theorem B_mono_x (v1 : Set A1) {x1 x2 : Set S} (hx : x1 ≤ x2) (s : S) :
    C.B v1 x1 s ≤ C.B v1 x2 s := by
  intro a2 ha2
  obtain ⟨a1, ha1, s', hs'⟩ := ha2
  exact ⟨a1, ha1, s', hs'.1, hx hs'.2⟩

/-- **The payoff, a degeneracy at the escape target.** `B`'s escape test always fails when the
    target itself is empty: intersecting any support with `∅` is `∅`, so no witness `a1` can ever
    make the intersection nonempty, regardless of the row-action pool `v1`. Needed wherever a
    fixed-point iteration for an `Apre1`/`Lpre1`-style operator starts its escape target from `⊥`
    (i.e. `∅`). -/
theorem B_empty_x (v1 : Set A1) (s : S) : C.B v1 (∅ : Set S) s = ∅ := by
  ext a2
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a1, _, hne⟩
  rw [Set.inter_empty] at hne
  exact Set.not_nonempty_empty hne

/-- **The payoff, the dual degeneracy at the row-action pool.** `B`'s escape test always fails
    when the row-action pool itself is empty: there is no `a1` to witness the existential at all,
    regardless of the escape target `x`. Needed wherever a fixed-point iteration for an
    `Apre1`/`Lpre1`-style *inner* row-action step (`LStep`/`LFWStep`) starts from `⊥` (i.e. `∅`) on
    `Set A1`. -/
theorem B_empty_v1 (x : Set S) (s : S) : C.B (∅ : Set A1) x s = ∅ := by
  ext a2
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a1, ha1, _⟩
  exact ha1

/-- **The payoff, a degeneracy at the excused-columns argument.** `A`'s safety test always
    succeeds when every column is already excused: `a2 ∈ v2` holds trivially for any `a2` when
    `v2 = univ`, so the `∀a2, a2 ∈ v2 ∨ ...` condition needs no support check at all, and holds for
    *every* row action `a1`. Needed wherever a fixed-point iteration threading a *growing* excused
    set (`AFV`/`LFV`'s own inner steps) reaches `univ`. -/
theorem A_univ_v2 (y : Set S) (s : S) : C.A (Set.univ : Set A2) y s = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a1 a2
  exact Or.inl (Set.mem_univ a2)

/-- **The payoff.** `A` is monotone in the excused-columns argument `v2`: a wider `v2` only makes
    "already excused" easier to satisfy, for the same row action. The one monotonicity fact about
    `A`/`B` `Apre1` never needs (it only ever calls `A` with `v2 = ∅` fixed) -- needed once `AFpre1`
    below, and separately `Lpre1` (`Csg.QualitativeLimitSure`), thread a *growing* set through this
    slot inside their own fixed points. -/
theorem A_mono_v2 (y : Set S) {v2 v2' : Set A2} (hv : v2 ≤ v2') (s : S) :
    C.A v2 y s ≤ C.A v2' y s := by
  intro a1 ha1 a2
  rcases ha1 a2 with h | h
  · exact Or.inl (hv h)
  · exact Or.inr h

/-! ## `Apre1`, the almost-sure one-step predecessor -/

/-- The almost-sure one-step predecessor operator (`Apre1`/`apreXY` in the paper and in the Java):
    `s` is in `Apre1 x y` if, restricting the row player to the actions already safe for `y` against
    every column response (`A ∅ y`), *every* column action can still be driven to escape into `x`.
    Uses `A` with `v2 = ∅`, exactly matching the Java's own `A(mdist, new BitSet(), y)` call inside
    `apreXY`. -/
noncomputable def Apre1 (x y : Set S) : Set S :=
  {s | C.B (C.A ∅ y s) x s = Set.univ}

/-- **The payoff.** `Apre1` is monotone in `x`, for fixed `y`: `B_mono_x` applied at the (already
    full) escape set, then squeezed back to equality against `Set.univ` from both sides. -/
theorem Apre1_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) :
    C.Apre1 x1 y ≤ C.Apre1 x2 y := by
  intro s hs
  have hsub : C.B (C.A ∅ y s) x1 s ≤ C.B (C.A ∅ y s) x2 s := C.B_mono_x (C.A ∅ y s) hx s
  rw [hs] at hsub
  exact Set.Subset.antisymm (Set.subset_univ _) hsub

/-- **The payoff.** `Apre1` is monotone in `y`, for fixed `x`: `A_mono_y` widens the safe row-action
    pool, `B_mono_v1` then widens the resulting escape set, squeezed back to equality against
    `Set.univ` exactly as `Apre1_mono_x` does. -/
theorem Apre1_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) :
    C.Apre1 x y1 ≤ C.Apre1 x y2 := by
  intro s hs
  have hsub : C.B (C.A ∅ y1 s) x s ≤ C.B (C.A ∅ y2 s) x s :=
    C.B_mono_v1 x (C.A_mono_y ∅ hy s) s
  rw [hs] at hsub
  exact Set.Subset.antisymm (Set.subset_univ _) hsub

/-! ## `AF`: almost-sure reachability -/

/-- `AF`'s **inner** (`μX`) step, for a fixed outer candidate `y`: no case split on `b` at all,
    unlike `AGF` -- `Apre1(X,Y) ∨ b`, the direct almost-sure mirror of `SF`'s own `Pre1(X) ∨ b`. -/
noncomputable def AFInnerFun (b y x : Set S) : Set S := C.Apre1 x y ∪ b

theorem AFInnerFun_mono (b y : Set S) : Monotone (C.AFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl (C.Apre1_mono_x hx y h)
  · exact Or.inr h

/-- The inner Bellman step, bundled as an `OrderHom` for a fixed outer candidate `y`. -/
noncomputable def AFInner (b y : Set S) : Set S →o Set S where
  toFun := C.AFInnerFun b y
  monotone' := C.AFInnerFun_mono b y

theorem AFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.AFInnerFun b y1 x ≤ C.AFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl (C.Apre1_mono_y x hy h)
  · exact Or.inr h

/-- **The payoff.** The `AF` Bellman operator, `Y ↦ μX.AFInnerFun b Y X`, bundled as an `OrderHom`
    on `Set S` via `OrderHom.lfp_mono_of_le` applied to `AFInnerFun_mono_y`. -/
noncomputable def AFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.AFInner b y).lfp
  monotone' := fun y1 y2 hy => OrderHom.lfp_mono_of_le (fun x => C.AFInnerFun_mono_y b hy x)

/-- **The payoff.** Almost-sure reachability (`AF` in the Java, per LICS 2000): the greatest fixed
    point of `AFOuter`, the states from which the row player can force reaching `b` almost
    surely. -/
noncomputable def AF (b : Set S) : Set S := (C.AFOuter b).gfp

/-! ## `AGF`: almost-sure Büchi -/

/-- `AGF`'s **inner** (`μX`) step, for a fixed outer candidate `y`: a `b`-state plays `Pre1` against
    `y` exactly as `SGFInnerFun` (`Csg.QualitativeSure`) does (banking a completed visit with
    certainty); a non-`b` state plays `Apre1` (not `Pre1`) against `x`, the one swap the Java's
    `AGF` makes relative to `SGF`. -/
noncomputable def AGFInnerFun (b y x : Set S) : Set S := (C.Apre1 x y ∩ bᶜ) ∪ (C.Pre1 y ∩ b)

/-- **The payoff.** `AGFInnerFun` is monotone in the inner continuation `x`, for fixed `b`/`y` --
    `Apre1_mono_x` on the non-`b` branch, the `b` branch untouched since it doesn't mention `x`. -/
theorem AGFInnerFun_mono (b y : Set S) : Monotone (C.AGFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Apre1_mono_x hx y h.1, h.2⟩
  · exact Or.inr h

/-- The inner Bellman step, bundled as an `OrderHom` for a fixed outer candidate `y` --
    `AGFInnerFun` plus its own monotonicity, exactly `SGFInner`'s own pattern. -/
noncomputable def AGFInner (b y : Set S) : Set S →o Set S where
  toFun := C.AGFInnerFun b y
  monotone' := C.AGFInnerFun_mono b y

/-- **The payoff.** `AGFInnerFun` is *also* monotone in the outer candidate `y`, for any fixed
    inner continuation `x` -- `Apre1_mono_y` on the non-`b` branch, `Pre1_mono` on the `b` branch,
    needed to bundle the outer (`νY`) level via `OrderHom.lfp_mono_of_le`. -/
theorem AGFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.AGFInnerFun b y1 x ≤ C.AGFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Apre1_mono_y x hy h.1, h.2⟩
  · exact Or.inr ⟨C.Pre1_mono hy h.1, h.2⟩

/-- **The payoff.** The `AGF` Bellman operator, `Y ↦ μX.AGFInnerFun b Y X`, bundled as an
    `OrderHom` on `Set S` via `OrderHom.lfp_mono_of_le` applied to `AGFInnerFun_mono_y` -- the exact
    same construction `SGFOuter` uses, with `Apre1` standing in for `Pre1` on the non-`b` branch. -/
noncomputable def AGFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.AGFInner b y).lfp
  monotone' := fun y1 y2 hy => OrderHom.lfp_mono_of_le (fun x => C.AGFInnerFun_mono_y b hy x)

/-- **The payoff.** Almost-sure Büchi (`AGF` in the Java, per LICS 2000 eq. 3, S4.1): the greatest
    fixed point of `AGFOuter`, the states from which the row player can force visiting `b`
    infinitely often *almost surely* (probability 1, but not necessarily with outright certainty --
    that's `SGF`, `Csg.QualitativeSure`). -/
noncomputable def AGF (b : Set S) : Set S := (C.AGFOuter b).gfp

/-! ## `AFpre1`, the 3-argument almost-sure predecessor -/

/-- The per-state step whose greatest fixed point is `apreXYZ`'s own row-action witness set `v`:
    `V ↦ A(∅,z,s) ∩ A(B(V,x,s), y, s)` -- the first factor is a constant (independent of `V`), the
    second is `B_mono_v1`-then-`A_mono_v2` composed, so the whole map is monotone in `V`. -/
noncomputable def AFVStep (x y z : Set S) (s : S) : Set A1 →o Set A1 where
  toFun V := C.A ∅ z s ∩ C.A (C.B V x s) y s
  monotone' := by
    intro V1 V2 hV a1 ha1
    exact ⟨ha1.1, C.A_mono_v2 y (C.B_mono_v1 x hV s) s ha1.2⟩

/-- The almost-sure 3-argument predecessor's row-action witness set at state `s` -- unnamed in the
    Java, the value `v` converges to inside `apreXYZ`'s loop: the greatest fixed point of
    `AFVStep`. -/
noncomputable def AFV (x y z : Set S) (s : S) : Set A1 := (C.AFVStep x y z s).gfp

theorem AFVStepFun_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S) (V : Set A1) :
    C.AFVStep x y z1 s V ≤ C.AFVStep x y z2 s V := by
  intro a1 ha1
  exact ⟨C.A_mono_y ∅ hz s ha1.1, ha1.2⟩

/-- **The payoff.** `AFV` is monotone in `z`, for fixed `x`/`y` -- `z` only appears in the constant
    first factor, via `A_mono_y` applied at the `∅`/`z` call. -/
theorem AFV_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S) :
    C.AFV x y z1 s ≤ C.AFV x y z2 s :=
  OrderHom.gfp_mono_of_le (fun V => C.AFVStepFun_mono_z x y hz s V)

theorem AFVStepFun_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) (s : S)
    (V : Set A1) : C.AFVStep x y1 z s V ≤ C.AFVStep x y2 z s V := by
  intro a1 ha1
  exact ⟨ha1.1, C.A_mono_y (C.B V x s) hy s ha1.2⟩

/-- **The payoff.** `AFV` is monotone in `y`, for fixed `x`/`z` -- `y` only appears in the second
    factor's own target slot, via `A_mono_y` applied at the `B(V,x,s)`/`y` call. -/
theorem AFV_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) (s : S) :
    C.AFV x y1 z s ≤ C.AFV x y2 z s :=
  OrderHom.gfp_mono_of_le (fun V => C.AFVStepFun_mono_y x hy z s V)

theorem AFVStepFun_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) (s : S) (V : Set A1) :
    C.AFVStep x1 y z s V ≤ C.AFVStep x2 y z s V := by
  intro a1 ha1
  exact ⟨ha1.1, C.A_mono_v2 y (C.B_mono_x V hx s) s ha1.2⟩

/-- **The payoff.** `AFV` is monotone in `x`, for fixed `y`/`z`: the constant first factor
    (`A ∅ z s`) never calls `B` at all, so it doesn't depend on `x` and transfers unchanged; only
    the second factor's `B(V,x,s)` moves, via `B_mono_x` then `A_mono_v2` exactly as `AFV_mono_y`'s
    proof uses `A_mono_y` at the same slot. -/
theorem AFV_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) (s : S) :
    C.AFV x1 y z s ≤ C.AFV x2 y z s :=
  OrderHom.gfp_mono_of_le (fun V => C.AFVStepFun_mono_x hx y z s V)

/-- The almost-sure 3-argument predecessor operator (`AFpre1`/`apreXYZ` in the paper and in the
    Java): `s` is in `AFpre1 x y z` iff its row-action witness set `AFV x y z s` is nonempty,
    matching the Java's own `!(v.isEmpty())`. -/
noncomputable def AFpre1 (x y z : Set S) : Set S := {s | (C.AFV x y z s).Nonempty}

theorem AFpre1_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) :
    C.AFpre1 x y z1 ≤ C.AFpre1 x y z2 := fun s hs => hs.mono (C.AFV_mono_z x y hz s)

theorem AFpre1_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) :
    C.AFpre1 x y1 z ≤ C.AFpre1 x y2 z := fun s hs => hs.mono (C.AFV_mono_y x hy z s)

theorem AFpre1_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) :
    C.AFpre1 x1 y z ≤ C.AFpre1 x2 y z := fun s hs => hs.mono (C.AFV_mono_x hx y z s)

/-! ## `AFG`: almost-sure co-Büchi -/

/-- `AFG`'s **innermost** (`νY`) step, for fixed outer candidates `z`/`x`: a `b`-state reads
    `AFpre1(X,Y,Z)`; a non-`b` state reads `Apre1(X,Z)` -- note `Z`, the *outer* variable, not `Y`,
    confirmed directly against the Java's own `AFG` rather than assumed. -/
noncomputable def AFGInnerFun (b z x y : Set S) : Set S :=
  (C.AFpre1 x y z ∩ b) ∪ (bᶜ ∩ C.Apre1 x z)

theorem AFGInnerFun_mono_y (b z x : Set S) : Monotone (C.AFGInnerFun b z x) := by
  intro y1 y2 hy s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.AFpre1_mono_y x hy z h.1, h.2⟩
  · exact Or.inr h

/-- The innermost Bellman step, bundled as an `OrderHom` for fixed outer candidates `z`/`x`. -/
noncomputable def AFGInner (b z x : Set S) : Set S →o Set S where
  toFun := C.AFGInnerFun b z x
  monotone' := C.AFGInnerFun_mono_y b z x

/-- `AFG`'s **innermost** (`νY`) fixed point, for fixed outer candidates `z`/`x`. -/
noncomputable def AFGY (b z x : Set S) : Set S := (C.AFGInner b z x).gfp

theorem AFGInnerFun_mono_x (b z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) :
    C.AFGInnerFun b z x1 y ≤ C.AFGInnerFun b z x2 y := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.AFpre1_mono_x hx y z h.1, h.2⟩
  · exact Or.inr ⟨h.1, C.Apre1_mono_x hx z h.2⟩

/-- **The payoff.** `AFGY` is monotone in `x`, for fixed `z` -- `OrderHom.gfp_mono_of_le` applied
    to `AFGInnerFun_mono_x`, needed to bundle the middle (`μX`) level. -/
theorem AFGY_mono_x (b z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) :
    C.AFGY b z x1 ≤ C.AFGY b z x2 :=
  OrderHom.gfp_mono_of_le (fun y => C.AFGInnerFun_mono_x b z hx y)

/-- `AFG`'s **middle** (`μX`) step, bundled as an `OrderHom` for a fixed outer candidate `z`. -/
noncomputable def AFGMiddle (b z : Set S) : Set S →o Set S where
  toFun x := C.AFGY b z x
  monotone' := fun x1 x2 hx => C.AFGY_mono_x b z hx

/-- `AFG`'s **middle** (`μX`) fixed point, for a fixed outer candidate `z`. -/
noncomputable def AFGX (b z : Set S) : Set S := (C.AFGMiddle b z).lfp

theorem AFGInnerFun_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (x y : Set S) :
    C.AFGInnerFun b z1 x y ≤ C.AFGInnerFun b z2 x y := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.AFpre1_mono_z x y hz h.1, h.2⟩
  · exact Or.inr ⟨h.1, C.Apre1_mono_y x hz h.2⟩

theorem AFGY_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (x : Set S) :
    C.AFGY b z1 x ≤ C.AFGY b z2 x :=
  OrderHom.gfp_mono_of_le (fun y => C.AFGInnerFun_mono_z b hz x y)

/-- **The payoff.** `AFGX` is monotone in `z` -- `OrderHom.lfp_mono_of_le` applied to `AFGY_mono_z`,
    needed to bundle the outer (`νZ`) level. -/
theorem AFGX_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) :
    C.AFGX b z1 ≤ C.AFGX b z2 :=
  OrderHom.lfp_mono_of_le (fun x => C.AFGY_mono_z b hz x)

/-- **The payoff.** `AFG`'s outer (`νZ`) step, bundled as an `OrderHom` on `Set S`. -/
noncomputable def AFGOuter (b : Set S) : Set S →o Set S where
  toFun z := C.AFGX b z
  monotone' := fun z1 z2 hz => C.AFGX_mono_z b hz

/-- **The payoff.** Almost-sure co-Büchi (`AFG` in the Java, per LICS 2000 eq. 4, S4.2): the
    greatest fixed point of `AFGOuter`, the states from which the row player can force `b` to hold
    from some point on, almost surely. Three genuine `OrderHom` levels (`νZ.μX.νY`), the deepest
    almost-sure construction -- `LFG` (`Csg.QualitativeLimitSure`), one fixed-point layer deeper
    again via `LFpre1`'s nested `νV.μW`, is its limit-sure counterpart. -/
noncomputable def AFG (b : Set S) : Set S := (C.AFGOuter b).gfp

end CSG
end Csg
