/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.QualitativeAlmostSure

/-!
# Qualitative winning regions: limit-sure mode

**Status: confirmed by a clean `lake build`.** `Lpre1_empty_x` (a small general degeneracy fact,
`Lpre1 ∅ y = ∅`) supports `Csg.SkirmishProperties`'s limit-sure reachability argument.

**Why this file exists.** `Csg.QualitativeSure` and `Csg.QualitativeAlmostSure` split the
qualitative line along the *mode* axis the paper itself uses -- sure, almost-sure, limit-sure, each
computing the same four objective shapes (safety `G`, reachability `F`, co-Büchi `FG`, Büchi `GF`)
-- rather than along the order the pieces happened to get built in. This file is everything
limit-sure mode needs: `Lpre1` (the limit-sure analogue of `Apre1`), `LF`/`LGF` (reachability/
Büchi, both relocated from the old `QualitativeReachability.lean`), and `LFpre1`/`LFG` (the
3-argument predecessor and the co-Büchi construction on top of it, relocated from the old
`QualitativeLimitRecurrence.lean`).

**`Lpre1` (`lpreXY` in the Java), the one primitive this mode needs beyond
`Csg.QualitativeAlmostSure`.** Unlike `Apre1`, which is computed *directly* from `A`/`B` with no
fixed point of its own, `Lpre1`
needs an extra inner fixed point first -- per the Java's `lpreXY`, a least fixed point over
row-action subsets, `W = μW.(A(B(W,x),y))` (`LW`/`LStep` below), with `Lpre1 x y` then reading off
`B(W,x) = univ` exactly as `Apre1` does with its own (fixed-point-free) row-action witness set.
`LStep`'s monotonicity is the same `B_mono_v1`-then-`A_mono_v2` composition `AFpre1`'s own proofs
already use (`A_mono_v2`, monotone in the *excused-columns* argument, now lives in
`Csg.QualitativeAlmostSure` for exactly this reason -- both modes need it).

**`LF`/`LGF`'s shape.** Both are the same coupled `νY.μX` attractor-of-attractor construction
`AGF`/`SGF` already use (confirmed directly from the Java: `LF`'s outer `y` starts full and is
repeatedly reset to the inner `μX`-fixed-point, the identical control-flow shape `AGF` has --
almost/limit-sure reachability needs the coupling because `Apre1`/`Lpre1` themselves accumulate
probability across repeated attempts, unlike sure mode's plain `Pre1`, which is why `SF` alone
sufficed as a single `μX` there). `LF`'s inner formula drops `LGF`'s case split on `b` (just
`Lpre1(X,Y) ∨ b`, matching `AF`'s own case-split-free formula); `LGF` keeps the case split verbatim,
swapping `Apre1` for `Lpre1` on the non-`b` branch, matching the Java's own `LGF` relative to `AGF`.

**`LFpre1` (`lpreXYZ` in the paper and in the Java), and `LFG`'s shape.** Confirmed by a direct
re-read of `LFG` alongside `AFG` rather than assumed from the shared shape alone: `LFG`'s outer
control flow is `AFG`'s verbatim, with `lpreXYZ`/`lpreXY` substituted for `apreXYZ`/`apreXY` -- the
same substitution `LF`/`LGF` already made relative to `AF`/`AGF`. So `LFGInner`/`LFGMiddle`/
`LFGOuter` are line-for-line copies of `AFGInner`/`AFGMiddle`/`AFGOuter`, with `LFpre1`/`Lpre1`
standing in for `AFpre1`/`Apre1`. `AFpre1`'s own `AFV` needed only a single per-state `νV`: the map
`V ↦ A(∅,z,s) ∩ A(B(V,x,s),y,s)` has no fixed point of its own to solve, since the first factor is a
plain constant. `lpreXYZ`'s outer `v`-loop is not so simple -- for each candidate `v`, `ay :=
A(B(v,x,s),y,s)` is computed once and held constant while an *inner* variable `w` converges to its
own least fixed point, `μW.(A(B(W,x,s),z,s) ∩ ay)` (`LFW`/`LFWStep` below), before the outer loop
moves on. Only once `LFW` (the inner `μW` fixed point, as a function of `v`) is in hand does the
outer step make sense: `v ↦ LFW(v,x,y,z,s)` (`LFV`/`LFVStep`), one whole fixed-point layer deeper
than `AFV`'s single level, the deepest construction in the whole qualitative line. Three
monotonicity directions (`x`/`y`/`z`) are needed on `LFV`, each proved twice -- once at the inner
`μW` level, pointwise in `W`, then lifted to the outer `νV` level via `OrderHom.lfp_mono_of_le`, and
finally to `LFV` itself via `OrderHom.gfp_mono_of_le`.

Together with `Csg.QualitativeSure` (`G`/`SF`/`SFG`/`SGF`) and `Csg.QualitativeAlmostSure`
(`A`/`B`/`Apre1`/`AF`/`AGF`/`AFpre1`/`AFG`), this file completes every operator from the original
scope: `G`, `LF`, `LFG`, `LGF`, `A`, `AF`, `AFG`, `SF`, `SFG`, `SGF`, plus `AGF` from the agreed
scope-expansion.
-/

namespace Csg
namespace CSG

variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

/-! ## `Lpre1`, the limit-sure one-step predecessor -/

/-- **The payoff.** The per-state step whose least fixed point is `lpreXY`'s own row-action witness
    set `w`: `W ↦ A(B(W,x,s), y, s)`, monotone in `W` via `B_mono_v1` (widening the row-action pool
    `B` gets restricted to) then `A_mono_v2` (widening the excused-columns set that feeds `A`). -/
theorem LStepFun_mono (x y : Set S) (s : S) :
    Monotone (fun w : Set A1 => C.A (C.B w x s) y s) :=
  fun w1 w2 hw => C.A_mono_v2 y (C.B_mono_v1 x hw s) s

/-- `LStepFun` bundled as an `OrderHom` on `Set A1`, for a fixed state `s` and targets `x`/`y`. -/
noncomputable def LStep (x y : Set S) (s : S) : Set A1 →o Set A1 where
  toFun w := C.A (C.B w x s) y s
  monotone' := C.LStepFun_mono x y s

/-- The limit-sure predecessor's row-action witness set at state `s` -- unnamed in the Java, the
    value `w` converges to inside `lpreXY`'s inner loop: the least fixed point of `LStep`. -/
noncomputable def LW (x y : Set S) (s : S) : Set A1 := (C.LStep x y s).lfp

theorem LStepFun_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S) (w : Set A1) :
    C.A (C.B w x s) y1 s ≤ C.A (C.B w x s) y2 s :=
  C.A_mono_y (C.B w x s) hy s

/-- **The payoff.** `LW` is monotone in `y`, for fixed `x`: `LStepFun_mono_y` gives a pointwise
    operator inequality, and `OrderHom.lfp_mono_of_le` lifts it to the fixed points themselves. -/
theorem LW_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S) :
    C.LW x y1 s ≤ C.LW x y2 s :=
  OrderHom.lfp_mono_of_le (fun w => C.LStepFun_mono_y x hy s w)

theorem LStepFun_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) (s : S) (w : Set A1) :
    C.A (C.B w x1 s) y s ≤ C.A (C.B w x2 s) y s :=
  C.A_mono_v2 y (C.B_mono_x w hx s) s

/-- **The payoff.** `LW` is monotone in `x`, for fixed `y` -- the mirror of `LW_mono_y`. -/
theorem LW_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) (s : S) :
    C.LW x1 y s ≤ C.LW x2 y s :=
  OrderHom.lfp_mono_of_le (fun w => C.LStepFun_mono_x hx y s w)

/-- The limit-sure one-step predecessor operator (`Lpre1`/`lpreXY` in the paper and in the Java):
    `s` is in `Lpre1 x y` if the row-action witness set `LW x y s` (built by `lpreXY`'s own inner
    fixed point, rather than read off directly the way `Apre1`'s `A ∅ y s` is) already lets *every*
    column action escape into `x`. -/
noncomputable def Lpre1 (x y : Set S) : Set S := {s | C.B (C.LW x y s) x s = Set.univ}

/-- **The payoff, a degeneracy at the escape target.** `Lpre1 ∅ y` is `∅` outright, for any `y`:
    whatever `LW ∅ y s` converges to, `B`'s own escape test against the empty target `∅` always
    fails (`CSG.B_empty_x`), regardless. Needed wherever a fixed-point iteration for an `LF`-style
    operator starts its escape target from `⊥` (i.e. `∅`). -/
theorem Lpre1_empty_x (y : Set S) : C.Lpre1 (∅ : Set S) y = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  have heq : C.B (C.LW ∅ y s) (∅ : Set S) s = (Set.univ : Set A2) := hs
  rw [C.B_empty_x (C.LW ∅ y s) s] at heq
  have hmem : (Classical.arbitrary A2) ∈ (Set.univ : Set A2) := Set.mem_univ _
  rw [← heq] at hmem
  exact hmem

/-- **The payoff.** `Lpre1` is monotone in `y`, for fixed `x` -- `LW_mono_y` then `B_mono_v1`,
    squeezed back to equality against `Set.univ` exactly as `Apre1_mono_y` does. -/
theorem Lpre1_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) :
    C.Lpre1 x y1 ≤ C.Lpre1 x y2 := by
  intro s hs
  have hsub : C.B (C.LW x y1 s) x s ≤ C.B (C.LW x y2 s) x s :=
    C.B_mono_v1 x (C.LW_mono_y x hy s) s
  rw [hs] at hsub
  exact Set.Subset.antisymm (Set.subset_univ _) hsub

/-- **The payoff.** `Lpre1` is monotone in `x`, for fixed `y` -- `x` appears in both `LW` (via
    `LW_mono_x`) and the final `B` call, so this chains two steps: `LW_mono_x` first widens the
    row-action witness set, then `B_mono_x` widens the escape target itself. -/
theorem Lpre1_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) :
    C.Lpre1 x1 y ≤ C.Lpre1 x2 y := by
  intro s hs
  have hstep1 : C.B (C.LW x1 y s) x1 s ≤ C.B (C.LW x2 y s) x1 s :=
    C.B_mono_v1 x1 (C.LW_mono_x hx y s) s
  have hstep2 : C.B (C.LW x2 y s) x1 s ≤ C.B (C.LW x2 y s) x2 s :=
    C.B_mono_x (C.LW x2 y s) hx s
  have hsub := hstep1.trans hstep2
  rw [hs] at hsub
  exact Set.Subset.antisymm (Set.subset_univ _) hsub

/-! ## `LF`: limit-sure reachability -/

/-- `LF`'s **inner** (`μX`) step, for a fixed outer candidate `y`: `AFInnerFun` with `Apre1` swapped
    for `Lpre1`, matching the Java's own `LF` relative to `AF`. -/
noncomputable def LFInnerFun (b y x : Set S) : Set S := C.Lpre1 x y ∪ b

theorem LFInnerFun_mono (b y : Set S) : Monotone (C.LFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl (C.Lpre1_mono_x hx y h)
  · exact Or.inr h

/-- The inner Bellman step, bundled as an `OrderHom` for a fixed outer candidate `y`. -/
noncomputable def LFInner (b y : Set S) : Set S →o Set S where
  toFun := C.LFInnerFun b y
  monotone' := C.LFInnerFun_mono b y

theorem LFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.LFInnerFun b y1 x ≤ C.LFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl (C.Lpre1_mono_y x hy h)
  · exact Or.inr h

/-- **The payoff.** The `LF` Bellman operator, `Y ↦ μX.LFInnerFun b Y X`, bundled as an `OrderHom`
    on `Set S` via `OrderHom.lfp_mono_of_le` applied to `LFInnerFun_mono_y`. -/
noncomputable def LFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.LFInner b y).lfp
  monotone' := fun y1 y2 hy => OrderHom.lfp_mono_of_le (fun x => C.LFInnerFun_mono_y b hy x)

/-- **The payoff.** Limit-sure reachability (`LF` in the Java, per LICS 2000): the greatest fixed
    point of `LFOuter`, the states from which the row player can force reaching `b` in the limit. -/
noncomputable def LF (b : Set S) : Set S := (C.LFOuter b).gfp

/-! ## `LGF`: limit-sure Büchi -/

/-- `LGF`'s **inner** (`μX`) step, for a fixed outer candidate `y`: `AGFInnerFun` with `Apre1`
    swapped for `Lpre1` on the non-`b` branch, matching the Java's own `LGF` relative to `AGF`. -/
noncomputable def LGFInnerFun (b y x : Set S) : Set S := (C.Lpre1 x y ∩ bᶜ) ∪ (C.Pre1 y ∩ b)

theorem LGFInnerFun_mono (b y : Set S) : Monotone (C.LGFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Lpre1_mono_x hx y h.1, h.2⟩
  · exact Or.inr h

/-- The inner Bellman step, bundled as an `OrderHom` for a fixed outer candidate `y`. -/
noncomputable def LGFInner (b y : Set S) : Set S →o Set S where
  toFun := C.LGFInnerFun b y
  monotone' := C.LGFInnerFun_mono b y

theorem LGFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.LGFInnerFun b y1 x ≤ C.LGFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Lpre1_mono_y x hy h.1, h.2⟩
  · exact Or.inr ⟨C.Pre1_mono hy h.1, h.2⟩

/-- **The payoff.** The `LGF` Bellman operator, `Y ↦ μX.LGFInnerFun b Y X`, bundled as an
    `OrderHom` on `Set S` via `OrderHom.lfp_mono_of_le` applied to `LGFInnerFun_mono_y`. -/
noncomputable def LGFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.LGFInner b y).lfp
  monotone' := fun y1 y2 hy => OrderHom.lfp_mono_of_le (fun x => C.LGFInnerFun_mono_y b hy x)

/-- **The payoff.** Limit-sure Büchi (`LGF` in the Java, per LICS 2000): the greatest fixed point
    of `LGFOuter`, the states from which the row player can force visiting `b` infinitely often in
    the limit. -/
noncomputable def LGF (b : Set S) : Set S := (C.LGFOuter b).gfp

/-! ## `LFpre1`, the 3-argument limit-sure predecessor -/

/-- The per-state, per-outer-candidate `v` step whose least fixed point is `lpreXYZ`'s own inner
    row-action witness set `w`: `W ↦ A(B(W,x,s),z,s) ∩ A(B(v,x,s),y,s)` -- the first factor is
    `LStepFun`'s own `B_mono_v1`-then-`A_mono_v2` composition, the second is a constant (independent
    of `W`), so the whole map is monotone in `W`. -/
noncomputable def LFWStep (v : Set A1) (x y z : Set S) (s : S) : Set A1 →o Set A1 where
  toFun W := C.A (C.B W x s) z s ∩ C.A (C.B v x s) y s
  monotone' := by
    intro W1 W2 hW a1 ha1
    exact ⟨C.A_mono_v2 z (C.B_mono_v1 x hW s) s ha1.1, ha1.2⟩

/-- The limit-sure 3-argument predecessor's *inner* row-action witness set, for a fixed outer
    candidate `v` -- unnamed in the Java, the value `w` converges to inside `lpreXYZ`'s inner loop:
    the least fixed point of `LFWStep`. -/
noncomputable def LFW (v : Set A1) (x y z : Set S) (s : S) : Set A1 := (C.LFWStep v x y z s).lfp

theorem LFWStep_mono_v (x y z : Set S) {v1 v2 : Set A1} (hv : v1 ≤ v2) (s : S) (W : Set A1) :
    C.LFWStep v1 x y z s W ≤ C.LFWStep v2 x y z s W := by
  intro a1 ha1
  exact ⟨ha1.1, C.A_mono_v2 y (C.B_mono_v1 x hv s) s ha1.2⟩

/-- **The payoff.** `LFW` is monotone in the outer candidate `v`, for fixed `x`/`y`/`z` -- `v` only
    appears in the constant second factor, via `A_mono_v2`-then-`B_mono_v1` applied at the
    `B(v,x,s)`/`y` call. Needed to bundle the outer (`νV`) level. -/
theorem LFW_mono_v (x y z : Set S) {v1 v2 : Set A1} (hv : v1 ≤ v2) (s : S) :
    C.LFW v1 x y z s ≤ C.LFW v2 x y z s :=
  OrderHom.lfp_mono_of_le (fun W => C.LFWStep_mono_v x y z hv s W)

theorem LFWStep_mono_x (v : Set A1) (y z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) (s : S)
    (W : Set A1) : C.LFWStep v x1 y z s W ≤ C.LFWStep v x2 y z s W := by
  intro a1 ha1
  exact ⟨C.A_mono_v2 z (C.B_mono_x W hx s) s ha1.1, C.A_mono_v2 y (C.B_mono_x v hx s) s ha1.2⟩

/-- **The payoff.** `LFW` is monotone in `x`, for fixed `v`/`y`/`z` -- unlike `v`/`y`/`z`, `x`
    appears in *both* factors (every `B` call reads it), so both move: `B_mono_x` then `A_mono_v2`
    at the first factor's `B(W,x,s)`/`z` call, and again at the second factor's `B(v,x,s)`/`y`
    call. -/
theorem LFW_mono_x (v : Set A1) (y z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) (s : S) :
    C.LFW v x1 y z s ≤ C.LFW v x2 y z s :=
  OrderHom.lfp_mono_of_le (fun W => C.LFWStep_mono_x v y z hx s W)

theorem LFWStep_mono_y (v : Set A1) (x z : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S)
    (W : Set A1) : C.LFWStep v x y1 z s W ≤ C.LFWStep v x y2 z s W := by
  intro a1 ha1
  exact ⟨ha1.1, C.A_mono_y (C.B v x s) hy s ha1.2⟩

/-- **The payoff.** `LFW` is monotone in `y`, for fixed `v`/`x`/`z` -- `y` only appears in the
    constant second factor's own target slot, via `A_mono_y` at the `B(v,x,s)`/`y` call. -/
theorem LFW_mono_y (v : Set A1) (x z : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S) :
    C.LFW v x y1 z s ≤ C.LFW v x y2 z s :=
  OrderHom.lfp_mono_of_le (fun W => C.LFWStep_mono_y v x z hy s W)

theorem LFWStep_mono_z (v : Set A1) (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S)
    (W : Set A1) : C.LFWStep v x y z1 s W ≤ C.LFWStep v x y z2 s W := by
  intro a1 ha1
  exact ⟨C.A_mono_y (C.B W x s) hz s ha1.1, ha1.2⟩

/-- **The payoff.** `LFW` is monotone in `z`, for fixed `v`/`x`/`y` -- `z` only appears in the
    `W`-dependent first factor's own target slot, via `A_mono_y` at the `B(W,x,s)`/`z` call. -/
theorem LFW_mono_z (v : Set A1) (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S) :
    C.LFW v x y z1 s ≤ C.LFW v x y z2 s :=
  OrderHom.lfp_mono_of_le (fun W => C.LFWStep_mono_z v x y hz s W)

/-- `lpreXYZ`'s outer step, for a fixed state `s`: `V ↦ LFW(V,x,y,z,s)`, the inner `μW` fixed point
    read as a function of the outer candidate `V` -- monotone via `LFW_mono_v`, needed to bundle the
    outer (`νV`) level. -/
noncomputable def LFVStep (x y z : Set S) (s : S) : Set A1 →o Set A1 where
  toFun V := C.LFW V x y z s
  monotone' := fun v1 v2 hv => C.LFW_mono_v x y z hv s

/-- The limit-sure 3-argument predecessor's *outer* row-action witness set at state `s`, one whole
    fixed-point layer deeper than `AFV`: the greatest fixed point of `LFVStep`. -/
noncomputable def LFV (x y z : Set S) (s : S) : Set A1 := (C.LFVStep x y z s).gfp

theorem LFV_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) (s : S) :
    C.LFV x1 y z s ≤ C.LFV x2 y z s :=
  OrderHom.gfp_mono_of_le (fun V => C.LFW_mono_x V y z hx s)

theorem LFV_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) (s : S) :
    C.LFV x y1 z s ≤ C.LFV x y2 z s :=
  OrderHom.gfp_mono_of_le (fun V => C.LFW_mono_y V x z hy s)

theorem LFV_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S) :
    C.LFV x y z1 s ≤ C.LFV x y z2 s :=
  OrderHom.gfp_mono_of_le (fun V => C.LFW_mono_z V x y hz s)

/-- The limit-sure 3-argument predecessor operator (`LFpre1`/`lpreXYZ` in the paper and in the
    Java): `s` is in `LFpre1 x y z` iff its outer row-action witness set `LFV x y z s` is nonempty,
    matching the Java's own `!(v.isEmpty())`. -/
noncomputable def LFpre1 (x y z : Set S) : Set S := {s | (C.LFV x y z s).Nonempty}

theorem LFpre1_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) :
    C.LFpre1 x1 y z ≤ C.LFpre1 x2 y z := fun s hs => hs.mono (C.LFV_mono_x hx y z s)

theorem LFpre1_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) :
    C.LFpre1 x y1 z ≤ C.LFpre1 x y2 z := fun s hs => hs.mono (C.LFV_mono_y x hy z s)

theorem LFpre1_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) :
    C.LFpre1 x y z1 ≤ C.LFpre1 x y z2 := fun s hs => hs.mono (C.LFV_mono_z x y hz s)

/-! ## `LFG`: limit-sure co-Büchi -/

/-- `LFG`'s **innermost** (`νY`) step, for fixed outer candidates `z`/`x`: `AFGInnerFun` with
    `AFpre1`/`Apre1` swapped for `LFpre1`/`Lpre1`, matching the Java's own `LFG` relative to `AFG`.
    A `b`-state reads `LFpre1(X,Y,Z)`; a non-`b` state reads `Lpre1(X,Z)`, again the *outer*
    variable `Z`, not the innermost `Y`. -/
noncomputable def LFGInnerFun (b z x y : Set S) : Set S :=
  (C.LFpre1 x y z ∩ b) ∪ (bᶜ ∩ C.Lpre1 x z)

theorem LFGInnerFun_mono_y (b z x : Set S) : Monotone (C.LFGInnerFun b z x) := by
  intro y1 y2 hy s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.LFpre1_mono_y x hy z h.1, h.2⟩
  · exact Or.inr h

/-- The innermost Bellman step, bundled as an `OrderHom` for fixed outer candidates `z`/`x`. -/
noncomputable def LFGInner (b z x : Set S) : Set S →o Set S where
  toFun := C.LFGInnerFun b z x
  monotone' := C.LFGInnerFun_mono_y b z x

/-- `LFG`'s **innermost** (`νY`) fixed point, for fixed outer candidates `z`/`x`. -/
noncomputable def LFGY (b z x : Set S) : Set S := (C.LFGInner b z x).gfp

theorem LFGInnerFun_mono_x (b z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) :
    C.LFGInnerFun b z x1 y ≤ C.LFGInnerFun b z x2 y := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.LFpre1_mono_x hx y z h.1, h.2⟩
  · exact Or.inr ⟨h.1, C.Lpre1_mono_x hx z h.2⟩

/-- **The payoff.** `LFGY` is monotone in `x`, for fixed `z` -- `OrderHom.gfp_mono_of_le` applied
    to `LFGInnerFun_mono_x`, needed to bundle the middle (`μX`) level. -/
theorem LFGY_mono_x (b z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) :
    C.LFGY b z x1 ≤ C.LFGY b z x2 :=
  OrderHom.gfp_mono_of_le (fun y => C.LFGInnerFun_mono_x b z hx y)

/-- `LFG`'s **middle** (`μX`) step, bundled as an `OrderHom` for a fixed outer candidate `z`. -/
noncomputable def LFGMiddle (b z : Set S) : Set S →o Set S where
  toFun x := C.LFGY b z x
  monotone' := fun x1 x2 hx => C.LFGY_mono_x b z hx

/-- `LFG`'s **middle** (`μX`) fixed point, for a fixed outer candidate `z`. -/
noncomputable def LFGX (b z : Set S) : Set S := (C.LFGMiddle b z).lfp

theorem LFGInnerFun_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (x y : Set S) :
    C.LFGInnerFun b z1 x y ≤ C.LFGInnerFun b z2 x y := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.LFpre1_mono_z x y hz h.1, h.2⟩
  · exact Or.inr ⟨h.1, C.Lpre1_mono_y x hz h.2⟩

theorem LFGY_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (x : Set S) :
    C.LFGY b z1 x ≤ C.LFGY b z2 x :=
  OrderHom.gfp_mono_of_le (fun y => C.LFGInnerFun_mono_z b hz x y)

/-- **The payoff.** `LFGX` is monotone in `z` -- `OrderHom.lfp_mono_of_le` applied to
    `LFGY_mono_z`, needed to bundle the outer (`νZ`) level. -/
theorem LFGX_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) :
    C.LFGX b z1 ≤ C.LFGX b z2 :=
  OrderHom.lfp_mono_of_le (fun x => C.LFGY_mono_z b hz x)

/-- **The payoff.** `LFG`'s outer (`νZ`) step, bundled as an `OrderHom` on `Set S`. -/
noncomputable def LFGOuter (b : Set S) : Set S →o Set S where
  toFun z := C.LFGX b z
  monotone' := fun z1 z2 hz => C.LFGX_mono_z b hz

/-- **The payoff.** Limit-sure co-Büchi (`LFG` in the Java, per LICS 2000): the greatest fixed
    point of `LFGOuter`, the states from which the row player can force `b` to hold from some point
    on, in the limit. Three genuine `OrderHom` levels (`νZ.μX.νY`) exactly as `AFG` needed, each now
    built on `LFpre1`'s own two-fixed-point-layer predecessor rather than `AFpre1`'s single layer --
    the deepest construction in the qualitative line. -/
noncomputable def LFG (b : Set S) : Set S := (C.LFGOuter b).gfp

end CSG
end Csg
