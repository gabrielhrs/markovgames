/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Comp.FixLoop

/-!
# The qualitative operators, over a support function

**Status: confirmed by a clean `lake build`.**

Every qualitative operator in `Csg/` -- `Pre1`, `A`, `B`, `LW`, `Apre1`, `Lpre1`, and the fixed
points `G`, `AF` and `LF` above them -- consults the kernel through one thing only: the support of
`K s a1 a2`. None of them reads a probability. So each can be written once, as a computable
function of

    supp : S → A1 → A2 → Finset S

with no game in sight, and that is what this file does. It imports no `Csg` file and proves nothing
about one; it is the algorithm.

**What supplies `supp`** is up to the caller: a filter over a rational kernel row, the keys of a
sparse distribution, a table written out for one game. The operators neither know nor care, and two
callers with equal support functions run the same code on the same data.

**What says the result means anything** is `Comp/QualBridge.lean`: whenever `supp s a1 a2` is the
support of `C.K s a1 a2`, each operator here is the corresponding operator of `C` under
`Finset.coe`, and each loop returns the corresponding fixed point.

**The loops.** `gRegion`, `afRegion` and `lfRegion` run `Comp/FixLoop.lean`'s apply-compare-stop
loop, one, two and three levels deep. `mid` is the limit-sure middle step with the innermost climb
given as an iteration count rather than run to termination, for callers who certify that count
themselves.

**Instance arguments.** Each definition takes the `Fintype` and `DecidableEq` instances its own
body uses and no others, so the sections below differ in what they assume.
-/

namespace Comp

namespace Qual

variable {S A1 A2 : Type*}

/-! ## `Pre1`, and sure safety -/

section Pre1

variable [Fintype S] [Fintype A1] [Fintype A2] [DecidableEq S]

/-- The states from which some row action keeps every column response inside `x`. -/
def pre1 (supp : S → A1 → A2 → Finset S) (x : Finset S) : Finset S :=
  Finset.univ.filter fun s => ∃ a1, ∀ a2, supp s a1 a2 ⊆ x

@[simp]
theorem mem_pre1 (supp : S → A1 → A2 → Finset S) (x : Finset S) (s : S) :
    s ∈ pre1 supp x ↔ ∃ a1, ∀ a2, supp s a1 a2 ⊆ x := by
  simp only [pre1, Finset.mem_filter, Finset.mem_univ, true_and]

/-- One turn of the sure-safety descent: `Pre1(x) ∩ safe`. -/
def gStep (supp : S → A1 → A2 → Finset S) (safe x : Finset S) : Finset S :=
  pre1 supp x ∩ safe

/-- The sure-safety region: the descent from `Finset.univ`, run until it stops. -/
def gRegion (supp : S → A1 → A2 → Finset S) (safe : Finset S) : Finset S :=
  fixFrom (gStep supp safe) Finset.univ

end Pre1

/-! ## `A` and `B` -/

section A

variable [Fintype A1] [Fintype A2] [DecidableEq S] [DecidableEq A2]

/-- The row actions at `s` that keep every column response outside `v2` inside `y`. -/
def aSet (supp : S → A1 → A2 → Finset S) (v2 : Finset A2) (y : Finset S) (s : S) : Finset A1 :=
  Finset.univ.filter fun a1 => ∀ a2, a2 ∈ v2 ∨ supp s a1 a2 ⊆ y

@[simp]
theorem mem_aSet (supp : S → A1 → A2 → Finset S) (v2 : Finset A2) (y : Finset S) (s : S)
    (a1 : A1) : a1 ∈ aSet supp v2 y s ↔ ∀ a2, a2 ∈ v2 ∨ supp s a1 a2 ⊆ y := by
  simp only [aSet, Finset.mem_filter, Finset.mem_univ, true_and]

end A

section B

variable [Fintype A2] [DecidableEq S]

/-- The column actions at `s` against which some row action in `v1` can reach `x`. -/
def bSet (supp : S → A1 → A2 → Finset S) (v1 : Finset A1) (x : Finset S) (s : S) : Finset A2 :=
  Finset.univ.filter fun a2 => ∃ a1 ∈ v1, (supp s a1 a2 ∩ x).Nonempty

@[simp]
theorem mem_bSet (supp : S → A1 → A2 → Finset S) (v1 : Finset A1) (x : Finset S) (s : S)
    (a2 : A2) : a2 ∈ bSet supp v1 x s ↔ ∃ a1 ∈ v1, (supp s a1 a2 ∩ x).Nonempty := by
  simp only [bSet, Finset.mem_filter, Finset.mem_univ, true_and]

end B

/-! ## `Apre1`, and almost-sure reachability -/

section Apre1

variable [Fintype S] [Fintype A1] [Fintype A2] [DecidableEq S] [DecidableEq A2]

/-- One turn of the innermost `μW` climb: `w ↦ A (B w x s) y s`. -/
def lStep (supp : S → A1 → A2 → Finset S) (x y : Finset S) (s : S) (w : Finset A1) :
    Finset A1 :=
  aSet supp (bSet supp w x s) y s

/-- The states at which every column action can be driven into `x` by a row action safe for
    `y`. The row-action pool is read off `A ∅ y s`, with no fixed point. -/
def apre1 (supp : S → A1 → A2 → Finset S) (x y : Finset S) : Finset S :=
  Finset.univ.filter fun s => bSet supp (aSet supp ∅ y s) x s = Finset.univ

@[simp]
theorem mem_apre1 (supp : S → A1 → A2 → Finset S) (x y : Finset S) (s : S) :
    s ∈ apre1 supp x y ↔ bSet supp (aSet supp ∅ y s) x s = Finset.univ := by
  simp only [apre1, Finset.mem_filter, Finset.mem_univ, true_and]

/-- One turn of the almost-sure middle chain: `Apre1(x, y) ∪ b`. -/
def afStep (supp : S → A1 → A2 → Finset S) (b y x : Finset S) : Finset S :=
  apre1 supp x y ∪ b

/-- The middle `μX` fixed point at `y`: the climb from `∅`, run until it stops. -/
def afInner (supp : S → A1 → A2 → Finset S) (b y : Finset S) : Finset S :=
  fixFrom (afStep supp b y) ∅

/-- The almost-sure reachability region: the outer `νY` descent from `Finset.univ`, each step of
    which runs the middle loop. -/
def afRegion (supp : S → A1 → A2 → Finset S) (b : Finset S) : Finset S :=
  fixFrom (afInner supp b) Finset.univ

end Apre1

/-! ## `Lpre1`, and limit-sure reachability -/

section Lpre1

variable [Fintype S] [Fintype A2] [DecidableEq S] [DecidableEq A2]

/-- `Lpre1`, given a family `w` of row-action witness sets, one per state: the states at which
    every column action can be driven into `x` by a row action in `w s`. The second region `y` does
    not appear, because it enters only through `w`. -/
def lpre1 (supp : S → A1 → A2 → Finset S) (w : S → Finset A1) (x : Finset S) : Finset S :=
  Finset.univ.filter fun s => bSet supp (w s) x s = Finset.univ

@[simp]
theorem mem_lpre1 (supp : S → A1 → A2 → Finset S) (w : S → Finset A1) (x : Finset S) (s : S) :
    s ∈ lpre1 supp w x ↔ bSet supp (w s) x s = Finset.univ := by
  simp only [lpre1, Finset.mem_filter, Finset.mem_univ, true_and]

end Lpre1

section Loops

variable [Fintype S] [Fintype A1] [Fintype A2] [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

/-- The innermost `μW` fixed point at `(x, y, s)`: the climb from `∅`, run until it stops. -/
def lw (supp : S → A1 → A2 → Finset S) (x y : Finset S) (s : S) : Finset A1 :=
  fixFrom (lStep supp x y s) ∅

/-- One turn of the limit-sure middle chain, with the witness family taken to be `k` steps of the
    innermost climb. For a caller that certifies `k` suffices; `lmid` needs no such count. -/
def mid (supp : S → A1 → A2 → Finset S) (k : ℕ) (b y x : Finset S) : Finset S :=
  lpre1 supp (fun s => (lStep supp x y s)^[k] ∅) x ∪ b

/-- One turn of the limit-sure middle chain: `Lpre1(x, y) ∪ b`, with the witness family
    computed by the innermost loop. -/
def lmid (supp : S → A1 → A2 → Finset S) (b y x : Finset S) : Finset S :=
  lpre1 supp (lw supp x y) x ∪ b

/-- The middle `μX` fixed point at `y`. -/
def lfInner (supp : S → A1 → A2 → Finset S) (b y : Finset S) : Finset S :=
  fixFrom (lmid supp b y) ∅

/-- The limit-sure reachability region, which is the value-1 set: the outer `νY` descent from
    `Finset.univ`, over the middle `μX` climb, over the innermost `μW` climb at every state. -/
def lfRegion (supp : S → A1 → A2 → Finset S) (b : Finset S) : Finset S :=
  fixFrom (lfInner supp b) Finset.univ

end Loops

end Qual

end Comp
