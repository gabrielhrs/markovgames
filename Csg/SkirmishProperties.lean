/-
Copyright (c) 2026 Gabriel Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Santos
-/
import Csg.Skirmish
import Csg.QualitativeSure
import Csg.QualitativeAlmostSure
import Csg.QualitativeLimitSure

/-!
# Plain SKIRMISH: the 14 `skirmish.prism.props` sure/almost/limit facts

**Status: confirmed by a clean `lake build` through Section 7.** All 14 `sure`/`almost`/`limit`
facts from `skirmish.prism.props`, plus the three Büchi
facts Section 7 adds (`sure`/`almost` `false`, `limit` `true` -- the second headline
sure/almost-vs-limit divergence, alongside Section 3/4's reachability one), are now proven.
The single home for every qualitative fact about `Csg.Skirmish`'s model, one file rather than
branching into a new file per mode or per objective shape -- renamed from this file's original
name, `SkirmishSafety`, now that it is meant to grow past just safety. Organised into `##`-headed
sections below, one per `skirmish.prism.props` result group, in the order that file lists them and
in the agreed easier-first pace.

**Section 1: safety (`G`), and its trivial co-Büchi corollary -- done, confirmed clean.**
* `<<p1>> sure [ G !(s=1) ]` -- `RESULT: true` -- `skirmish_G_safe_true`.
* `<<p1>> sure [ G s=0 ]` -- `RESULT: false` -- `skirmish_hide_not_mem_G_singleton`.
* `<<p1>> sure [ F G !(s=1) ]` -- `RESULT: true` -- `skirmish_SFG_safe_true`.

Sure mode's `SFG b := SF (G b)` is a one-line reuse of `G`/`SF` themselves, so this one co-Büchi
fact rode along for free once safety was in hand. The almost-sure and limit-sure counterparts
(`AFG`/`LFG`, both also `true` per the props file) do **not** get the same shortcut -- unlike
`SFG`, they are genuine three-level `νZ.μX.νY` fixed points
(`Csg.QualitativeAlmostSure`/`Csg.QualitativeLimitSure`) with no reduction to `G`/`SF` -- so they
are deferred to a later section here, alongside Büchi, rather than attempted in this easy pass.

**Section 2: reachability (`F`), sure mode only -- done, confirmed clean.**
* `<<p1>> sure [ F s=2 ]` -- `RESULT: false` -- `skirmish_hide_not_mem_SF_home`.

The dual of Section 1's safety collapse: `SF`'s goal set `{home}` turns out to already be an
*exact* fixed point of its own one-step operator, so `SF {home} = {home}` on the nose.

**Section 3: reachability (`F`), almost-sure mode -- done, confirmed clean.**
* `<<p1>> almost [ F s=2 ]` -- `RESULT: false` -- `skirmish_hide_not_mem_AF_home`.

The first half of the headline sure/almost-vs-limit divergence LICS 2000 is about -- and, once
found, it does **not** need a genuine strategy-level probability argument in Lean at all: `AF` is
itself a *symbolic* (support-based) fixed-point algorithm, computable by hand exactly like `SF`
was, just with two nested fixed-point layers (`AFOuter`'s `νY`, wrapping `AFInner`'s `μX`) instead
of one. Hand-iterating `AFOuter {home}` downward from `⊤` converges in exactly two steps --
`⊤ ↦ skirmishSafe ↦ {home}` -- and a general two-step order-theoretic fact
(`OrderHom.gfp_le_map_map_top` below: `f.gfp ≤ f (f ⊤)`, for *any* monotone `f`, no continuity
hypothesis needed) turns that hand computation directly into a Lean proof: bound each step from
above by a single `OrderHom.lfp_le` pre-fixed-point check (`skirmish_AFOuter_top_le_safe`,
`skirmish_AFOuter_safe_le_home`) rather than computing the inner `lfp`s exactly. The one new
per-state fact both checks lean on, `skirmish_wet_not_mem_Apre1`, is reusable well beyond this
file: `wet`'s transition is constant, so it can never almost-surely escape into any goal set that
excludes it, regardless of `Apre1`'s other argument -- exactly the kind of fact `AFG`/`LFG`/`GF`
will need again later.

**Section 4: reachability (`F`), limit-sure mode -- done, confirmed clean.**
* `<<p1>> limit [ F s=2 ]` -- `RESULT: true` -- `skirmish_hide_mem_LF_home`.

The other half of the headline divergence, and genuinely the deepest proof in this file so far:
`LF` is `true`, so no finite *downward* iteration from `⊤` can witness it the way Section 3's
downward-to-`{home}` collapse witnessed `AF`'s `false` -- proving membership in a `gfp` needs a
*lower* bound, the dual technique. Mirroring `OrderHom.gfp_le_map_map_top`, a second general fact
(`OrderHom.map_map_bot_le_lfp`, added alongside it below: `f (f ⊥) ≤ f.lfp`, for any monotone `f`)
lower-bounds any least fixed point by two steps *up* from `⊥`, used **twice**, nested: once to
lower-bound the inner `LW` (`lpreXY`'s own row-action witness set, a `Set A1`-valued `lfp`) at
`hide`, showing it reaches `Set.univ` (both `SoldierMove`s) after two steps -- `∅ ↦ {hide}` (`hide`
alone is safe for `skirmishSafe`) `↦ {hide, run}` (once `throw` is escaped via `hide`, `run`
becomes safe too, since `wait` is now excused) -- and again to lower-bound the *outer*
`LFOuter {home}` at `skirmishSafe`, showing `skirmishSafe ↦ {home} ↦ skirmishSafe` closes the loop
(`skirmishSafe ⊆ LFOuter {home} skirmishSafe`), handing `OrderHom.le_gfp` exactly what it needs.
Two small general degeneracy facts about `B`/`Lpre1` at the empty set (`CSG.B_empty_v1`,
`CSG.B_empty_x` in `Csg.QualitativeAlmostSure`; `CSG.Lpre1_empty_x` in
`Csg.QualitativeLimitSure`) supply the `⊥`-level base case each nested computation starts from.

**Section 5: co-Büchi (`FG`), almost-sure mode -- done, confirmed clean.**
* `<<p1>> almost [ F G !(s=1) ]` -- `RESULT: true` -- `skirmish_hide_mem_AFG_safe`.

Unlike Section 1's sure-mode `SFG`, `AFG` gets no free ride off `A`/`G` alone -- it is a genuine
three-level `νZ.μX.νY` fixed point (`AFGOuter`'s `νZ`, wrapping `AFGMiddle`'s `μX`, wrapping
`AFGInner`'s `νY`). The saving grace, found by hand-simulating the construction on this tiny game:
setting *every* argument to `skirmishSafe` (`b = z = x = y = skirmishSafe`) makes every level
either an *exact* fixed point or a direct one-step post-fixed-point check, with no deep Kleene
iteration needed anywhere near as involved as Section 4's -- the one place genuine two-step
iteration still shows up is bounding `AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)` (the
`⊥`-level base case the middle `μX` level starts from), reusing `OrderHom.map_map_bot_le_lfp` a
second time, nested one level deeper than Section 4's own use of it. Two new per-state facts about
`A` (`skirmish_A_safe_hide_eq_singleton_hide`, `skirmish_A_safe_home_eq_univ`, the latter needing
no case split at all -- `home`'s transition is safe unconditionally) and two about `B`
(`skirmish_B_singleton_hide_safe_hide_eq_univ`, `skirmish_B_univ_safe_home_eq_univ`) feed the
`AFVStep` fixed-point checks at both states; the general `CSG.A_univ_v2` (added to
`Csg.QualitativeAlmostSure` alongside this section) is what turns "every column already excused"
into "every row action qualifies," needed once `AFVStep`'s witness set `V` itself reaches
`Set.univ`.

**Section 6: co-Büchi (`FG`), limit-sure mode -- done, confirmed clean.**
* `<<p1>> limit [ F G !(s=1) ]` -- `RESULT: true` -- `skirmish_hide_mem_LFG_safe`.

The outer `νZ.μX.νY` skeleton is `AFG`'s verbatim (`Csg.QualitativeLimitSure`'s own docstring
confirms `LFGInner`/`LFGMiddle`/`LFGOuter` are line-for-line copies of `AFGInner`/`AFGMiddle`/
`AFGOuter`, with `LFpre1`/`Lpre1` standing in for `AFpre1`/`Apre1`), and setting `b = z = x = y =
skirmishSafe` throughout carries over unchanged. The genuinely new work is one level further down:
`LFpre1`'s own witness set (`LFV`) is a `νV` wrapping an *inner* `μW` (`LFW`), one whole
fixed-point layer deeper than `AFpre1`'s `AFV` (a single, constant, fixed-point-free `νV`) -- the
deepest construction in the whole qualitative line, per `Csg.QualitativeLimitSure`'s own docstring.
Two shapes of `LFW` show up, both reusing Section 5's `A`/`B` facts directly rather than needing
new game-specific arithmetic: at the escape target `x := ∅`, `LFW` collapses to a *constant* map
(`CSG.B_empty_x` erases both its `B` calls at once, `skirmish_LFW_empty_safe_safe`) exactly as
`AFVStep` did at `x := ∅` in Section 5e; at `x := skirmishSafe`, picking the outer witness `v :=
Set.univ` makes `LFW`'s own `μW` fixed point reachable in the *same* two Kleene steps Section 4b's
`LW` needed (`∅ ↦ {hide} ↦ Set.univ` at `hide`, one step at `home`) -- `OrderHom.map_map_bot_le_lfp`
reused a third time, now to bound an *inner* `lfp` feeding an *outer* `gfp` (`LFV`) rather than a
bare top-level one. One new per-state `B` fact, `skirmish_B_univ_safe_hide_eq_univ`, is a one-line
monotonicity lift of Section 5b's `skirmish_B_singleton_hide_safe_hide_eq_univ` (widening the
row-action pool from `{hide}` to `Set.univ` can only add escapes) -- `home`'s analogue
(`skirmish_B_univ_safe_home_eq_univ`, Section 5b) already exists, no new fact needed there.

**Two new general lemmas Section 1/2 lean on**, added to `Csg.QualitativeSure` alongside this
file's first version: `CSG.G_subset` (`G safe ⊆ safe`, always) and `CSG.subset_SF` (`b ⊆ SF b`,
always), each a one-line read of `map_gfp`/`map_lfp`'s own fixed-point equation.

**Section 7: Büchi (`GF`) -- new this section.**
* `<<p1>> sure [ G F s=2 ]` -- `RESULT: false` -- `skirmish_hide_not_mem_SGF_home`.
* `<<p1>> almost [ G F s=2 ]` -- `RESULT: false` -- `skirmish_hide_not_mem_AGF_home`.
* `<<p1>> limit [ G F s=2 ]` -- `RESULT: true` -- `skirmish_hide_mem_LGF_home`.

The second headline divergence, and -- matching the intuition that motivated drafting it -- markedly
*less* work than the quantitative Büchi operator (`Csg.BuchiOp`) or even Sections 5/6's co-Büchi
`νZ.μX.νY` constructions: `SGF`/`AGF`/`LGF` are each a single coupled `νY.μX` fixed point (exactly
`SF`/`AF`/`LF`'s own shape, Sections 2-4), not a triple-nested one, and `SGFInnerFun`/`AGFInnerFun`/
`LGFInnerFun`'s non-`b` branch calls `Pre1`/`Apre1`/`Lpre1` directly -- the very same primitives
Sections 1-4 already fully worked out, with no extra fixed-point layer of their own (unlike `LFG`'s
`LFpre1`, which needed one). The result: almost every fact this section needs was already proven for
`SF`/`AF`/`LF`, reused here unchanged (`skirmishReachGoal_pre1_empty`, `skirmish_wet_not_mem_Apre1`,
`skirmish_Apre1_home_safe_subset`, `skirmish_hide_mem_Lpre1_home_safe`, `skirmishSafe_pre1`),
needing only *one* new Skirmish-specific fact (`skirmish_wet_not_mem_Pre1`, the `Pre1` sibling of
`skirmish_wet_not_mem_Apre1`) and no new general lemmas in any `Qualitative*.lean` file. `SGF`/`AGF`
both collapse `{home}` downward from `⊤` in exactly the same two Kleene steps (`⊤ ↦ skirmishSafe ↦
{home}`) `AF` used in Section 3, via the same `OrderHom.gfp_le_map_map_top` two-step bound; `LGF`
climbs `skirmishSafe` upward from `⊥` in exactly the same two Kleene steps (`⊥ ↦ {home} ↦
skirmishSafe`) `LF` used in Section 4, via the same `OrderHom.map_map_bot_le_lfp` two-step bound --
`skirmish_hide_mem_Lpre1_home_safe` doing all the real work again, unchanged. **Rabin-chain is
deliberately left out of this file's scope** (the paper's own harder tier, correctly anticipated as
"the tricky one" -- deferred pending a fresh go-ahead, not started here).

**Sections still to come**: none, for this file's original `sure`/`almost`/`limit`/`GF` scope --
every `skirmish.prism.props` result Sections 1-7 set out to reproduce is now proven. Rabin-chain
generalisation remains explicitly out of scope for this file, to be taken up separately if and when
it is wanted.
-/

/-- **A small general order-theoretic fact**, not specific to `CSG`/`Skirmish` at all: for *any*
    monotone `f` on *any* complete lattice, `f.gfp ≤ f (f ⊤)` -- no `ωScottContinuous`/continuity
    hypothesis needed, unlike the general Kleene-style characterisation
    (`OrderHom.gfp_eq_sInf_iterate`). Proof: `f.gfp ≤ ⊤` trivially, so by monotonicity
    `f (f.gfp) ≤ f ⊤`, and `f (f.gfp) = f.gfp` (`map_gfp`) turns this into `f.gfp ≤ f ⊤`; apply `f`
    (monotone) once more and use `map_gfp` again to get `f.gfp ≤ f (f ⊤)`. Kept local to this file
    since its only use here is bounding `AF`/`AFOuter` from above by two hand-computed steps rather
    than needing the exact fixed point. -/
theorem OrderHom.gfp_le_map_map_top {α : Type*} [CompleteLattice α] (f : α →o α) :
    f.gfp ≤ f (f ⊤) := by
  have h1 : f.gfp ≤ f ⊤ := by
    calc f.gfp = f f.gfp := f.map_gfp.symm
      _ ≤ f ⊤ := f.mono le_top
  calc f.gfp = f f.gfp := f.map_gfp.symm
    _ ≤ f (f ⊤) := f.mono h1

/-- **The dual small general order-theoretic fact**, needed for Section 4 below: for *any*
    monotone `f` on *any* complete lattice, `f (f ⊥) ≤ f.lfp` -- the mirror of
    `OrderHom.gfp_le_map_map_top` on the `lfp` side, proved the same way with `bot_le`/`map_lfp` in
    place of `le_top`/`map_gfp`. Where the `gfp` version *upper*-bounds a greatest fixed point by
    iterating down from `⊤`, this one *lower*-bounds a least fixed point by iterating up from `⊥`
    -- exactly what showing something is a *member* of a `gfp`-of-`lfp` construction like `LF`
    needs, dual to Section 3's membership-exclusion argument. -/
theorem OrderHom.map_map_bot_le_lfp {α : Type*} [CompleteLattice α] (f : α →o α) :
    f (f ⊥) ≤ f.lfp := by
  have h1 : f ⊥ ≤ f.lfp := by
    calc f ⊥ ≤ f f.lfp := f.mono bot_le
      _ = f.lfp := f.map_lfp
  calc f (f ⊥) ≤ f f.lfp := f.mono h1
    _ = f.lfp := f.map_lfp

namespace Csg

/-! ## Section 1a: the "avoid wet" safe set, and its pre-fixed-point fact -/

/-- The safety target from `skirmish.prism.props`'s `G !(s=1)`: every position except `wet`. An
    `abbrev`, not a `noncomputable def`, so that `DecidablePred`/`Decidable` instances for
    membership in it synthesise by unfolding during typeclass search -- the same reason
    `RockPaperScissorsSafety.lean`'s `rpsSafeUnresolved` is an `abbrev` rather than a `def`. -/
abbrev skirmishSafe : Set SkirmishPos := {s | s ≠ .wet}

/-- **The payoff.** `skirmishSafe` is a pre-fixed point of `Pre1`: from `hide`, staying put
    (`.hide`) keeps every sniper response inside `safe`; from `home`, *any* soldier move does,
    since `skirmishK_support_home` lands back at `hide ∈ safe` unconditionally regardless of the
    joint move. -/
theorem skirmishSafe_pre1 : skirmishSafe ⊆ skirmishCSG.Pre1 skirmishSafe := by
  intro s hs
  cases s with
  | wet => exact absurd rfl hs
  | hide =>
      refine ⟨.hide, ?_⟩
      intro a2
      cases a2 with
      | wait =>
          rw [skirmishK_support_hide_hide_wait]
          exact Set.singleton_subset_iff.mpr (by decide)
      | throw =>
          rw [skirmishK_support_hide_hide_throw]
          exact Set.singleton_subset_iff.mpr (by decide)
  | home =>
      refine ⟨.hide, ?_⟩
      intro a2
      rw [skirmishK_support_home]
      exact Set.singleton_subset_iff.mpr (by decide)

/-! ## Section 1b: `G !(s=1)`, sure-mode safety collapse -/

/-- **The payoff.** `G safe` is not merely *at least* `safe` -- it is *exactly* `safe`: `⊆` from
    the general `CSG.G_subset`; `⊇` from `OrderHom.le_gfp` applied to `skirmishSafe_pre1` (`safe`
    is already its own witness that it is a pre-fixed point of `GOrderHom safe`). -/
theorem skirmishSafe_eq_G : skirmishCSG.G skirmishSafe = skirmishSafe := by
  apply le_antisymm (skirmishCSG.G_subset skirmishSafe)
  have hle : skirmishSafe ≤ skirmishCSG.GOrderHom skirmishSafe skirmishSafe := by
    intro s hs
    exact ⟨skirmishSafe_pre1 hs, hs⟩
  exact (skirmishCSG.GOrderHom skirmishSafe).le_gfp hle

/-- **The headline true result.** `<<p1>> sure [ G !(s=1) ]`: from `hide`, the soldier can force
    avoiding `wet` forever, with certainty. -/
theorem skirmish_G_safe_true : SkirmishPos.hide ∈ skirmishCSG.G skirmishSafe := by
  rw [skirmishSafe_eq_G]
  decide

/-! ## Section 1c: `G s=0`, the non-trivial sure-mode false case -/

/-- **The headline false result.** `<<p1>> sure [ G s=0 ]`: from `hide`, the soldier canNOT force
    staying at `hide` forever -- every attempt to hold position is defeated by *some* sniper
    response (`(hide,throw)` or `(run,wait)`, both landing at `home`), so no single move survives
    every opponent reply. -/
theorem skirmish_hide_not_mem_G_singleton :
    SkirmishPos.hide ∉ skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos) := by
  intro hmem
  have hsub : skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos) ⊆ {SkirmishPos.hide} :=
    skirmishCSG.G_subset {SkirmishPos.hide}
  have h : skirmishCSG.GOrderHom ({SkirmishPos.hide} : Set SkirmishPos)
        (skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos))
      = skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos) :=
    (skirmishCSG.GOrderHom {SkirmishPos.hide}).map_gfp
  rw [← h] at hmem
  have hpre : SkirmishPos.hide ∈
      skirmishCSG.Pre1 (skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos)) := hmem.1
  have hpre' : SkirmishPos.hide ∈ skirmishCSG.Pre1 ({SkirmishPos.hide} : Set SkirmishPos) :=
    skirmishCSG.Pre1_mono hsub hpre
  obtain ⟨a1, ha1⟩ := hpre'
  cases a1 with
  | hide =>
      have hthrow := ha1 .throw
      rw [skirmishK_support_hide_hide_throw] at hthrow
      have hmemhide : SkirmishPos.home ∈ ({SkirmishPos.hide} : Set SkirmishPos) :=
        Set.singleton_subset_iff.mp hthrow
      exact absurd (Set.eq_of_mem_singleton hmemhide) (by decide)
  | run =>
      have hwait := ha1 .wait
      rw [skirmishK_support_hide_run_wait] at hwait
      have hmemhide : SkirmishPos.home ∈ ({SkirmishPos.hide} : Set SkirmishPos) :=
        Set.singleton_subset_iff.mp hwait
      exact absurd (Set.eq_of_mem_singleton hmemhide) (by decide)

/-! ## Section 1d: `F G !(s=1)`, sure-mode co-Büchi, a trivial regression check -/

/-- **The regression check.** `<<p1>> sure [ F G !(s=1) ]`: once "always avoid `wet`" is already
    forceable (`skirmish_G_safe_true`), "eventually always avoid `wet`" is immediate -- reaching a
    set you already occupy takes no strategy at all (`CSG.subset_SF`). No new fixed-point content
    beyond `skirmishSafe_eq_G`. -/
theorem skirmish_SFG_safe_true : SkirmishPos.hide ∈ skirmishCSG.SFG skirmishSafe := by
  change SkirmishPos.hide ∈ skirmishCSG.SF (skirmishCSG.G skirmishSafe)
  rw [skirmishSafe_eq_G]
  exact skirmishCSG.subset_SF skirmishSafe (by decide)

/-! ## Section 2a: `Pre1 {home} = ∅`, the dual of Section 1a -/

/-- **The payoff.** No state -- not even `home` itself -- has a row action that forces landing
    back in `{home}` in one more step against *every* sniper response: `wet` and `home` both
    ignore the joint move entirely and land somewhere else (`wet`/`hide` respectively, checked
    against any witness sniper move); `hide` fails for both its own row actions (`hide` loses to
    `(hide,wait)→hide`, `run` loses to `(run,throw)→wet`). The dual of `skirmishSafe_pre1`, which
    showed `safe` *does* sustain itself; here `{home}` provably does not. -/
theorem skirmishReachGoal_pre1_empty :
    skirmishCSG.Pre1 ({SkirmishPos.home} : Set SkirmishPos) = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  obtain ⟨a1, ha1⟩ := hs
  cases s with
  | wet =>
      have h := ha1 SniperMove.wait
      rw [skirmishK_support_wet] at h
      exact absurd (Set.eq_of_mem_singleton (Set.singleton_subset_iff.mp h)) (by decide)
  | home =>
      have h := ha1 SniperMove.wait
      rw [skirmishK_support_home] at h
      exact absurd (Set.eq_of_mem_singleton (Set.singleton_subset_iff.mp h)) (by decide)
  | hide =>
      cases a1 with
      | hide =>
          have h := ha1 .wait
          rw [skirmishK_support_hide_hide_wait] at h
          exact absurd (Set.eq_of_mem_singleton (Set.singleton_subset_iff.mp h)) (by decide)
      | run =>
          have h := ha1 .throw
          rw [skirmishK_support_hide_run_throw] at h
          exact absurd (Set.eq_of_mem_singleton (Set.singleton_subset_iff.mp h)) (by decide)

/-! ## Section 2b: `F s=2`, sure-mode reachability collapse -/

/-- **The payoff.** `SF {home}` is not merely *at most* `{home}` -- it is *exactly* `{home}`: `⊇`
    from the general `CSG.subset_SF`; `⊆` from `OrderHom.lfp_le_fixed` applied to
    `skirmishReachGoal_pre1_empty` (`{home}` is an exact fixed point of `SFOrderHom {home}`, since
    `Pre1 {home} ∪ {home} = ∅ ∪ {home} = {home}`). The dual of `skirmishSafe_eq_G`. -/
theorem skirmishReachGoal_eq_SF :
    skirmishCSG.SF ({SkirmishPos.home} : Set SkirmishPos) = {SkirmishPos.home} := by
  have hfixed : skirmishCSG.SFOrderHom ({SkirmishPos.home} : Set SkirmishPos)
      ({SkirmishPos.home} : Set SkirmishPos) = {SkirmishPos.home} := by
    change skirmishCSG.Pre1 ({SkirmishPos.home} : Set SkirmishPos) ∪ {SkirmishPos.home}
        = ({SkirmishPos.home} : Set SkirmishPos)
    rw [skirmishReachGoal_pre1_empty, Set.empty_union]
  exact le_antisymm
    ((skirmishCSG.SFOrderHom {SkirmishPos.home}).lfp_le_fixed hfixed)
    (skirmishCSG.subset_SF {SkirmishPos.home})

/-- **The headline false result.** `<<p1>> sure [ F s=2 ]`: from `hide`, the soldier canNOT force
    reaching `home` with certainty -- `hide` never even gets *added* to the sure-reachability
    fixed point, since nothing outside `{home}` can force its way in against an adversarial
    sniper, in even one more step. -/
theorem skirmish_hide_not_mem_SF_home :
    SkirmishPos.hide ∉ skirmishCSG.SF ({SkirmishPos.home} : Set SkirmishPos) := by
  rw [skirmishReachGoal_eq_SF]
  intro h
  exact absurd (Set.eq_of_mem_singleton h) (by decide)

/-! ## Section 3a: `wet` can never almost-surely escape a `wet`-free goal -/

/-- **The payoff, general beyond this section.** `wet`'s transition is constant (`skirmishK_wet`):
    whatever the joint move, the outcome is `wet` again, so its support can only ever meet a
    target `x` that already contains `wet`. If `x` doesn't, `B _ x wet` is `∅` for *any* row-action
    pool -- not just the specific one `A ∅ y wet` computes -- so `wet` fails `Apre1 x y`'s
    `B (...) = univ` test outright, regardless of `y`. -/
theorem skirmish_wet_not_mem_Apre1 (x y : Set SkirmishPos) (hx : SkirmishPos.wet ∉ x) :
    SkirmishPos.wet ∉ skirmishCSG.Apre1 x y := by
  intro hmem
  have heq : skirmishCSG.B (skirmishCSG.A ∅ y SkirmishPos.wet) x SkirmishPos.wet
      = (Set.univ : Set SniperMove) := hmem
  have hW : SniperMove.wait ∈
      skirmishCSG.B (skirmishCSG.A ∅ y SkirmishPos.wet) x SkirmishPos.wet := by
    rw [heq]; exact Set.mem_univ _
  obtain ⟨a1, _, y', hy'⟩ := hW
  rw [skirmishK_support_wet] at hy'
  have hyeq : y' = SkirmishPos.wet := Set.mem_singleton_iff.mp hy'.1
  rw [hyeq] at hy'
  exact hx hy'.2

/-! ## Section 3b: `AFOuter {home}` collapses from `⊤` to `{home}` in two steps -/

/-- **The payoff.** One step down from `⊤`: `AFOuter {home} ⊤ ≤ skirmishSafe` -- `wet` is excluded
    by `skirmish_wet_not_mem_Apre1` (`wet ∉ skirmishSafe`), and `hide`/`home` are trivially inside
    `skirmishSafe` regardless of whether they are genuinely in `Apre1` or not. A single
    `OrderHom.lfp_le` pre-fixed-point check against the candidate `skirmishSafe`, not an exact
    computation of the inner `lfp`. -/
theorem skirmish_Apre1_safe_top_subset :
    skirmishCSG.Apre1 skirmishSafe (⊤ : Set SkirmishPos) ⊆ skirmishSafe := by
  intro s hs
  cases s with
  | hide => decide
  | home => decide
  | wet => exact absurd hs (skirmish_wet_not_mem_Apre1 skirmishSafe ⊤ (by decide))

theorem skirmish_AFOuter_top_le_safe :
    skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤ ≤ skirmishSafe := by
  apply (skirmishCSG.AFInner ({SkirmishPos.home} : Set SkirmishPos) ⊤).lfp_le
  change skirmishCSG.Apre1 skirmishSafe (⊤ : Set SkirmishPos)
      ∪ ({SkirmishPos.home} : Set SkirmishPos) ⊆ skirmishSafe
  exact Set.union_subset skirmish_Apre1_safe_top_subset
    (Set.singleton_subset_iff.mpr (by decide))

/-- **The payoff.** The second step down, from `skirmishSafe` to `{home}`: `wet` is excluded again
    by `skirmish_wet_not_mem_Apre1`; `hide` needs real work -- restricting to row actions safe for
    `skirmishSafe` (`A ∅ skirmishSafe hide`) rules out `run` outright (`(run,throw) → wet ∉
    skirmishSafe`), leaving only `hide` itself, whose *own* outcome against `wait` is `hide`, not
    `home` -- so `wait` can never be escaped into `{home}`, and `Apre1`'s `B (...) = univ` test
    fails. Matches the informal check already recorded against `skirmish.prism`: `hide`'s only
    "safe" move stalls forever against a sniper who always waits. -/
theorem skirmish_hide_not_mem_Apre1_home_safe :
    SkirmishPos.hide ∉ skirmishCSG.Apre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by
  intro hmem
  have hrun_not_mem : SoldierMove.run ∉ skirmishCSG.A ∅ skirmishSafe SkirmishPos.hide := by
    intro hrun
    rcases hrun SniperMove.throw with h | h
    · exact h
    · rw [skirmishK_support_hide_run_throw] at h
      exact absurd (Set.singleton_subset_iff.mp h) (by decide)
  have heq : skirmishCSG.B (skirmishCSG.A ∅ skirmishSafe SkirmishPos.hide)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide
      = (Set.univ : Set SniperMove) := hmem
  have hW : SniperMove.wait ∈ skirmishCSG.B (skirmishCSG.A ∅ skirmishSafe SkirmishPos.hide)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide := by
    rw [heq]; exact Set.mem_univ _
  obtain ⟨a1, ha1, y', hy'⟩ := hW
  cases a1 with
  | run => exact hrun_not_mem ha1
  | hide =>
      rw [skirmishK_support_hide_hide_wait] at hy'
      have hyeq : y' = SkirmishPos.hide := Set.mem_singleton_iff.mp hy'.1
      rw [hyeq] at hy'
      exact absurd (Set.eq_of_mem_singleton hy'.2) (by decide)

theorem skirmish_Apre1_home_safe_subset :
    skirmishCSG.Apre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ⊆ ({SkirmishPos.home} : Set SkirmishPos) := by
  intro s hs
  cases s with
  | home => rfl
  | hide => exact absurd hs skirmish_hide_not_mem_Apre1_home_safe
  | wet => exact absurd hs (skirmish_wet_not_mem_Apre1 _ skirmishSafe (by decide))

theorem skirmish_AFOuter_safe_le_home :
    skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by
  apply (skirmishCSG.AFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe).lfp_le
  change skirmishCSG.Apre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ∪ ({SkirmishPos.home} : Set SkirmishPos) ⊆ ({SkirmishPos.home} : Set SkirmishPos)
  exact Set.union_subset skirmish_Apre1_home_safe_subset (Set.Subset.refl _)

/-! ## Section 3c: `F s=2`, almost-sure reachability collapse -/

/-- **The payoff.** `AF {home} ≤ {home}`: `OrderHom.gfp_le_map_map_top` turns the two hand-checked
    steps above (`⊤ ↦ skirmishSafe ↦ {home}`) directly into a bound on the actual greatest fixed
    point, with no need to compute it exactly. -/
theorem skirmish_AF_home_le_home :
    skirmishCSG.AF ({SkirmishPos.home} : Set SkirmishPos)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by
  have hstep : skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos)
      (skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
    ((skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos)).mono
      skirmish_AFOuter_top_le_safe).trans skirmish_AFOuter_safe_le_home
  exact (OrderHom.gfp_le_map_map_top
      (skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos))).trans hstep

/-- **The headline false result.** `<<p1>> almost [ F s=2 ]`: from `hide`, the soldier canNOT force
    reaching `home` almost surely (probability 1) -- the first half of the sure/almost-vs-limit
    divergence LICS 2000 is about. -/
theorem skirmish_hide_not_mem_AF_home :
    SkirmishPos.hide ∉ skirmishCSG.AF ({SkirmishPos.home} : Set SkirmishPos) := by
  intro hmem
  exact absurd (Set.eq_of_mem_singleton (skirmish_AF_home_le_home hmem)) (by decide)

/-! ## Section 4a: two per-state facts feeding the inner `LW` computation -/

/-- **The payoff.** `hide` is unconditionally safe for `skirmishSafe`, with *no* column actions
    excused: both of `hide`'s own responses (`(hide,wait) → hide`, `(hide,throw) → home`) already
    land in `skirmishSafe`. The base case (`v2 = ∅`) the inner `LW` computation starts from. -/
theorem skirmish_hide_mem_A_safe_hide :
    SoldierMove.hide ∈ skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide := by
  intro a2
  cases a2 with
  | wait =>
      right
      rw [skirmishK_support_hide_hide_wait]
      exact Set.singleton_subset_iff.mpr (by decide)
  | throw =>
      right
      rw [skirmishK_support_hide_hide_throw]
      exact Set.singleton_subset_iff.mpr (by decide)

/-- **The payoff.** `throw` escapes into `{home}` from `hide`, using the row action `hide` alone:
    `(hide,throw) → home`. Feeds the first real step of the inner `LW` computation. -/
theorem skirmish_throw_mem_B_singleton_hide_home :
    SniperMove.throw ∈ skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide := by
  refine ⟨SoldierMove.hide, rfl, SkirmishPos.home, ?_, rfl⟩
  rw [skirmishK_support_hide_hide_throw]
  rfl

/-- **The payoff.** Once `throw` is excused (already known escapable), *both* row actions become
    safe for `skirmishSafe`: `hide` because `throw` is excused and `wait → hide ∈ skirmishSafe`;
    `run` because `throw` is excused and `wait → home ∈ skirmishSafe`. The second real step of the
    inner `LW` computation, reaching `Set.univ`. -/
theorem skirmish_univ_subset_A_throw_safe_hide :
    (Set.univ : Set SoldierMove) ⊆
      skirmishCSG.A ({SniperMove.throw} : Set SniperMove) skirmishSafe SkirmishPos.hide := by
  intro a1 _
  cases a1 with
  | hide =>
      intro a2
      cases a2 with
      | throw => left; rfl
      | wait =>
          right
          rw [skirmishK_support_hide_hide_wait]
          exact Set.singleton_subset_iff.mpr (by decide)
  | run =>
      intro a2
      cases a2 with
      | throw => left; rfl
      | wait =>
          right
          rw [skirmishK_support_hide_run_wait]
          exact Set.singleton_subset_iff.mpr (by decide)

/-! ## Section 4b: the inner `LW` and `Lpre1` computations at `hide` -/

/-- **The payoff.** The inner row-action witness set `LW` reaches `Set.univ` at `hide`, against
    goal `{home}` and safety target `skirmishSafe`, in exactly two steps up from `⊥`:
    `∅ ↦ {hide} ↦ {hide, run} = univ`. `OrderHom.map_map_bot_le_lfp` turns this two-step hand
    computation directly into a lower bound on the actual least fixed point. -/
theorem skirmish_LW_home_safe_hide_eq_univ :
    skirmishCSG.LW ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe SkirmishPos.hide
      = (Set.univ : Set SoldierMove) := by
  apply le_antisymm (Set.subset_univ _)
  have hbot : skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      SkirmishPos.hide ⊥ = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide := by
    change skirmishCSG.A
        (skirmishCSG.B (⊥ : Set SoldierMove) ({SkirmishPos.home} : Set SkirmishPos)
          SkirmishPos.hide)
        skirmishSafe SkirmishPos.hide
      = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide
    rw [Set.bot_eq_empty, skirmishCSG.B_empty_v1]
  have hthrow_mem : SniperMove.throw ∈ skirmishCSG.B
      (skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        SkirmishPos.hide ⊥)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide := by
    rw [hbot]
    exact skirmishCSG.B_mono_v1 _
      (Set.singleton_subset_iff.mpr skirmish_hide_mem_A_safe_hide) _
      skirmish_throw_mem_B_singleton_hide_home
  have hffbot : (Set.univ : Set SoldierMove) ⊆
      skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe SkirmishPos.hide
        (skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
          SkirmishPos.hide ⊥) := by
    change (Set.univ : Set SoldierMove) ⊆ skirmishCSG.A
        (skirmishCSG.B
          (skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
            SkirmishPos.hide ⊥)
          ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide)
        skirmishSafe SkirmishPos.hide
    exact skirmish_univ_subset_A_throw_safe_hide.trans
      (skirmishCSG.A_mono_v2 skirmishSafe (Set.singleton_subset_iff.mpr hthrow_mem) _)
  exact hffbot.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LStep ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe SkirmishPos.hide))

/-- **The payoff.** Once `LW` is `Set.univ` (both row actions available with no columns excused),
    escaping into `{home}` from `hide` succeeds against *every* sniper response: `wait` via `run`
    (`(run,wait) → home`), `throw` via `hide` (`(hide,throw) → home`). -/
theorem skirmish_B_univ_home_hide_eq_univ :
    skirmishCSG.B (Set.univ : Set SoldierMove) ({SkirmishPos.home} : Set SkirmishPos)
      SkirmishPos.hide = (Set.univ : Set SniperMove) := by
  apply Set.eq_univ_of_forall
  intro a2
  cases a2 with
  | wait =>
      refine ⟨SoldierMove.run, Set.mem_univ _, SkirmishPos.home, ?_, rfl⟩
      rw [skirmishK_support_hide_run_wait]
      rfl
  | throw =>
      refine ⟨SoldierMove.hide, Set.mem_univ _, SkirmishPos.home, ?_, rfl⟩
      rw [skirmishK_support_hide_hide_throw]
      rfl

/-- **The payoff.** `hide` qualifies for `Lpre1 {home} skirmishSafe` outright: its `LW` witness set
    reaches `Set.univ` (`skirmish_LW_home_safe_hide_eq_univ`), and `Set.univ` escapes into `{home}`
    against every sniper response (`skirmish_B_univ_home_hide_eq_univ`) -- exactly `Lpre1`'s own
    `B (...) = univ` test. -/
theorem skirmish_hide_mem_Lpre1_home_safe :
    SkirmishPos.hide ∈ skirmishCSG.Lpre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by
  change skirmishCSG.B
      (skirmishCSG.LW ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe SkirmishPos.hide)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide = (Set.univ : Set SniperMove)
  rw [skirmish_LW_home_safe_hide_eq_univ]
  exact skirmish_B_univ_home_hide_eq_univ

/-! ## Section 4c: `F s=2`, limit-sure reachability collapse -/

/-- **The payoff.** `skirmishSafe` is a post-fixed point of `LFOuter {home}`, in exactly two steps
    up from `⊥`: `∅ ↦ {home} ↦ skirmishSafe` (`home` trivially, via the union with `b`; `hide` via
    `skirmish_hide_mem_Lpre1_home_safe`). `OrderHom.map_map_bot_le_lfp` turns this into a genuine
    lower bound on the inner `lfp`, handing `OrderHom.le_gfp` exactly the post-fixed-point
    hypothesis it needs. -/
theorem skirmish_safe_le_LFOuter_safe :
    skirmishSafe ≤ skirmishCSG.LFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by
  have hbot : skirmishCSG.LFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe ⊥
      = ({SkirmishPos.home} : Set SkirmishPos) := by
    change skirmishCSG.Lpre1 (⊥ : Set SkirmishPos) skirmishSafe
        ∪ ({SkirmishPos.home} : Set SkirmishPos) = ({SkirmishPos.home} : Set SkirmishPos)
    rw [Set.bot_eq_empty, skirmishCSG.Lpre1_empty_x, Set.empty_union]
  have hffbot : skirmishSafe ⊆
      skirmishCSG.LFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        (skirmishCSG.LFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe ⊥) := by
    rw [hbot]
    change skirmishSafe ⊆
        skirmishCSG.Lpre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
          ∪ ({SkirmishPos.home} : Set SkirmishPos)
    intro s hs
    cases s with
    | hide => exact Or.inl skirmish_hide_mem_Lpre1_home_safe
    | home => exact Or.inr rfl
    | wet => exact absurd hs (by decide)
  exact hffbot.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe))

/-- **The headline true result.** `<<p1>> limit [ F s=2 ]`: from `hide`, the soldier CAN force
    reaching `home` in the limit -- the other half of the sure/almost-vs-limit divergence LICS
    2000 is about. -/
theorem skirmish_hide_mem_LF_home :
    SkirmishPos.hide ∈ skirmishCSG.LF ({SkirmishPos.home} : Set SkirmishPos) :=
  (skirmishCSG.LFOuter ({SkirmishPos.home} : Set SkirmishPos)).le_gfp
    skirmish_safe_le_LFOuter_safe (by decide)

/-! ## Section 5a: two exact-value facts about `A ∅ safe` at `hide`/`home` -/

/-- **The payoff, the exclusion half of `skirmish_A_safe_hide_eq_singleton_hide`.** `run` is never
    safe for `skirmishSafe` at `hide`, columns unexcused: `(run,throw) → wet ∉ skirmishSafe`. The
    same argument already used inline inside Section 3b's `skirmish_hide_not_mem_Apre1_home_safe`,
    extracted here as its own fact for reuse. -/
theorem skirmish_run_not_mem_A_safe_hide :
    SoldierMove.run ∉ skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide := by
  intro hrun
  rcases hrun SniperMove.throw with h | h
  · exact h
  · rw [skirmishK_support_hide_run_throw] at h
    exact absurd (Set.singleton_subset_iff.mp h) (by decide)

/-- **The payoff.** `A ∅ safe hide` is not merely nonempty -- it is *exactly* `{hide}`: `⊇` from
    the already-proven `skirmish_hide_mem_A_safe_hide` (Section 4a); `⊆` from
    `skirmish_run_not_mem_A_safe_hide` (`SoldierMove` has only two constructors, so failing `run`
    leaves only `hide`). The exact value the `AFVStep` fixed-point check below needs -- an
    inclusion alone would not pin `AFVStep`'s image down to `{hide}` on the nose. -/
theorem skirmish_A_safe_hide_eq_singleton_hide :
    skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide = {SoldierMove.hide} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨skirmish_hide_mem_A_safe_hide, ?_⟩
  intro a1 ha1
  cases a1 with
  | hide => rfl
  | run => exact absurd ha1 skirmish_run_not_mem_A_safe_hide

/-- **The payoff, no case split needed at all.** Every row action is safe for `skirmishSafe` at
    `home`, columns unexcused: `home`'s transition (`skirmishK_support_home`) lands at `hide ∈
    skirmishSafe` unconditionally, regardless of *either* half of the joint move. -/
theorem skirmish_A_safe_home_eq_univ :
    skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.home = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a1 a2
  right
  rw [skirmishK_support_home]
  exact Set.singleton_subset_iff.mpr (by decide)

/-! ## Section 5b: two exact-value facts about `B` feeding the `AFVStep` fixed-point checks -/

/-- **The payoff.** Every sniper response escapes into `skirmishSafe` from `hide`, using the row
    action `hide` alone: `wait` via `(hide,wait) → hide ∈ skirmishSafe`, `throw` via `(hide,throw)
    → home ∈ skirmishSafe`. Simpler than Section 4a's analogous `{home}`-target computation, since
    the broader target `skirmishSafe` (rather than the singleton `{home}`) needs no two-step
    iteration -- `hide`'s own two outcomes already cover it. -/
theorem skirmish_B_singleton_hide_safe_hide_eq_univ :
    skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) skirmishSafe SkirmishPos.hide
      = (Set.univ : Set SniperMove) := by
  apply Set.eq_univ_of_forall
  intro a2
  cases a2 with
  | wait =>
      refine ⟨SoldierMove.hide, rfl, SkirmishPos.hide, ?_, by decide⟩
      rw [skirmishK_support_hide_hide_wait]
      rfl
  | throw =>
      refine ⟨SoldierMove.hide, rfl, SkirmishPos.home, ?_, by decide⟩
      rw [skirmishK_support_hide_hide_throw]
      rfl

/-- **The payoff.** Every sniper response escapes into `skirmishSafe` from `home`, for *any*
    row-action pool containing `hide` (in particular `Set.univ`): `home`'s transition lands at
    `hide ∈ skirmishSafe` regardless of the sniper's move, so `hide` alone already witnesses the
    escape for every `a2`. -/
theorem skirmish_B_univ_safe_home_eq_univ :
    skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home
      = (Set.univ : Set SniperMove) := by
  apply Set.eq_univ_of_forall
  intro a2
  refine ⟨SoldierMove.hide, Set.mem_univ _, SkirmishPos.hide, ?_, by decide⟩
  rw [skirmishK_support_home]
  rfl

/-! ## Section 5c: `{hide}`/`Set.univ` are exact fixed points of `AFVStep safe safe safe` -/

/-- **The payoff.** `{hide}` is an *exact* fixed point of `AFVStep safe safe safe` at `hide`: the
    constant first factor is `A ∅ safe hide = {hide}` (`skirmish_A_safe_hide_eq_singleton_hide`);
    the second factor collapses to `A Set.univ safe hide = Set.univ`
    (`skirmish_B_singleton_hide_safe_hide_eq_univ` feeding the general `CSG.A_univ_v2`), so the
    intersection is just the first factor again, on the nose. -/
theorem skirmish_AFVStep_safe_hide_fixed :
    skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide
        ({SoldierMove.hide} : Set SoldierMove)
      = ({SoldierMove.hide} : Set SoldierMove) := by
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide ∩
      skirmishCSG.A
        (skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) skirmishSafe SkirmishPos.hide)
        skirmishSafe SkirmishPos.hide
    = ({SoldierMove.hide} : Set SoldierMove)
  rw [skirmish_B_singleton_hide_safe_hide_eq_univ, skirmishCSG.A_univ_v2,
    skirmish_A_safe_hide_eq_singleton_hide, Set.inter_univ]

/-- **The payoff, the dual case at `home`.** `Set.univ` is an *exact* fixed point of `AFVStep safe
    safe safe` at `home`: both factors collapse to `Set.univ` on their own
    (`skirmish_A_safe_home_eq_univ`; `skirmish_B_univ_safe_home_eq_univ` feeding `CSG.A_univ_v2`
    again), so the intersection is `Set.univ` too. -/
theorem skirmish_AFVStep_safe_home_fixed :
    skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home
        (Set.univ : Set SoldierMove)
      = (Set.univ : Set SoldierMove) := by
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.home ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home)
        skirmishSafe SkirmishPos.home
    = (Set.univ : Set SoldierMove)
  rw [skirmish_B_univ_safe_home_eq_univ, skirmishCSG.A_univ_v2,
    skirmish_A_safe_home_eq_univ, Set.inter_univ]

/-- **The payoff.** `hide` is a member of `AFV safe safe safe hide` -- `OrderHom.le_gfp` applied to
    the exact fixed point `skirmish_AFVStep_safe_hide_fixed` (read backwards, as a post-fixed-point
    hypothesis), then `hide ∈ {hide}` trivially (`rfl`). -/
theorem skirmish_hide_mem_AFV_safe_safe_safe_hide :
    SoldierMove.hide ∈ skirmishCSG.AFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide :=
  (skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide).le_gfp
    (le_of_eq skirmish_AFVStep_safe_hide_fixed.symm) rfl

/-- **The payoff, the dual case at `home`.** `hide` is a member of `AFV safe safe safe home` too --
    the fixed point there is `Set.univ`, so *any* `SoldierMove` is a member, `hide` included. -/
theorem skirmish_hide_mem_AFV_safe_safe_safe_home :
    SoldierMove.hide ∈ skirmishCSG.AFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home :=
  (skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home).le_gfp
    (le_of_eq skirmish_AFVStep_safe_home_fixed.symm) (Set.mem_univ _)

/-! ## Section 5d: `AFpre1 safe safe safe` covers all of `skirmishSafe` -/

theorem skirmish_hide_mem_AFpre1_safe_safe_safe :
    SkirmishPos.hide ∈ skirmishCSG.AFpre1 skirmishSafe skirmishSafe skirmishSafe :=
  ⟨SoldierMove.hide, skirmish_hide_mem_AFV_safe_safe_safe_hide⟩

theorem skirmish_home_mem_AFpre1_safe_safe_safe :
    SkirmishPos.home ∈ skirmishCSG.AFpre1 skirmishSafe skirmishSafe skirmishSafe :=
  ⟨SoldierMove.hide, skirmish_hide_mem_AFV_safe_safe_safe_home⟩

/-- **The payoff.** Both non-`wet` states qualify for `AFpre1 safe safe safe`, so `skirmishSafe`
    itself sits inside it -- `wet` is excluded outright (`by decide`, `wet ∉ skirmishSafe` on the
    hypothesis side makes the `wet` case vacuous). Feeds Section 5f's innermost `νY` post-fixed
    check directly. -/
theorem skirmish_safe_subset_AFpre1_safe_safe_safe :
    skirmishSafe ⊆ skirmishCSG.AFpre1 skirmishSafe skirmishSafe skirmishSafe := by
  intro s hs
  cases s with
  | hide => exact skirmish_hide_mem_AFpre1_safe_safe_safe
  | home => exact skirmish_home_mem_AFpre1_safe_safe_safe
  | wet => exact absurd hs (by decide)

/-! ## Section 5e: the same chain again, with the escape target `x` set to `∅` -/

/-- **The payoff.** With the escape target `x` set to `∅`, `AFVStep`'s second factor collapses to
    a *constant* (`CSG.B_empty_x`: `B V ∅ s = ∅` for *any* row-action pool `V`), so the whole map
    no longer depends on its input `V` at all -- `{hide}` (in fact, *every* `V`) is trivially an
    exact fixed point at `hide`, since both factors reduce to the same constant
    `A ∅ safe hide = {hide}` (`Set.inter_self`). -/
theorem skirmish_AFVStep_empty_safe_safe_hide_fixed :
    skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.hide
        ({SoldierMove.hide} : Set SoldierMove)
      = ({SoldierMove.hide} : Set SoldierMove) := by
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide ∩
      skirmishCSG.A
        (skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) (∅ : Set SkirmishPos)
          SkirmishPos.hide)
        skirmishSafe SkirmishPos.hide
    = ({SoldierMove.hide} : Set SoldierMove)
  rw [skirmishCSG.B_empty_x, skirmish_A_safe_hide_eq_singleton_hide, Set.inter_self]

/-- **The payoff, the dual case at `home`.** The same constant-map collapse, at `home`: both
    factors reduce to `A ∅ safe home = Set.univ`, so `Set.univ` is the (trivial) exact fixed
    point. -/
theorem skirmish_AFVStep_empty_safe_safe_home_fixed :
    skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.home
        (Set.univ : Set SoldierMove)
      = (Set.univ : Set SoldierMove) := by
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.home ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) (∅ : Set SkirmishPos) SkirmishPos.home)
        skirmishSafe SkirmishPos.home
    = (Set.univ : Set SoldierMove)
  rw [skirmishCSG.B_empty_x, skirmish_A_safe_home_eq_univ, Set.inter_self]

theorem skirmish_hide_mem_AFV_empty_safe_safe_hide :
    SoldierMove.hide ∈
      skirmishCSG.AFV (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.hide :=
  (skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.hide).le_gfp
    (le_of_eq skirmish_AFVStep_empty_safe_safe_hide_fixed.symm) rfl

theorem skirmish_hide_mem_AFV_empty_safe_safe_home :
    SoldierMove.hide ∈
      skirmishCSG.AFV (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.home :=
  (skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.home).le_gfp
    (le_of_eq skirmish_AFVStep_empty_safe_safe_home_fixed.symm) (Set.mem_univ _)

theorem skirmish_hide_mem_AFpre1_empty_safe_safe :
    SkirmishPos.hide ∈ skirmishCSG.AFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe :=
  ⟨SoldierMove.hide, skirmish_hide_mem_AFV_empty_safe_safe_hide⟩

theorem skirmish_home_mem_AFpre1_empty_safe_safe :
    SkirmishPos.home ∈ skirmishCSG.AFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe :=
  ⟨SoldierMove.hide, skirmish_hide_mem_AFV_empty_safe_safe_home⟩

theorem skirmish_safe_subset_AFpre1_empty_safe_safe :
    skirmishSafe ⊆ skirmishCSG.AFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by
  intro s hs
  cases s with
  | hide => exact skirmish_hide_mem_AFpre1_empty_safe_safe
  | home => exact skirmish_home_mem_AFpre1_empty_safe_safe
  | wet => exact absurd hs (by decide)

/-! ## Section 5f: the innermost `νY` and middle `μX` post-fixed-point checks -/

/-- **The payoff.** `skirmishSafe` is a post-fixed point of `AFGInner safe safe safe`, at `y =
    safe`: every `s ∈ safe` takes the `b`-branch (`AFpre1 safe safe safe ∩ safe`), since it is
    already in both conjuncts (`skirmish_safe_subset_AFpre1_safe_safe_safe`, and `hs` itself). -/
theorem skirmish_safe_le_AFGInner_safe_safe_safe :
    skirmishSafe ≤ skirmishCSG.AFGInner skirmishSafe skirmishSafe skirmishSafe skirmishSafe := by
  intro s hs
  change s ∈ (skirmishCSG.AFpre1 skirmishSafe skirmishSafe skirmishSafe ∩ skirmishSafe) ∪
      (skirmishSafeᶜ ∩ skirmishCSG.Apre1 skirmishSafe skirmishSafe)
  exact Or.inl ⟨skirmish_safe_subset_AFpre1_safe_safe_safe hs, hs⟩

/-- **The payoff.** `skirmishSafe ≤ AFGY safe safe safe` -- `OrderHom.le_gfp` applied directly to
    the post-fixed-point check above. -/
theorem skirmish_safe_le_AFGY_safe_safe_safe :
    skirmishSafe ≤ skirmishCSG.AFGY skirmishSafe skirmishSafe skirmishSafe :=
  (skirmishCSG.AFGInner skirmishSafe skirmishSafe skirmishSafe).le_gfp
    skirmish_safe_le_AFGInner_safe_safe_safe

/-- **The payoff, the `x := ∅` analogue.** The exact same post-fixed-point argument, with the
    escape target threaded through `AFpre1`/`Apre1` set to `∅` instead of `skirmishSafe` -- feeds
    the `⊥`-level base case `AFGY safe safe ∅` the middle `μX` level's two-step bound needs. -/
theorem skirmish_safe_le_AFGInner_safe_safe_empty :
    skirmishSafe ≤
      skirmishCSG.AFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos) skirmishSafe := by
  intro s hs
  change s ∈
      (skirmishCSG.AFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe ∩ skirmishSafe) ∪
        (skirmishSafeᶜ ∩ skirmishCSG.Apre1 (∅ : Set SkirmishPos) skirmishSafe)
  exact Or.inl ⟨skirmish_safe_subset_AFpre1_empty_safe_safe hs, hs⟩

theorem skirmish_safe_le_AFGY_safe_safe_empty :
    skirmishSafe ≤ skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos) :=
  (skirmishCSG.AFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos)).le_gfp
    skirmish_safe_le_AFGInner_safe_safe_empty

/-- **The payoff, the middle `μX` level.** `skirmishSafe ≤ AFGX safe safe`: chase `AFGY`'s own
    monotonicity in `x` (`CSG.AFGY_mono_x`) from the `⊥`-level bound just established up to
    `skirmishSafe` itself, giving a two-step-from-`⊥` lower bound on `AFGMiddle safe safe`'s image,
    then hand it to `OrderHom.map_map_bot_le_lfp` -- the exact same technique Section 4c uses for
    `LFOuter`, nested one level deeper here. -/
theorem skirmish_safe_le_AFGX_safe_safe :
    skirmishSafe ≤ skirmishCSG.AFGX skirmishSafe skirmishSafe := by
  have hmono : skirmishCSG.AFGY skirmishSafe skirmishSafe skirmishSafe ≤
      skirmishCSG.AFGY skirmishSafe skirmishSafe
        (skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)) :=
    skirmishCSG.AFGY_mono_x skirmishSafe skirmishSafe skirmish_safe_le_AFGY_safe_safe_empty
  have hchain : skirmishSafe ≤
      skirmishCSG.AFGY skirmishSafe skirmishSafe
        (skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)) :=
    skirmish_safe_le_AFGY_safe_safe_safe.trans hmono
  have hbot : skirmishCSG.AFGMiddle skirmishSafe skirmishSafe (⊥ : Set SkirmishPos)
      = skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos) := by
    change skirmishCSG.AFGY skirmishSafe skirmishSafe (⊥ : Set SkirmishPos)
      = skirmishCSG.AFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)
    rw [Set.bot_eq_empty]
  have hffbot : skirmishSafe ≤
      skirmishCSG.AFGMiddle skirmishSafe skirmishSafe
        (skirmishCSG.AFGMiddle skirmishSafe skirmishSafe ⊥) := by
    change skirmishSafe ≤ skirmishCSG.AFGY skirmishSafe skirmishSafe
        (skirmishCSG.AFGMiddle skirmishSafe skirmishSafe ⊥)
    rw [hbot]
    exact hchain
  exact hffbot.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.AFGMiddle skirmishSafe skirmishSafe))

/-! ## Section 5g: `F G !(s=1)`, almost-sure co-Büchi collapse -/

/-- **The headline true result.** `<<p1>> almost [ F G !(s=1) ]`: from `hide`, the soldier CAN
    force eventually always avoiding `wet`, almost surely -- `OrderHom.le_gfp` applied to the outer
    (`νZ`) post-fixed-point check, `skirmishSafe ≤ AFGX safe safe`, then `hide ∈ skirmishSafe`
    trivially (`by decide`). -/
theorem skirmish_hide_mem_AFG_safe :
    SkirmishPos.hide ∈ skirmishCSG.AFG skirmishSafe :=
  (skirmishCSG.AFGOuter skirmishSafe).le_gfp skirmish_safe_le_AFGX_safe_safe (by decide)

/-! ## Section 6a: `B Set.univ safe hide = Set.univ`, the one new `B` fact this section needs -/

/-- **The payoff.** A one-line monotonicity lift of Section 5b's `skirmish_B_singleton_hide_safe_
    hide_eq_univ`: widening the row-action pool from `{hide}` to `Set.univ` can only add escapes,
    and the target is already `Set.univ` on the nose, so equality survives. -/
theorem skirmish_B_univ_safe_hide_eq_univ :
    skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.hide
      = (Set.univ : Set SniperMove) := by
  apply le_antisymm (Set.subset_univ _)
  calc (Set.univ : Set SniperMove)
      = skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) skirmishSafe SkirmishPos.hide :=
        skirmish_B_singleton_hide_safe_hide_eq_univ.symm
    _ ≤ skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.hide :=
        skirmishCSG.B_mono_v1 skirmishSafe
          (Set.subset_univ ({SoldierMove.hide} : Set SoldierMove)) SkirmishPos.hide

/-! ## Section 6b: `LFW` collapses to a constant, at the escape target `x := ∅` -/

/-- **The payoff.** With the escape target `x` set to `∅`, *both* of `LFWStep`'s `B` calls
    collapse via `CSG.B_empty_x` regardless of their row-action argument (the inner `W` and the
    outer witness `v` alike), leaving the same constant `A ∅ safe s` on both sides of the
    intersection (`Set.inter_self`) -- so `LFW`'s own `μW` fixed point is exactly that constant,
    for *any* outer witness `v`. The `LFpre1`-level mirror of Section 5e's `AFVStep`-at-`x:=∅`
    collapse, one layer further in. -/
theorem skirmish_LFW_empty_safe_safe (v : Set SoldierMove) (s : SkirmishPos) :
    skirmishCSG.LFW v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s
      = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s := by
  have hconst : ∀ W : Set SoldierMove,
      skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s W
        = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s := by
    intro W
    change skirmishCSG.A (skirmishCSG.B W (∅ : Set SkirmishPos) s) skirmishSafe s ∩
        skirmishCSG.A (skirmishCSG.B v (∅ : Set SkirmishPos) s) skirmishSafe s
      = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s
    rw [skirmishCSG.B_empty_x, skirmishCSG.B_empty_x, Set.inter_self]
  apply le_antisymm
  · exact (skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s).lfp_le
      (le_of_eq (hconst (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s)))
  · calc skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s
        = skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s ⊥ :=
          (hconst ⊥).symm
      _ ≤ skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s
            (skirmishCSG.LFW v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s) :=
          (skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s).mono bot_le
      _ = skirmishCSG.LFW v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s :=
          (skirmishCSG.LFWStep v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s).map_lfp

/-! ## Section 6c: `LFpre1 ∅ safe safe` covers all of `skirmishSafe` -/

/-- **The payoff.** Since `LFVStep ∅ safe safe s` is `V ↦ LFW V ∅ safe safe s`, and the latter is
    the *same* constant `A ∅ safe s` regardless of `V` (`skirmish_LFW_empty_safe_safe`), that
    constant is trivially a post-fixed point of `LFVStep ∅ safe safe s` at itself -- `OrderHom.
    le_gfp` turns this into a lower bound on the actual `LFV`. -/
theorem skirmish_A_empty_safe_le_LFV_empty_safe_safe (s : SkirmishPos) :
    skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s ≤
      skirmishCSG.LFV (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s := by
  apply (skirmishCSG.LFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s).le_gfp
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s ≤
      skirmishCSG.LFW (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s)
        (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s
  exact le_of_eq
    (skirmish_LFW_empty_safe_safe (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s) s).symm

theorem skirmish_hide_mem_LFpre1_empty_safe_safe :
    SkirmishPos.hide ∈ skirmishCSG.LFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by
  have hne : (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide).Nonempty :=
    ⟨SoldierMove.hide, skirmish_hide_mem_A_safe_hide⟩
  exact hne.mono (skirmish_A_empty_safe_le_LFV_empty_safe_safe SkirmishPos.hide)

theorem skirmish_home_mem_LFpre1_empty_safe_safe :
    SkirmishPos.home ∈ skirmishCSG.LFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by
  have hne : (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.home).Nonempty := by
    rw [skirmish_A_safe_home_eq_univ]
    exact ⟨SoldierMove.hide, Set.mem_univ _⟩
  exact hne.mono (skirmish_A_empty_safe_le_LFV_empty_safe_safe SkirmishPos.home)

theorem skirmish_safe_subset_LFpre1_empty_safe_safe :
    skirmishSafe ⊆ skirmishCSG.LFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by
  intro s hs
  cases s with
  | hide => exact skirmish_hide_mem_LFpre1_empty_safe_safe
  | home => exact skirmish_home_mem_LFpre1_empty_safe_safe
  | wet => exact absurd hs (by decide)

/-! ## Section 6d: the innermost `νY` post-fixed check, at the escape target `x := ∅` -/

/-- **The payoff, the `LFG` mirror of Section 5f's `AFG` version.** `skirmishSafe` is a post-fixed
    point of `LFGInner safe safe ∅`, at `y = safe`: every `s ∈ safe` takes the `b`-branch, since it
    is already in both conjuncts (`skirmish_safe_subset_LFpre1_empty_safe_safe`, and `hs` itself).
    Feeds the `⊥`-level base case the middle `μX` level's two-step bound needs. -/
theorem skirmish_safe_le_LFGInner_safe_safe_empty :
    skirmishSafe ≤
      skirmishCSG.LFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos) skirmishSafe := by
  intro s hs
  change s ∈
      (skirmishCSG.LFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe ∩ skirmishSafe) ∪
        (skirmishSafeᶜ ∩ skirmishCSG.Lpre1 (∅ : Set SkirmishPos) skirmishSafe)
  exact Or.inl ⟨skirmish_safe_subset_LFpre1_empty_safe_safe hs, hs⟩

theorem skirmish_safe_le_LFGY_safe_safe_empty :
    skirmishSafe ≤ skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos) :=
  (skirmishCSG.LFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos)).le_gfp
    skirmish_safe_le_LFGInner_safe_safe_empty

/-! ## Section 6e: `LFW Set.univ safe safe · = Set.univ`, the deepest computation in this file -/

/-- **The payoff.** At `x := skirmishSafe`, picking the outer witness `v := Set.univ` makes the
    second (constant) factor of `LFWStep` reduce to `Set.univ` outright
    (`skirmish_B_univ_safe_hide_eq_univ` feeding `CSG.A_univ_v2`), so the whole map reduces to
    `LStep safe safe hide` alone (`Set.inter_univ`) -- the *same* map Section 4b's `LW` already
    Kleene-iterated, converging in the *same* two steps: `∅ ↦ {hide} ↦ Set.univ`.
    `OrderHom.map_map_bot_le_lfp` turns this into a genuine lower bound on `LFW`'s own `μW` fixed
    point, pinning it to `Set.univ` exactly since `Set.univ` is already the top. -/
theorem skirmish_LFW_univ_safe_hide_eq_univ :
    skirmishCSG.LFW (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
        SkirmishPos.hide
      = (Set.univ : Set SoldierMove) := by
  apply le_antisymm (Set.subset_univ _)
  have hconst : skirmishCSG.A
      (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.hide)
      skirmishSafe SkirmishPos.hide = (Set.univ : Set SoldierMove) := by
    rw [skirmish_B_univ_safe_hide_eq_univ, skirmishCSG.A_univ_v2]
  have hbot : skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe
      skirmishSafe SkirmishPos.hide ⊥ = ({SoldierMove.hide} : Set SoldierMove) := by
    change skirmishCSG.A
        (skirmishCSG.B (⊥ : Set SoldierMove) skirmishSafe SkirmishPos.hide) skirmishSafe
        SkirmishPos.hide ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.hide) skirmishSafe
        SkirmishPos.hide
      = ({SoldierMove.hide} : Set SoldierMove)
    rw [Set.bot_eq_empty, skirmishCSG.B_empty_v1, hconst, Set.inter_univ,
      skirmish_A_safe_hide_eq_singleton_hide]
  have hstep2 : skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe
      skirmishSafe SkirmishPos.hide
      (skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
        SkirmishPos.hide ⊥)
      = (Set.univ : Set SoldierMove) := by
    rw [hbot]
    change skirmishCSG.A
        (skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) skirmishSafe SkirmishPos.hide)
        skirmishSafe SkirmishPos.hide ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.hide) skirmishSafe
        SkirmishPos.hide
      = (Set.univ : Set SoldierMove)
    rw [skirmish_B_singleton_hide_safe_hide_eq_univ, skirmishCSG.A_univ_v2, hconst,
      Set.inter_univ]
  exact (le_of_eq hstep2.symm).trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
      SkirmishPos.hide))

/-- **The payoff, the dual case at `home`.** The same argument at `home`: both factors already
    reduce to `Set.univ` after just *one* step from `⊥` (`skirmish_A_safe_home_eq_univ`,
    `skirmish_B_univ_safe_home_eq_univ` feeding `CSG.A_univ_v2`), so the second Kleene step (`hbot`
    substituted into itself) simply reconfirms `Set.univ`, and `OrderHom.map_map_bot_le_lfp` still
    applies unchanged. -/
theorem skirmish_LFW_univ_safe_home_eq_univ :
    skirmishCSG.LFW (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
        SkirmishPos.home
      = (Set.univ : Set SoldierMove) := by
  apply le_antisymm (Set.subset_univ _)
  have hconst : skirmishCSG.A
      (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home)
      skirmishSafe SkirmishPos.home = (Set.univ : Set SoldierMove) := by
    rw [skirmish_B_univ_safe_home_eq_univ, skirmishCSG.A_univ_v2]
  have hbot : skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe
      skirmishSafe SkirmishPos.home ⊥ = (Set.univ : Set SoldierMove) := by
    change skirmishCSG.A
        (skirmishCSG.B (⊥ : Set SoldierMove) skirmishSafe SkirmishPos.home) skirmishSafe
        SkirmishPos.home ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home) skirmishSafe
        SkirmishPos.home
      = (Set.univ : Set SoldierMove)
    rw [Set.bot_eq_empty, skirmishCSG.B_empty_v1, skirmish_A_safe_home_eq_univ, hconst,
      Set.inter_univ]
  have hstep2 : skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe
      skirmishSafe SkirmishPos.home
      (skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
        SkirmishPos.home ⊥)
      = (Set.univ : Set SoldierMove) := by
    rw [hbot]
    change skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home) skirmishSafe
        SkirmishPos.home ∩
      skirmishCSG.A
        (skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home) skirmishSafe
        SkirmishPos.home
      = (Set.univ : Set SoldierMove)
    rw [hconst, Set.inter_univ]
  exact (le_of_eq hstep2.symm).trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LFWStep (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
      SkirmishPos.home))

/-! ## Section 6f: `LFpre1 safe safe safe` covers all of `skirmishSafe` -/

/-- **The payoff.** `Set.univ` is a post-fixed point of `LFVStep safe safe safe hide` at itself
    (`LFVStep`'s own value there is exactly `LFW Set.univ safe safe safe hide`,
    `skirmish_LFW_univ_safe_hide_eq_univ`) -- `OrderHom.le_gfp` turns this into a lower bound on
    the actual `LFV`. -/
theorem skirmish_univ_le_LFV_safe_safe_safe_hide :
    (Set.univ : Set SoldierMove) ≤
      skirmishCSG.LFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide :=
  (skirmishCSG.LFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide).le_gfp
    (le_of_eq skirmish_LFW_univ_safe_hide_eq_univ.symm)

/-- **The payoff, the dual case at `home`.** -/
theorem skirmish_univ_le_LFV_safe_safe_safe_home :
    (Set.univ : Set SoldierMove) ≤
      skirmishCSG.LFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home :=
  (skirmishCSG.LFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home).le_gfp
    (le_of_eq skirmish_LFW_univ_safe_home_eq_univ.symm)

theorem skirmish_hide_mem_LFpre1_safe_safe_safe :
    SkirmishPos.hide ∈ skirmishCSG.LFpre1 skirmishSafe skirmishSafe skirmishSafe := by
  have hne : (Set.univ : Set SoldierMove).Nonempty := ⟨SoldierMove.hide, Set.mem_univ _⟩
  exact hne.mono skirmish_univ_le_LFV_safe_safe_safe_hide

theorem skirmish_home_mem_LFpre1_safe_safe_safe :
    SkirmishPos.home ∈ skirmishCSG.LFpre1 skirmishSafe skirmishSafe skirmishSafe := by
  have hne : (Set.univ : Set SoldierMove).Nonempty := ⟨SoldierMove.hide, Set.mem_univ _⟩
  exact hne.mono skirmish_univ_le_LFV_safe_safe_safe_home

theorem skirmish_safe_subset_LFpre1_safe_safe_safe :
    skirmishSafe ⊆ skirmishCSG.LFpre1 skirmishSafe skirmishSafe skirmishSafe := by
  intro s hs
  cases s with
  | hide => exact skirmish_hide_mem_LFpre1_safe_safe_safe
  | home => exact skirmish_home_mem_LFpre1_safe_safe_safe
  | wet => exact absurd hs (by decide)

/-! ## Section 6g: the innermost `νY` and middle `μX` post-fixed-point checks, at `x := safe` -/

theorem skirmish_safe_le_LFGInner_safe_safe_safe :
    skirmishSafe ≤ skirmishCSG.LFGInner skirmishSafe skirmishSafe skirmishSafe skirmishSafe := by
  intro s hs
  change s ∈ (skirmishCSG.LFpre1 skirmishSafe skirmishSafe skirmishSafe ∩ skirmishSafe) ∪
      (skirmishSafeᶜ ∩ skirmishCSG.Lpre1 skirmishSafe skirmishSafe)
  exact Or.inl ⟨skirmish_safe_subset_LFpre1_safe_safe_safe hs, hs⟩

theorem skirmish_safe_le_LFGY_safe_safe_safe :
    skirmishSafe ≤ skirmishCSG.LFGY skirmishSafe skirmishSafe skirmishSafe :=
  (skirmishCSG.LFGInner skirmishSafe skirmishSafe skirmishSafe).le_gfp
    skirmish_safe_le_LFGInner_safe_safe_safe

/-- **The payoff, the middle `μX` level -- the `LFG` mirror of Section 5f's `skirmish_safe_le_
    AFGX_safe_safe`.** `skirmishSafe ≤ LFGX safe safe`: chase `LFGY`'s own monotonicity in `x`
    (`CSG.LFGY_mono_x`, already general-purpose infrastructure in `Csg.QualitativeLimitSure`) from
    the `⊥`-level bound up to `skirmishSafe` itself, then hand the resulting two-step-from-`⊥`
    lower bound to `OrderHom.map_map_bot_le_lfp` -- line-for-line the same shape as `AFG`'s own
    version, with `LFG*` substituted for `AFG*` throughout. -/
theorem skirmish_safe_le_LFGX_safe_safe :
    skirmishSafe ≤ skirmishCSG.LFGX skirmishSafe skirmishSafe := by
  have hmono : skirmishCSG.LFGY skirmishSafe skirmishSafe skirmishSafe ≤
      skirmishCSG.LFGY skirmishSafe skirmishSafe
        (skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)) :=
    skirmishCSG.LFGY_mono_x skirmishSafe skirmishSafe skirmish_safe_le_LFGY_safe_safe_empty
  have hchain : skirmishSafe ≤
      skirmishCSG.LFGY skirmishSafe skirmishSafe
        (skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)) :=
    skirmish_safe_le_LFGY_safe_safe_safe.trans hmono
  have hbot : skirmishCSG.LFGMiddle skirmishSafe skirmishSafe (⊥ : Set SkirmishPos)
      = skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos) := by
    change skirmishCSG.LFGY skirmishSafe skirmishSafe (⊥ : Set SkirmishPos)
      = skirmishCSG.LFGY skirmishSafe skirmishSafe (∅ : Set SkirmishPos)
    rw [Set.bot_eq_empty]
  have hffbot : skirmishSafe ≤
      skirmishCSG.LFGMiddle skirmishSafe skirmishSafe
        (skirmishCSG.LFGMiddle skirmishSafe skirmishSafe ⊥) := by
    change skirmishSafe ≤ skirmishCSG.LFGY skirmishSafe skirmishSafe
        (skirmishCSG.LFGMiddle skirmishSafe skirmishSafe ⊥)
    rw [hbot]
    exact hchain
  exact hffbot.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LFGMiddle skirmishSafe skirmishSafe))

/-! ## Section 6h: `F G !(s=1)`, limit-sure co-Büchi collapse -/

/-- **The headline true result.** `<<p1>> limit [ F G !(s=1) ]`: from `hide`, the soldier CAN force
    eventually always avoiding `wet`, in the limit -- `OrderHom.le_gfp` applied to the outer (`νZ`)
    post-fixed-point check, `skirmishSafe ≤ LFGX safe safe`, then `hide ∈ skirmishSafe` trivially
    (`by decide`). The last of this file's `sure`/`almost`/`limit` facts before Büchi (`GF`),
    deferred to its own section. -/
theorem skirmish_hide_mem_LFG_safe :
    SkirmishPos.hide ∈ skirmishCSG.LFG skirmishSafe :=
  (skirmishCSG.LFGOuter skirmishSafe).le_gfp skirmish_safe_le_LFGX_safe_safe (by decide)

/-! ## Section 7a: `wet` can never sure-escape a `wet`-free goal -/

/-- **The payoff, the `Pre1` sibling of `skirmish_wet_not_mem_Apre1`.** `wet`'s transition is
    constant (`skirmishK_wet`), so its support can only ever meet a target `x` that already
    contains `wet` -- if it doesn't, `wet` fails `Pre1`'s existential outright, using the concrete
    witness `SniperMove.wait` rather than needing to range over every column action. -/
theorem skirmish_wet_not_mem_Pre1 (x : Set SkirmishPos) (hx : SkirmishPos.wet ∉ x) :
    SkirmishPos.wet ∉ skirmishCSG.Pre1 x := by
  intro hmem
  obtain ⟨a1, ha1⟩ := hmem
  have h := ha1 SniperMove.wait
  rw [skirmishK_support_wet] at h
  exact hx (Set.singleton_subset_iff.mp h)

/-! ## Section 7b: `G F s=2`, sure-mode Büchi collapse -/

/-- **The payoff.** One step down from `⊤`: `SGFOuter {home} ⊤ ≤ skirmishSafe` -- `wet` is excluded
    by `skirmish_wet_not_mem_Pre1`; `hide`/`home` are trivially inside `skirmishSafe` regardless of
    which disjunct of `SGFInnerFun` actually holds. The `SGF` mirror of Section 3b's
    `skirmish_Apre1_safe_top_subset`, with `Pre1` standing in for `Apre1` on the non-`b` branch. -/
theorem skirmish_SGFInnerFun_top_safe_subset :
    skirmishCSG.SGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) (⊤ : Set SkirmishPos)
        skirmishSafe
      ⊆ skirmishSafe := by
  intro s hs
  rcases hs with ⟨h1, _⟩ | ⟨_, h2⟩
  · cases s with
    | hide => decide
    | home => decide
    | wet => exact absurd h1 (skirmish_wet_not_mem_Pre1 skirmishSafe (by decide))
  · rw [Set.eq_of_mem_singleton h2]
    decide

theorem skirmish_SGFOuter_top_le_safe :
    skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤ ≤ skirmishSafe :=
  (skirmishCSG.SGFInner ({SkirmishPos.home} : Set SkirmishPos) ⊤).lfp_le
    skirmish_SGFInnerFun_top_safe_subset

/-- **The payoff.** The second step down, from `skirmishSafe` to `{home}`: `wet` is excluded again;
    `hide` fails outright, since `Pre1 {home} = ∅` (`skirmishReachGoal_pre1_empty`, Section 2a)
    leaves its first disjunct empty and it isn't `home` itself for the second; `home` survives via
    the second disjunct, `home ∈ {home}`. -/
theorem skirmish_SGFInnerFun_safe_home_subset :
    skirmishCSG.SGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        ({SkirmishPos.home} : Set SkirmishPos)
      ⊆ ({SkirmishPos.home} : Set SkirmishPos) := by
  intro s hs
  rcases hs with ⟨h1, _⟩ | ⟨_, h2⟩
  · rw [skirmishReachGoal_pre1_empty] at h1
    simp at h1
  · exact h2

theorem skirmish_SGFOuter_safe_le_home :
    skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
  (skirmishCSG.SGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe).lfp_le
    skirmish_SGFInnerFun_safe_home_subset

/-- **The payoff.** `SGF {home} ≤ {home}`: `OrderHom.gfp_le_map_map_top` turns the two hand-checked
    steps above (`⊤ ↦ skirmishSafe ↦ {home}`) directly into a bound on the actual greatest fixed
    point, exactly Section 3c's `skirmish_AF_home_le_home` with `SGF` substituted for `AF`. -/
theorem skirmish_SGF_home_le_home :
    skirmishCSG.SGF ({SkirmishPos.home} : Set SkirmishPos)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by
  have hstep : skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos)
      (skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
    ((skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos)).mono
      skirmish_SGFOuter_top_le_safe).trans skirmish_SGFOuter_safe_le_home
  exact (OrderHom.gfp_le_map_map_top
      (skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos))).trans hstep

/-- **The headline false result.** `<<p1>> sure [ G F s=2 ]`: from `hide`, the soldier canNOT force
    visiting `home` infinitely often with certainty. -/
theorem skirmish_hide_not_mem_SGF_home :
    SkirmishPos.hide ∉ skirmishCSG.SGF ({SkirmishPos.home} : Set SkirmishPos) := by
  intro hmem
  exact absurd (Set.eq_of_mem_singleton (skirmish_SGF_home_le_home hmem)) (by decide)

/-! ## Section 7c: `G F s=2`, almost-sure-mode Büchi collapse -/

/-- **The payoff.** One step down from `⊤`: `AGFOuter {home} ⊤ ≤ skirmishSafe` -- the `AGF` mirror
    of `skirmish_SGFInnerFun_top_safe_subset`, with `Apre1` standing in for `Pre1` on the non-`b`
    branch and `skirmish_wet_not_mem_Apre1` (Section 3a) excluding `wet`. -/
theorem skirmish_AGFInnerFun_top_safe_subset :
    skirmishCSG.AGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) (⊤ : Set SkirmishPos)
        skirmishSafe
      ⊆ skirmishSafe := by
  intro s hs
  rcases hs with ⟨h1, _⟩ | ⟨_, h2⟩
  · cases s with
    | hide => decide
    | home => decide
    | wet => exact absurd h1 (skirmish_wet_not_mem_Apre1 skirmishSafe ⊤ (by decide))
  · rw [Set.eq_of_mem_singleton h2]
    decide

theorem skirmish_AGFOuter_top_le_safe :
    skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤ ≤ skirmishSafe :=
  (skirmishCSG.AGFInner ({SkirmishPos.home} : Set SkirmishPos) ⊤).lfp_le
    skirmish_AGFInnerFun_top_safe_subset

/-- **The payoff.** The second step down, from `skirmishSafe` to `{home}`: `wet` is excluded again;
    `hide` fails outright, since `Apre1 {home} skirmishSafe ⊆ {home}`
    (`skirmish_Apre1_home_safe_subset`, Section 3b) rules out its first disjunct while `hide` isn't
    `home` for the second; `home` survives via the second disjunct. -/
theorem skirmish_AGFInnerFun_safe_home_subset :
    skirmishCSG.AGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        ({SkirmishPos.home} : Set SkirmishPos)
      ⊆ ({SkirmishPos.home} : Set SkirmishPos) := by
  intro s hs
  rcases hs with ⟨h1, h2⟩ | ⟨_, h2⟩
  · exact absurd (skirmish_Apre1_home_safe_subset h1) h2
  · exact h2

theorem skirmish_AGFOuter_safe_le_home :
    skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
  (skirmishCSG.AGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe).lfp_le
    skirmish_AGFInnerFun_safe_home_subset

/-- **The payoff.** `AGF {home} ≤ {home}`, exactly Section 7b's `skirmish_SGF_home_le_home` with
    `AGF` substituted for `SGF`. -/
theorem skirmish_AGF_home_le_home :
    skirmishCSG.AGF ({SkirmishPos.home} : Set SkirmishPos)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by
  have hstep : skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos)
      (skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
    ((skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos)).mono
      skirmish_AGFOuter_top_le_safe).trans skirmish_AGFOuter_safe_le_home
  exact (OrderHom.gfp_le_map_map_top
      (skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos))).trans hstep

/-- **The headline false result.** `<<p1>> almost [ G F s=2 ]`: from `hide`, the soldier canNOT
    force visiting `home` infinitely often almost surely -- the second half of the almost-vs-limit
    Büchi divergence. -/
theorem skirmish_hide_not_mem_AGF_home :
    SkirmishPos.hide ∉ skirmishCSG.AGF ({SkirmishPos.home} : Set SkirmishPos) := by
  intro hmem
  exact absurd (Set.eq_of_mem_singleton (skirmish_AGF_home_le_home hmem)) (by decide)

/-! ## Section 7d: `G F s=2`, limit-sure-mode Büchi collapse -/

/-- **The payoff.** `skirmishSafe` is a post-fixed point of `LGFInner {home} skirmishSafe`, one step
    up from `⊥`, at `home`: `home`'s own second disjunct (`Pre1 skirmishSafe ∩ {home}`) already
    holds via `skirmishSafe_pre1` (Section 1a). The base case the two-step-up-from-`⊥` bound below
    starts from. -/
theorem skirmish_home_le_LGFInnerFun_safe_bot :
    ({SkirmishPos.home} : Set SkirmishPos) ⊆
      skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        (⊥ : Set SkirmishPos) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  rw [hs]
  change SkirmishPos.home ∈ (skirmishCSG.Lpre1 (⊥ : Set SkirmishPos) skirmishSafe ∩
      ({SkirmishPos.home} : Set SkirmishPos)ᶜ) ∪
    (skirmishCSG.Pre1 skirmishSafe ∩ ({SkirmishPos.home} : Set SkirmishPos))
  exact Or.inr ⟨skirmishSafe_pre1 (by decide), rfl⟩

/-- **The payoff.** `skirmishSafe` maps into `LGFInnerFun {home} skirmishSafe {home}`: `hide` via
    its first disjunct, `skirmish_hide_mem_Lpre1_home_safe` (Section 4b) doing all the real work
    exactly as it did for `LF` itself; `home` via the second disjunct, `skirmishSafe_pre1` again. -/
theorem skirmish_safe_le_LGFInnerFun_safe_home :
    skirmishSafe ⊆
      skirmishCSG.LGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        ({SkirmishPos.home} : Set SkirmishPos) := by
  intro s hs
  cases s with
  | hide => exact Or.inl ⟨skirmish_hide_mem_Lpre1_home_safe, by decide⟩
  | home => exact Or.inr ⟨skirmishSafe_pre1 (by decide), rfl⟩
  | wet => exact absurd hs (by decide)

/-- **The payoff.** `skirmishSafe ≤ LGFOuter {home} skirmishSafe`, in exactly the two Kleene steps
    up from `⊥` Section 4c's `skirmish_safe_le_LFOuter_safe` used for `LF` (`⊥ ↦ {home} ↦
    skirmishSafe`, here re-derived one operator over for `LGFInner`) --
    `OrderHom.map_map_bot_le_lfp` turning the two hand-checked steps into a genuine lower bound on
    the inner `lfp`. -/
theorem skirmish_safe_le_LGFOuter_safe :
    skirmishSafe ≤ skirmishCSG.LGFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by
  have hmono : skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ({SkirmishPos.home} : Set SkirmishPos) ≤
      skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        (skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
          (⊥ : Set SkirmishPos)) :=
    (skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe).mono
      skirmish_home_le_LGFInnerFun_safe_bot
  have hchain : skirmishSafe ≤
      skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        (skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
          (⊥ : Set SkirmishPos)) :=
    skirmish_safe_le_LGFInnerFun_safe_home.trans hmono
  exact hchain.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe))

/-- **The headline true result.** `<<p1>> limit [ G F s=2 ]`: from `hide`, the soldier CAN force
    visiting `home` infinitely often in the limit -- the second headline sure/almost-vs-limit
    divergence, alongside Section 3/4's reachability one. `OrderHom.le_gfp` applied to
    `skirmish_safe_le_LGFOuter_safe`, then `hide ∈ skirmishSafe` trivially (`by decide`). -/
theorem skirmish_hide_mem_LGF_home :
    SkirmishPos.hide ∈ skirmishCSG.LGF ({SkirmishPos.home} : Set SkirmishPos) :=
  (skirmishCSG.LGFOuter ({SkirmishPos.home} : Set SkirmishPos)).le_gfp
    skirmish_safe_le_LGFOuter_safe (by decide)

end Csg
