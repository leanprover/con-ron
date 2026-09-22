/-
# `ConRon.Bridge.ExprOps.InstLP` — Theorem 1 for the LEVEL side of `ExprOps`

DESIGN §8.2's Theorem 1 at the eight twins of `Arena/ExprOps.lean` whose
subject is a level, a derived bit or a handle comparison:
`instLPGo` / `instLPFast`, the three level helpers `substLevelList`,
`substLMemoAt`, `substLsMemoAt`, the two `O(1)` derived-bit reads
`LIdx.hasParam` / `EIdx.hasLevelParam`, and `exprPtrBEq`.

Written against `ExprOps/Inst1.lean`, the tier's exemplar: the same `…Spec`
record for one level of the recursion, the same fuel induction, the same
per-arm `_step` lemmas "in the shape `mvcgen` actually produces", the same
`lp_hyp` and the same `attribute [-grind]` line.

## Why the level work is an EQUATION and not a simulation

DESIGN §8.3's lesson 4 ("Levels and names: intern the representation, not
the algorithm").  `readLevelM` / `readLevelsM` ARE `denoteL` / `denoteLs`
(`Bridge/Specs.lean`'s `readLevelM_spec` is an equation), so `instLPGo`'s two
level arms run **con-leche's own** `Level.subst` on a transient tree and
re-intern the answer.  Nothing in this file simulates a level algorithm; the
level obligations are `Level.subst`-shaped facts about `denoteL`.

## The four deviations these twins carry

1. **`instLPGo`'s `ks`/`us` are transient `List Name` / `List Level`**, not a
   handle list and an `LsIdx` (DESIGN §8.3 lesson 4; `ExprOps.lean`'s
   "Levels: read back, not twinned").  `instLPFast` reads them back once at
   the entry with `readNamesM`/`readLevelsM`, so `instLPFast_spec`'s
   hypothesis is that the handle list and the `LsIdx` DENOTE `ks` and `us`,
   and the walk's theorem takes `ks`/`us` as plain values.
2. **The `hasLP` cutoff** (`instLPGo`'s first act, and `instLPFast`'s own
   hoisted copy, task #97-P6-10).  Its licence is con-leche's
   `Expr.instantiateLevelParams_eq_self` (`ExprOps.lean:2465`) composed with
   `Expr.hasLP_eq` (`:2541`) and the store's `EStore.derived_exact`.
3. **The upward `internRebuilt` cutoff** (task #97-P6-5) at all six rebuilding
   arms; `Bridge/Specs.lean`'s `internRebuilt*_spec` family discharges it and
   `Bridge/Rel.lean`'s `denoteEView_ext` is what makes the `same = true`
   branch's conclusion the other branch's.
4. **`LIdx.hasParam` and `EIdx.hasLevelParam` are not walks at all**: they
   read a derived word in `O(1)`.  Their theorems are exactness statements
   against con-leche's `Level.hasParam` / `Expr.hasLevelParam`, proved from
   `LStore.derived_exact` / `EStore.derived_exact` (`Arena/WFProofs.lean`)
   plus con-leche's own `Expr.data` formula (`levelHasParam_eq`, `hasLP_eq`).

## What this module does not claim

* `instLPGo` calls `readLevelM` / `readLevelsM`, which WRITE the readback
  caches, so no theorem here can frame `s'.caches = s₀.caches`.  What is
  framed instead is exactly what the caller needs: the two readback cache
  clauses are preserved (`ReadLCacheOK`, `ReadLsCacheOK`), and `pins` and the
  ten other memo tables stand still.  This is a frame condition
  `Bridge/StateOK.lean`'s `CheckOK.mono` cannot consume as it stands — see
  the report's finding list.
* `exprPtrBEq`'s converse (`denoteE st a = denoteE st b → a == b`) is a free
  corollary of `denoteE_inj` and is stated below as `exprPtrBEq_exact`, but
  the checker's soundness never needs it: con-leche's `exprPtrBEq` only ever
  answers `true` as a shortcut.
-/
import ConRon.Bridge.ExprOps.MemoSpecs

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ### Attribute hygiene (task #97s round 2, item 1) -/
attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-- con-leche: none — `mvcgen` hands an arm its projection read as
`some fields = st.viewC h`, i.e. REVERSED, so the one-line `assumption` that
supplies a step lemma's hypothesis has to try both orientations. -/
macro "lp_hyp" : tactic => `(tactic| first
  | assumption
  | (symm; assumption)
  | grind only [Ext.trans, Ext.refl])

/-! ## 1. `exprPtrBEq` — handle equality IS expression equality

`Arena/ExprOps.lean:1868`.  The twin takes no monad: it is one machine-word
comparison, and `denoteE_inj` (`Arena/WFProofs.lean`) is the whole content. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2384-2390 exprPtrBEq — **THEOREM 1
for `exprPtrBEq`**: the arena's index comparison answering `true` means the
two handles denote one term.  This is the direction the checker's soundness
needs (the twin is a SHORTCUT: a `true` licenses skipping a comparison), and
it needs no well-formedness at all — equal handles have equal denotations by
congruence. -/
theorem exprPtrBEq_sound {st : EStore} {a b : EIdx}
    (h : exprPtrBEq a b = true) : denoteE st a = denoteE st b := by
  unfold exprPtrBEq at h
  simp only [beq_iff_eq] at h
  rw [h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2384-2390 exprPtrBEq — the same
as an exactness statement against con-leche's own function, in the `RelV`
idiom: on a well-formed arena the handle comparison and the structural
comparison agree.  The `→` direction is `exprPtrBEq_sound`; the `←`
direction is `denoteE_inj`, and it is the only place this tier needs it.
Not required by any caller — con-leche's `exprPtrBEq` is a one-sided
shortcut — but free, and it is what says the arena's comparison is not
*weaker* than the pure one. -/
theorem exprPtrBEq_exact {st : EStore} (hwf : StoreWF st) {a b : EIdx}
    {ea eb : Expr} (ha : denoteE st a = some ea) (hb : denoteE st b = some eb) :
    exprPtrBEq a b = Expr.exprPtrBEq ea eb := by
  have hp : Expr.exprPtrBEq ea eb = (ea == eb) := by
    unfold ConLeche.Expr.exprPtrBEq withPtrEq; rfl
  rw [hp]
  unfold exprPtrBEq
  by_cases hab : a = b
  · subst hab
    rw [ha] at hb
    obtain rfl := Option.some.inj hb
    simp
  · have hne : ea ≠ eb := by
      intro hee
      subst hee
      exact hab (denoteE_inj hwf ha hb)
    have h1 : (a == b) = false := by
      cases hh : (a == b) with
      | false => rfl
      | true => exact absurd (eq_of_beq hh) hab
    have h2 : (ea == eb) = false := by
      cases hh : (ea == eb) with
      | false => rfl
      | true => exact absurd (eq_of_beq hh) hne
    rw [h1, h2]

/-! ## 2. The two derived-bit reads — `Arena/ExprOps.lean:1875`, `:1883`

Neither is a walk: `LIdx.hasParam` reads `LDer.hasParam` off the level
store's derived column and `EIdx.hasLevelParam` reads the `hasLP` bit off the
expression store's packed word.  `LStore.derived_exact` and
`EStore.derived_exact` say those columns are con-leche's own computed fields,
and con-leche's `Expr.levelHasParam_eq` / `Expr.hasLP_eq` say those fields
are `Level.hasParam` / `Expr.hasLevelParam`. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2401-2408 Level.hasParam — the
answer relation for a LEVEL subject and a representation-free answer.  The
shape `Bridge/Rel.lean` does not have (it has `RelV` at an `EIdx` subject and
`RelL` at a level answer, but not this one); it belongs beside them. -/
def RelLV {α : Type} (f : Level → α) (st : EStore) (c : LIdx) (x : α) : Prop :=
  ∀ u, denoteL st.ls c = some u → x = f u

/-- con-leche: none — `RelLV`'s one eliminator. -/
theorem RelLV.apply {α : Type} {f : Level → α} {st : EStore} {c : LIdx}
    {x : α} {u : Level} (h : RelLV f st c x) (hu : denoteL st.ls c = some u) :
    x = f u := h u hu

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2401-2408 Level.hasParam —
**THEOREM 1 for `LIdx.hasParam`**: the `O(1)` bit read is con-leche's walk.
con-leche walks the level tree; the arena reads `LDer.hasParam`, which
`LStore.derived_exact` pins to `levelHasParam` of the denotation and
`Expr.levelHasParam_eq` identifies with `Level.hasParam`. -/
theorem LIdx_hasParam_spec (s₀ : AState) (h : LIdx) (hok : StateOK s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ LIdx.hasParam h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ RelLV Level.hasParam s₀.store h r⌝⦄ := by
  mvcgen [LIdx.hasParam]
  spec_fails
  bridge_peel
  subst_vars
  refine ⟨rfl, ?_⟩
  intro u hu
  obtain ⟨rk, hrk⟩ := hok.wf
  have hd := LStore.derived_exact hrk.lsWF hu
  simp only [EStore.lder, hd, Expr.Expr.levelHasParam_eq]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2422-2437 Expr.hasLevelParam —
**THEOREM 1 for `EIdx.hasLevelParam`**: the `hasLP` bit of the packed derived
word is con-leche's `Expr.hasLevelParam`.  `EStore.derived_exact` says the
word is `e.data`; `Expr.hasLP_eq` (con-leche `ExprOps.lean:2541`) says
`lpOfData e.data = e.hasLevelParam`. -/
theorem EIdx_hasLevelParam_spec (s₀ : AState) (h : EIdx) (hok : StateOK s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ EIdx.hasLevelParam h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ RelV Expr.hasLevelParam s₀.store h r⌝⦄ := by
  mvcgen [EIdx.hasLevelParam]
  spec_fails
  bridge_peel
  subst_vars
  refine ⟨rfl, ?_⟩
  intro e he
  rw [EStore.derived_exact hok.wf he]
  exact Expr.Expr.hasLP_eq e

/-! ## 3. `substLevelList` — `Arena/ExprOps.lean:1901`

con-leche writes `vs.map (Level.subst ks us)`; DESIGN §3.4 forbids the closure
in code Aeneas must translate, so the twin is explicit recursion.  Theorem 1
is therefore an EQUATION between the two pure functions, with no state in
it. -/

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — **THEOREM 1 for
`substLevelList`**: the explicit recursion is con-leche's `.map`. -/
theorem substLevelList_eq (ks : List ConLeche.Name) (us : List Level) :
    ∀ vs : List Level, substLevelList ks us vs = vs.map (Level.subst ks us) := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v rest ih => simp only [substLevelList, List.map_cons, ih]

/-! ## 4. The level interners' specs

`Bridge/Specs.lean` has `internLNode_spec` and `internLsNode_spec` (the NODE
interners) but not the two TRANSIENT-TREE interners `internLevel` /
`internLevels` that DESIGN §8.3 lesson 4 makes the level algorithms' only
exit.  They are `internName_spec`'s shape exactly — a structural induction on
the transient value — and they belong in `Bridge/Specs.lean` beside it; they
are here because P3's group split put `Specs.lean` out of this file's
reach. -/

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — intern a transient
level tree, by induction on the `Level` (the recursion `internLevel` takes: a
`Level` is a value, not a DAG, so no fuel). -/
@[spec] theorem internLevel_spec (s₀ : AState) (u : Level)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLevel u
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteL s'.store.ls h = some u⌝⦄ := by
  induction u generalizing s₀ with
  | zero =>
    mvcgen [internLevel, internLNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteLView, Arena.LStore.ViewOK, LNodeView.lchildren,
                 LNodeView.nchildren, Ext.refl])
  | succ a ih =>
    mvcgen [internLevel, ih, internLNode_spec]
    all_goals bridge_vcs [denoteLView, Arena.LStore.ViewOK,
      LNodeView.lchildren, LNodeView.nchildren, lview_isSome_of_denote,
      denoteL_ext]
  | max a b ih1 ih2 =>
    mvcgen [internLevel, ih1, ih2, internLNode_spec]
    all_goals bridge_vcs [denoteLView, Arena.LStore.ViewOK,
      LNodeView.lchildren, LNodeView.nchildren, lview_isSome_of_denote,
      denoteL_ext]
  | imax a b ih1 ih2 =>
    mvcgen [internLevel, ih1, ih2, internLNode_spec]
    all_goals bridge_vcs [denoteLView, Arena.LStore.ViewOK,
      LNodeView.lchildren, LNodeView.nchildren, lview_isSome_of_denote,
      denoteL_ext]
  | param nm =>
    mvcgen [internLevel, internName_spec, internLNode_spec]
    all_goals bridge_vcs [denoteLView, Arena.LStore.ViewOK,
      LNodeView.lchildren, LNodeView.nchildren, nview_isSome_of_denote,
      denoteN_ext, EStore.ns, EStore.ls, Arena.LsStore.ns]

/-- con-leche: none — intern a list of transient levels, one handle each. -/
@[spec] theorem internLevelList_spec (s₀ : AState) (us : List Level)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLevelList us
    ⦃⇓? hs s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteLList s'.store.ls hs = some us⌝⦄ := by
  induction us generalizing s₀ with
  | nil =>
    mvcgen [internLevelList]
    all_goals (bridge_peel; subst_vars; grind [denoteLList, Ext.refl])
  | cons u rest ih =>
    mvcgen [internLevelList, internLevel_spec, ih]
    all_goals bridge_vcs [denoteLList, denoteL_ext, denoteLList_ext]

/-- con-leche: none — a level-handle list that denotes has views at every
member: `internLsNode`'s `ViewOK` at a list the walk has just built.  A
general-purpose store fact; it belongs in `Bridge/Rel.lean`'s group 8 beside
`view_isSome`. -/
theorem lview_isSome_of_denoteLList {st : LStore} :
    ∀ (hs : List LIdx) (xs : List Level), denoteLList st hs = some xs →
      ∀ c ∈ hs, (st.view c).isSome = true := by
  intro hs
  induction hs with
  | nil => intro _ _ c hc; simp at hc
  | cons a as ih =>
    intro xs h c hc
    simp only [denoteLList, opt2_eq_some_iff] at h
    obtain ⟨x, ys, hx, hys, _⟩ := h
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact lview_isSome_of_denote hx
    · exact ih ys hys c hc'

/-- con-leche: none — intern a list of transient levels and hash-cons the
list node. -/
@[spec] theorem internLevels_spec (s₀ : AState) (us : List Level)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLevels us
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteLs s'.store.lss h = some us⌝⦄ := by
  mvcgen [internLevels, internLevelList_spec, internLsNode_spec]
  all_goals bridge_vcs [denoteLs, denoteLsView, Arena.LsStore.ViewOK,
    lview_isSome_of_denote, denoteLList, denoteLListE_ext, EStore.ls,
    lview_isSome_of_denoteLList]

/-- con-leche: none — `RelL` from the two denotations, which is the shape a
memo insert's side condition has (`instLPLSet_spec`'s `hr`).  `RelL` is a
`def`, so `grind` will not build one; this lemma is what it applies instead.
It belongs in `Bridge/Rel.lean` beside `RelE.self`. -/
theorem RelL.of_denote {f : Level → Level} {st st' : EStore} {c r : LIdx}
    {u : Level} (hc : denoteL st.ls c = some u)
    (hr : denoteL st'.ls r = some (f u)) : RelL f st c st' r := by
  intro u' hu'
  rw [hc] at hu'
  obtain rfl := Option.some.inj hu'
  exact hr

/-- con-leche: none — the same at a universe-argument LIST handle. -/
theorem RelLs.of_denote {f : List Level → List Level} {st st' : EStore}
    {c r : LsIdx} {us : List Level} (hc : denoteLs st.lss c = some us)
    (hr : denoteLs st'.lss r = some (f us)) : RelLs f st c st' r := by
  intro us' hus'
  rw [hc] at hus'
  obtain rfl := Option.some.inj hus'
  exact hr

/-! ## 5. `substLMemoAt` / `substLsMemoAt` — `Arena/ExprOps.lean:1914`, `:1925`

The level substitution behind its per-call memo (task #97-P6-13).  Both are
"probe, else read back, run con-leche's function, re-intern, record": the
readback is `denoteL` / `denoteLs` by `readLevelM_spec` / `readLevelsM_spec`,
so the answer relation is `RelL` / `RelLs` at con-leche's `Level.subst`
without a single level lemma.

**The frame is not `s'.caches = s₀.caches`**: the memoised readback writes
`caches.readLC` / `caches.readLsC`.  What the caller gets instead is the two
readback clauses preserved — which is what `instLPGo` needs to call them
again — and, since round 4, the RECORD equation
`s'.caches = { s₀.caches with readLC := … }`, which frames the *other thirteen*
cache tables in one line.  That is what carries `ReadNCacheOK` across
`instLPGo` and so lets `instLPFast_spec` state a cache frame at all; the
individual `readLC`/`readLsC` sibling equations these two used to carry are
its projections. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo —
**THEOREM 1 for `substLMemoAt`**: the memoised level substitution answers
`Level.subst ks us` of what the key denotes. -/
theorem substLMemoAt_spec (s₀ : AState) (ks : List ConLeche.Name)
    (us : List Level) (u : LIdx) (hok : StateOK s₀)
    (hm : InstLPLMemoA ks us s₀)
    (hc : ReadLCacheOK s₀.caches.readLC s₀.store)
    (hu : (denoteL s₀.store.ls u).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ substLMemoAt ks us u
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.pins = s₀.pins ∧
        s'.memos.instLPC = s₀.memos.instLPC ∧
        s'.memos.instLPLsC = s₀.memos.instLPLsC ∧
        InstLPLMemoA ks us s' ∧
        ReadLCacheOK s'.caches.readLC s'.store ∧
        s'.caches = { s₀.caches with readLC := s'.caches.readLC } ∧
        RelL (Level.subst ks us) s₀.store u s'.store r⌝⦄ := by
  mvcgen [substLMemoAt]
  all_goals bridge_vcs [MemoLOK.insert, MemoLOK.get, RelL.of_ext, RelL.ext,
    RelL.of_denote, denoteL_ext, ReadLCacheOK.mono, Option.isSome_iff_exists]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo —
**THEOREM 1 for `substLsMemoAt`**: the same at a universe-argument LIST
handle, whose answer is con-leche's `vs.map (Level.subst ks us)` by
`substLevelList_eq`. -/
theorem substLsMemoAt_spec (s₀ : AState) (ks : List ConLeche.Name)
    (us : List Level) (vs : LsIdx) (hok : StateOK s₀)
    (hm : InstLPLsMemoA ks us s₀)
    (hc : ReadLsCacheOK s₀.caches.readLsC s₀.store)
    (hvs : (denoteLs s₀.store.lss vs).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ substLsMemoAt ks us vs
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.pins = s₀.pins ∧
        s'.memos.instLPC = s₀.memos.instLPC ∧
        s'.memos.instLPLC = s₀.memos.instLPLC ∧
        InstLPLsMemoA ks us s' ∧
        ReadLsCacheOK s'.caches.readLsC s'.store ∧
        s'.caches = { s₀.caches with readLsC := s'.caches.readLsC } ∧
        RelLs (fun ws => ws.map (Level.subst ks us)) s₀.store vs s'.store r⌝⦄ := by
  mvcgen [substLsMemoAt]
  all_goals bridge_vcs [MemoLsOK.insert, MemoLsOK.get, MemoLsOK.mono,
    RelLs.of_ext, RelLs.ext, RelLs.of_denote, denoteLs_ext, substLevelList_eq,
    ReadLsCacheOK.mono, Option.isSome_iff_exists]

end ConRon.Bridge.ExprOps
