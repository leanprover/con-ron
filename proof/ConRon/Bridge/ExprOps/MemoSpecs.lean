/-
# `ConRon.Bridge.ExprOps.MemoSpecs` — the memo-set specs with the pure function INSIDE

**A finding of P3's group B, and the file that should be folded into
`Bridge/Specs.lean`.**

`Bridge/Specs.lean` states each memo insert's spec with the walk's own
parameters as THEOREM PARAMETERS:

```lean
@[spec] theorem instLPLsSet_spec (s₀) (ks : List Name) (us : List Level)
    (h r : LsIdx) (hm : InstLPLsMemoA ks us s₀) … : ⦃…⦄ instLPLsSet h r ⦃…⦄
```

Those parameters do not occur in the PROGRAM, so when the verification
condition generator selects the spec it has nothing to pin them against.
`mvcgen` (before task #111) did not leave them as metavariables for the
closer to solve either: it assigned them from whatever was in scope at the
right type; `vcgen` leaves them as goals of their own type, to be
supplied by hand (`f_spec (x := x)`).  Measured under `mvcgen` in
`ExprOps/InstLP.lean`'s `substLsMemoAt`: the readback list `ls : List Level` is in scope, so the
arm's memo verification condition comes out as `InstLPLsMemoA ks ls s` — not
merely hard, **false**.  (`substLMemoAt` is spared only because its readback
is a `Level` and not a `List Level`, so `us` is the sole candidate of its
type.  This is task #97b finding 2's trap in its worst form: the wrong
assignment is silent.)

The fix is `Bridge/Specs.lean`'s own `internBindIE_spec'` trick — template
rule 4 applied to the memo's pure function: **move the parameters inside the
postcondition**.  Then the spec's statement has no metavariable at all, the
arm gets the memo implication as a hypothesis, and it applies it at the
function the walk is about.

It buys a second thing the group needed anyway: `abstractRangeGo` shares
`abs1C` with `abstract1Go` (`Arena/ExprOps.lean`'s "That is a table
IDENTITY, not a clause"), so the one table carries two different invariants.
`Specs.lean`'s `abs1Set_spec` fixes `Abs1MemoA d` and cannot serve the
`abstractRange` walk at all; the internalised form is generic in `f` and
serves both.

The specs below are `@[spec high]` because `vcgen`'s spec lookup
(`Lean.Elab.Tactic.VCGen`'s `SpecTheorems.findSpecs`) sorts the candidates by
priority and `Specs.lean`'s versions match the same
program; `attribute [-spec]` is refused by the attribute (measured), so the
priority is the only lever.  Each is proved by `vcgen [f]`, which unfolds a
definition named in its list.
-/
import ConRon.Bridge.Specs
import ConRon.Bridge.Grind

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-- con-leche: ConLeche/Kernel/Level.lean:28-40 Level.subst — the same for
`instLPLSet`, the LEVEL-handle memo. -/
@[spec high] theorem instLPLSet_specI (s₀ : AState) (h r : LIdx)
    (hk : (denoteL s₀.store.ls h).isSome = true) :
    ⦃fun s => s = s₀⦄ instLPLSet h r
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLPLC := s₀.memos.instLPLC.insert h r } ∧
        ∀ f : Level → Level, MemoLOK f s₀.memos.instLPLC s₀.store →
          RelL f s₀.store h s₀.store r →
            MemoLOK f s'.memos.instLPLC s'.store; ⊤⦄ := by
  dsimp only
  vcgen [instLPLSet]
  subst_vars
  refine ⟨rfl, rfl, rfl, rfl, fun f hm hr => ?_⟩
  exact MemoLOK.insert hm rfl hk hr

/-- con-leche: ConLeche/Kernel/Level.lean:28-40 Level.subst — the same for
`instLPLsSet`, the universe-argument-LIST memo.  This is the one the trap was
measured on. -/
@[spec high] theorem instLPLsSet_specI (s₀ : AState) (h r : LsIdx)
    (hk : (denoteLs s₀.store.lss h).isSome = true) :
    ⦃fun s => s = s₀⦄ instLPLsSet h r
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos =
          { s₀.memos with instLPLsC := s₀.memos.instLPLsC.insert h r } ∧
        ∀ f : List Level → List Level, MemoLsOK f s₀.memos.instLPLsC s₀.store →
          RelLs f s₀.store h s₀.store r →
            MemoLsOK f s'.memos.instLPLsC s'.store; ⊤⦄ := by
  dsimp only
  vcgen [instLPLsSet]
  subst_vars
  refine ⟨rfl, rfl, rfl, rfl, fun f hm hr => ?_⟩
  exact MemoLsOK.insert hm rfl hk hr

/-! ## The readback memos, with the frame the walks need

`Bridge/Specs.lean`'s `readLevelM_spec` / `readLevelsM_spec` frame the store,
the per-call memos and the pins, but **not the other thirteen cache tables**.
`instLPGo` needs them: its `.sort` arm reads a LEVEL back and its `.const` arm
reads a universe-argument LIST back, so each arm must carry the OTHER arm's
cache clause across.  Without the frame the walk's invariant cannot be
maintained at all — the readback clause is the one hypothesis
`readLevelM_spec` itself demands.

Two specs, same shape as the ones in `Specs.lean` plus two equations, and they
belong there. -/

-- The frame at a hit is structure eta at the cache record (as in `Specs.lean`).
attribute [local bridge_grind ext] Caches

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — `readLevelM` with the
sibling readback tables framed. -/
@[spec high] theorem readLevelM_specF (s₀ : AState) (h : LIdx)
    (hc : ReadLCacheOK s₀.caches.readLC s₀.store) :
    ⦃fun s => s = s₀⦄ readLevelM h
    ⦃fun u s' => s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readLC := s'.caches.readLC } ∧
        denoteL s₀.store.ls h = some u ∧
        ReadLCacheOK s'.caches.readLC s'.store; ⊤⦄ := by
  dsimp only
  sym only [bridge_grind, ReadLCacheOK, Std.HashMap.getElem?_insert] =>
    vcgen [readLevelM] <;> finish

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — `readLevelsM` with the
sibling readback tables framed. -/
@[spec high] theorem readLevelsM_specF (s₀ : AState) (h : LsIdx)
    (hc : ReadLsCacheOK s₀.caches.readLsC s₀.store) :
    ⦃fun s => s = s₀⦄ readLevelsM h
    ⦃fun us s' => s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readLsC := s'.caches.readLsC } ∧
        denoteLs s₀.store.lss h = some us ∧
        ReadLsCacheOK s'.caches.readLsC s'.store; ⊤⦄ := by
  dsimp only
  sym only [bridge_grind, ReadLsCacheOK, Std.HashMap.getElem?_insert] =>
    vcgen [readLevelsM] <;> finish

/-! ## The intern specs with the two MONOTONICITY conjuncts

**The second finding of P3's group B, and the one that retired
`ExprOps/Inst1.lean`'s last open goal.**

`Bridge/Rel.lean`'s `Ext` is about DENOTATIONS: "every handle of `st` denotes
the same in `st'`".  A rebuilding walk needs two facts it does not give.

1. `internRebuilt*_spec`'s own hypothesis `hsame : same = true → s₀.store.view
   h = some v` is asked at the store the walk's RECURSIVE CALLS left behind,
   while the walk read the view before them.  `view` is not carried by `Ext`,
   so the arm cannot discharge it — for EVERY rebuilding arm of every walk of
   this tier (five walks, twenty-nine arms).
2. `internBindIE_spec'`'s precondition `(s.store.viewBM mi).isSome` is asked
   at the same later store, which is exactly the gap
   `ExprOps/Inst1.lean`'s note describes ("threading it is a mechanical
   postcondition change across the twelve `intern` specs; it is the next
   round's first item").

Both facts hold of the store operation: `EStore.view_intern_mono`
(`Arena/WFProofs.lean:2263`) and `EStore.viewBM_intern_mono`
(`Bridge/StoreBM.lean:86`) are proved and unused.  What was missing is the
conjunct in the monadic specs, which is what this section adds.  They belong
in `Bridge/Specs.lean`, replacing the versions there. -/

/-- con-leche: none — `internLamE`'s two outcomes: a cons hit moves
nothing, a miss is `EStore.internBind` at the `lam` tag. -/
theorem internLamE_ok {ty b : EIdx} {s : AState} {r : EIdx} {s' : AState}
    (h : internLamE ty b s = .ok (r, s')) :
    s' = s ∨ s' = { s with store := (s.store.internBind ETag.lam ty b).1 } := by
  unfold internLamE at h
  cases hf : s.store.findBind ETag.lam ty b with
  | some i =>
    simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      Except.pure, Except.bind, hf, StateT.pure] at h
    exact Or.inl h.2.symm
  | none =>
    by_cases hc : (if s.store.scratchOn = true then s.store.scr.bindSizeOf ETag.lam
                else s.store.pers.bindSizeOf ETag.lam) < Idx.idxCap
    · simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, StateT.pure, set, StateT.set, ite_eq_left hc,
        Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inr h.2.symm
    · simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, hc, fail, throwThe, MonadExceptOf.throw,
        StateT.lift] at h

/-- con-leche: none — and `internForallEE`'s. -/
theorem internForallEE_ok {ty b : EIdx} {s : AState} {r : EIdx} {s' : AState}
    (h : internForallEE ty b s = .ok (r, s')) :
    s' = s ∨ s' = { s with store := (s.store.internBind ETag.forallE ty b).1 } := by
  unfold internForallEE at h
  cases hf : s.store.findBind ETag.forallE ty b with
  | some i =>
    simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      Except.pure, Except.bind, hf, StateT.pure] at h
    exact Or.inl h.2.symm
  | none =>
    by_cases hc : (if s.store.scratchOn = true then s.store.scr.bindSizeOf ETag.forallE
                else s.store.pers.bindSizeOf ETag.forallE) < Idx.idxCap
    · simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, StateT.pure, set, StateT.set, ite_eq_left hc,
        Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inr h.2.symm
    · simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, hc, fail, throwThe, MonadExceptOf.throw,
        StateT.lift] at h

/-- con-leche: none — `internE` moves no node read: the node arms end at a
cons hit or at `EStore.intern`, the two binder arms at a cons hit or at
`EStore.internBind`. -/
theorem internE_view_mono {s s' : AState} {w : ENodeView} {h : EIdx}
    (hrun : internE w s = .ok (h, s')) :
    ∀ i v, s.store.view i = some v → s'.store.view i = some v := by
  intro i v hi
  cases w
  case lam ty b =>
    rcases internLamE_ok (internE_lam_split hrun) with rfl | rfl
    · exact hi
    · exact EStore.view_internBind_mono _ _ _ _ hi
  case forallE ty b =>
    rcases internForallEE_ok (internE_forallE_split hrun) with rfl | rfl
    · exact hi
    · exact EStore.view_internBind_mono _ _ _ _ hi
  all_goals
    rcases internNodeE_ok hrun with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · exact hi
    · exact EStore.view_intern_mono _ _ hi

/-- con-leche: none — `internE` with view monotonicity: `internE_spec` and
`internE_view_mono`. -/
@[spec high] theorem internE_specV (s₀ : AState) (w : ENodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK w) :
    ⦃fun s => s = s₀⦄ internE w
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i v, s₀.store.view i = some v → s'.store.view i = some v) ∧
        s'.store.view h = some w ∧
        denoteE s'.store h = denoteEView s'.store w; ⊤⦄ := by
  refine AM.triple_of_run_at fun h s' hrun => ?_
  obtain ⟨p1, p2, p4, -, p6, p7, p8, p9, p10⟩ :=
    AM.of_run (P := fun t => t = s₀) rfl hrun (internE_spec s₀ w hwf hv)
  exact ⟨p1, p2, p4, p6, p7, p8, internE_view_mono hrun, p9, p10⟩

/-- con-leche: none — `internRebuilt` with the same two conjuncts.  The
`same = true` branch answers the handle it was given, so both are
reflexive there. -/
@[spec high] theorem internRebuilt_specV (s₀ : AState) (h : EIdx) (same : Bool)
    (v : ENodeView) (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK v)
    (hsame : same = true → s₀.store.view h = some v) :
    ⦃fun s => s = s₀⦄ internRebuilt h same v
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i w, s₀.store.view i = some w → s'.store.view i = some w) ∧
        denoteE s'.store r = denoteEView s'.store v; ⊤⦄ := by
  sym only [bridge_grind, denoteE_view_eq hwf] =>
    vcgen [internRebuilt, internE_specV] <;> finish

/-! ### The binder intern at the V shape

`internLamE` / `internForallEE` are not `internE`'s faces (they probe the
binder RECORD), so they get their own view-monotone specs:
`Bridge/Specs.lean`'s `_spec_view` and `internLamE_ok` / `internForallEE_ok`
for the monotonicity.  Not `@[spec]`: a walk that wants them says
`attribute [local spec high] internRebuiltBind_specV`. -/

/-- con-leche: none — `internLamE` with view monotonicity. -/
theorem internLamE_specV (s₀ : AState) (ty b : EIdx) (hwf : StoreWF s₀.store)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => s = s₀⦄ internLamE ty b
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        s'.store.view h = some (.lam ty b) ∧
        denoteE s'.store h = denoteEView s'.store (.lam ty b); ⊤⦄ := by
  refine AM.triple_of_run_at fun h s' hrun => ?_
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ :=
    AM.of_run (P := fun t => t = s₀) rfl hrun (internLamE_spec_view s₀ ty b hwf hty hb)
  refine ⟨p1, p2, p3, p4, p5, p6, p7, fun j w hj => ?_, p8, p9⟩
  rcases internLamE_ok hrun with rfl | rfl
  · exact hj
  · exact EStore.view_internBind_mono _ _ _ _ hj

/-- con-leche: none — `internForallEE` with view monotonicity. -/
theorem internForallEE_specV (s₀ : AState) (ty b : EIdx) (hwf : StoreWF s₀.store)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => s = s₀⦄ internForallEE ty b
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        s'.store.view h = some (.forallE ty b) ∧
        denoteE s'.store h = denoteEView s'.store (.forallE ty b); ⊤⦄ := by
  refine AM.triple_of_run_at fun h s' hrun => ?_
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ :=
    AM.of_run (P := fun t => t = s₀) rfl hrun
      (internForallEE_spec_view s₀ ty b hwf hty hb)
  refine ⟨p1, p2, p3, p4, p5, p6, p7, fun j w hj => ?_, p8, p9⟩
  rcases internForallEE_ok hrun with rfl | rfl
  · exact hj
  · exact EStore.view_internBind_mono _ _ _ _ hj

/-- con-leche: none — the two binder arms at a tag the caller carries, with
view monotonicity. -/
theorem internBindE_specV (s₀ : AState) (tag : UInt32) (ty b : EIdx)
    (hwf : StoreWF s₀.store) (htag : ETag.isBind tag = true)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => s = s₀⦄ internBindE tag ty b
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        s'.store.view h = some (eBindView tag ty b) ∧
        denoteE s'.store h = denoteEView s'.store (eBindView tag ty b); ⊤⦄ := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · simpa [internBindE, eBindView] using internLamE_specV s₀ ty b hwf hty hb
  · simpa [internBindE, eBindView, ETag.lam, ETag.forallE] using
      internForallEE_specV s₀ ty b hwf hty hb

/-- con-leche: none — `internRebuiltBind` at the V shape.  The `same = true`
branch answers the handle it was given, so the view monotonicity is reflexive
there. -/
theorem internRebuiltBind_specV (s₀ : AState) (h : EIdx) (same : Bool)
    (tag : UInt32) (ty b : EIdx) (hwf : StoreWF s₀.store)
    (htag : ETag.isBind tag = true)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (eBindView tag ty b)) :
    ⦃fun s => s = s₀⦄ internRebuiltBind h same tag ty b
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        s'.store.view r = some (eBindView tag ty b) ∧
        denoteE s'.store r = denoteEView s'.store (eBindView tag ty b); ⊤⦄ := by
  by_cases hc : same = true
  · have hprog : internRebuiltBind h same tag ty b = pure h := by
      simp [internRebuiltBind, hc]
    rw [hprog]
    vcgen
    subst s₀
    exact ⟨hwf, Ext.refl _, rfl, rfl, rfl, rfl, rfl, fun _ _ hj => hj, hsame hc,
      denoteE_view_eq hwf (hsame hc)⟩
  · have hprog : internRebuiltBind h same tag ty b = internBindE tag ty b := by
      simp [internRebuiltBind, hc]
    rw [hprog]
    exact internBindE_specV s₀ tag ty b hwf htag hty hb

/-! ### The per-constructor faces, at the V shape

One line each, exactly as `Bridge/Specs.lean`'s are: `internRebuiltX h same
args` IS `internRebuilt h same (.X args)`. -/

@[spec high] theorem internRebuiltFVar_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (idx : Nat) (ty : EIdx) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.fvar idx ty)) :
    ⦃fun s => s = s₀⦄ internRebuiltFVar h same idx ty
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        denoteE s'.store r = denoteEView s'.store (.fvar idx ty); ⊤⦄ :=
  internRebuilt_specV s₀ h same (.fvar idx ty) hwf (viewOK_fvar hty) hsame

@[spec high] theorem internRebuiltSort_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (u : LIdx) (hwf : StoreWF s₀.store)
    (hu : (s₀.store.ls.view u).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.sort u)) :
    ⦃fun s => s = s₀⦄ internRebuiltSort h same u
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        denoteE s'.store r = denoteEView s'.store (.sort u); ⊤⦄ :=
  internRebuilt_specV s₀ h same (.sort u) hwf (viewOK_sort hu) hsame

@[spec high] theorem internRebuiltConst_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (n : NIdx) (us : LsIdx) (hwf : StoreWF s₀.store)
    (hn : (s₀.store.ns.view n).isSome = true)
    (hus : (s₀.store.lss.view us).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.const n us)) :
    ⦃fun s => s = s₀⦄ internRebuiltConst h same n us
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        denoteE s'.store r = denoteEView s'.store (.const n us); ⊤⦄ :=
  internRebuilt_specV s₀ h same (.const n us) hwf (viewOK_const hn hus) hsame

@[spec high] theorem internRebuiltApp_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (f a : EIdx) (hwf : StoreWF s₀.store)
    (hf : (denoteE s₀.store f).isSome = true)
    (ha : (denoteE s₀.store a).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.app f a)) :
    ⦃fun s => s = s₀⦄ internRebuiltApp h same f a
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        denoteE s'.store r = denoteEView s'.store (.app f a); ⊤⦄ :=
  internRebuilt_specV s₀ h same (.app f a) hwf (viewOK_app hf ha) hsame

@[spec high] theorem internRebuiltLam_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (ty b : EIdx) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.lam ty b)) :
    ⦃fun s => s = s₀⦄ internRebuiltLam h same ty b
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        denoteE s'.store r = denoteEView s'.store (.lam ty b); ⊤⦄ :=
  internRebuilt_specV s₀ h same (.lam ty b) hwf (viewOK_lam hty hb) hsame

@[spec high] theorem internRebuiltForallE_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (ty b : EIdx) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.forallE ty b)) :
    ⦃fun s => s = s₀⦄ internRebuiltForallE h same ty b
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        denoteE s'.store r = denoteEView s'.store (.forallE ty b); ⊤⦄ :=
  internRebuilt_specV s₀ h same (.forallE ty b) hwf (viewOK_forallE hty hb)
    hsame

@[spec high] theorem internRebuiltLetE_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (ty val b : EIdx) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hval : (denoteE s₀.store val).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.letE ty val b)) :
    ⦃fun s => s = s₀⦄ internRebuiltLetE h same ty val b
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        denoteE s'.store r = denoteEView s'.store (.letE ty val b); ⊤⦄ :=
  internRebuilt_specV s₀ h same (.letE ty val b) hwf
    (viewOK_letE hty hval hb) hsame

@[spec high] theorem internRebuiltProj_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (n : NIdx) (i : Nat) (e : EIdx) (hwf : StoreWF s₀.store)
    (hn : (s₀.store.ns.view n).isSome = true)
    (he : (denoteE s₀.store e).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.proj n i e)) :
    ⦃fun s => s = s₀⦄ internRebuiltProj h same n i e
    ⦃fun r s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        denoteE s'.store r = denoteEView s'.store (.proj n i e); ⊤⦄ :=
  internRebuilt_specV s₀ h same (.proj n i e) hwf (viewOK_proj hn he) hsame

/-- con-leche: none — `internBVarE` at the V shape: the `fvar` arms of the two
abstraction walks intern a fresh `bvar` rather than rebuilding, so they need
`internE`'s face and not `internRebuilt`'s. -/
@[spec high] theorem internBVarE_specV (s₀ : AState) (i : Nat)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => s = s₀⦄ internBVarE i
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        s'.store.view h = some (.bvar i) ∧
        denoteE s'.store h = denoteEView s'.store (.bvar i); ⊤⦄ :=
  internE_specV s₀ (.bvar i) hwf viewOK_bvar

/-! ## The three "hop" helpers

A walk that reads `fvarB` before it reads the store has every `view` fact at a
store EQUAL to but not syntactically `s₀.store` (`fvarB` writes `fvarBC`, so
its Theorem 1 frames the store with an equation).  Inside a lemma the two
stores are variables and `subst` closes the gap in one step; in a
verification condition they are projections and it cannot.  These are
the facts the binder arm needs, stated so the hop happens inside. -/

end ConRon.Bridge.ExprOps
