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

Those parameters do not occur in the PROGRAM, so when `mvcgen` selects the
spec it has nothing to pin them against, and it does not leave them as
metavariables for the closer to solve either: it assigns them from whatever
is in scope at the right type.  Measured in `ExprOps/InstLP.lean`'s
`substLsMemoAt`: the readback list `ls : List Level` is in scope, so the
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

The specs below are `@[spec high]` because `Lean.Elab.Tactic.Do.findSpec`
sorts the candidates by priority and `Specs.lean`'s versions match the same
program; `attribute [-spec]` is refused by the attribute (measured), so the
priority is the only lever.  Each is proved by `unfold` + `mvcgen` and NOT by
`mvcgen [f]`, for the same reason: with `Specs.lean`'s spec in the database,
`mvcgen [f]` applies it instead of unfolding `f`.
-/
import ConRon.Bridge.Specs
import ConRon.Bridge.StoreBM

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1772-1774 Abs1MemoInv — `abs1Set`
with the memo's pure function moved inside the postcondition.  Generic in
`f`, which is what lets `abstract1Go` and `abstractRangeGo` share the one
table. -/
@[spec high] theorem abs1Set_specI (s₀ : AState) (k : EIdx × Nat) (r : EIdx)
    (hk : (denoteE s₀.store k.1).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ abs1Set k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with abs1C := s₀.memos.abs1C.insert k r } ∧
        ∀ f : Nat → Expr → Expr, MemoOK f s₀.memos.abs1C s₀.store →
          RelE (f k.2) s₀.store k.1 s₀.store r →
            MemoOK f s'.memos.abs1C s'.store⌝⦄ := by
  unfold abs1Set
  mvcgen
  rename_i s hs _s1
  subst hs
  refine ⟨rfl, rfl, rfl, rfl, fun f hm hr => ?_⟩
  show MemoOK f (s.memos.abs1C.insert k r) s.store
  exact MemoOK.insert hm rfl hk hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:562-564 ResetMemoInv — the same
for `resetSet`. -/
@[spec high] theorem resetSet_specI (s₀ : AState) (k : EIdx × Nat) (r : EIdx)
    (hk : (denoteE s₀.store k.1).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ resetSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with resetC := s₀.memos.resetC.insert k r } ∧
        ∀ f : Nat → Expr → Expr, MemoOK f s₀.memos.resetC s₀.store →
          RelE (f k.2) s₀.store k.1 s₀.store r →
            MemoOK f s'.memos.resetC s'.store⌝⦄ := by
  unfold resetSet
  mvcgen
  rename_i s hs _s1
  subst hs
  refine ⟨rfl, rfl, rfl, rfl, fun f hm hr => ?_⟩
  show MemoOK f (s.memos.resetC.insert k r) s.store
  exact MemoOK.insert hm rfl hk hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:983-985 RenameMemoInv — the same
for `renameSet`.  Here the internalisation is load-bearing twice over: the
renaming `fn : Name → Name` is the module's one higher-order parameter, and
as a theorem parameter it is exactly what `mvcgen` cannot guess. -/
@[spec high] theorem renameSet_specI (s₀ : AState) (k : EIdx × Nat) (r : EIdx)
    (hk : (denoteE s₀.store k.1).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with renameC := s₀.memos.renameC.insert k r } ∧
        ∀ f : Nat → Expr → Expr, MemoOK f s₀.memos.renameC s₀.store →
          RelE (f k.2) s₀.store k.1 s₀.store r →
            MemoOK f s'.memos.renameC s'.store⌝⦄ := by
  unfold renameSet
  mvcgen
  rename_i s hs _s1
  subst hs
  refine ⟨rfl, rfl, rfl, rfl, fun f hm hr => ?_⟩
  show MemoOK f (s.memos.renameC.insert k r) s.store
  exact MemoOK.insert hm rfl hk hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2546-2550 InstLPMemoInv — the same
for `instLPSet`. -/
@[spec high] theorem instLPSet_specI (s₀ : AState) (k : EIdx × Nat) (r : EIdx)
    (hk : (denoteE s₀.store k.1).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLPC := s₀.memos.instLPC.insert k r } ∧
        ∀ f : Nat → Expr → Expr, MemoOK f s₀.memos.instLPC s₀.store →
          RelE (f k.2) s₀.store k.1 s₀.store r →
            MemoOK f s'.memos.instLPC s'.store⌝⦄ := by
  unfold instLPSet
  mvcgen
  rename_i s hs _s1
  subst hs
  refine ⟨rfl, rfl, rfl, rfl, fun f hm hr => ?_⟩
  show MemoOK f (s.memos.instLPC.insert k r) s.store
  exact MemoOK.insert hm rfl hk hr

/-- con-leche: ConLeche/Kernel/Level.lean:28-40 Level.subst — the same for
`instLPLSet`, the LEVEL-handle memo. -/
@[spec high] theorem instLPLSet_specI (s₀ : AState) (h r : LIdx)
    (hk : (denoteL s₀.store.ls h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPLSet h r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLPLC := s₀.memos.instLPLC.insert h r } ∧
        ∀ f : Level → Level, MemoLOK f s₀.memos.instLPLC s₀.store →
          RelL f s₀.store h s₀.store r →
            MemoLOK f s'.memos.instLPLC s'.store⌝⦄ := by
  unfold instLPLSet
  mvcgen
  rename_i s hs _s1
  subst hs
  refine ⟨rfl, rfl, rfl, rfl, fun f hm hr => ?_⟩
  show MemoLOK f (s.memos.instLPLC.insert h r) s.store
  exact MemoLOK.insert hm rfl hk hr

/-- con-leche: ConLeche/Kernel/Level.lean:28-40 Level.subst — the same for
`instLPLsSet`, the universe-argument-LIST memo.  This is the one the trap was
measured on. -/
@[spec high] theorem instLPLsSet_specI (s₀ : AState) (h r : LsIdx)
    (hk : (denoteLs s₀.store.lss h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPLsSet h r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos =
          { s₀.memos with instLPLsC := s₀.memos.instLPLsC.insert h r } ∧
        ∀ f : List Level → List Level, MemoLsOK f s₀.memos.instLPLsC s₀.store →
          RelLs f s₀.store h s₀.store r →
            MemoLsOK f s'.memos.instLPLsC s'.store⌝⦄ := by
  unfold instLPLsSet
  mvcgen
  rename_i s hs _s1
  subst hs
  refine ⟨rfl, rfl, rfl, rfl, fun f hm hr => ?_⟩
  show MemoLsOK f (s.memos.instLPLsC.insert h r) s.store
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

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — `readLevelM` with the
sibling readback tables framed. -/
@[spec high] theorem readLevelM_specF (s₀ : AState) (h : LIdx)
    (hc : ReadLCacheOK s₀.caches.readLC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevelM h
    ⦃⇓? u s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readLC := s'.caches.readLC } ∧
        denoteL s₀.store.ls h = some u ∧
        ReadLCacheOK s'.caches.readLC s'.store⌝⦄ := by
  unfold readLevelM
  mvcgen
  all_goals (bridge_peel; subst_vars) <;>
    first
    | (refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadLCacheOK])
    | (intro hf; exact False.elim hf)
    | grind [ReadLCacheOK]

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — `readLevelsM` with the
sibling readback tables framed. -/
@[spec high] theorem readLevelsM_specF (s₀ : AState) (h : LsIdx)
    (hc : ReadLsCacheOK s₀.caches.readLsC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevelsM h
    ⦃⇓? us s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readLsC := s'.caches.readLsC } ∧
        denoteLs s₀.store.lss h = some us ∧
        ReadLsCacheOK s'.caches.readLsC s'.store⌝⦄ := by
  unfold readLevelsM
  mvcgen
  all_goals (bridge_peel; subst_vars) <;>
    first
    | (refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadLsCacheOK])
    | (intro hf; exact False.elim hf)
    | grind [ReadLsCacheOK]


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

/-- con-leche: none — `internE` moves no node read: the node arms end at a
cons hit or at `EStore.intern`, the two binder arms (task #97-T2-LOCKSTEP D6)
at `EStore.internBM` and then `EStore.internBindI`. -/
theorem internE_view_mono {s s' : AState} {w : ENodeView} {h : EIdx}
    (hrun : internE w s = .ok (h, s')) :
    ∀ i v, s.store.view i = some v → s'.store.view i = some v := by
  intro i v hi
  cases w
  case lam ty b m =>
    obtain ⟨mi, s₁, h1, h2⟩ := internE_lam_split hrun
    obtain ⟨-, rfl, rfl⟩ := internBME_ok h1
    obtain ⟨-, rfl⟩ := internLamIE_ok h2
    exact EStore.view_internBindI_mono _ _ _ _ _ (EStore.view_internBM_mono _ m hi)
  case forallE ty b m =>
    obtain ⟨mi, s₁, h1, h2⟩ := internE_forallE_split hrun
    obtain ⟨-, rfl, rfl⟩ := internBME_ok h1
    obtain ⟨-, rfl⟩ := internForallEIE_ok h2
    exact EStore.view_internBindI_mono _ _ _ _ _ (EStore.view_internBM_mono _ m hi)
  all_goals
    rcases internNodeE_ok hrun with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · exact hi
    · exact EStore.view_intern_mono _ _ hi

/-- con-leche: none — `internE` with view and binder-datum monotonicity:
`internE_spec` (whose `BMExt` conjunct is the datum half) and
`internE_view_mono`. -/
@[spec high] theorem internE_specV (s₀ : AState) (w : ENodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK w) :
    ⦃fun s => ⌜s = s₀⌝⦄ internE w
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i v, s₀.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        s'.store.view h = some w ∧
        denoteE s'.store h = denoteEView s'.store w⌝⦄ := by
  refine AM.triple_of_run_at fun h s' hrun => ?_
  obtain ⟨p1, p2, p3, p4, -, p6, p7, p8, p9, p10⟩ :=
    AM.of_run (P := fun t => t = s₀) rfl hrun (internE_spec s₀ w hwf hv)
  exact ⟨p1, p2, p4, p6, p7, p8, internE_view_mono hrun, p3, p9, p10⟩

/-- con-leche: none — `internRebuilt` with the same two conjuncts.  The
`same = true` branch answers the handle it was given, so both are
reflexive there. -/
@[spec high] theorem internRebuilt_specV (s₀ : AState) (h : EIdx) (same : Bool)
    (v : ENodeView) (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK v)
    (hsame : same = true → s₀.store.view h = some v) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuilt h same v
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i w, s₀.store.view i = some w → s'.store.view i = some w) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        denoteE s'.store r = denoteEView s'.store v⌝⦄ := by
  unfold internRebuilt
  mvcgen [internE_specV]
  case vc1.isTrue =>
    rename_i hc s hs
    subst hs
    exact ⟨hwf, Ext.refl _, rfl, rfl, rfl, rfl, fun _ _ hi => hi,
      fun _ _ hmi => hmi, denoteE_view_eq hwf (hsame hc)⟩
  case vc2.isFalse.post.success =>
    rename_i _hc s hs _r _s2
    subst hs
    intro a bb c dd e f g hh hi hj
    exact ⟨a, bb, c, dd, e, f, g, hh, hj⟩
  all_goals (intro s hs; subst hs; first | exact hwf | exact hv)

/-! ### The per-constructor faces, at the V shape

One line each, exactly as `Bridge/Specs.lean`'s are: `internRebuiltX h same
args` IS `internRebuilt h same (.X args)`. -/

@[spec high] theorem internRebuiltBVar_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (i : Nat) (hwf : StoreWF s₀.store)
    (hsame : same = true → s₀.store.view h = some (.bvar i)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltBVar h same i
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        denoteE s'.store r = denoteEView s'.store (.bvar i)⌝⦄ :=
  internRebuilt_specV s₀ h same (.bvar i) hwf viewOK_bvar hsame

@[spec high] theorem internRebuiltFVar_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (idx : Nat) (ty : EIdx) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.fvar idx ty)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltFVar h same idx ty
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        denoteE s'.store r = denoteEView s'.store (.fvar idx ty)⌝⦄ :=
  internRebuilt_specV s₀ h same (.fvar idx ty) hwf (viewOK_fvar hty) hsame

@[spec high] theorem internRebuiltSort_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (u : LIdx) (hwf : StoreWF s₀.store)
    (hu : (s₀.store.ls.view u).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.sort u)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltSort h same u
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        denoteE s'.store r = denoteEView s'.store (.sort u)⌝⦄ :=
  internRebuilt_specV s₀ h same (.sort u) hwf (viewOK_sort hu) hsame

@[spec high] theorem internRebuiltConst_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (n : NIdx) (us : LsIdx) (hwf : StoreWF s₀.store)
    (hn : (s₀.store.ns.view n).isSome = true)
    (hus : (s₀.store.lss.view us).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.const n us)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltConst h same n us
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        denoteE s'.store r = denoteEView s'.store (.const n us)⌝⦄ :=
  internRebuilt_specV s₀ h same (.const n us) hwf (viewOK_const hn hus) hsame

@[spec high] theorem internRebuiltApp_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (f a : EIdx) (hwf : StoreWF s₀.store)
    (hf : (denoteE s₀.store f).isSome = true)
    (ha : (denoteE s₀.store a).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.app f a)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltApp h same f a
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        denoteE s'.store r = denoteEView s'.store (.app f a)⌝⦄ :=
  internRebuilt_specV s₀ h same (.app f a) hwf (viewOK_app hf ha) hsame

@[spec high] theorem internRebuiltLam_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (ty b : EIdx) (m : BinderMeta) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.lam ty b m)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltLam h same ty b m
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi mm, s₀.store.viewBM mi = some mm → s'.store.viewBM mi = some mm) ∧
        denoteE s'.store r = denoteEView s'.store (.lam ty b m)⌝⦄ :=
  internRebuilt_specV s₀ h same (.lam ty b m) hwf (viewOK_lam hty hb) hsame

@[spec high] theorem internRebuiltForallE_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (ty b : EIdx) (m : BinderMeta) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.forallE ty b m)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltForallE h same ty b m
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi mm, s₀.store.viewBM mi = some mm → s'.store.viewBM mi = some mm) ∧
        denoteE s'.store r = denoteEView s'.store (.forallE ty b m)⌝⦄ :=
  internRebuilt_specV s₀ h same (.forallE ty b m) hwf (viewOK_forallE hty hb)
    hsame

@[spec high] theorem internRebuiltLetE_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (ty val b : EIdx) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hval : (denoteE s₀.store val).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.letE ty val b)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltLetE h same ty val b
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        denoteE s'.store r = denoteEView s'.store (.letE ty val b)⌝⦄ :=
  internRebuilt_specV s₀ h same (.letE ty val b) hwf
    (viewOK_letE hty hval hb) hsame

@[spec high] theorem internRebuiltProj_specV (s₀ : AState) (h : EIdx)
    (same : Bool) (n : NIdx) (i : Nat) (e : EIdx) (hwf : StoreWF s₀.store)
    (hn : (s₀.store.ns.view n).isSome = true)
    (he : (denoteE s₀.store e).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.proj n i e)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltProj h same n i e
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        denoteE s'.store r = denoteEView s'.store (.proj n i e)⌝⦄ :=
  internRebuilt_specV s₀ h same (.proj n i e) hwf (viewOK_proj hn he) hsame

/-- con-leche: none — `internBVarE` at the V shape: the `fvar` arms of the two
abstraction walks intern a fresh `bvar` rather than rebuilding, so they need
`internE`'s face and not `internRebuilt`'s. -/
@[spec high] theorem internBVarE_specV (s₀ : AState) (i : Nat)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internBVarE i
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        s'.store.view h = some (.bvar i) ∧
        denoteE s'.store h = denoteEView s'.store (.bvar i)⌝⦄ :=
  internE_specV s₀ (.bvar i) hwf viewOK_bvar


/-! ## The three generic step lemmas `Bridge/Rel.lean` is missing

`Bridge/Rel.lean`'s group 7 has `RelE.of_view` and the five per-site instances
for the BRANCHING constructors (`app`, `lam`, `forallE`, `letE`, `proj`).
Three walks of this tier rebuild a constructor that group 7 does not cover:
`resetMeta` and `renameConsts` descend into a `fvar`'s annotation, and
`instLPGo` rebuilds a `sort` and a `const`.  These are the same lemma at those
three constructors, and they belong beside the other five. -/

/-- con-leche: none — `RelE.of_view` at `fvar`, whose child is the type
ANNOTATION (`resetMeta`, `renameConsts` and `instantiateLevelParams` are the
three pure functions that descend into it). -/
theorem RelE.fvar {F Ft : Expr → Expr} {st st' : EStore} {h ty rt r : EIdx}
    {idx : Nat} (hwf : StoreWF st)
    (hview : st.view h = some (.fvar idx ty))
    (hdec : ∀ x, F (.fvar idx x) = .fvar idx (Ft x))
    (ht : RelE Ft st ty st' rt)
    (hr : denoteE st' r = denoteEView st' (.fvar idx rt)) :
    RelE F st h st' r := by
  intro e he
  obtain ⟨t, rfl, hdt⟩ := denote_fvar_inv hwf hview he
  rw [hr, denoteEView, hdec, ht t hdt]
  rfl

/-- con-leche: none — `RelE.of_view` at `sort`, whose child is a LEVEL handle:
the answer's level is related to the subject's by `RelL` (`instLPGo`'s
`.sort` arm, the one place an expression walk calls a level algorithm). -/
theorem RelE.sort {F : Expr → Expr} {Fl : Level → Level} {st st' : EStore}
    {h r : EIdx} {u ru : LIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.sort u))
    (hdec : ∀ l, F (.sort l) = .sort (Fl l))
    (hu : RelL Fl st u st' ru)
    (hr : denoteE st' r = denoteEView st' (.sort ru)) : RelE F st h st' r := by
  intro e he
  obtain ⟨l, rfl, hdl⟩ := denote_sort_inv hwf hview he
  rw [hr, denoteEView, hdec, hu l hdl]
  rfl

/-- con-leche: none — `RelE.of_view` at `const`, whose children are a NAME
handle (carried, possibly renamed) and a universe-argument LIST handle
(related by `RelLs`). -/
theorem RelE.const {F : Expr → Expr} {Fls : List Level → List Level}
    {st st' : EStore} {h r : EIdx} {n n' : NIdx} {us rus : LsIdx}
    {nm nm' : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.const n us))
    (hdec : ∀ ls, F (.const nm ls) = .const nm' (Fls ls))
    (hn0 : denoteN st.ns n = some nm) (hn' : denoteN st'.ns n' = some nm')
    (hus : RelLs Fls st us st' rus)
    (hr : denoteE st' r = denoteEView st' (.const n' rus)) :
    RelE F st h st' r := by
  intro e he
  obtain ⟨nm2, ls, rfl, hdn, hdl⟩ := denote_const_inv hwf hview he
  rw [hn0] at hdn
  obtain rfl := Option.some.inj hdn
  rw [hr, denoteEView, hdec, hn', hus ls hdl]
  rfl


/-- con-leche: none — `RelE.retarget` at the answer's OWN store, which is the
only target a memo insert ever needs: the row is recorded against the store
the call ended in.  `RelE.retarget` leaves that store a metavariable and the
closer cannot guess it (measured); this form determines it from the answer. -/
theorem RelE.retarget_self {f : Expr → Expr} {st st' : EStore} {c r : EIdx}
    (h : RelE f st c st' r) (hx : Ext st st')
    (hs : (denoteE st c).isSome = true) : RelE f st' c st' r :=
  h.retarget hx hs

/-! ## The three "hop" helpers

A walk that reads `fvarB` before it reads the store has every `view` fact at a
store EQUAL to but not syntactically `s₀.store` (`fvarB` writes `fvarBC`, so
its Theorem 1 frames the store with an equation).  Inside a lemma the two
stores are variables and `subst` closes the gap in one step; in a
verification condition they are projections and it cannot.  These three are
the facts the binder arm needs, stated so the hop happens inside. -/

/-- con-leche: none — `view_of_viewBindI_wf` across a store equation. -/
theorem view_of_viewBindI_hop {st st0 : EStore} (hst : st0 = st)
    (hwf : StoreWF st) {i ty b : EIdx} {mi : BMIdx}
    (htg : ETag.isBind i.tag = true) (h1 : some (ty, b, mi) = st0.viewBindI i) :
    ∃ m, st0.viewBM mi = some m ∧ mi.tag = 0 ∧
      st0.view i = some (eBindView i.tag ty b m) := by
  subst hst
  exact view_of_viewBindI_wf hwf htg h1.symm

/-- con-leche: none — the binder datum still decodes at the store the two
recursive calls left behind. -/
theorem bmOK_hop {st st0 s1 s2 : EStore} (hst : st0 = st) (hwf : StoreWF st)
    {i ty b : EIdx} {mi : BMIdx} (h1 : some (ty, b, mi) = st0.viewBindI i)
    (hbm1 : ∀ mj m, st0.viewBM mj = some m → s1.viewBM mj = some m)
    (hbm2 : ∀ mj m, s1.viewBM mj = some m → s2.viewBM mj = some m) :
    (s2.viewBM mi).isSome = true := by
  subst hst
  obtain ⟨hb, _⟩ := bmOK_of_viewBindI hwf h1.symm
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hb
  rw [hbm2 mi m (hbm1 mi m hm)]
  rfl

/-- con-leche: none — the binder's two children denote, at the store the walk
read the binder in. -/
theorem bindI_children_hop {st st0 : EStore} (hst : st0 = st)
    (hwf : StoreWF st) {i ty b : EIdx} {mi : BMIdx}
    (htg : ETag.isBind i.tag = true) (h1 : some (ty, b, mi) = st0.viewBindI i)
    (hden : (denoteE st i).isSome = true) :
    (denoteE st0 ty).isSome = true ∧ (denoteE st0 b).isSome = true := by
  subst hst
  obtain ⟨m, hbm, _, hvw⟩ := view_of_viewBindI_wf hwf htg h1.symm
  exact isSome_eBindView hwf hvw hden

/-- con-leche: none — an answer handle has a view at any later store: the
`internRebuilt` arms' `ViewOK` obligation, in one lemma. -/
theorem view_isSome_of_rel {f : Expr → Expr} {st s1 s2 : EStore} {c r : EIdx}
    (hden : (denoteE st c).isSome = true) (hr : RelE f st c s1 r)
    (hx : Ext s1 s2) : (s2.view r).isSome = true :=
  view_isSome (denote_isSome_ext (hr.isSome hden) hx)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — **the binder
arm's `internRebuilt` obligation**: if the two children came back unchanged
then the rebuilt binder view IS the handle's view, at the store the intern
happens in.  The datum's value is the one the walk carried, which is why the
statement quantifies over it exactly as `internRebuiltBindI_spec'` does. -/
theorem bindI_hsame {st s1 s2 : EStore} (hwf : StoreWF st)
    {i ty b rt rb : EIdx} {mi : BMIdx} {tg : UInt32} (htg : tg = i.tag)
    (htgb : ETag.isBind i.tag = true)
    (h1 : some (ty, b, mi) = st.viewBindI i)
    (hvm1 : ∀ j w, st.view j = some w → s1.view j = some w)
    (hvm2 : ∀ j w, s1.view j = some w → s2.view j = some w)
    (hbm1 : ∀ mj m, st.viewBM mj = some m → s1.viewBM mj = some m)
    (hbm2 : ∀ mj m, s1.viewBM mj = some m → s2.viewBM mj = some m) :
    ∀ m, s2.viewBM mi = some m → (rt == ty && rb == b) = true →
      s2.view i = some (eBindView tg rt rb m) := by
  intro m hbm hsame
  obtain ⟨m0, hbm0, _, hvw⟩ := view_of_viewBindI_wf hwf htgb h1.symm
  have hchain := hbm2 mi m0 (hbm1 mi m0 hbm0)
  rw [hbm] at hchain
  obtain rfl := Option.some.inj hchain
  simp only [Bool.and_eq_true, beq_iff_eq] at hsame
  obtain ⟨rfl, rfl⟩ := hsame
  rw [htg]
  exact hvm2 i _ (hvm1 i _ hvw)

end ConRon.Bridge.ExprOps
