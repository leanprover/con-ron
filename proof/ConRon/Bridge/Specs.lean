/-
# `ConRon.Bridge.Specs` — one `@[spec]` theorem per `Monad.lean` primitive

The thing task #97s's spike exists to fix: **one spec theorem per (B)
primitive, in one shape**, so that `mvcgen` can walk a twin's body without any
store reasoning appearing in the proof text.  The shape is the spike's
seven-rule template (DESIGN §8.6, `P2s SPIKE`, and task #97s's own section):

```lean
@[spec] theorem f_spec (s₀ : AState) (args…) (pre…) :
    ⦃fun s => ⌜s = s₀⌝⦄ f args ⦃⇓? r s' => ⌜Post s₀ r s'⌝⦄
```

1. **the precondition is `s = s₀` and nothing else** — every real
   precondition is an ordinary hypothesis of the theorem, so `mspec` turns it
   into a side goal instead of an entailment to discharge in the logic;
2. **`⇓?` (partial correctness), never `⇓`** — a (B) function may fail and
   Theorem 1 claims nothing then (con-leche's `SimAt`,
   `Verify/SimI.lean:244`);
3. **the postcondition names `s₀`**, the only way to state
   `Ext s₀.store s'.store` in a triple;
4. **"the subject denotes" is an `isSome`, never a named `Expr`**;
5. **the answer is a named relation** (`Bridge/Rel.lean`'s `RelE` family),
   never a bare `∀ e, … → …`;
6. **a memo insert's spec states that the INVARIANT is preserved**, not that
   the table grew — the single highest-value change of the spike;
7. **one named failure primitive** (`fail`), because a bare `throw` in
   `StateT σ (Except ε)` leaves `mvcgen` with universe metavariables.

## The frame conditions

`AState` has four fields and the `Memos` record has thirteen tables, so a
naive frame condition would be sixteen equations per spec.  Task #97b put the
per-call tables in ONE record and task #97c the per-declaration ones in
another for exactly this reason: every spec below frames the state in at most
four equations, and a memo write frames the other twelve tables with one
(`s'.memos = { s₀.memos with xC := … }`).

`Bridge/StateOK.lean`'s `CheckOK.mono` is what those equations buy: the whole
checker invariant crosses an `ExprOps` call on `Ext` plus
`s'.caches = s₀.caches` plus `s'.pins = s₀.pins`.

## What is NOT here, and why

* **`internPersistentE` / `…N` / `…L` / `…Ls`.**  `Arena/Store.lean`'s own
  note (the section "Interning into the PERSISTENT tier") states the
  obligation for the BRACKET and not for the operation: `internPersistent`
  breaks `fresh` transiently, and it is `promote … dropScratch` as a whole
  that takes `StoreWF` to `StoreWF`.  Its four specs therefore belong to the
  `Promote` tier, whose statement is that bracket, not to this file.
* **the eleven `internRebuilt*` faces of `ExprOps.lean`** are here, at the
  end: they are `internE` plus task #97-P6-5's upward cutoff, and every
  rebuilding walk goes through them.

## The closer

`bridge_vcs` at the end of this file is task #97s round 2's recipe: ONE
curated `grind` list, a `bridge_peel` in front of it, and a second stage that
puts the `RelE` transports back for the handful of verification conditions
that genuinely have to move an answer along the extension chain.  The arm
files erase the transports from `grind`'s set with `attribute [-grind]`
(round 2's item 1, worth 70 s → 11.5 s on the spike's one file), and because
`attribute [-grind]` does not travel through an import each of them repeats
the line.
-/
import ConRon.Bridge.StateOK
import ConRon.Bridge.StoreNested
import ConRon.Bridge.StoreBind
import Std.Tactic.Do

namespace ConRon.Bridge

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena Std.Do

/-! ## Two one-line tactics for the barrels

Under `⇓?` every failing branch of a primitive leaves a verification
condition of the shape `False → <postcondition>` — `fail_spec`'s success
barrel, applied.  `spec_fails` closes exactly those and nothing else (`intro`
fails on a conjunction, so the `try` cannot touch a real goal), and `spec_ro`
is the whole proof of a read-only primitive: the barrels, then one `grind`. -/

/-- con-leche: none — close the `False` barrels of a `⇓?` postcondition. -/
macro "spec_fails" : tactic =>
  `(tactic| all_goals try (intro hf; exact False.elim hf))

/-- con-leche: none — the whole proof of a state-reading primitive. -/
macro "spec_ro" : tactic => `(tactic| (spec_fails; all_goals grind))

/-! ## The derived `match` auxiliaries, given an owner (task #97-P3-ExprOps
round 4)

**The clash `lakefile.toml` and `Bridge/Core/Walks/Spine.lean` both record.**
`grind` derives a congruence auxiliary for the `match` of an
`Arena/**` definition *on demand*, into whatever module first needs it, under
a deterministic PUBLIC name — `<f>.match_1.congr_eq_1._sparseCasesOn_2`.  Two
modules that each derive the same one cannot then sit in one import closure:

    import ConRon.Bridge.Core.EnsureSort failed, environment already contains
    'ConRon.Arena.piResultIsProp.match_1.congr_eq_1._sparseCasesOn_2'
    from ConRon.Bridge.Core.Walks.Owed

That is what forced `Bridge/Core/Walks/Spine.lean` into a sibling module off
the knot-facing chain, and what `Arms/{InferIO,Annotate,Infer}` — all three ON
the chain and all three calling `ensureSort` — would hit next.

**The repair is to give the auxiliary ONE owner, and this file is it**: every
module of `ConRon/Bridge/**` imports it, and a derivation finds an imported
one and reuses it rather than adding a second.  That was measured, not
assumed: a module carrying `mvcgen [forallPw]` and importing a module
carrying only the two lines below re-uses the owner's auxiliary
(`getModuleIdxFor?` names the owner) and adds nothing.

**The spelling matters** (the `Refine2/Core/Eqns.lean` precedent).  What
forces the derivation is a `grind` on a goal whose head IS the matcher and
which cannot be closed without splitting it; a `grind` on `f x = f x`, or one
whose goal is `True`, closes first and derives nothing.  Hence the shape
below: the matcher at `motive := fun _ => Nat`, one branch `1`, the catch-all
`0`, and `≤ 1` as the claim.  It costs this file under a second per matcher
and it names no fact anyone has to maintain.

Add a line here when a new clash appears; the auxiliary's name in the error
message says which matcher to force. -/

/-- con-leche: none — the owner of `ConRon.Arena.piResultIsProp`'s
`ENodeView` match auxiliary (`Bridge/Core/EnsureSort.lean` and
`Bridge/Core/Walks/Owed.lean` both derived it). -/
theorem matchOwner_piResultIsProp (x : ENodeView) :
    ConRon.Arena.piResultIsProp.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — the owner of `ConRon.Arena.forallPw`'s `ENodeView`
match auxiliary (the clash `lakefile.toml`'s `ConRonBridge` note records,
between two modules of the `ExprOps` tier). -/
theorem matchOwner_forallPw (x : ENodeView) :
    ConRon.Arena.forallPw.match_1 (motive := fun _ => Nat) x
      (fun _ _ _ => 1) (fun _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — `ConRon.Arena.isLam`'s (`ExprOps/Spine.lean` against
`ExprOps/Walks.lean`). -/
theorem matchOwner_isLam (x : ENodeView) :
    ConRon.Arena.isLam.match_1 (motive := fun _ => Nat) x
      (fun _ _ _ => 1) (fun _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — `ConRon.Arena.isCtorApp`'s (`Core/Walks/Guards.lean`
against `Core/Walks/Spine.lean`). -/
theorem matchOwner_isCtorApp (x : ENodeView) :
    ConRon.Arena.isCtorApp.match_5 (motive := fun _ => Nat) x
      (fun _ _ => 1) (fun _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — `ConRon.Arena.denoteLs`' (`Frontend` against
`Inductives`). -/
theorem matchOwner_denoteLs (x : Option LsNodeView) :
    ConRon.Arena.denoteLs.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — the five `instantiate1Arm*` probe matches, shared by
`ExprOps/{Abs,Inst1,Reset,Subst}.lean`.  They are the `Option` shape of a
memo probe and of a `viewApp`/`viewBindI` projection, so every rebuilding
walk of the tier grinds over one. -/
theorem matchOwner_instantiate1ArmApp (x : Option (EIdx × EIdx)) :
    ConRon.Arena.instantiate1ArmApp.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ _ => 0) ≤ 1 := by
  grind

theorem matchOwner_instantiate1ArmApp3 (x : Option EIdx) :
    ConRon.Arena.instantiate1ArmApp.match_3 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  grind

theorem matchOwner_instantiate1ArmBVar (x : Option Nat) :
    ConRon.Arena.instantiate1ArmBVar.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  grind

theorem matchOwner_instantiate1ArmBind (x : Option (EIdx × EIdx × BMIdx)) :
    ConRon.Arena.instantiate1ArmBind.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ _ _ => 0) ≤ 1 := by
  grind

theorem matchOwner_instantiate1ArmLet (x : Option (EIdx × EIdx × EIdx)) :
    ConRon.Arena.instantiate1ArmLet.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ _ _ => 0) ≤ 1 := by
  grind

theorem matchOwner_instantiate1ArmProj (x : Option (NIdx × Nat × EIdx)) :
    ConRon.Arena.instantiate1ArmProj.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ _ _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — the three TEN-way `ENodeView` dispatch matches:
`fvarLeaves` (`ExprOps/{Leaves,Walks}.lean`), `liftLooseBVarsGo`
(`ExprOps/{Abs,Ranges,Walks}.lean`) and `resetMetaGo`
(`ExprOps/{Leaves,Reset,Walks}.lean`).  Ten `congr_eq`s each, and one `grind`
derives all ten. -/
theorem matchOwner_fvarLeaves (x : ENodeView) :
    ConRon.Arena.fvarLeaves.match_1 (motive := fun _ => Nat) x
      (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => 1)
      (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ _ => 1) (fun _ => 0) ≤ 1 := by
  grind

theorem matchOwner_liftLooseBVarsGo (x : ENodeView) :
    ConRon.Arena.liftLooseBVarsGo.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ _ => 1) (fun _ => 1) (fun _ _ => 1) (fun _ => 1)
      (fun _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => 1)
      (fun _ _ _ => 0) ≤ 1 := by
  grind

theorem matchOwner_resetMetaGo (x : ENodeView) :
    ConRon.Arena.resetMetaGo.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ => 1) (fun _ _ => 1) (fun _ => 1) (fun _ _ => 1)
      (fun _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => 1)
      (fun _ _ _ => 0) ≤ 1 := by
  grind

/-! ## The failure primitives (template rule 7) -/

/-- con-leche: ConLeche/Kernel/Core.lean:53-72 CheckError — **the failure
spec**: a `fail` never returns, so under `⇓?` its success barrel is `False`
and every continuation goal it produces closes by `.elim`. -/
@[spec] theorem fail_spec {α : Type} (e : Arena.CheckError) :
    ⦃fun _ => ⌜True⌝⦄ (fail e : AM α) ⦃⇓? _r _s' => ⌜False⌝⦄ := by
  intro _ _; trivial

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `none` arm of
`view`, spelled once (task #97-P6-10). -/
@[spec] theorem failDanglingE_spec {α : Type} :
    ⦃fun _ => ⌜True⌝⦄ (failDanglingE : AM α) ⦃⇓? _r _s' => ⌜False⌝⦄ := by
  intro _ _; trivial

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — the `none` arm of
`viewLs`, spelled once. -/
@[spec] theorem failDanglingLs_spec {α : Type} :
    ⦃fun _ => ⌜True⌝⦄ (failDanglingLs : AM α) ⦃⇓? _r _s' => ⌜False⌝⦄ := by
  intro _ _; trivial

/-! ## The expression store: `view`, `derivedE`, `internE` -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — `view` does not touch
the state and returns the store's own decoding. -/
@[spec] theorem view_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ view h
    ⦃⇓? v s' => ⌜s' = s₀ ∧ s₀.store.view h = some v⌝⦄ := by
  mvcgen [view]
  spec_ro

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — `derivedE` does not
touch the state and returns the packed word; with `EStore.derived_exact` that
word is `e.data` for the denoted `e`, which is what every cutoff reads. -/
@[spec] theorem derivedE_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ derivedE h
    ⦃⇓? w s' => ⌜s' = s₀ ∧ w = s₀.store.derived h⌝⦄ := by
  mvcgen [derivedE]
  spec_ro

/-- con-leche: none — `EStore.intern` does not change the TIER the store is
appending to: it is `internAt` at the datum `internBMOfView` chose, and
`Bridge/StoreBind.lean`'s `EStore.scratchOn_internAt` is that fact at
`internAt`.

Declared HERE rather than in `Bridge/Frontend/Shared.lean` (where task
#97-P4 first proved it) because `internE_spec`'s own frame needs it: a
persistence proof reaches `PersE_of_view` only at a state it knows is still
off the scratch tier, and it cannot know that unless the intern spec says
so. -/
theorem EStore.scratchOn_intern (st : EStore) (w : ENodeView) :
    (st.intern w).1.scratchOn = st.scratchOn := by
  rw [EStore.intern, EStore.scratchOn_internAt]
  rcases EStore.internBMOfView_cases st w with he | ⟨m, he⟩ | ⟨m, he⟩ <;> rw [he]

/-- con-leche: none — **the one spec that carries the arena**: a handle for
the node, the store still well formed, the arena only grown, the three other
state fields untouched, and the three nested stores literally unchanged (so a
name or level handle that had a view still has one).

The capacity test is `internE`'s own branch (DESIGN §8.3: "the Rust raises
`Native` at the limit, the Lean `throw`s the same kind"), which is what
discharges `EStore.intern_spec`'s `capOK` hypothesis without a precondition
here — task #97a follow-up 3 made `capOK` *literally* that branch condition
for exactly this reason. -/
@[spec] theorem internE_spec (s₀ : AState) (w : ENodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK w) :
    ⦃fun s => ⌜s = s₀⌝⦄ internE w
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some w ∧
        denoteE s'.store h = denoteEView s'.store w⌝⦄ := by
  mvcgen [internE]
  spec_fails
  -- **The cons HIT** (task #97-P5-1's finding 9, fixed in the twin at
  -- #97-P3-1): `internE` probes before it tests the capacity, exactly as the
  -- Rust does, so this branch answers the handle the cons table already
  -- holds and moves nothing.  `EStore.view_of_find` is `StoreWF`'s own
  -- `consP`/`consS` clause read left to right — no capacity in it.
  case vc1.h_1 =>
    rename_i s hs i hfind
    subst hs
    have hview := EStore.view_of_find hwf hfind
    obtain ⟨rk, hwf'⟩ := hwf
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, rfl, rfl, hview,
      denoteE_unfold hwf' hview⟩
  rename_i s hs _hfind _n _nbm hcap _st _s'
  subst hs
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcap
  have hcap' : EStore.capOK s.store w := by
    refine ⟨hcap.1, fun hbm => ?_⟩
    simp only [EStore.capOKBM]
    rcases hcap.2 with hh | hh
    · rw [hbm] at hh; exact absurd hh (by simp)
    · exact hh
  obtain ⟨h1, h2, h3, h4⟩ := EStore.intern_spec hwf hv hcap'
  exact ⟨h1, h2, BMExt.intern _ _, EStore.lss_intern _ _,
    EStore.scratchOn_intern _ _, rfl, rfl, rfl, h3, h4⟩

/-! ### The ten per-constructor faces of `internE`

`Store.lean`'s own words: "the equation the bridge owes is
`internCE (fields) = internE (.C fields)`, `rfl`".  So each spec is
`internE_spec` at that constructor, and the `unfold` is the whole proof. -/

@[spec] theorem internBVarE_spec (s₀ : AState) (i : Nat)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internBVarE i
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.bvar i) ∧
        denoteE s'.store h = denoteEView s'.store (.bvar i)⌝⦄ :=
  internE_spec s₀ (.bvar i) hwf viewOK_bvar

@[spec] theorem internLitE_spec (s₀ : AState) (l : ConLeche.Literal)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLitE l
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.lit l) ∧
        denoteE s'.store h = denoteEView s'.store (.lit l)⌝⦄ :=
  internE_spec s₀ (.lit l) hwf viewOK_lit

@[spec] theorem internFVarE_spec (s₀ : AState) (idx : Nat) (ty : EIdx)
    (hwf : StoreWF s₀.store) (hty : (denoteE s₀.store ty).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internFVarE idx ty
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.fvar idx ty) ∧
        denoteE s'.store h = denoteEView s'.store (.fvar idx ty)⌝⦄ :=
  internE_spec s₀ (.fvar idx ty) hwf (viewOK_fvar hty)

@[spec] theorem internSortE_spec (s₀ : AState) (u : LIdx)
    (hwf : StoreWF s₀.store) (hu : (s₀.store.ls.view u).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internSortE u
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.sort u) ∧
        denoteE s'.store h = denoteEView s'.store (.sort u)⌝⦄ :=
  internE_spec s₀ (.sort u) hwf (viewOK_sort hu)

@[spec] theorem internConstE_spec (s₀ : AState) (n : NIdx) (us : LsIdx)
    (hwf : StoreWF s₀.store) (hn : (s₀.store.ns.view n).isSome = true)
    (hus : (s₀.store.lss.view us).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internConstE n us
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.const n us) ∧
        denoteE s'.store h = denoteEView s'.store (.const n us)⌝⦄ :=
  internE_spec s₀ (.const n us) hwf (viewOK_const hn hus)

@[spec] theorem internAppE_spec (s₀ : AState) (f a : EIdx)
    (hwf : StoreWF s₀.store) (hf : (denoteE s₀.store f).isSome = true)
    (ha : (denoteE s₀.store a).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internAppE f a
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.app f a) ∧
        denoteE s'.store h = denoteEView s'.store (.app f a)⌝⦄ :=
  internE_spec s₀ (.app f a) hwf (viewOK_app hf ha)

@[spec] theorem internLamE_spec (s₀ : AState) (ty b : EIdx) (m : BinderMeta)
    (hwf : StoreWF s₀.store) (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLamE ty b m
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.lam ty b m) ∧
        denoteE s'.store h = denoteEView s'.store (.lam ty b m)⌝⦄ :=
  internE_spec s₀ (.lam ty b m) hwf (viewOK_lam hty hb)

@[spec] theorem internForallEE_spec (s₀ : AState) (ty b : EIdx)
    (m : BinderMeta) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internForallEE ty b m
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.forallE ty b m) ∧
        denoteE s'.store h = denoteEView s'.store (.forallE ty b m)⌝⦄ :=
  internE_spec s₀ (.forallE ty b m) hwf (viewOK_forallE hty hb)

@[spec] theorem internLetEE_spec (s₀ : AState) (ty val b : EIdx)
    (hwf : StoreWF s₀.store) (hty : (denoteE s₀.store ty).isSome = true)
    (hval : (denoteE s₀.store val).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLetEE ty val b
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.letE ty val b) ∧
        denoteE s'.store h = denoteEView s'.store (.letE ty val b)⌝⦄ :=
  internE_spec s₀ (.letE ty val b) hwf (viewOK_letE hty hval hb)

@[spec] theorem internProjE_spec (s₀ : AState) (n : NIdx) (i : Nat) (e : EIdx)
    (hwf : StoreWF s₀.store) (hn : (s₀.store.ns.view n).isSome = true)
    (he : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internProjE n i e
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.proj n i e) ∧
        denoteE s'.store h = denoteEView s'.store (.proj n i e)⌝⦄ :=
  internE_spec s₀ (.proj n i e) hwf (viewOK_proj hn he)

/-! ### The two binder faces over a datum HANDLE (task #97-P6-16)

`internLamIE` / `internForallEIE` do NOT go through `internE`: they call
`EStore.internLamI` / `internForallEI`, whose cons key is the datum's handle
and which never decode it.  `Bridge/StoreBind.lean`'s
`EStore.internBindI_spec` is the store fact; the two specs below are that fact
under the monadic wrapper's own capacity branch.

Both wrappers PROBE FIRST since task #97-P5-Twin, as `internE` has since
#97-P3-1, so each proof has two arms: the cons HIT, where the store does not
move and `EStore.view_of_findBindI` names the handle's view, and the MISS,
which is `internBindI_spec` at the tier the append goes to. -/

@[spec] theorem internLamIE_spec (s₀ : AState) (ty b : EIdx) (mi : BMIdx)
    (m : BinderMeta) (hwf : StoreWF s₀.store) (hmi0 : mi.tag = 0)
    (hbm : s₀.store.viewBM mi = some m)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLamIE ty b mi
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.lam ty b m) ∧
        denoteE s'.store h = denoteEView s'.store (.lam ty b m)⌝⦄ := by
  mvcgen [internLamIE]
  spec_fails
  -- **The cons HIT**: the probe comes first, so this arm answers the handle
  -- the `lams` table already holds and moves nothing.
  case vc1.h_1 =>
    rename_i s hs i hfind
    subst hs
    have hview :=
      EStore.view_of_findBindI (tag := ETag.lam) hwf (by decide) hbm hmi0 hfind
    have heb : eBindView ETag.lam ty b m = ENodeView.lam ty b m := by
      simp [eBindView]
    rw [heb] at hview
    obtain ⟨rk, hwf'⟩ := hwf
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, rfl, rfl, hview,
      denoteE_unfold hwf' hview⟩
  rename_i s hs _hfind _n hcap _st _s'
  subst hs
  obtain ⟨h1, h2, hbe, h3, h4, h5, h6⟩ :=
    EStore.internBindI_spec (tag := ETag.lam) hwf (by decide) hbm hmi0 hty hb hcap
  have heb : eBindView ETag.lam ty b m = ENodeView.lam ty b m := by
    simp [eBindView]
  rw [heb] at h5 h6
  exact ⟨h1, h2, hbe, h3, h4, rfl, rfl, rfl, h5, h6⟩

@[spec] theorem internForallEIE_spec (s₀ : AState) (ty b : EIdx) (mi : BMIdx)
    (m : BinderMeta) (hwf : StoreWF s₀.store) (hmi0 : mi.tag = 0)
    (hbm : s₀.store.viewBM mi = some m)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internForallEIE ty b mi
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.forallE ty b m) ∧
        denoteE s'.store h = denoteEView s'.store (.forallE ty b m)⌝⦄ := by
  mvcgen [internForallEIE]
  spec_fails
  case vc1.h_1 =>
    rename_i s hs i hfind
    subst hs
    have hview :=
      EStore.view_of_findBindI (tag := ETag.forallE) hwf (by decide) hbm hmi0 hfind
    have heb : eBindView ETag.forallE ty b m = ENodeView.forallE ty b m := by
      simp [eBindView, ETag.lam, ETag.forallE]
    rw [heb] at hview
    obtain ⟨rk, hwf'⟩ := hwf
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, rfl, rfl, hview,
      denoteE_unfold hwf' hview⟩
  rename_i s hs _hfind _n hcap _st _s'
  subst hs
  obtain ⟨h1, h2, hbe, h3, h4, h5, h6⟩ :=
    EStore.internBindI_spec (tag := ETag.forallE) hwf (by decide) hbm hmi0 hty hb hcap
  have heb : eBindView ETag.forallE ty b m = ENodeView.forallE ty b m := by
    simp [eBindView, ETag.lam, ETag.forallE]
  rw [heb] at h5 h6
  exact ⟨h1, h2, hbe, h3, h4, rfl, rfl, rfl, h5, h6⟩

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the two binder
arms at a tag the caller carries.  One spec, stated at `eBindView`, so that a
walk whose binder clause is shared between `lam` and `forallE` needs no case
split (which is the whole point of the tag-carrying form). -/
theorem internBindIE_spec (s₀ : AState) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) (m : BinderMeta) (hwf : StoreWF s₀.store) (hmi0 : mi.tag = 0)
    (htag : ETag.isBind tag = true) (hbm : s₀.store.viewBM mi = some m)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internBindIE tag ty b mi
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (eBindView tag ty b m) ∧
        denoteE s'.store h = denoteEView s'.store (eBindView tag ty b m)⌝⦄ := by
  rcases (show tag = ETag.lam ∨ tag = ETag.forallE by
      simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at htag; exact htag)
    with rfl | rfl
  · simpa [internBindIE, eBindView] using
      internLamIE_spec s₀ ty b mi m hwf hmi0 hbm hty hb
  · simpa [internBindIE, eBindView, ETag.lam, ETag.forallE] using
      internForallEIE_spec s₀ ty b mi m hwf hmi0 hbm hty hb

/-! ## The per-constructor projections of `view` (tasks #97-P6-10, #97-P6-13)

Thirteen specs, all of the same shape: the state does not move and the answer
is the store's own projection.  `Bridge/Rel.lean`'s group 6 turns each into a
`view` fact at the tag the caller has already tested. -/

@[spec] theorem viewApp_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewApp h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewApp h⌝⦄ := by
  mvcgen [viewApp]
  spec_ro

@[spec] theorem viewBVar_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewBVar h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewBVar h⌝⦄ := by
  mvcgen [viewBVar]
  spec_ro

@[spec] theorem viewSort_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewSort h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewSort h⌝⦄ := by
  mvcgen [viewSort]
  spec_ro

@[spec] theorem viewConst_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewConst h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewConst h⌝⦄ := by
  mvcgen [viewConst]
  spec_ro

@[spec] theorem viewConstName_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewConstName h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewConstName h⌝⦄ := by
  mvcgen [viewConstName]
  spec_ro

@[spec] theorem viewFVarIdx_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewFVarIdx h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewFVarIdx h⌝⦄ := by
  mvcgen [viewFVarIdx]
  spec_ro

@[spec] theorem viewFVarTy_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewFVarTy h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewFVarTy h⌝⦄ := by
  mvcgen [viewFVarTy]
  spec_ro

@[spec] theorem viewLit_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewLit h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewLit h⌝⦄ := by
  mvcgen [viewLit]
  spec_ro

@[spec] theorem viewLet_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewLet h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewLet h⌝⦄ := by
  mvcgen [viewLet]
  spec_ro

@[spec] theorem viewProj_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewProj h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewProj h⌝⦄ := by
  mvcgen [viewProj]
  spec_ro

@[spec] theorem viewBind_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewBind h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewBind h⌝⦄ := by
  mvcgen [viewBind]
  spec_ro

@[spec] theorem viewBindI_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewBindI h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewBindI h⌝⦄ := by
  mvcgen [viewBindI]
  spec_ro

@[spec] theorem viewBM_spec (s₀ : AState) (mi : BMIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewBM mi
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.viewBM mi⌝⦄ := by
  mvcgen [viewBM]
  spec_ro

/-! ## The name store -/

@[spec] theorem viewN_spec (s₀ : AState) (h : NIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewN h
    ⦃⇓? v s' => ⌜s' = s₀ ∧ s₀.store.ns.view h = some v⌝⦄ := by
  mvcgen [viewN]
  spec_ro

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — **the readback IS the
denotation** (DESIGN §8.3 lesson 4), so this spec is an equation and not a
simulation. -/
@[spec] theorem readName_spec (s₀ : AState) (h : NIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ readName h
    ⦃⇓? x s' => ⌜s' = s₀ ∧ denoteN s₀.store.ns h = some x⌝⦄ := by
  mvcgen [readName]
  spec_ro

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the readback of a name
LIST, by induction on the list (the recursion `readNames` itself takes). -/
@[spec] theorem readNames_spec (s₀ : AState) (hs : List NIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ readNames hs
    ⦃⇓? xs s' => ⌜s' = s₀ ∧ Frontend.denoteNList s₀.store.ns hs = some xs⌝⦄ := by
  induction hs generalizing s₀ with
  | nil => mvcgen [readNames]; try grind [Frontend.denoteNList]
  | cons a as ih =>
    mvcgen [readNames, ih]
    all_goals (bridge_peel; subst_vars; grind [Frontend.denoteNList])

/-- con-leche: none — hash-cons a name node, through the nesting.  The store
half is `Bridge/StoreNested.lean`'s `EStore.internName_spec`; this is that
fact under the wrapper's own capacity branch. -/
@[spec] theorem internNNode_spec (s₀ : AState) (v : NNodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ns.ViewOK v) :
    ⦃fun s => ⌜s = s₀⌝⦄ internNNode v
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.ns.view h = some v ∧
        denoteN s'.store.ns h = denoteNView s'.store.ns v⌝⦄ := by
  mvcgen [internNNode]
  spec_fails
  -- **The cons HIT** (task #97-P5-1's finding 9): the wrapper probes before
  -- it tests the capacity, exactly as the Rust does.
  case vc1.h_1 =>
    rename_i s hs _ns i hfind
    subst hs
    obtain ⟨rk, hwf'⟩ := hwf
    obtain ⟨rkn, hnw⟩ := hwf'.nsWF
    have hview := NStore.view_of_find ⟨rkn, hnw⟩ hfind
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl, hview,
      denoteN_unfold hnw hview⟩
  rename_i s hs _ns _hfind _n hcap _st _s'
  subst hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    EStore.internName_spec hwf hv (by exact hcap)
  exact ⟨h1, h2, h3, h4, h5, rfl, rfl, rfl, h6, h7⟩

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — intern a transient
name, by induction on the `Name` tree (the recursion `internName` takes: a
`Name` is a value, not a DAG, so no fuel). -/
@[spec] theorem internName_spec (s₀ : AState) (nm : ConLeche.Name)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internName nm
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteN s'.store.ns h = some nm⌝⦄ := by
  induction nm generalizing s₀ with
  | anonymous =>
    mvcgen [internName, internNNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteNView, Arena.NStore.ViewOK, NNodeView.children])
  | str p str ih =>
    mvcgen [internName, ih, internNNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteNView, Arena.NStore.ViewOK, NNodeView.children,
                 nview_isSome_of_denote, Ext.trans])
  | num p k ih =>
    mvcgen [internName, ih, internNNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteNView, Arena.NStore.ViewOK, NNodeView.children,
                 nview_isSome_of_denote, Ext.trans])

/-! ## The level store -/

@[spec] theorem viewL_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewL h
    ⦃⇓? v s' => ⌜s' = s₀ ∧ s₀.store.ls.view h = some v⌝⦄ := by
  mvcgen [viewL]
  spec_ro

@[spec] theorem derivedL_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ derivedL h
    ⦃⇓? d s' => ⌜s' = s₀ ∧ d = s₀.store.lder h⌝⦄ := by
  mvcgen [derivedL]
  spec_ro

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — **the level readback
IS `denoteL`** (DESIGN §8.3 lesson 4: "intern the representation, not the
algorithm"), which is what makes every level-algorithm obligation a pure
`Level` fact. -/
@[spec] theorem readLevel_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevel h
    ⦃⇓? u s' => ⌜s' = s₀ ∧ denoteL s₀.store.ls h = some u⌝⦄ := by
  mvcgen [readLevel]
  spec_ro

@[spec] theorem internLNode_spec (s₀ : AState) (v : LNodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ls.ViewOK v) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLNode v
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.ls.view h = some v ∧
        denoteL s'.store.ls h = denoteLView s'.store.ls v⌝⦄ := by
  mvcgen [internLNode]
  spec_fails
  -- **The cons HIT** (task #97-P5-1's finding 9): the wrapper probes before
  -- it tests the capacity, exactly as the Rust does.
  case vc1.h_1 =>
    rename_i s hs _ls i hfind
    subst hs
    obtain ⟨rk, hwf'⟩ := hwf
    obtain ⟨rkl, hlw⟩ := hwf'.lsWF
    have hview := LStore.view_of_find ⟨rkl, hlw⟩ hfind
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl, hview,
      denoteL_unfold hlw hview⟩
  rename_i s hs _ls _hfind _n hcap _st _s'
  subst hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    EStore.internLevel_spec hwf hv (by exact hcap)
  exact ⟨h1, h2, h3, h4, h5, rfl, rfl, rfl, h6, h7⟩

/-! ## The level-list store -/

@[spec] theorem viewLs_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewLs h
    ⦃⇓? v s' => ⌜s' = s₀ ∧ s₀.store.lss.view h = some v⌝⦄ := by
  mvcgen [viewLs]
  spec_ro

@[spec] theorem viewLsLen_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewLsLen h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.store.lss.viewLen h⌝⦄ := by
  mvcgen [viewLsLen]
  spec_ro

@[spec] theorem readLevels_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevels h
    ⦃⇓? us s' => ⌜s' = s₀ ∧ denoteLs s₀.store.lss h = some us⌝⦄ := by
  mvcgen [readLevels]
  spec_ro

@[spec] theorem internLsNode_spec (s₀ : AState) (v : LsNodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.lss.ViewOK v) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLsNode v
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.lss.view h = some v ∧
        denoteLs s'.store.lss h = denoteLsView s'.store.lss v⌝⦄ := by
  mvcgen [internLsNode]
  spec_fails
  -- **The cons HIT** (task #97-P5-1's finding 9): the wrapper probes before
  -- it tests the capacity, exactly as the Rust does.
  case vc1.h_1 =>
    rename_i s hs _lss i hfind
    subst hs
    obtain ⟨rk, hwf'⟩ := hwf
    have hview := LsStore.view_of_find hwf'.lssWF hfind
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl, hview,
      denoteLs_unfold hview⟩
  rename_i s hs _lss _hfind _n hcap _st _s'
  subst hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    EStore.internLevels_spec hwf hv (by exact hcap)
  exact ⟨h1, h2, h3, h4, h5, rfl, rfl, rfl, h6, h7⟩

/-! ## The readback memos (task #97-P6-13)

The obligation is a MEMO obligation and not a new algorithm: `denoteL`,
`denoteN` and `denoteLs` are functions of the store, so a hit answers with the
row the miss stored.  Which is why these three specs have the SAME conclusion
as their unmemoised siblings, plus the cache frame.

**The frame is a record EQUATION and not a table equation** (task
#97-P3-CoreWalks): `s'.caches = { s₀.caches with readLC := s'.caches.readLC }`
says in one line that the call moved this readback memo and *none of the
other thirteen tables*, which is what a caller rebuilding `CheckOK` needs and
what the first spelling of these three omitted.  Without it no walk of
`Arena/Core.lean` that reads a name, a level or a universe-argument list back
could keep the state invariant, and — since `[spec]` cannot be erased — a
caller could not prove the missing conjunct for itself either.  It costs
these three proofs one `rfl` each. -/

@[spec] theorem readLevelM_spec (s₀ : AState) (h : LIdx)
    (hc : ReadLCacheOK s₀.caches.readLC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevelM h
    ⦃⇓? u s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readLC := s'.caches.readLC } ∧
        denoteL s₀.store.ls h = some u ∧
        ReadLCacheOK s'.caches.readLC s'.store⌝⦄ := by
  mvcgen [readLevelM]
  all_goals (bridge_peel; subst_vars) <;>
    first
    | (refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadLCacheOK])
    | (intro hf; exact False.elim hf)
    | grind [ReadLCacheOK]

@[spec] theorem readNameM_spec (s₀ : AState) (h : NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readNameM h
    ⦃⇓? x s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readNC := s'.caches.readNC } ∧
        denoteN s₀.store.ns h = some x ∧
        ReadNCacheOK s'.caches.readNC s'.store⌝⦄ := by
  mvcgen [readNameM]
  all_goals (bridge_peel; subst_vars) <;>
    first
    | (refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadNCacheOK])
    | (intro hf; exact False.elim hf)
    | grind [ReadNCacheOK]

@[spec] theorem readLevelsM_spec (s₀ : AState) (h : LsIdx)
    (hc : ReadLsCacheOK s₀.caches.readLsC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevelsM h
    ⦃⇓? us s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readLsC := s'.caches.readLsC } ∧
        denoteLs s₀.store.lss h = some us ∧
        ReadLsCacheOK s'.caches.readLsC s'.store⌝⦄ := by
  mvcgen [readLevelsM]
  all_goals (bridge_peel; subst_vars) <;>
    first
    | (refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadLsCacheOK])
    | (intro hf; exact False.elim hf)
    | grind [ReadLsCacheOK]

/-! ## The thirteen memo tables

Three specs per handle-valued table — probe, record, drop — and the record's
spec states that the INVARIANT is preserved (template rule 6): `MemoOK` in
*goal* position is skolemised by `grind` into `∀ k r, …` before any lemma can
fire, so the invariant has to arrive as a hypothesis.

The frame is one equation for the other twelve tables
(`s'.memos = { s₀.memos with xC := … }`), which is what putting them in a
record bought. -/

@[spec] theorem inst1Get_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Get k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.inst1C[k]?⌝⦄ := by
  mvcgen [inst1Get]
  spec_ro

@[spec] theorem inst1Set_spec (s₀ : AState) (ve : Expr) (k : EIdx × Nat)
    (r : EIdx) (hm : Inst1MemoA ve s₀)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (fun e => Expr.instantiate1 e ve k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Set k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with inst1C := s₀.memos.inst1C.insert k r } ∧
        Inst1MemoA ve s'⌝⦄ := by
  mvcgen [inst1Set]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

@[spec] theorem inst1Clear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Clear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with inst1C := ∅ } ∧
        ∀ ve, Inst1MemoA ve s'⌝⦄ := by
  mvcgen [inst1Clear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem instLGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.instLC[k]?⌝⦄ := by
  mvcgen [instLGet]
  spec_ro

@[spec] theorem instLSet_spec (s₀ : AState) (ws : List Expr) (k : EIdx × Nat)
    (r : EIdx) (hm : InstLMemoA ws s₀)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (fun e => Expr.instantiateList e ws k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLC := s₀.memos.instLC.insert k r } ∧
        InstLMemoA ws s'⌝⦄ := by
  mvcgen [instLSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

@[spec] theorem instLClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with instLC := ∅ } ∧
        ∀ ws, InstLMemoA ws s'⌝⦄ := by
  mvcgen [instLClear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem liftGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ liftGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.liftC[k]?⌝⦄ := by
  mvcgen [liftGet]
  spec_ro

@[spec] theorem liftSet_spec (s₀ : AState) (amount : Nat) (k : EIdx × Nat)
    (r : EIdx) (hm : LiftMemoA amount s₀)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (Expr.liftLooseBVars amount k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ liftSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with liftC := s₀.memos.liftC.insert k r } ∧
        LiftMemoA amount s'⌝⦄ := by
  mvcgen [liftSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

@[spec] theorem liftClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ liftClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with liftC := ∅ } ∧
        ∀ amount, LiftMemoA amount s'⌝⦄ := by
  mvcgen [liftClear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem resetGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ resetGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.resetC[k]?⌝⦄ := by
  mvcgen [resetGet]
  spec_ro

@[spec] theorem resetSet_spec (s₀ : AState) (k : EIdx × Nat) (r : EIdx)
    (hm : ResetMemoA s₀) (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE Expr.resetMeta s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ resetSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with resetC := s₀.memos.resetC.insert k r } ∧
        ResetMemoA s'⌝⦄ := by
  mvcgen [resetSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

@[spec] theorem resetClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ resetClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with resetC := ∅ } ∧
        ResetMemoA s'⌝⦄ := by
  mvcgen [resetClear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.of_empty rfl⟩

@[spec] theorem renameGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.renameC[k]?⌝⦄ := by
  mvcgen [renameGet]
  spec_ro

@[spec] theorem renameSet_spec (s₀ : AState)
    (fn : ConLeche.Name → ConLeche.Name) (k : EIdx × Nat) (r : EIdx)
    (hm : RenameMemoA fn s₀) (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (Expr.renameConsts fn) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with renameC := s₀.memos.renameC.insert k r } ∧
        RenameMemoA fn s'⌝⦄ := by
  mvcgen [renameSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

@[spec] theorem renameClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with renameC := ∅ } ∧
        ∀ fn, RenameMemoA fn s'⌝⦄ := by
  mvcgen [renameClear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem abs1Get_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ abs1Get k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.abs1C[k]?⌝⦄ := by
  mvcgen [abs1Get]
  spec_ro

@[spec] theorem abs1Set_spec (s₀ : AState) (d : Nat) (k : EIdx × Nat)
    (r : EIdx) (hm : Abs1MemoA d s₀)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (fun e => Expr.abstract1 e d k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ abs1Set k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with abs1C := s₀.memos.abs1C.insert k r } ∧
        Abs1MemoA d s'⌝⦄ := by
  mvcgen [abs1Set]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

@[spec] theorem abs1Clear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ abs1Clear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with abs1C := ∅ } ∧
        ∀ d, Abs1MemoA d s'⌝⦄ := by
  mvcgen [abs1Clear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem lowerGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ lowerGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.lowerC[k]?⌝⦄ := by
  mvcgen [lowerGet]
  spec_ro

@[spec] theorem lowerSet_spec (s₀ : AState) (amount : Nat) (k : EIdx × Nat)
    (r : EIdx) (hm : LowerMemoA amount s₀)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (Expr.lowerBVars amount k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ lowerSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with lowerC := s₀.memos.lowerC.insert k r } ∧
        LowerMemoA amount s'⌝⦄ := by
  mvcgen [lowerSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

@[spec] theorem lowerClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ lowerClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with lowerC := ∅ } ∧
        ∀ amount, LowerMemoA amount s'⌝⦄ := by
  mvcgen [lowerClear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem inst1LGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1LGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.inst1LC[k]?⌝⦄ := by
  mvcgen [inst1LGet]
  spec_ro

@[spec] theorem inst1LSet_spec (s₀ : AState) (ve : Expr) (k : EIdx × Nat)
    (r : EIdx) (hm : Inst1LMemoA ve s₀)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (fun e => Expr.instantiate1Lift e ve k.2) s₀.store k.1
      s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1LSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with inst1LC := s₀.memos.inst1LC.insert k r } ∧
        Inst1LMemoA ve s'⌝⦄ := by
  mvcgen [inst1LSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

@[spec] theorem inst1LClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1LClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with inst1LC := ∅ } ∧
        ∀ ve, Inst1LMemoA ve s'⌝⦄ := by
  mvcgen [inst1LClear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem instLPGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.instLPC[k]?⌝⦄ := by
  mvcgen [instLPGet]
  spec_ro

@[spec] theorem instLPSet_spec (s₀ : AState) (ks : List ConLeche.Name)
    (us : List Level) (k : EIdx × Nat) (r : EIdx) (hm : InstLPMemoA ks us s₀)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (fun e => e.instantiateLevelParams ks us) s₀.store k.1
      s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLPC := s₀.memos.instLPC.insert k r } ∧
        InstLPMemoA ks us s'⌝⦄ := by
  mvcgen [instLPSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2720-2722 Expr.instLPFast — the
one `Clear` that drops THREE tables: `instLPFast`'s memo depends on `ks` and
`us`, and so do the two level-handle tables task #97-P6-13 added beside it. -/
@[spec] theorem instLPClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLPC := ∅, instLPLC := ∅, instLPLsC := ∅ } ∧
        (∀ ks us, InstLPMemoA ks us s') ∧ (∀ ks us, InstLPLMemoA ks us s') ∧
        ∀ ks us, InstLPLsMemoA ks us s'⌝⦄ := by
  mvcgen [instLPClear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => MemoOK.of_empty rfl,
    fun _ _ => MemoLOK.of_empty rfl, fun _ _ => MemoLsOK.of_empty rfl⟩

@[spec] theorem instLPLGet_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPLGet h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.instLPLC[h]?⌝⦄ := by
  mvcgen [instLPLGet]
  spec_ro

@[spec] theorem instLPLSet_spec (s₀ : AState) (ks : List ConLeche.Name)
    (us : List Level) (h r : LIdx) (hm : InstLPLMemoA ks us s₀)
    (hk : (denoteL s₀.store.ls h).isSome = true)
    (hr : RelL (Level.subst ks us) s₀.store h s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPLSet h r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLPLC := s₀.memos.instLPLC.insert h r } ∧
        InstLPLMemoA ks us s'⌝⦄ := by
  mvcgen [instLPLSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoLOK.insert hm rfl hk hr⟩

@[spec] theorem instLPLsGet_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPLsGet h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.instLPLsC[h]?⌝⦄ := by
  mvcgen [instLPLsGet]
  spec_ro

@[spec] theorem instLPLsSet_spec (s₀ : AState) (ks : List ConLeche.Name)
    (us : List Level) (h r : LsIdx) (hm : InstLPLsMemoA ks us s₀)
    (hk : (denoteLs s₀.store.lss h).isSome = true)
    (hr : RelLs (fun vs => vs.map (Level.subst ks us)) s₀.store h s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPLsSet h r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos =
          { s₀.memos with instLPLsC := s₀.memos.instLPLsC.insert h r } ∧
        InstLPLsMemoA ks us s'⌝⦄ := by
  mvcgen [instLPLsSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoLsOK.insert hm rfl hk hr⟩

@[spec] theorem bvarBGet_spec (s₀ : AState) (k : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ bvarBGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.bvarBC[k]?⌝⦄ := by
  mvcgen [bvarBGet]
  spec_ro

@[spec] theorem bvarBSet_spec (s₀ : AState) (k : EIdx) (r : Nat)
    (hm : MemoBA s₀) (hk : (denoteE s₀.store k).isSome = true)
    (hr : RelV Expr.bvarBound s₀.store k r) :
    ⦃fun s => ⌜s = s₀⌝⦄ bvarBSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with bvarBC := s₀.memos.bvarBC.insert k r } ∧
        MemoBA s'⌝⦄ := by
  mvcgen [bvarBSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoVOK.insert hm rfl hk hr⟩

@[spec] theorem bvarBClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ bvarBClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with bvarBC := ∅ } ∧
        MemoBA s'⌝⦄ := by
  mvcgen [bvarBClear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoVOK.of_empty rfl⟩

@[spec] theorem fvarBGet_spec (s₀ : AState) (k : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarBGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.fvarBC[k]?⌝⦄ := by
  mvcgen [fvarBGet]
  spec_ro

@[spec] theorem fvarBSet_spec (s₀ : AState) (k : EIdx) (r : Nat)
    (hm : MemoFA s₀) (hk : (denoteE s₀.store k).isSome = true)
    (hr : RelV Expr.fvarRange s₀.store k r) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarBSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with fvarBC := s₀.memos.fvarBC.insert k r } ∧
        MemoFA s'⌝⦄ := by
  mvcgen [fvarBSet]
  rename_i s hs _mp _s1
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoVOK.insert hm rfl hk hr⟩

@[spec] theorem fvarBClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarBClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with fvarBC := ∅ } ∧
        MemoFA s'⌝⦄ := by
  mvcgen [fvarBClear]
  rename_i s hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoVOK.of_empty rfl⟩

/-! ## The `ExprOps` intern faces with the upward cutoff (task #97-P6-5)

`internRebuilt h same v` answers `h` itself when the walk's children all came
back unchanged, and `internE v` otherwise.  Its spec takes the caller's own
obligation for the `same` branch — "if `same` then `v` IS `h`'s view" — which
is exactly what the walk knows, and answers the same postcondition in both
branches.  `denoteEView_ext` (`Bridge/Rel.lean` group 6b) is what makes the
`same` branch's conclusion the other's. -/

@[spec] theorem internRebuilt_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (v : ENodeView) (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK v)
    (hsame : same = true → s₀.store.view h = some v) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuilt h same v
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store v⌝⦄ := by
  mvcgen [internRebuilt, internE_spec]
  case vc1.isTrue =>
    rename_i hc s hs
    subst hs
    exact ⟨hwf, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, rfl, rfl,
      denoteE_view_eq hwf (hsame hc)⟩
  case vc2.isFalse.post.success =>
    rename_i _hc s hs _r _s2
    subst hs
    intro a bb bm c sc d e f _g hh
    exact ⟨a, bb, bm, c, sc, d, e, f, hh⟩
  all_goals (intro s hs; subst hs; first | exact hwf | exact hv)

/-! ### The eleven per-constructor faces of `internRebuilt` (task #97-P6-15)

`internRebuiltApp h same f a` is `internRebuilt h same (.app f a)` — the view
is never built — so each spec is `internRebuilt_spec` at that constructor and
the definitional unfolding is the whole proof.  The two BINDER faces are the
exception: `internRebuiltBind` takes the tag INSIDE the `else` branch, so the
`if` on the tag and the `if` on `same` commute rather than coincide, and the
proof is a two-case split. -/

@[spec] theorem internRebuiltBVar_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (i : Nat) (hwf : StoreWF s₀.store)
    (hsame : same = true → s₀.store.view h = some (.bvar i)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltBVar h same i
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.bvar i)⌝⦄ :=
  internRebuilt_spec s₀ h same (.bvar i) hwf viewOK_bvar hsame

@[spec] theorem internRebuiltLit_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (l : ConLeche.Literal) (hwf : StoreWF s₀.store)
    (hsame : same = true → s₀.store.view h = some (.lit l)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltLit h same l
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.lit l)⌝⦄ :=
  internRebuilt_spec s₀ h same (.lit l) hwf viewOK_lit hsame

@[spec] theorem internRebuiltFVar_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (idx : Nat) (ty : EIdx) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.fvar idx ty)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltFVar h same idx ty
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.fvar idx ty)⌝⦄ :=
  internRebuilt_spec s₀ h same (.fvar idx ty) hwf (viewOK_fvar hty) hsame

@[spec] theorem internRebuiltSort_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (u : LIdx) (hwf : StoreWF s₀.store)
    (hu : (s₀.store.ls.view u).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.sort u)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltSort h same u
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.sort u)⌝⦄ :=
  internRebuilt_spec s₀ h same (.sort u) hwf (viewOK_sort hu) hsame

@[spec] theorem internRebuiltConst_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (n : NIdx) (us : LsIdx) (hwf : StoreWF s₀.store)
    (hn : (s₀.store.ns.view n).isSome = true)
    (hus : (s₀.store.lss.view us).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.const n us)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltConst h same n us
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.const n us)⌝⦄ :=
  internRebuilt_spec s₀ h same (.const n us) hwf (viewOK_const hn hus) hsame

@[spec] theorem internRebuiltApp_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (f a : EIdx) (hwf : StoreWF s₀.store)
    (hf : (denoteE s₀.store f).isSome = true)
    (ha : (denoteE s₀.store a).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.app f a)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltApp h same f a
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.app f a)⌝⦄ :=
  internRebuilt_spec s₀ h same (.app f a) hwf (viewOK_app hf ha) hsame

@[spec] theorem internRebuiltLam_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (ty b : EIdx) (m : BinderMeta) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.lam ty b m)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltLam h same ty b m
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.lam ty b m)⌝⦄ :=
  internRebuilt_spec s₀ h same (.lam ty b m) hwf (viewOK_lam hty hb) hsame

@[spec] theorem internRebuiltForallE_spec (s₀ : AState) (h : EIdx)
    (same : Bool) (ty b : EIdx) (m : BinderMeta) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.forallE ty b m)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltForallE h same ty b m
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.forallE ty b m)⌝⦄ :=
  internRebuilt_spec s₀ h same (.forallE ty b m) hwf (viewOK_forallE hty hb)
    hsame

@[spec] theorem internRebuiltLetE_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (ty val b : EIdx) (hwf : StoreWF s₀.store)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hval : (denoteE s₀.store val).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.letE ty val b)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltLetE h same ty val b
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.letE ty val b)⌝⦄ :=
  internRebuilt_spec s₀ h same (.letE ty val b) hwf
    (viewOK_letE hty hval hb) hsame

@[spec] theorem internRebuiltProj_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (n : NIdx) (i : Nat) (e : EIdx) (hwf : StoreWF s₀.store)
    (hn : (s₀.store.ns.view n).isSome = true)
    (he : (denoteE s₀.store e).isSome = true)
    (hsame : same = true → s₀.store.view h = some (.proj n i e)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltProj h same n i e
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (.proj n i e)⌝⦄ :=
  internRebuilt_spec s₀ h same (.proj n i e) hwf (viewOK_proj hn he) hsame

/-- con-leche: none — `internRebuilt` at a binder view the caller carries as a
TAG (task #97-P6-5 at #97-P6-16's shape): the `if` on the tag lives inside the
`else`, so the proof is the two-case split and not a definitional
unfolding. -/
@[spec] theorem internRebuiltBind_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (tag : UInt32) (ty b : EIdx) (m : BinderMeta) (hwf : StoreWF s₀.store)
    (htag : ETag.isBind tag = true)
    (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (eBindView tag ty b m)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltBind h same tag ty b m
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = denoteEView s'.store (eBindView tag ty b m)⌝⦄ := by
  rcases (show tag = ETag.lam ∨ tag = ETag.forallE by
      simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at htag; exact htag)
    with rfl | rfl
  · have := internRebuilt_spec s₀ h same (.lam ty b m) hwf
      (viewOK_lam hty hb) (by simpa [eBindView] using hsame)
    simpa [internRebuiltBind, internRebuilt, internLamE, eBindView] using this
  · have := internRebuilt_spec s₀ h same (.forallE ty b m) hwf
      (viewOK_forallE hty hb)
      (by simpa [eBindView, ETag.lam, ETag.forallE] using hsame)
    simpa [internRebuiltBind, internRebuilt, internForallEE, eBindView,
      ETag.lam, ETag.forallE] using this

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta —
`internRebuiltBind` at a binder datum the walk is CARRYING ACROSS (task
#97-P6-16): a substituting walk takes a binder apart and puts it back with the
same datum, so the round trip never decodes it. -/
theorem internRebuiltBindI_spec (s₀ : AState) (h : EIdx) (same : Bool)
    (tag : UInt32) (ty b : EIdx) (mi : BMIdx) (m : BinderMeta)
    (hwf : StoreWF s₀.store) (hmi0 : mi.tag = 0)
    (htag : ETag.isBind tag = true) (hbm : s₀.store.viewBM mi = some m)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true)
    (hsame : same = true → s₀.store.view h = some (eBindView tag ty b m)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltBindI h same tag ty b mi
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view r = some (eBindView tag ty b m) ∧
        denoteE s'.store r = denoteEView s'.store (eBindView tag ty b m)⌝⦄ := by
  by_cases hc : same = true
  · have hprog : internRebuiltBindI h same tag ty b mi = pure h := by
      simp [internRebuiltBindI, hc]
    rw [hprog]
    mvcgen
    rename_i s hs
    subst hs
    exact ⟨hwf, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, rfl, rfl, hsame hc,
      denoteE_view_eq hwf (hsame hc)⟩
  · have hprog :
        internRebuiltBindI h same tag ty b mi = internBindIE tag ty b mi := by
      simp [internRebuiltBindI, hc]
    rw [hprog]
    exact internBindIE_spec s₀ tag ty b mi m hwf hmi0 htag hbm hty hb

/-! ### The two binder interns, in the form `mvcgen` can use

Task #97b's "one measured trap", at the binder datum: the datum's VALUE `m`
does not appear in the PROGRAM, so `mvcgen` has nothing to pin it against and
leaves the arm a goal `⊢ BinderMeta` (measured here, verification condition
`vc30.m` of `instantiate1Go`).  The fix is template rule 4 applied to the
datum: the precondition is `(viewBM mi).isSome`, and the value is recovered
INSIDE the postcondition.  These — not the two above — are the `@[spec]`
theorems the walks use; `Bridge/Rel.lean`'s `bmOK_of_viewBindI` is what
discharges their two side conditions from the `viewBindI` read. -/

@[spec] theorem internBindIE_spec' (s₀ : AState) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) (hwf : StoreWF s₀.store) (hmi0 : mi.tag = 0)
    (htag : ETag.isBind tag = true)
    (hbm : (s₀.store.viewBM mi).isSome = true)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internBindIE tag ty b mi
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        ∀ m, s₀.store.viewBM mi = some m →
          (s'.store.view h = some (eBindView tag ty b m) ∧
            denoteE s'.store h =
              denoteEView s'.store (eBindView tag ty b m))⌝⦄ := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hbm
  have h := internBindIE_spec s₀ tag ty b mi m hwf hmi0 htag hm hty hb
  refine Std.Do.Triple.of_entails_wp (Std.Do.Triple.entails_wp_of_post h ?_)
  refine ⟨fun _a => ?_, Std.Do.ExceptConds.entails.refl _⟩
  intro s' hp
  obtain ⟨p1, p2, pbe, p3, p4, p5, p6, p7, p8, p9⟩ := hp
  refine ⟨p1, p2, pbe, p3, p4, p5, p6, p7, fun m' hm' => ?_⟩
  rw [hm] at hm'
  obtain rfl := Option.some.inj hm'
  exact ⟨p8, p9⟩

@[spec] theorem internRebuiltBindI_spec' (s₀ : AState) (h : EIdx) (same : Bool)
    (tag : UInt32) (ty b : EIdx) (mi : BMIdx) (hwf : StoreWF s₀.store)
    (hmi0 : mi.tag = 0) (htag : ETag.isBind tag = true)
    (hbm : (s₀.store.viewBM mi).isSome = true)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true)
    (hsame : ∀ m, s₀.store.viewBM mi = some m → same = true →
      s₀.store.view h = some (eBindView tag ty b m)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltBindI h same tag ty b mi
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        ∀ m, s₀.store.viewBM mi = some m →
          (s'.store.view r = some (eBindView tag ty b m) ∧
            denoteE s'.store r =
              denoteEView s'.store (eBindView tag ty b m))⌝⦄ := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hbm
  have hh0 := internRebuiltBindI_spec s₀ h same tag ty b mi m hwf hmi0 htag hm
    hty hb (hsame m hm)
  refine Std.Do.Triple.of_entails_wp (Std.Do.Triple.entails_wp_of_post hh0 ?_)
  refine ⟨fun _a => ?_, Std.Do.ExceptConds.entails.refl _⟩
  intro s' hp
  obtain ⟨p1, p2, pbe, p3, p4, p5, p6, p7, p8, p9⟩ := hp
  refine ⟨p1, p2, pbe, p3, p4, p5, p6, p7, fun m' hm' => ?_⟩
  rw [hm] at hm'
  obtain rfl := Option.some.inj hm'
  exact ⟨p8, p9⟩

/-! ### The bulk-instantiation cutoff (task #97f's deviation)

`instListCutoff` reads the packed loose-bvar bound off the derived column and
compares it with the cursor.  What its caller needs is the *positive*
direction — a `true` answer licenses the early return — so that is what the
spec says; a `false` answer licenses nothing and the walk recurses. -/

@[spec] theorem instListCutoff_spec (s₀ : AState) (h : EIdx) (d : Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ instListCutoff h d
    ⦃⇓? r s' => ⌜s' = s₀ ∧ (r = true →
        (bvarOfData (s₀.store.derived h)).toNat < satRange ∧
        (bvarOfData (s₀.store.derived h)).toNat ≤ d)⌝⦄ := by
  mvcgen [instListCutoff]
  spec_fails
  all_goals grind

/-! ## The per-declaration bracket (DESIGN §8.3, "Drop")

`flushCaches` drops the fourteen per-declaration tables whole — which is
con-leche's own `flushC` (task #97f's amendment) — `dropScratch` does that and
drops the store's scratch tier with it, and `enterScratch` opens the tier and
clears the per-call `Memos` (whose keys the new tier may reuse).

`Caches.dropScratchEntries` stays in `Arena/CoreState.lean` as the
SPECIFICATION of a surviving row; `flushed ⊑ dropScratchEntries` as caches,
which is why flushing is sound and why the bridge only ever needs
`CacheOK.of_empty`. -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the EMPTY cache set
satisfies every clause, at every mode and every environment.  This is the
whole content of the flush's soundness: a dropped row is a cache miss and
nothing else. -/
theorem CacheOK.of_empty {mode : CheckMode} {env : Env} {s : AState}
    (h : s.caches = Caches.empty) : CacheOK mode env s where
  whnfCore := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  whnf := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  infer := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  inferIO := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  annot := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  defeq := by intro k r hk; rw [h] at hk; simp [Caches.empty] at hk
  lvlEq := by intro k r hk; rw [h] at hk; simp [Caches.empty] at hk
  lvlsEq := by intro k r hk; rw [h] at hk; simp [Caches.empty] at hk
  constTy := by intro k i hk; rw [h] at hk; simp [Caches.empty] at hk
  constVal := by intro k i hk; rw [h] at hk; simp [Caches.empty] at hk
  ruleRhs := by intro k i hk; rw [h] at hk; simp [Caches.empty] at hk
  readL := by intro k u hk; rw [h] at hk; simp [Caches.empty] at hk
  readN := by intro k x hk; rw [h] at hk; simp [Caches.empty] at hk
  readLs := by intro k us hk; rw [h] at hk; simp [Caches.empty] at hk

@[spec] theorem flushCaches_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ flushCaches
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧ s'.caches = Caches.empty ∧
        ∀ mode env, CacheOK mode env s'⌝⦄ := by
  mvcgen [flushCaches]
  rename_i s hs
  subst hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first | rfl | trivial | exact fun _ _ => CacheOK.of_empty rfl

/-- con-leche: none — **the per-declaration bracket, closed**: the scratch
tier goes and the caches go with it.  A persistent handle keeps its bits, its
view and its denotation (DESIGN §8.3 lesson 6, the identity embedding); a
scratch handle denotes nothing afterwards, which is what makes a stale cache
row impossible rather than merely unlikely. -/
@[spec] theorem dropScratch_spec (s₀ : AState) (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ dropScratch
    ⦃⇓? _u s' => ⌜StoreWF s'.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧ s'.caches = Caches.empty ∧
        (∀ mode env, CacheOK mode env s') ∧
        (∀ i, i.isPersistent = true → s'.store.view i = s₀.store.view i) ∧
        (∀ i e, i.isPersistent = true → denoteE s₀.store i = some e →
          denoteE s'.store i = some e) ∧
        (∀ i, i.isPersistent = false → denoteE s'.store i = none)⌝⦄ := by
  mvcgen [dropScratch, flushCaches_spec]
  rename_i heq _u s hs _st _s1
  obtain ⟨e1, e2, e3, e4, _e5⟩ := hs
  rw [heq] at e1 e2 e3
  obtain ⟨h1, h2, h3, h4⟩ :=
    EStore.dropScratch_spec (st := s.store) (by rw [e1]; exact hwf)
  refine ⟨h1, e2, e3, e4, fun _ _ => CacheOK.of_empty e4, ?_, ?_, h4⟩
  · intro i hi
    show s.store.dropScratch.view i = s₀.store.view i
    rw [h2 i hi, e1]
  · intro i e hi hd
    show denoteE s.store.dropScratch i = some e
    exact h3 i e hi (by rw [e1]; exact hd)

/-- con-leche: none — **the per-declaration bracket, opened**: the scratch
tier comes back empty and the per-call memo tables go with it. -/
@[spec] theorem enterScratch_spec (s₀ : AState) (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ enterScratch
    ⦃⇓? _u s' => ⌜StoreWF s'.store ∧ s'.memos = Memos.empty ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i, i.isPersistent = true → s'.store.view i = s₀.store.view i) ∧
        (∀ i, i.isPersistent = false → denoteE s'.store i = none)⌝⦄ := by
  mvcgen [enterScratch]
  rename_i s hs _st _s1
  subst hs
  obtain ⟨h1, h2, h3⟩ := EStore.enableScratch_spec hwf
  exact ⟨h1, rfl, rfl, rfl, h2, h3⟩

/-! ## The pin table (task #97-P6-4a)

One spec per reader.  `pinAt`'s is the only one with content: the table is an
`Array` and its `i`-th slot denotes `pinNames`' `i`-th name, which is what
`PinsOK` says and `denoteNL_get` extracts. -/

/-- con-leche: none — the `i`-th slot of a denoting handle list denotes the
`i`-th name.  `PinsOK.names` is the list form; `pinAt` indexes. -/
theorem denoteNL_get {st : EStore} : ∀ (hs : List NIdx)
    (xs : List ConLeche.Name) (i : Nat) (n : NIdx) (x : ConLeche.Name),
    denoteNL st hs xs → hs[i]? = some n → xs[i]? = some x →
      denoteN st.ns n = some x := by
  intro hs
  induction hs with
  | nil => intro _ _ _ _ _ h1 _; simp at h1
  | cons a as ih =>
    intro xs i n x hd h1 h2
    cases xs with
    | nil => exact hd.elim
    | cons y ys =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1; subst h2; exact hd.1
      | succ k =>
        simp only [List.getElem?_cons_succ] at h1 h2
        exact ih ys k n x hd.2 h1 h2

@[spec] theorem pinAt_spec (s₀ : AState) (i : Nat) (hp : PinsOK s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ pinAt i
    ⦃⇓? n s' => ⌜s' = s₀ ∧ ∀ x, pinNames[i]? = some x →
        denoteN s₀.store.ns n = some x⌝⦄ := by
  mvcgen [pinAt]
  spec_fails
  rename_i s hs hlt
  subst hs
  refine ⟨rfl, fun x hx => ?_⟩
  refine denoteNL_get s.pins.names.toList pinNames i _ x hp.names ?_ hx
  have hlt' : i < s.pins.names.toList.length := by simpa using hlt
  rw [List.getElem?_eq_getElem hlt']
  simp

@[spec] theorem pinReserved_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ pinReserved
    ⦃⇓? ns s' => ⌜s' = s₀ ∧ denoteNL s₀.store ns reservedBasisNameValues⌝⦄ := by
  mvcgen [pinReserved]
  spec_fails
  rename_i s hs _hr
  subst hs
  exact ⟨rfl, hp.reserved⟩

@[spec] theorem pinEmptyLevels_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ pinEmptyLevels
    ⦃⇓? us s' => ⌜s' = s₀ ∧ denoteLs s₀.store.lss us = some []⌝⦄ := by
  mvcgen [pinEmptyLevels]
  spec_fails
  rename_i s hs _hr
  subst hs
  exact ⟨rfl, hp.emptyLevels⟩

@[spec] theorem pinZeroLevel_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ pinZeroLevel
    ⦃⇓? u s' => ⌜s' = s₀ ∧ denoteL s₀.store.ls u = some .zero⌝⦄ := by
  mvcgen [pinZeroLevel]
  spec_fails
  rename_i s hs _hr
  subst hs
  exact ⟨rfl, hp.zeroLevel⟩

@[spec] theorem pinSortOne_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ pinSortOne
    ⦃⇓? e s' => ⌜s' = s₀ ∧
        denoteE s₀.store e = some (.sort (.succ .zero))⌝⦄ := by
  mvcgen [pinSortOne]
  spec_fails
  rename_i s hs _hr
  subst hs
  exact ⟨rfl, hp.sortOne⟩

/-! ## The closer

Task #97s round 2's recipe, item by item.  ONE curated `grind` list; a
`bridge_peel` in front of it, which is what lets `grind` see one state where
the verification condition shows seven; and a second stage that puts the
`RelE` transports back and raises the instance budget, for the verification
conditions that genuinely have to move an answer along the extension chain.

**The arm files erase the transports.**  `RelE.ext`, `.of_ext` and
`.retarget` close the answer relation under `Ext` in both directions, so every
intermediate store multiplies every answer already known — measured on the
spike's one file, 70 s against 11.5 s.  The `_step` lemmas of
`Bridge/Rel.lean` group 7 already carry the chain, so the transports are
redundant *and* explosive; `attribute [-grind] RelE.ext RelE.of_ext
RelE.retarget` at the top of each arm file is the single highest-value line in
it, and because `attribute [-grind]` does not travel through an import each
file repeats it. -/

/-- con-leche: none — **the uniform closer** for Theorem 1's verification
conditions.  ONE curated list, plus the walk's own pure function where a
walk's arms need it: `bridge_vcs [Expr.instantiate1]` is how `ExprOps/Inst1`
calls it.  The second stage puts the `RelE` transports back and raises the
instance budget, for the handful of verification conditions that genuinely
have to move an answer along the extension chain. -/
syntax "bridge_vcs" (" [" (Lean.Parser.Tactic.grindParam),* "]")? : tactic

macro_rules
  -- NOT `bridge_vcs []`: an empty splice expands to a leading comma and
  -- `grind` reports "unexpected grind parameter" (group C's finding).
  | `(tactic| bridge_vcs) => `(tactic| bridge_vcs [Ext.refl])
  | `(tactic| bridge_vcs [$ts,*]) => `(tactic| first
      | (intro hf; exact False.elim hf)
      | (bridge_peel
         subst_vars
         grind (instances := 1000) [$ts,*, StateOK, MemoOK.mono, MemoOK.insert, MemoOK.of_empty,
           MemoVOK.of_empty, MemoLOK.of_empty, MemoLsOK.of_empty,
           MemoVOK.mono, MemoVOK.insert, MemoLOK.mono, MemoLsOK.mono,
           Ext.trans, Ext.refl, BMExt.trans, BMExt.refl,
           viewOK_bvar, viewOK_lit, viewOK_fvar,
           viewOK_sort, viewOK_const, viewOK_app, viewOK_lam, viewOK_forallE,
           viewOK_letE, viewOK_proj, viewOK_eBindView, denoteEView,
           opt2_eq_some_iff, opt3_eq_some_iff, Option.isSome_iff_exists,
           Option.map_eq_some_iff])
      | (bridge_peel
         subst_vars
         grind (instances := 4000) [$ts,*, StateOK, MemoOK.mono, MemoOK.insert, MemoOK.of_empty,
           MemoVOK.of_empty, MemoLOK.of_empty, MemoLsOK.of_empty,
           MemoVOK.mono, MemoVOK.insert, MemoLOK.mono, MemoLsOK.mono,
           Ext.trans, Ext.refl, BMExt.trans, BMExt.refl,
           RelE.ext, RelE.of_ext, RelV.of_ext,
           viewOK_bvar, viewOK_lit, viewOK_fvar, viewOK_sort, viewOK_const,
           viewOK_app, viewOK_lam, viewOK_forallE, viewOK_letE, viewOK_proj,
           viewOK_eBindView, denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
           Option.isSome_iff_exists, Option.map_eq_some_iff]))

end ConRon.Bridge
