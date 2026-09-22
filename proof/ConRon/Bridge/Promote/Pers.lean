/-
# `ConRon.Bridge.Promote.Pers` — the PERSISTENT extension, and what survives a drop

DESIGN.md §8.2 states Theorem 1's second conjunct as `Ext st st'`.  **At the
per-declaration STEP that conjunct is false as written**, and this module is
the correction (task #97-P3-Checker, finding 1).

`Ext st st'` (`Arena/Denote.lean:274`) is TOTAL: *every* handle of `st`
denotes the same in `st'`.  `Arena/Checker.lean`'s `checkDeclStep` ends in
`dropScratch`, which takes the scratch tier away, and `Arena/WFProofs.lean`'s
own `dropScratch_spec` says exactly what then happens to a scratch handle:
`denoteE st.dropScratch i = none`.  So a bracketed step CANNOT deliver `Ext`,
and the conjunct it does deliver — the one the fold actually needs, and the
one that is the tier discipline in a line — is

    PExt st st' :  every PERSISTENT handle that denotes in `st`
                   denotes the same in `st'`

`Ext` implies it, `PExt` composes, and `dropScratch` preserves it.  Everything
the fold carries across a step boundary — the environment, the pending
records, the pin table — is persistent by construction (that is what
`Arena/Promote.lean` exists for), so `PExt` transports all of it.

The second half of the module is the vocabulary for "by construction":
`PersE` and its siblings at the four handle kinds, lifted to the declaration
layer (`PersCV`, `PersCI`, `PersDecl`, `PersVG`, `PersIFEnv`, `PersPins`).  A
`Pers…` predicate is decided by the handles' tier bits alone — it says nothing
about any store — which is what lets `Arena/Promote.lean`'s theorems establish
it and the fold consume it without either mentioning the other's store.
-/
import ConRon.Bridge.StateOK

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The persistent extension -/

/-- con-leche: none — `NExt` restricted to persistent handles. -/
def PNExt (st st' : NStore) : Prop :=
  ∀ i n, i.isPersistent = true → denoteN st i = some n → denoteN st' i = some n

/-- con-leche: none — `LExt` restricted to persistent handles. -/
structure PLExt (st st' : LStore) : Prop where
  ns : PNExt st.ns st'.ns
  lvl : ∀ i u, i.isPersistent = true → denoteL st i = some u → denoteL st' i = some u

/-- con-leche: none — `LsExt` restricted to persistent handles. -/
structure PLsExt (st st' : LsStore) : Prop where
  ls : PLExt st.ls st'.ls
  lst : ∀ i us, i.isPersistent = true → denoteLs st i = some us →
    denoteLs st' i = some us

/-- con-leche: none — **the tier discipline in one relation** (DESIGN §8.2,
corrected): every PERSISTENT handle of `st` denotes the same in `st'`.  This
is what a bracketed fold step delivers where §8.2 writes `Ext`; `Ext` is an
unbracketed call's conjunct and implies this one. -/
structure PExt (st st' : EStore) : Prop where
  lss : PLsExt st.lss st'.lss
  expr : ∀ i e, i.isPersistent = true → denoteE st i = some e →
    denoteE st' i = some e

theorem PNExt.refl (st : NStore) : PNExt st st := fun _ _ _ h => h
theorem PLExt.refl (st : LStore) : PLExt st st := ⟨PNExt.refl _, fun _ _ _ h => h⟩
theorem PLsExt.refl (st : LsStore) : PLsExt st st :=
  ⟨PLExt.refl _, fun _ _ _ h => h⟩
theorem PExt.refl (st : EStore) : PExt st st := ⟨PLsExt.refl _, fun _ _ _ h => h⟩

theorem PNExt.trans {a b c : NStore} (h₁ : PNExt a b) (h₂ : PNExt b c) :
    PNExt a c := fun i n hp h => h₂ i n hp (h₁ i n hp h)

theorem PLExt.trans {a b c : LStore} (h₁ : PLExt a b) (h₂ : PLExt b c) :
    PLExt a c :=
  ⟨h₁.ns.trans h₂.ns, fun i u hp h => h₂.lvl i u hp (h₁.lvl i u hp h)⟩

theorem PLsExt.trans {a b c : LsStore} (h₁ : PLsExt a b) (h₂ : PLsExt b c) :
    PLsExt a c :=
  ⟨h₁.ls.trans h₂.ls, fun i us hp h => h₂.lst i us hp (h₁.lst i us hp h)⟩

theorem PExt.trans {a b c : EStore} (h₁ : PExt a b) (h₂ : PExt b c) : PExt a c :=
  ⟨h₁.lss.trans h₂.lss, fun i e hp h => h₂.expr i e hp (h₁.expr i e hp h)⟩

/-! ### `Ext` implies it

The unbracketed direction: an `intern`, a walk, a whole `checkDecl` — none of
them drops a tier, so each delivers the total `Ext`, and every consumer below
takes the restricted one. -/

theorem PNExt.of_ext {a b : NStore} (h : NExt a b) : PNExt a b :=
  fun i n _ hd => h i n hd

theorem PLExt.of_ext {a b : LStore} (h : LExt a b) : PLExt a b :=
  ⟨PNExt.of_ext h.ns, fun i u _ hd => h.lvl i u hd⟩

theorem PLsExt.of_ext {a b : LsStore} (h : LsExt a b) : PLsExt a b :=
  ⟨PLExt.of_ext h.ls, fun i us _ hd => h.lst i us hd⟩

/-- con-leche: none — the total extension implies the restricted one. -/
theorem PExt.of_ext {a b : EStore} (h : Ext a b) : PExt a b :=
  ⟨PLsExt.of_ext h.lss, fun i e _ hd => h.expr i e hd⟩

/-! ### The bracket preserves it

`Arena/WFProofs.lean`'s four `dropScratch_spec`s, assembled. -/

theorem PExt.dropScratch {st : EStore} (h : StoreWF st) :
    PExt st st.dropScratch := by
  have hw : StoreWF st := h
  obtain ⟨rk, hwa⟩ := h
  have hlss : LsStoreWF st.lss := hwa.lss
  have hls : LStoreWF st.lss.ls := hlss.ls
  have hns : NStoreWF st.lss.ls.ns := by
    obtain ⟨rkl, hl⟩ := hls; exact hl.ns
  exact ⟨⟨⟨fun i n hp hd => (NStore.dropScratch_spec hns).2.2 i n hp hd,
      fun i u hp hd => (LStore.dropScratch_spec hls).2.2 i u hp hd⟩,
    fun i us hp hd => (LsStore.dropScratch_spec hlss).2.2 i us hp hd⟩,
    fun i e hp hd => EStore.dropScratch_denote_pers hw hp hd⟩

/-! ## Persistence of a handle, and of everything built out of handles

A `Pers…` predicate looks only at the tier bits, so it is a fact about the
VALUE and not about any store — which is what makes it survive a
`dropScratch` for free and what lets `Arena/Promote.lean` establish it. -/

/-- con-leche: none — a name handle lives in the persistent tier. -/
abbrev PersN (n : NIdx) : Prop := n.isPersistent = true
/-- con-leche: none — a level handle lives in the persistent tier. -/
abbrev PersL (l : LIdx) : Prop := l.isPersistent = true
/-- con-leche: none — a universe-argument list handle is persistent. -/
abbrev PersLs (l : LsIdx) : Prop := l.isPersistent = true
/-- con-leche: none — an expression handle lives in the persistent tier. -/
abbrev PersE (e : EIdx) : Prop := e.isPersistent = true

/-- con-leche: none — every handle of a name list is persistent. -/
def PersNList (ns : List NIdx) : Prop := ∀ n ∈ ns, PersN n
/-- con-leche: none — every handle of an expression list is persistent. -/
def PersEList (es : List EIdx) : Prop := ∀ e ∈ es, PersE e
/-- con-leche: none — every handle of a level list is persistent. -/
def PersLList (us : List LIdx) : Prop := ∀ u ∈ us, PersL u

/-- con-leche: none — a stored constant's header is persistent, field by
field (`Arena/Env.lean`'s `IConstantVal`). -/
structure PersCV (cv : IConstantVal) : Prop where
  name : PersN cv.name
  levelParams : PersNList cv.levelParams
  type : PersE cv.type

/-- con-leche: none — a recursor rule's firing mode is persistent. -/
def PersFire : IRecRuleFire → Prop
  | .inert => True
  | .plain => True
  | .nested lvls pins => PersLList lvls ∧ PersEList pins

/-- con-leche: none — a recursor rule is persistent. -/
structure PersRule (rl : IRecRule) : Prop where
  ctor : PersN rl.ctor
  fire : PersFire rl.fire
  rhs : PersE rl.rhs

/-- con-leche: none — every rule of the list is persistent. -/
def PersRules (rs : List IRecRule) : Prop := ∀ r ∈ rs, PersRule r

/-- con-leche: none — an inductive's capabilities record is persistent (its
one handle field is the eta constructor's name). -/
def PersCaps (c : IIndCaps) : Prop := PersN c.etaCtor

/-- con-leche: none — a projection table is persistent, field by field. -/
structure PersProjTable (t : IProjTable) : Prop where
  structName : PersN t.structName
  tableName : PersN t.tableName
  levelParams : PersNList t.levelParams
  ctor : PersN t.ctor
  structSort : PersL t.structSort
  bodies : PersEList t.bodies.toList
  guards : PersLList t.guards

/-- con-leche: none — **a stored constant is persistent**: the clause
`dropScratch` needs of the environment, and what `Arena/Promote.lean`'s
`promoteCI` delivers. -/
def PersCI : IConstantInfo → Prop
  | .axiomInfo v => PersCV v
  | .defnInfo v e _ => PersCV v ∧ PersE e
  | .thmInfo v e => PersCV v ∧ PersE e
  | .indInfo v c => PersCV v ∧ PersCaps c
  | .ctorInfo v _ _ => PersCV v
  | .recInfo v _ _ rs => PersCV v ∧ PersRules rs
  | .projInfo t => PersProjTable t

/-- con-leche: none — every member of a block is persistent. -/
def PersCIList (cs : List IConstantInfo) : Prop := ∀ c ∈ cs, PersCI c

/-- con-leche: none — every constant of the environment is persistent. -/
def PersIEnv (e : IEnv) : Prop := PersCIList e.consts

/-- con-leche: none — **the environment index is persistent**: both its list
and its rows.  The rows matter as much as the list — `Arena/Promote.lean`'s
`eraseInstalled`/`indexPromoted` exist because a stale row under a SCRATCH key
would answer a different constant once `dropScratch` hands that word back. -/
structure PersIFEnv (fe : IFEnv) : Prop where
  env : PersIEnv fe.env
  idx : ∀ n p, fe.idx[n]? = some p → PersN n ∧ PersCI p.2

/-- con-leche: none — a declaration record is persistent (the parse builds
them in the persistent tier, so this is the frontend tier's postcondition). -/
def PersDecl : IDeclaration → Prop
  | .axiomDecl v => PersCV v
  | .defnDecl v e _ => PersCV v ∧ PersE e
  | .thmDecl v e => PersCV v ∧ PersE e
  | .opaqueDecl v e => PersCV v ∧ PersE e
  | .basisDecl _ => True
  | .indDecl block _ => PersCIList block
  | .quotDecl _ v => PersCV v

/-- con-leche: none — the datum that crosses the install/check seam is
persistent: `Arena/Promote.lean`'s `promoteVG` is what makes it so, and it is
what lets phase B run after phase A's `dropScratch`. -/
structure PersVG (g : Arena.ValueGroup) : Prop where
  cvA : PersCV g.cvA
  jv : PersE g.jv

/-- con-leche: none — a `Nat`-operation pin variant is persistent
(`internAllPins` runs before the parse, with the scratch tier closed). -/
structure PersPinSet (p : INatOpPinSet) : Prop where
  pins : PersEList [p.divPin, p.modPin, p.gcdPin, p.landPin, p.lorPin,
    p.xorPin, p.shiftLeftPin, p.shiftRightPin]
  proofs : PersEList (p.divProofs ++ p.modProofs ++ p.gcdProofs ++
    p.landProofs ++ p.lorProofs ++ p.xorProofs ++ p.shiftLeftProofs ++
    p.shiftRightProofs)

/-- con-leche: none — every pin variant is persistent. -/
def PersPinSets (ps : List INatOpPinSet) : Prop := ∀ p ∈ ps, PersPinSet p

/-- con-leche: none — **the pin TABLE is persistent** — task #97-P3-0 §7's
"one more clause: the pin handles are persistent", which is what makes
`PinsOK` survive `dropScratch`.  It is free: the driver runs
`internReservedPins` before the prelude with the scratch tier closed. -/
structure PersPins (s : AState) : Prop where
  names : ∀ n ∈ s.pins.names, PersN n
  reserved : PersNList s.pins.reserved
  emptyLevels : PersLs s.pins.emptyLevels
  zeroLevel : PersL s.pins.zeroLevel
  sortOne : PersE s.pins.sortOne

end ConRon.Bridge
