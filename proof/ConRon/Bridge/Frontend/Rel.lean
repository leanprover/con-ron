/-
# `ConRon.Bridge.Frontend.Rel` — the parse-state relation

DESIGN §8.2's parser tier is one equation,

    denoteDecls (Arena.parse chunks) = parseChunks chunks   (exactness)

and the whole of this tier is the induction that proves it.  An induction over
a stream needs an invariant, and the invariant is this module: **the twin's
parse state denotes con-leche's, field for field**.

`Arena/Frontend/ExportC.lean`'s `StateD` is a field-for-field mirror of
`ConLeche/Frontend/ExportC.lean`'s — **four fields** (task #105 dropped the
in-process modeller's and the projection rewrite's fourteen census fields:
`projOwners`, `projLevels`, `projRewrites`, `constTypes`, `heights`,
`inModel`, `inModelled`, `genRecords`, `genOwner`, `inModelGen`, `indCount`,
`indBlocks`, `inModelCensus`, `inModelDeclined` are all gone), in the same
order, with `NIdx`/`LIdx`/`EIdx` where con-leche has `Name`/`Level`/`Expr` —
plus the projection-table naming invariant (`projNamed`, unrelated to the
deleted rewrite: it is about `IProjTable.tableName`, the kernel's own struct
projection bookkeeping, DESIGN §8.3) — so the relation is a field-for-field
conjunction, and the four shapes it needs are:

* **`OptRel`** — a relation lifted to `Option`, `none` matching `none`.  The
  three stream-index tables are `IdTable`s of handles against `IdTable`s of
  values and `IdTable.get?` is the only thing any proof reads of one
  (con-leche's own `Scan/Types.lean:374-381` note: "these are the only facts
  the semantic layer uses about the table"), so `IdTableRel` is `OptRel` at
  every index and its three laws come from con-leche's three
  (`Scan/Types.lean:383/386/390`);
* **`MapRel`** — a `Std.HashMap NIdx _` against a `Std.HashMap Name _`, keyed
  through `denoteN`.  Stated in BOTH directions (`hit` and `cover`,
  `Bridge/StateOK.lean`'s `IFEnvOK` shape and for the same reason: the naive
  "a miss is a miss" is not preserved by an arena extension, but "every entry
  of the value side is named by a handle the twin's side knows" is);
* **`ListRel`** — Mathlib's `List.Forall₂` under another name; the library
  imports no Mathlib (task #97-P3-0) and core has no such relation, so the
  tier carries its own four-line inductive;
* the declaration ARRAY, which is `Bridge/Checker/Inv.lean`'s `denoteDecls` on
  `Array.toList`.

**Why the relation carries the STORE and the state does not.**  `denoteE` is
a function of the store, and the store is the `AM` state's; so the relation is
`StateDRel st sd sc` with `st : EStore` a parameter, and a step's theorem
reads `StateDRel s.store sd sc → … → StateDRel s'.store sd' sc'`.  Every
clause transports across `Ext` (`Bridge/Rel.lean`'s ten `…_ext` lemmas) and
across `PExt` at persistent handles (`Bridge/Checker/Inv.lean`'s nineteen
`…_pext` twins) — and the parse never opens the scratch tier, so in this tier
the transport is always the `Ext` one.

**`PersStateD`** is the second half of what the fold theorems' `hpd`
asks the frontend for: *every handle the parse state holds is persistent*.
The parse runs with `scratchOn = false` (`Arena/Main.lean` interns the
reserved pins first, then parses; `enterScratch` is the fold's and the fold
has not started), so it is free — but it has to be STATED, because without it
the first declaration's `dropScratch` makes the rest of the stream
undecodable.

**The monad seam, once and for all.**  con-leche's frontend runs in
`abbrev M := Except String` (`Frontend/Export.lean:117`) and (B)'s runs in
`AM` (DESIGN §8.4), which `Arena/Frontend/Types.lean`'s module note records as
the one place the transliteration is knowingly too crude.  So every theorem of
this tier is *one-directional*: **the twin accepting implies con-leche
accepting**, with the denotation of the answer.  A twin `fail` claims nothing,
exactly as `Bridge/Checker`'s arms claim nothing about a `native` decline.

**The import is `Bridge/Checker/Inv.lean`, not `Bridge/Checker.lean`** (task
#97-P3-Layout).  This module uses exactly three names of the checker tier —
`FoldOK`, `denoteDecls` and `denoteDecl_pext` — and all three are in
`Inv.lean`, the BOTTOM of that tier.  The blanket import that used to stand
here pulled all fourteen checker modules in for those three, which put
`Bridge/Frontend/Shared.lean`'s intern exactness ABOVE every module that needs
to read it; `Bridge/Checker/Pins.lean` now imports `Shared.lean` instead, and
only `Bridge/Frontend/Capstone.lean` imports the checker tier whole.
-/
import ConRon.Bridge.Checker.Inv
import ConLeche.Frontend.ExportC

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

universe u v

/-! ## Inverting an `AM` run

Every theorem of this tier reads a hypothesis of the shape `f … s = .ok (x,
s')` and has to take it apart one `do`-step at a time.  The bind's inversion
is the Checker tier's (`Bridge/Checker/Fold.lean`'s `AM.bind_ok`); what the
frontend adds is the two leaves, because its functions end in a `pure` or a
`fail` in almost every arm. -/

/-- con-leche: none — `get` moves nothing and answers the state. -/
theorem AM.get_ok {s s' t : AState} (h : (get : AM AState) s = .ok (t, s')) :
    t = s ∧ s' = s := by
  have he : ((s, s) : AState × AState) = (t, s') := Except.ok.inj h
  exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- con-leche: none — a `pure` moves nothing and answers itself. -/
theorem AM.pure_ok {α : Type} {a b : α} {s s' : AState}
    (h : (pure a : AM α) s = .ok (b, s')) : b = a ∧ s' = s := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq]
    at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- con-leche: none — a `fail` never returns, so a theorem premised on a
successful run never reaches one. -/
theorem AM.fail_ok {α : Type} {e : Arena.CheckError} {s s' : AState} {a : α}
    (h : (fail e : AM α) s = .ok (a, s')) : False := by
  simp only [fail, throwThe, MonadExceptOf.throw] at h
  exact nomatch h

/-- con-leche: none — the name store's own well-formedness, off `StateOK`
(`Arena/WFProofs.lean`'s `EWFAt.nsWF`, unpacked once). -/
theorem nsWF_of_StateOK {s : AState} (hok : StateOK s) : NStoreWF s.store.ns := by
  obtain ⟨rk, hrk⟩ := hok.wf
  exact hrk.nsWF

/-! ## Persistence, from a view and the closed scratch tier

The `PersStateD` half of every theorem of this tier is this observation and
nothing else: **a scratch handle reads as ABSENT while the scratch tier is
off** (`Arena/Store.lean:475`'s `view` — `if i.isPersistent then … else if
st.scratchOn then … else none`), so a handle that HAS a view on a closed store
is persistent.  The parse runs with the scratch tier closed, so every handle
it interns — every handle `Bridge/Specs.lean`'s intern specs hand back with a
`view` conjunct — is persistent for free.

Task #97-P3-Frontend-2's round 2 replaces finding 9.1 with this: what
`StateD_init_run` was missing was not an intern lemma at all, it was the
observation above plus the `sync` chain that carries `scratchOn = false` down
the nesting.  (The three store-layer twins of
`EStore.intern_isPersistent_of_off` went in anyway — `Arena/WFProofs.lean`'s
last section — because they are the fact stated where it belongs, and a caller
that has the capacity bound but not the view wants them.) -/

/-- con-leche: none — the scratch flag is the same at every level of the
nesting: `EWFAt.sync`, `LsWF.sync` and `LWFAt.sync` composed. -/
theorem scratchOn_nested {st : EStore} (hwf : StoreWF st) :
    st.lss.scratchOn = st.scratchOn ∧ st.ls.scratchOn = st.scratchOn ∧
      st.ns.scratchOn = st.scratchOn := by
  obtain ⟨rk, h⟩ := hwf
  have h1 : st.scratchOn = st.lss.scratchOn := h.sync
  have hlsw := h.lss
  have h2 : st.lss.scratchOn = st.lss.ls.scratchOn := hlsw.sync
  obtain ⟨rkl, hl⟩ := hlsw.ls
  have h3 : st.lss.ls.scratchOn = st.lss.ls.ns.scratchOn := hl.sync
  exact ⟨h1.symm, (h1.trans h2).symm, (h1.trans (h2.trans h3)).symm⟩

/-- con-leche: none — **a name handle with a view on a closed store is
persistent.** -/
theorem PersN_of_view {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {h : NIdx} {v : NNodeView}
    (hv : st.ns.view h = some v) : PersN h := by
  by_cases hp : h.isPersistent = true
  · exact hp
  · exfalso
    rw [Arena.NStore.view, if_neg hp,
      if_neg (by rw [(scratchOn_nested hwf).2.2, hoff]; simp)] at hv
    exact absurd hv (by simp)

/-- con-leche: none — the same at a LEVEL handle. -/
theorem PersL_of_view {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {h : LIdx} {v : LNodeView}
    (hv : st.ls.view h = some v) : PersL h := by
  by_cases hp : h.isPersistent = true
  · exact hp
  · exfalso
    rw [Arena.LStore.view, if_neg hp,
      if_neg (by rw [(scratchOn_nested hwf).2.1, hoff]; simp)] at hv
    exact absurd hv (by simp)

/-- con-leche: none — the same at an EXPRESSION handle. -/
theorem PersE_of_view {st : EStore} (_hwf : StoreWF st)
    (hoff : st.scratchOn = false) {h : EIdx} {v : ENodeView}
    (hv : st.view h = some v) : PersE h := by
  by_cases hp : h.isPersistent = true
  · exact hp
  · exfalso
    rw [Arena.EStore.view] at hv
    by_cases hb : ETag.isBind h.tag
    · rw [if_pos hb] at hv
      have hbi : st.viewBindI h = none := by
        rw [Arena.EStore.viewBindI, if_neg hp, if_neg (by rw [hoff]; simp)]
      rw [Arena.EStore.viewBind, hbi] at hv
      exact absurd hv (by simp)
    · rw [if_neg hb, if_neg hp, if_neg (by rw [hoff]; simp)] at hv
      exact absurd hv (by simp)

/-! ## The frame

One record for the five conjuncts every step of the parse carries, so that a
composition reads `h₁.trans h₂` rather than five `And.intro`s.  It is
`Bridge/StateOK.lean`'s `CheckOK.monoF` hypothesis, plus the scratch flag the
frontend tier needs and the Core tier does not.

The frame conjuncts are what every caller needs and what nothing in the
frontend breaks: **the parse interns, compares levels and reads handles
back.**  It never enters the scratch tier (`Arena/Main.lean` runs
`internReservedPins` first and the fold's bracket has not started) and never
touches the pin table — which is what makes `PersStateD` free and what makes
the fold theorems' `FoldOK` (their `hok`) reachable at the post-parse state.

**No memo clause** (task #97-P3-Frontend round 8).  Until then the record
said `s'.memos = s.memos`, and that is false of the projection rewrite: every
`…Fast` walk it runs (`liftLooseBVarsFast`, `instantiate1LiftFast`,
`resetMetaFast`, `instLPFast`) CLEARS its per-call table on exit, so the
equation fails from any start with a non-empty table.  Nothing read it — the
capstones consume `ok`, `ext`, `scratch`, `cframe` and `pins` — so it is gone
rather than repaired.

**The cache conjunct is a FRAME and not an equation** (task #97-P3-Frame).
Round one said `s'.caches = s.caches`, and that is false of the parse:
`registerProjOwners` (`Arena/Frontend/ExportC.lean:401`) calls `projRecOwners`
(`Arena/Frontend/ProjRec.lean:510-515`), which calls `structPartsCore?` and
`nativeParts?`, each of which computes its `isProp` field with
`Arena/Core.lean`'s `lvlEq?` — a cached verdict walk that probes `lvlEqC` and
on a miss writes `readLC` (twice, through `readLevelM`) and `lvlEqC`.  The
Rust does the same at the same three call sites, so the port is not at fault
and the statement was.  `Bridge/StateOK.lean`'s `CacheFrame` is the honest
clause: the record equation that names those two tables — and, since round 8,
the two other readback tables `readNC`/`readLsC`, which `projRecValue`'s
`instLPFast` writes — plus their invariants as implications.  A caller holding `CheckOK` — which is where the invariants
live — gets them back through `CheckOK.monoF`; a caller at `StateOK` does not
need them. -/

/-- con-leche: none — **the parse's frame**: the store only grew, the scratch
tier stayed as it was, the pin table stood still, and the per-declaration
caches stood still up to the four tables a level comparison or a readback
writes. -/
structure ParseStep (s s' : AState) : Prop where
  ok : StateOK s'
  ext : Ext s.store s'.store
  scratch : s'.store.scratchOn = s.store.scratchOn
  cframe : CacheFrame s s'
  pins : s'.pins = s.pins

theorem ParseStep.refl {s : AState} (hok : StateOK s) : ParseStep s s :=
  ⟨hok, Ext.refl _, rfl, CacheFrame.refl _, rfl⟩

theorem ParseStep.trans {a b c : AState} (h₁ : ParseStep a b) (h₂ : ParseStep b c) :
    ParseStep a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, by rw [h₂.scratch, h₁.scratch],
    h₁.cframe.trans h₂.cframe, by rw [h₂.pins, h₁.pins]⟩

/-- con-leche: none — the frame of a parse step that writes no
per-declaration table at all, which is every step but the owner census.  The
shape a proof reaches when it has the plain cache equation in hand. -/
theorem ParseStep.of_caches {s s' : AState} (hok : StateOK s')
    (hx : Ext s.store s'.store) (hsc : s'.store.scratchOn = s.store.scratchOn)
    (hc : s'.caches = s.caches)
    (hp : s'.pins = s.pins) : ParseStep s s' :=
  ⟨hok, hx, hsc, CacheFrame.of_eq hc hx, hp⟩

/-! ## The three readback invariants, threaded through the parse

Task #97-P3-Frontend round 8.  The projection rewrite's `instLPFast` answers
exactly only where `readNC`, `readLC` and `readLsC` are sound (`Bridge/ExprOps/
Owed.lean`'s `instLPFast_spec`), so the parse carries the three invariants from
the capstones' empty caches.  They survive every parse step through
`ParseStep.cframe`'s implications — which is why those are implications and
not equations. -/

/-! ## The two generic shapes -/

/-- con-leche: none — a relation lifted to `Option`: `none` relates to `none`
and nothing else.  The three stream-index tables are partial maps and this is
what "the same map, up to the denotation" means at one index. -/
def OptRel {α : Type u} {β : Type v} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem OptRel.refl_none {α : Type u} {β : Type v} {R : α → β → Prop} :
    OptRel R (none : Option α) (none : Option β) := trivial

theorem OptRel.isSome {α : Type u} {β : Type v} {R : α → β → Prop}
    {a : Option α} {b : Option β} (h : OptRel R a b) : a.isSome = b.isSome := by
  cases a <;> cases b <;> simp_all [OptRel]

theorem OptRel.some_left {α : Type u} {β : Type v} {R : α → β → Prop}
    {a : Option α} {b : Option β} {x : α} (h : OptRel R a b) (ha : a = some x) :
    ∃ y, b = some y ∧ R x y := by
  cases b with
  | none => rw [ha] at h; exact absurd h (by simp [OptRel])
  | some y => rw [ha] at h; exact ⟨y, rfl, h⟩

theorem OptRel.none_left {α : Type u} {β : Type v} {R : α → β → Prop}
    {a : Option α} {b : Option β} (h : OptRel R a b) (ha : a = none) : b = none := by
  cases b with
  | none => rfl
  | some _ => rw [ha] at h; exact absurd h (by simp [OptRel])

/-- con-leche: none — two lists, element for element.  Mathlib's
`List.Forall₂` under another name: the `ConRonBridge` library imports no
Mathlib (task #97-P3-0), and core has no such relation, so the tier carries
its own four-line inductive. -/
inductive ListRel {α : Type u} {β : Type v} (R : α → β → Prop) :
    List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

theorem ListRel.length_eq {α : Type u} {β : Type v} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → as.length = bs.length := by
  intro as bs h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- con-leche: ConLeche/Frontend/Scan/Types.lean:342-345 IdTable — **two
stream-index tables are the same map, up to the denotation**: at every index
either both are unbound or both are bound and the handle denotes the value.
con-leche's three `get?` laws are the only facts any proof reads of a table,
so they are the only facts this needs. -/
def IdTableRel {α : Type} {β : Type} (R : α → β → Prop)
    (t : ConLeche.Frontend.IdTable α) (u : ConLeche.Frontend.IdTable β) : Prop :=
  ∀ i, OptRel R (t.get? i) (u.get? i)

/-- con-leche: ConLeche/Frontend/Scan/Types.lean:369-372 IdTable.bound — **the
rebinding test agrees**, which is what lets `parseNameEntryD`'s `freshName`
guard fail on the same indices on both sides.  Task #97-P3-0 §4's rule 4 in
miniature: the guard reads `bound`, so `bound` is what the relation must
give. -/
theorem IdTableRel.bound {α β : Type} {R : α → β → Prop}
    {t : ConLeche.Frontend.IdTable α} {u : ConLeche.Frontend.IdTable β}
    (h : IdTableRel R t u) (i : Nat) :
    t.bound i = u.bound i := by
  rw [ConLeche.Frontend.IdTable.bound_eq, ConLeche.Frontend.IdTable.bound_eq]
  exact (h i).isSome

/-- con-leche: ConLeche/Frontend/Scan/Types.lean:386 IdTable.get?_singleton —
the two initial tables relate: `StateD.init` interns `Name.anonymous` and
`Level.zero` where con-leche writes them. -/
theorem IdTableRel.singleton {α β : Type} {R : α → β → Prop} {x : α} {y : β}
    (h : R x y) :
    IdTableRel R (ConLeche.Frontend.IdTable.singleton x)
      (ConLeche.Frontend.IdTable.singleton y) := by
  intro i
  rw [ConLeche.Frontend.IdTable.get?_singleton,
    ConLeche.Frontend.IdTable.get?_singleton]
  split <;> simp_all [OptRel]

/-- con-leche: ConLeche/Frontend/Scan/Types.lean:390 IdTable.get?_insert — one
bound index, on both sides. -/
theorem IdTableRel.insert {α β : Type} {R : α → β → Prop}
    {t : ConLeche.Frontend.IdTable α} {u : ConLeche.Frontend.IdTable β}
    (h : IdTableRel R t u) {i : Nat} {x : α} {y : β} (hx : R x y) :
    IdTableRel R (t.insert i x) (u.insert i y) := by
  intro j
  rw [ConLeche.Frontend.IdTable.get?_insert,
    ConLeche.Frontend.IdTable.get?_insert]
  split
  · exact hx
  · exact h j

/-! ## The declaration array -/

/-- con-leche: none — `Bridge/Checker/Inv.lean`'s `denoteDecls` at an `Array`,
which is the shape `StateD.decls` and `ParseResultD.decls` are in. -/
def denoteDeclArray (st : EStore) (ds : Array IDeclaration) :
    Option (Array ConLeche.Declaration) :=
  (denoteDecls st ds.toList).map List.toArray

/-- con-leche: none — the EMPTY declaration array denotes the empty one: the
`decls` clause of `StateD.init`, and the base case of every list induction of
the tier. -/
theorem denoteDeclArray_empty (st : EStore) :
    denoteDeclArray st (#[] : Array IDeclaration) = some #[] := rfl

/-- con-leche: ConLeche/Frontend/Scan/Types.lean:342-345 IdTable — the two
EMPTY tables relate: three of `StateD.init`'s eighteen fields are this. -/
theorem IdTableRel.empty {α β : Type} (R : α → β → Prop) :
    IdTableRel R ({} : ConLeche.Frontend.IdTable α)
      ({} : ConLeche.Frontend.IdTable β) := by
  intro i
  have h1 : ({} : ConLeche.Frontend.IdTable α).get? i = none := by
    simp [ConLeche.Frontend.IdTable.get?]
  have h2 : ({} : ConLeche.Frontend.IdTable β).get? i = none := by
    simp [ConLeche.Frontend.IdTable.get?]
  simp only [h1, h2]
  exact OptRel.refl_none

/-- con-leche: none — `denoteDeclArray` read as a list equation, which is the
form every list induction of the tier wants. -/
theorem denoteDeclArray_iff {st : EStore} {ds : Array IDeclaration}
    {xs : Array ConLeche.Declaration} :
    denoteDeclArray st ds = some xs ↔ denoteDecls st ds.toList = some xs.toList := by
  constructor
  · intro h
    simp only [denoteDeclArray, Option.map_eq_some_iff] at h
    obtain ⟨ys, hys, hEq⟩ := h
    subst hEq
    simpa using hys
  · intro h
    simp only [denoteDeclArray, h, Option.map_some, Array.toArray_toList]

/-- con-leche: none — two streams' denotations concatenate: what
`preparePrelude`'s `front ++ rest` needs. -/
theorem denoteDecls_append {st : EStore} :
    ∀ {as bs : List IDeclaration} {xs ys : List ConLeche.Declaration},
      denoteDecls st as = some xs → denoteDecls st bs = some ys →
        denoteDecls st (as ++ bs) = some (xs ++ ys) := by
  intro as
  induction as with
  | nil =>
    intro bs xs ys ha hb
    simp only [denoteDecls, Option.some.injEq] at ha
    subst ha; simpa using hb
  | cons a as ih =>
    intro bs xs ys ha hb
    simp only [denoteDecls] at ha ⊢
    cases hd : ConRon.Arena.Frontend.denoteDecl st a with
    | none => rw [hd] at ha; simp at ha
    | some y =>
      cases hs : denoteDecls st as with
      | none => rw [hd, hs] at ha; simp at ha
      | some zs =>
        rw [hd, hs] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        rw [List.cons_append, denoteDecls, hd, ih hs hb]
        rfl

/-- con-leche: none — the same at an `Array`. -/
theorem denoteDeclArray_append {st : EStore} {as bs : Array IDeclaration}
    {xs ys : Array ConLeche.Declaration}
    (ha : denoteDeclArray st as = some xs) (hb : denoteDeclArray st bs = some ys) :
    denoteDeclArray st (as ++ bs) = some (xs ++ ys) := by
  rw [denoteDeclArray_iff] at ha hb ⊢
  simpa using denoteDecls_append ha hb

/-- con-leche: none — the stream's denotation is record for record, so it has
the record's own length.  `Arena/Main.lean`'s verdict number is a LENGTH
(`r.decls.size - r.genRecords`), so the frontend tier owes this beside the
denotation itself. -/
theorem denoteDecls_length {st : EStore} :
    ∀ (ds : List IDeclaration) (xs : List ConLeche.Declaration),
      denoteDecls st ds = some xs → ds.length = xs.length := by
  intro ds
  induction ds with
  | nil => intro xs h; simp only [denoteDecls, Option.some.injEq] at h; subst h; rfl
  | cons a as ih =>
    intro xs h
    simp only [denoteDecls] at h
    cases ha : ConRon.Arena.Frontend.denoteDecl st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : denoteDecls st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [ih ys has]

/-! `IProjNamed`, `IProjTableOK.toNamed` and `IProjNamed.mono` are in
`Bridge/StateOK.lean` beside `IProjTableOK` since task #97-P3-Ind round 5 —
the maintainer's ruling on this round's finding, so that
`denoteCI_name_proj` can take the name clause alone.  They are in this
namespace's parent, so every use below reads unchanged. -/

/-- con-leche: none — a stored constant that is rightly named: the clause has
content at a `.projInfo` and nowhere else. -/
def CIProjNamed (st : EStore) (ci : IConstantInfo) : Prop :=
  ∀ t, ci = .projInfo t → IProjNamed st t

theorem CIProjNamed.mono {st st' : EStore} {ci : IConstantInfo}
    (h : CIProjNamed st ci) (hx : Ext st st') : CIProjNamed st' ci :=
  fun t ht => (h t ht).mono hx

/-- con-leche: none — the six constructors the clause is vacuous at. -/
theorem CIProjNamed.of_ne {st : EStore} {ci : IConstantInfo}
    (h : ∀ t, ci ≠ .projInfo t) : CIProjNamed st ci :=
  fun t ht => absurd ht (h t)

theorem CIProjNamed.of_proj {st : EStore} {t : IProjTable}
    (h : IProjNamed st t) : CIProjNamed st (.projInfo t) := by
  intro t' ht
  simp only [IConstantInfo.projInfo.injEq] at ht
  subst ht; exact h

/-- con-leche: none — a declaration record whose projection tables are rightly
named.  Only an `.indDecl` block can hold one, so the other six constructors
satisfy this vacuously. -/
def DeclProjNamed (st : EStore) (d : IDeclaration) : Prop :=
  ∀ block nP, d = .indDecl block nP → ∀ ci ∈ block, CIProjNamed st ci

theorem DeclProjNamed.mono {st st' : EStore} {d : IDeclaration}
    (h : DeclProjNamed st d) (hx : Ext st st') : DeclProjNamed st' d :=
  fun block nP hd ci hci => (h block nP hd ci hci).mono hx

/-- con-leche: none — the six constructors that carry no block. -/
theorem DeclProjNamed.of_axiomDecl {st : EStore} {v : IConstantVal} :
    DeclProjNamed st (.axiomDecl v) := by intro _ _ h; exact nomatch h

theorem DeclProjNamed.of_defnDecl {st : EStore} {v : IConstantVal} {e : EIdx}
    {h : ReducibilityHint} : DeclProjNamed st (.defnDecl v e h) := by
  intro _ _ h; exact nomatch h

theorem DeclProjNamed.of_thmDecl {st : EStore} {v : IConstantVal} {e : EIdx} :
    DeclProjNamed st (.thmDecl v e) := by intro _ _ h; exact nomatch h

theorem DeclProjNamed.of_opaqueDecl {st : EStore} {v : IConstantVal} {e : EIdx} :
    DeclProjNamed st (.opaqueDecl v e) := by intro _ _ h; exact nomatch h

theorem DeclProjNamed.of_quotDecl {st : EStore} {k : QuotKind} {v : IConstantVal} :
    DeclProjNamed st (.quotDecl k v) := by intro _ _ h; exact nomatch h

/-- con-leche: none — a parsed `.indDecl` block: the frontend's own
`installIndD` builds one out of `.indInfo`, `.ctorInfo` and `.recInfo`, never a
`.projInfo`, so the clause is vacuous there and this is the shape that says
so. -/
theorem DeclProjNamed.of_indDecl {st : EStore} {block : List IConstantInfo}
    {nP : Nat} (h : ∀ ci ∈ block, CIProjNamed st ci) :
    DeclProjNamed st (.indDecl block nP) := by
  intro block' nP' he
  simp only [IDeclaration.indDecl.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact h

/-- con-leche: none — the clause at a whole stream. -/
def DeclsProjNamed (st : EStore) (ds : Array IDeclaration) : Prop :=
  ∀ d ∈ ds, DeclProjNamed st d

theorem DeclsProjNamed.mono {st st' : EStore} {ds : Array IDeclaration}
    (h : DeclsProjNamed st ds) (hx : Ext st st') : DeclsProjNamed st' ds :=
  fun d hd => (h d hd).mono hx

theorem DeclsProjNamed.empty (st : EStore) : DeclsProjNamed st #[] := by
  intro d hd; simp at hd

theorem DeclsProjNamed.push {st : EStore} {ds : Array IDeclaration}
    (h : DeclsProjNamed st ds) {d : IDeclaration} (hd : DeclProjNamed st d) :
    DeclsProjNamed st (ds.push d) := by
  intro x hx
  rcases Array.mem_push.mp hx with hx | hx
  · exact h x hx
  · subst hx; exact hd


/-! ### Persistence, from the denotation

**The persistence half of an intern is not extra content: it is a CONSEQUENCE
of the denotation half.**  A handle that denotes has a view (`Arena/
WFProofs.lean`'s `denoteN_view` / `denoteL_view` / `denoteE_view`), and a
handle with a view on a store whose scratch tier is closed is persistent
(`PersN_of_view` / `PersL_of_view` / `PersE_of_view` above).  So `Pers… h`
follows from `denote… st h = some x` together with `StoreWF st` and
`st.scratchOn = false`, at the leaf — and every record denotation
(`Arena/Frontend/Readback.lean:93-199`) reads EVERY handle field of its
record, so the twelve record layers follow field for field.

**The one field a denotation does not read is a projection table's
`tableName`** — con-leche recomputes it, so `denoteProjTable` drops it
(`Readback.lean:156-168`'s own note).  That gap is exactly what `IProjNamed`
closes, and `internProjTable` carries the clause already, so the two
projection layers take it as a hypothesis and nothing is weakened.

This is what makes `Bridge/Frontend/Shared.lean`'s intern family
scratch-agnostic without a second copy of it: the family is stated over
`IStepS` with the denotation alone, and the `IStep` version — `hoff` in,
`Pers…` out — is a three-line corollary through these lemmas.  DESIGN
#97-P3-Frontend round 6. -/

/-- con-leche: none — a name handle that denotes on a closed store is
persistent. -/
theorem PersN_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {h : NIdx} {n : ConLeche.Name}
    (hd : denoteN st.ns h = some n) : PersN h := by
  obtain ⟨v, hv⟩ := Arena.denoteN_view hd
  exact PersN_of_view hwf hoff hv

/-- con-leche: none — the same at a LEVEL handle. -/
theorem PersL_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {h : LIdx} {u : Level}
    (hd : denoteL st.ls h = some u) : PersL h := by
  obtain ⟨v, hv⟩ := Arena.denoteL_view hd
  exact PersL_of_view hwf hoff hv

/-- con-leche: none — the same at an EXPRESSION handle. -/
theorem PersE_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) : PersE h := by
  obtain ⟨v, hv⟩ := Arena.denoteE_view hd
  exact PersE_of_view hwf hoff hv

/-- con-leche: none — a name-handle list that denotes is persistent. -/
theorem PersNList_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) :
    ∀ {hs : List NIdx} {ns : List ConLeche.Name},
      denoteNList st.ns hs = some ns → PersNList hs := by
  intro hs
  induction hs with
  | nil => intro ns _ n hn; simp at hn
  | cons a as ih =>
    intro ns hd
    rw [denoteNList] at hd
    cases h1 : denoteN st.ns a with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : denoteNList st.ns as with
      | none => rw [h1, h2] at hd; simp at hd
      | some xs =>
        intro n hn
        simp only [List.mem_cons] at hn
        rcases hn with rfl | hn
        · exact PersN_of_denote hwf hoff h1
        · exact ih h2 n hn

/-- con-leche: none — a level-handle list that denotes is persistent. -/
theorem PersLList_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) :
    ∀ {hs : List LIdx} {us : List Level},
      denoteLList st.ls hs = some us → PersLList hs := by
  intro hs
  induction hs with
  | nil => intro us _ u hu; simp at hu
  | cons a as ih =>
    intro us hd
    simp only [denoteLList, opt2_eq_some_iff] at hd
    obtain ⟨x, xs, h1, h2, -⟩ := hd
    intro u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact PersL_of_denote hwf hoff h1
    · exact ih h2 u hu

/-- con-leche: none — an expression-handle list that denotes is persistent. -/
theorem PersEList_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) :
    ∀ {hs : List EIdx} {es : List Expr},
      denoteEList st hs = some es → PersEList hs := by
  intro hs
  induction hs with
  | nil => intro es _ e he; simp at he
  | cons a as ih =>
    intro es hd
    rw [denoteEList] at hd
    cases h1 : denoteE st a with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : denoteEList st as with
      | none => rw [h1, h2] at hd; simp at hd
      | some xs =>
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact PersE_of_denote hwf hoff h1
        · exact ih h2 e he

/-- con-leche: none — a constant's header: `denoteCV` reads its three handle
fields and `PersCV` names the same three. -/
theorem PersCV_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {icv : IConstantVal} {cv : ConstantVal}
    (hd : denoteCV st icv = some cv) : PersCV icv := by
  rw [denoteCV] at hd
  cases h1 : denoteN st.ns icv.name with
  | none => rw [h1] at hd; simp at hd
  | some n =>
  cases h2 : denoteNList st.ns icv.levelParams with
  | none => rw [h1, h2] at hd; simp at hd
  | some lps =>
  cases h3 : denoteE st icv.type with
  | none => rw [h1, h2, h3] at hd; simp at hd
  | some ty =>
  exact ⟨PersN_of_denote hwf hoff h1, PersNList_of_denote hwf hoff h2,
    PersE_of_denote hwf hoff h3⟩

/-- con-leche: none — a recursor rule's firing mode; the two constant arms
carry no handle at all. -/
theorem PersFire_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {fr : IRecRuleFire} {f : RecRuleFire}
    (hd : denoteFire st fr = some f) : PersFire fr := by
  cases fr with
  | inert => trivial
  | plain => trivial
  | nested lvls pins =>
    rw [denoteFire] at hd
    cases h1 : denoteLList st.ls lvls with
    | none => rw [h1] at hd; simp at hd
    | some ls =>
    cases h2 : denoteEList st pins with
    | none => rw [h1, h2] at hd; simp at hd
    | some ps =>
    exact ⟨PersLList_of_denote hwf hoff h1, PersEList_of_denote hwf hoff h2⟩

/-- con-leche: none — one recursor rule. -/
theorem PersRule_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {rl : IRecRule} {r : RecRule}
    (hd : denoteRule st rl = some r) : PersRule rl := by
  rw [denoteRule] at hd
  cases h1 : denoteN st.ns rl.ctor with
  | none => rw [h1] at hd; simp at hd
  | some c =>
  cases h2 : denoteFire st rl.fire with
  | none => rw [h1, h2] at hd; simp at hd
  | some f =>
  cases h3 : denoteE st rl.rhs with
  | none => rw [h1, h2, h3] at hd; simp at hd
  | some rhs =>
  exact ⟨PersN_of_denote hwf hoff h1, PersFire_of_denote hwf hoff h2,
    PersE_of_denote hwf hoff h3⟩

/-- con-leche: none — a rule list. -/
theorem PersRules_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) :
    ∀ {rs : List IRecRule} {xs : List RecRule},
      denoteRules st rs = some xs → PersRules rs := by
  intro rs
  induction rs with
  | nil => intro xs _ r hr; simp at hr
  | cons a as ih =>
    intro xs hd
    rw [denoteRules] at hd
    cases h1 : denoteRule st a with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : denoteRules st as with
      | none => rw [h1, h2] at hd; simp at hd
      | some ys =>
        intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact PersRule_of_denote hwf hoff h1
        · exact ih h2 r hr

/-- con-leche: none — an inductive's capabilities record; its one handle field
is the eta constructor's name. -/
theorem PersCaps_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {c : IIndCaps} {cc : IndCaps}
    (hd : denoteCaps st c = some cc) : PersCaps c := by
  rw [denoteCaps] at hd
  cases h1 : denoteN st.ns c.etaCtor with
  | none => rw [h1] at hd; simp at hd
  | some n =>
  cases h2 : denoteNList st.ns c.all with
  | none => rw [h1, h2] at hd; simp at hd
  | some all =>
  cases h3 : denoteNList st.ns c.ctors with
  | none => rw [h1, h2, h3] at hd; simp at hd
  | some ctors =>
    exact ⟨PersN_of_denote hwf hoff h1, PersNList_of_denote hwf hoff h2,
      PersNList_of_denote hwf hoff h3⟩

/-- con-leche: none — a projection table.  Six of its seven handle fields are
read by `denoteProjTable`; the seventh, `tableName`, is the one con-leche
recomputes, so `IProjNamed` supplies it. -/
theorem PersProjTable_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {ti : IProjTable} {t : ProjTable}
    (hn : IProjNamed st ti) (hd : denoteProjTable st ti = some t) :
    PersProjTable ti := by
  obtain ⟨sn, -, htn⟩ := hn
  rw [denoteProjTable] at hd
  cases h1 : denoteN st.ns ti.structName with
  | none => rw [h1] at hd; simp at hd
  | some x1 =>
  cases h2 : denoteNList st.ns ti.levelParams with
  | none => rw [h1, h2] at hd; simp at hd
  | some x2 =>
  cases h3 : denoteN st.ns ti.ctor with
  | none => rw [h1, h2, h3] at hd; simp at hd
  | some x3 =>
  cases h4 : denoteL st.ls ti.structSort with
  | none => rw [h1, h2, h3, h4] at hd; simp at hd
  | some x4 =>
  cases h5 : denoteEArray st ti.bodies with
  | none => rw [h1, h2, h3, h4, h5] at hd; simp at hd
  | some x5 =>
  cases h6 : denoteLList st.ls ti.guards with
  | none => rw [h1, h2, h3, h4, h5, h6] at hd; simp at hd
  | some x6 =>
  refine ⟨PersN_of_denote hwf hoff h1, PersN_of_denote hwf hoff htn,
    PersNList_of_denote hwf hoff h2, PersN_of_denote hwf hoff h3,
    PersL_of_denote hwf hoff h4, ?_, PersLList_of_denote hwf hoff h6⟩
  rw [denoteEArray] at h5
  cases h7 : denoteEList st ti.bodies.toList with
  | none => rw [h7] at h5; simp at h5
  | some x7 => exact PersEList_of_denote hwf hoff h7

/-- con-leche: none — **a stored constant**: seven arms, each of them the
layers above assembled. -/
theorem PersCI_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {ci : IConstantInfo} {c : ConstantInfo}
    (hn : CIProjNamed st ci) (hd : denoteCI st ci = some c) : PersCI ci := by
  cases ci with
  | axiomInfo v =>
    rw [denoteCI] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv => exact PersCV_of_denote hwf hoff h1
  | ctorInfo v nP nF =>
    rw [denoteCI] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv => exact PersCV_of_denote hwf hoff h1
  | defnInfo v e h =>
    rw [denoteCI] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv =>
    cases h2 : denoteE st e with
    | none => rw [h1, h2] at hd; simp at hd
    | some x => exact ⟨PersCV_of_denote hwf hoff h1, PersE_of_denote hwf hoff h2⟩
  | thmInfo v e =>
    rw [denoteCI] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv =>
    cases h2 : denoteE st e with
    | none => rw [h1, h2] at hd; simp at hd
    | some x => exact ⟨PersCV_of_denote hwf hoff h1, PersE_of_denote hwf hoff h2⟩
  | indInfo v cp =>
    rw [denoteCI] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv =>
    cases h2 : denoteCaps st cp with
    | none => rw [h1, h2] at hd; simp at hd
    | some caps =>
      exact ⟨PersCV_of_denote hwf hoff h1, PersCaps_of_denote hwf hoff h2⟩
  | recInfo v mI rP rs =>
    rw [denoteCI] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv =>
    cases h2 : denoteRules st rs with
    | none => rw [h1, h2] at hd; simp at hd
    | some rules =>
      exact ⟨PersCV_of_denote hwf hoff h1, PersRules_of_denote hwf hoff h2⟩
  | projInfo t =>
    rw [denoteCI] at hd
    cases h1 : denoteProjTable st t with
    | none => rw [h1] at hd; simp at hd
    | some pt => exact PersProjTable_of_denote hwf hoff (hn t rfl) h1

/-- con-leche: none — a block. -/
theorem PersCIList_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) :
    ∀ {cis : List IConstantInfo} {cs : List ConstantInfo},
      (∀ ci ∈ cis, CIProjNamed st ci) → denoteCIList st cis = some cs →
      PersCIList cis := by
  intro cis
  induction cis with
  | nil => intro cs _ _ c hc; simp at hc
  | cons a as ih =>
    intro cs hn hd
    rw [denoteCIList] at hd
    cases h1 : denoteCI st a with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : denoteCIList st as with
      | none => rw [h1, h2] at hd; simp at hd
      | some xs =>
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact PersCI_of_denote hwf hoff (hn c (by simp)) h1
        · exact ih (fun ci hci => hn ci (by simp [hci])) h2 c hc

/-- con-leche: none — **a declaration record**: the frontend tier's
postcondition, and the fold theorems' second frontend obligation
(`hpd`). -/
theorem PersDecl_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {di : IDeclaration} {d : Declaration}
    (hn : DeclProjNamed st di) (hd : denoteDecl st di = some d) :
    PersDecl di := by
  cases di with
  | basisDecl k => trivial
  | axiomDecl v =>
    rw [denoteDecl] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv => exact PersCV_of_denote hwf hoff h1
  | quotDecl k v =>
    rw [denoteDecl] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv => exact PersCV_of_denote hwf hoff h1
  | defnDecl v e hh =>
    rw [denoteDecl] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv =>
    cases h2 : denoteE st e with
    | none => rw [h1, h2] at hd; simp at hd
    | some x => exact ⟨PersCV_of_denote hwf hoff h1, PersE_of_denote hwf hoff h2⟩
  | thmDecl v e =>
    rw [denoteDecl] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv =>
    cases h2 : denoteE st e with
    | none => rw [h1, h2] at hd; simp at hd
    | some x => exact ⟨PersCV_of_denote hwf hoff h1, PersE_of_denote hwf hoff h2⟩
  | opaqueDecl v e =>
    rw [denoteDecl] at hd
    cases h1 : denoteCV st v with
    | none => rw [h1] at hd; simp at hd
    | some cv =>
    cases h2 : denoteE st e with
    | none => rw [h1, h2] at hd; simp at hd
    | some x => exact ⟨PersCV_of_denote hwf hoff h1, PersE_of_denote hwf hoff h2⟩
  | indDecl block nP =>
    rw [denoteDecl] at hd
    cases h1 : denoteCIList st block with
    | none => rw [h1] at hd; simp at hd
    | some b =>
      exact PersCIList_of_denote hwf hoff (hn block nP rfl) h1

/-! The non-projection half is `Bridge/StateOK.lean`'s own `denoteCI_name`,
which landed there while this round ran; only the `.projInfo` half is restated
here, because that one asks `IProjTableOK` where this tier has only its `named`
clause.  When `denoteCI_name_proj`'s hypothesis is weakened to `IProjNamed` —
its proof uses `hok.named` and nothing else — the two below go away. -/

/-- con-leche: ConLeche/Kernel/Env.lean:642 ConstantInfo.toConstantVal (the
`.projInfo` arm) — and a projection table is named by its stored handle exactly
when `IProjNamed` says so.  That clause is not decoration: it is the only thing
that ties `tableName` to `ConLeche.projTableName`. -/
theorem ciName_denote_proj {st : EStore} {t : IProjTable} {c : ConstantInfo}
    (hn : IProjNamed st t)
    (h : ConRon.Arena.Frontend.denoteCI st (.projInfo t) = some c) :
    denoteN st.ns (IConstantInfo.name (.projInfo t)) = some c.name := by
  obtain ⟨sn, hsn, htn⟩ := hn
  simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at h
  obtain ⟨pt, hpt, rfl⟩ := h
  simp only [ConRon.Arena.Frontend.denoteProjTable, hsn] at hpt
  cases hlps : ConRon.Arena.Frontend.denoteNList st.ns t.levelParams with
  | none => rw [hlps] at hpt; simp at hpt
  | some lps =>
    cases hc : denoteN st.ns t.ctor with
    | none => rw [hlps, hc] at hpt; simp at hpt
    | some cn =>
      cases hss : denoteL st.ls t.structSort with
      | none => rw [hlps, hc, hss] at hpt; simp at hpt
      | some ss =>
        cases hbs : ConRon.Arena.Frontend.denoteEArray st t.bodies with
        | none => rw [hlps, hc, hss, hbs] at hpt; simp at hpt
        | some bs =>
          cases hgs : denoteLList st.ls t.guards with
          | none => rw [hlps, hc, hss, hbs, hgs] at hpt; simp at hpt
          | some gs =>
            rw [hlps, hc, hss, hbs, hgs] at hpt
            obtain rfl := Option.some.inj hpt
            exact htn

/-- con-leche: none — the two halves as one. -/
theorem ciName_denote_of {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (hproj : CIProjNamed st ci)
    (h : ConRon.Arena.Frontend.denoteCI st ci = some c) :
    denoteN st.ns ci.name = some c.name := by
  cases ci with
  | projInfo t => exact ciName_denote_proj (hproj t rfl) h
  | axiomInfo v => exact denoteCI_name (by simp) h
  | defnInfo v e hh => exact denoteCI_name (by simp) h
  | thmInfo v e => exact denoteCI_name (by simp) h
  | indInfo v caps => exact denoteCI_name (by simp) h
  | ctorInfo v nP nF => exact denoteCI_name (by simp) h
  | recInfo v mI rP rs => exact denoteCI_name (by simp) h

/-- con-leche: none — a block's names, at the list. -/
theorem ciNames_denote {st : EStore} :
    ∀ {block : List IConstantInfo} {bP : List ConstantInfo},
      (∀ ci ∈ block, CIProjNamed st ci) →
      ConRon.Arena.Frontend.denoteCIList st block = some bP →
      ConRon.Arena.Frontend.denoteNList st.ns (block.map (·.name))
        = some (bP.map (·.name))
  | [], bP, _, h => by
    simp only [ConRon.Arena.Frontend.denoteCIList, Option.some.injEq] at h
    subst h; rfl
  | ci :: cs, bP, hproj, h => by
    simp only [ConRon.Arena.Frontend.denoteCIList] at h
    cases hci : ConRon.Arena.Frontend.denoteCI st ci with
    | none => rw [hci] at h; simp at h
    | some c =>
      cases hcs : ConRon.Arena.Frontend.denoteCIList st cs with
      | none => rw [hci, hcs] at h; simp at h
      | some xs =>
        rw [hci, hcs] at h
        simp only [Option.some.injEq] at h
        subst h
        have h1 := ciName_denote_of (hproj ci (by simp)) hci
        have h2 := ciNames_denote (fun c hc => hproj c (by simp [hc])) hcs
        simp only [List.map_cons, ConRon.Arena.Frontend.denoteNList, h1, h2]

/-- con-leche: ConLeche/Kernel/Env.lean:659-670 Declaration.names — **the
record's declared names denote**, which is what round 4's finding 16 said a
bare `denoteDecl` does not give.  `DeclProjNamed` is exactly the missing
hypothesis and nothing more. -/
theorem declNames_denote {st : EStore} {d : IDeclaration} {dP : Declaration}
    (hpn : DeclProjNamed st d)
    (hd : ConRon.Arena.Frontend.denoteDecl st d = some dP) :
    ConRon.Arena.Frontend.denoteNList st.ns d.names = some dP.names := by
  have hcv : ∀ (v : IConstantVal) (cv : ConstantVal),
      ConRon.Arena.Frontend.denoteCV st v = some cv →
      denoteN st.ns v.name = some cv.name := by
    intro v cv hv
    simp only [ConRon.Arena.Frontend.denoteCV] at hv
    cases hn : denoteN st.ns v.name with
    | none => rw [hn] at hv; simp at hv
    | some n =>
      cases hl : ConRon.Arena.Frontend.denoteNList st.ns v.levelParams with
      | none => rw [hn, hl] at hv; simp at hv
      | some lps =>
        cases ht : denoteE st v.type with
        | none => rw [hn, hl, ht] at hv; simp at hv
        | some ty =>
          rw [hn, hl, ht] at hv
          obtain rfl := Option.some.inj hv
          rfl
  cases d with
  | axiomDecl v =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hv, rfl⟩ := hd
    simp only [IDeclaration.names, Declaration.names,
      ConRon.Arena.Frontend.denoteNList, hcv v cv hv]
  | defnDecl v e hh =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hv : ConRon.Arena.Frontend.denoteCV st v with
    | none => rw [hv] at hd; simp at hd
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hv, he] at hd; simp at hd
      | some x =>
        rw [hv, he] at hd
        obtain rfl := Option.some.inj hd
        simp only [IDeclaration.names, Declaration.names,
          ConRon.Arena.Frontend.denoteNList, hcv v cv hv]
  | thmDecl v e =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hv : ConRon.Arena.Frontend.denoteCV st v with
    | none => rw [hv] at hd; simp at hd
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hv, he] at hd; simp at hd
      | some x =>
        rw [hv, he] at hd
        obtain rfl := Option.some.inj hd
        simp only [IDeclaration.names, Declaration.names,
          ConRon.Arena.Frontend.denoteNList, hcv v cv hv]
  | opaqueDecl v e =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hv : ConRon.Arena.Frontend.denoteCV st v with
    | none => rw [hv] at hd; simp at hd
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hv, he] at hd; simp at hd
      | some x =>
        rw [hv, he] at hd
        obtain rfl := Option.some.inj hd
        simp only [IDeclaration.names, Declaration.names,
          ConRon.Arena.Frontend.denoteNList, hcv v cv hv]
  | basisDecl k =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.some.injEq] at hd
    subst hd
    rfl
  | quotDecl k v =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hv, rfl⟩ := hd
    simp only [IDeclaration.names, Declaration.names,
      ConRon.Arena.Frontend.denoteNList, hcv v cv hv]
  | indDecl block nP =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    exact ciNames_denote (hpn block nP rfl) hb

/-! ## The parse state -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:82-134 StateD — **THE PARSE-STATE
RELATION**: the twin's parse state denotes con-leche's, field for field, in
the store `st`.

Four clauses for four fields (task #105: the in-process modeller and the
projection rewrite's fourteen census fields are gone — see this file's
header note).  The three stream-index tables go through `IdTableRel`, the
declaration array through `denoteDeclArray`, and `projNamed` is the one
invariant that is not a raw field: the stream's projection tables (a kernel
concern, unrelated to the deleted rewrite) are rightly named. -/
structure StateDRel (st : EStore) (sd : StateD) (sc : ConLeche.Frontend.StateD) :
    Prop where
  names : IdTableRel (fun h n => denoteN st.ns h = some n) sd.names sc.names
  levels : IdTableRel (fun h u => denoteL st.ls h = some u) sd.levels sc.levels
  exprs : IdTableRel (fun h e => denoteE st h = some e) sd.exprs sc.exprs
  decls : denoteDeclArray st sd.decls = some sc.decls
  /-- **the stream's projection tables are rightly named** — round 4's
  finding 16, repaired the way `Bridge/StateOK.lean`'s `IFEnvOK` repaired the
  same gap one module over (`IFEnvOK.proj`).  `denoteProjTable` drops
  `tableName`, so `decls` alone does NOT give `IDeclaration.names`'s
  exactness; this clause does, through `declNames_denote`, and it travels
  through the whole streaming fold because the fold only ever transports the
  relation.  Its one debtor (task #105: the modeller's `pushGenList` is gone)
  is `pushDecl` — the only place a record ENTERS the stream, where a block is
  built out of `.indInfo`/`.ctorInfo`/`.recInfo` and the clause is vacuous. -/
  projNamed : DeclsProjNamed st sd.decls

/-! ## The parse result -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:732-753 ParseResultD — the parse
RESULT relation: the two fields `ParseResultD.ofState` copies out of the
state.  This is what DESIGN §8.2's exactness statement is about, and its
`decls` clause is the equation itself. -/
structure ParseResultRel (st : EStore) (r : ParseResultD)
    (rc : ConLeche.Frontend.ParseResultD) : Prop where
  decls : denoteDeclArray st r.decls = some rc.decls
  /-- the same clause at the parse RESULT, which is what carries round 4's
  finding 16 out of the parse and into `Bridge/Frontend/Prepare.lean`. -/
  projNamed : DeclsProjNamed st r.decls

/-- con-leche: ConLeche/Frontend/ExportC.lean:761-763 ParseResultD.ofState —
the result relation is the state relation's two clauses, read off.  The one
place the two records meet, and it is a projection. -/
theorem ParseResultRel.ofState {st : EStore} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (h : StateDRel st sd sc) :
    ParseResultRel st (ParseResultD.ofState sd)
      (ConLeche.Frontend.ParseResultD.ofState sc) :=
  { decls := h.decls, projNamed := h.projNamed }

/-! ## Transport across an append

Every clause of `StateDRel` is a denotation, and `Bridge/Rel.lean`'s ten
`…_ext` lemmas move a denotation across an append — so the whole relation
does, and the parse's induction never has to re-establish it.  This is the
`Ext` twin of `Bridge/Checker/Inv.lean`'s nineteen `…_pext` transports; the
frontend tier needs only the `Ext` one, because the parse never opens the
scratch tier.

**`MapRel`'s `cover` clause transports too, and it costs nothing.**  That is
worth saying, because `Bridge/StateOK.lean`'s `IFEnvOK` needs `cover` exactly
where the naive "a miss is a miss" fails: a handle that decoded to nothing
before an extension may decode after it.  `cover` says the opposite direction
— *every entry of the value side is named by a handle the twin's side knows*
— and an extension keeps that handle decoding, so the clause survives by
`denoteN_ext` alone. -/

theorem IdTableRel.mono {α β : Type} {R R' : α → β → Prop}
    (hR : ∀ a b, R a b → R' a b) {t : ConLeche.Frontend.IdTable α}
    {u : ConLeche.Frontend.IdTable β} (h : IdTableRel R t u) :
    IdTableRel R' t u := by
  intro i
  have hi := h i
  cases hu : t.get? i with
  | none => rw [hi.none_left hu]; exact OptRel.refl_none
  | some a =>
    obtain ⟨b, hv, hab⟩ := hi.some_left hu
    rw [hv]; exact hR _ _ hab

/-- con-leche: none — `Bridge/Rel.lean`'s `denoteCI_ext` at a BLOCK.  It has a
`…_pext` twin (`Bridge/Checker/Inv.lean:320`) and no `…_ext` one, because the
Checker tier only ever moves a block across a drop. -/
theorem denoteCIList_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (cs : List IConstantInfo) (xs : List ConstantInfo),
      ConRon.Arena.Frontend.denoteCIList st cs = some xs →
        ConRon.Arena.Frontend.denoteCIList st' cs = some xs := by
  intro cs
  induction cs with
  | nil => intro _ h; exact h
  | cons a as ih =>
    intro xs h
    simp only [ConRon.Arena.Frontend.denoteCIList] at h ⊢
    cases ha : ConRon.Arena.Frontend.denoteCI st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : ConRon.Arena.Frontend.denoteCIList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteCI_ext ha hx, ih ys has]
        exact h

/-- con-leche: none — a declaration record survives an append.  The `…_ext`
twin of `Bridge/Checker/Inv.lean`'s `denoteDecl_pext`. -/
theorem denoteDecl_ext {st st' : EStore} (hx : Ext st st') {pd : IDeclaration}
    {d : ConLeche.Declaration}
    (h : ConRon.Arena.Frontend.denoteDecl st pd = some d) :
    ConRon.Arena.Frontend.denoteDecl st' pd = some d := by
  cases pd with
  | basisDecl k => exact h
  | axiomDecl v =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_ext hcv hx, hc⟩
  | quotDecl k v =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_ext hcv hx, hc⟩
  | indDecl block nP =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at h ⊢
    obtain ⟨b, hb, hc⟩ := h
    exact ⟨b, denoteCIList_ext hx _ b hb, hc⟩
  | defnDecl v e hint =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at h ⊢
    cases hcv : ConRon.Arena.Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h; rw [denoteCV_ext hcv hx, denote_ext he hx]; exact h
  | thmDecl v e =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at h ⊢
    cases hcv : ConRon.Arena.Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h; rw [denoteCV_ext hcv hx, denote_ext he hx]; exact h
  | opaqueDecl v e =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at h ⊢
    cases hcv : ConRon.Arena.Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h; rw [denoteCV_ext hcv hx, denote_ext he hx]; exact h

/-- con-leche: none — the declaration STREAM survives an append, record by
record: the left-hand side of DESIGN §8.2's parser statement, carried across
every `intern` the parse does after it. -/
theorem denoteDecls_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (ds : List IDeclaration) (xs : List ConLeche.Declaration),
      denoteDecls st ds = some xs → denoteDecls st' ds = some xs := by
  intro ds
  induction ds with
  | nil => intro _ h; exact h
  | cons a as ih =>
    intro xs h
    simp only [denoteDecls] at h ⊢
    cases ha : ConRon.Arena.Frontend.denoteDecl st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : denoteDecls st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteDecl_ext hx ha, ih ys has]
        exact h

theorem denoteDeclArray_ext {st st' : EStore} (hx : Ext st st')
    {ds : Array IDeclaration} {xs : Array ConLeche.Declaration}
    (h : denoteDeclArray st ds = some xs) : denoteDeclArray st' ds = some xs := by
  simp only [denoteDeclArray, Option.map_eq_some_iff] at h ⊢
  obtain ⟨ys, hys, hEq⟩ := h
  exact ⟨ys, denoteDecls_ext hx _ ys hys, hEq⟩

/-- con-leche: none — **the parse-state relation survives an append**: the
fact the streaming fold's induction rests on, and the reason a line's theorem
may say `StateDRel s'.store sd' sc'` while the next line's hypothesis is
`StateDRel s''.store sd' sc'`.  Four clauses, one `Bridge/Rel.lean` `…_ext`
lemma each. -/
theorem StateDRel.ext {st st' : EStore} (hx : Ext st st') {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (h : StateDRel st sd sc) :
    StateDRel st' sd sc where
  names := h.names.mono (fun _ _ hd => denoteN_ext hd hx)
  levels := h.levels.mono (fun _ _ hd => denoteL_ext hd hx)
  exprs := h.exprs.mono (fun _ _ hd => denote_ext hd hx)
  decls := denoteDeclArray_ext hx h.decls
  projNamed := h.projNamed.mono hx

/-! ## Persistence

The fold theorems' second frontend obligation (`hpd`): every handle the
parse holds is in the persistent tier.  `Bridge/Promote/Pers.lean`'s `Pers…`
vocabulary, lifted to the parse state — the clause that matters is the one the
FOLD reads, which is `decls` and nothing else; the three tables are carried so
that the induction has one invariant rather than two. -/

/-- con-leche: none — every declaration record the parse state holds is
persistent (`Bridge/Promote/Pers.lean`'s `PersDecl`).  This is the clause
`Arena.installThenCheck_bridge` names `hpd`. -/
def PersDecls (ds : Array IDeclaration) : Prop := ∀ d ∈ ds, PersDecl d

/-- con-leche: none — the parse state's handles are persistent.  Free (the
parse runs with the scratch tier closed) and stated because the fold's first
`dropScratch` needs it. -/
structure PersStateD (sd : StateD) : Prop where
  names : ∀ i h, sd.names.get? i = some h → PersN h
  levels : ∀ i l, sd.levels.get? i = some l → PersL l
  exprs : ∀ i e, sd.exprs.get? i = some e → PersE e
  decls : PersDecls sd.decls

/-- con-leche: none — the parse result's declarations are persistent. -/
def PersParseResult (r : ParseResultD) : Prop := PersDecls r.decls

theorem PersParseResult.ofState {sd : StateD} (h : PersStateD sd) :
    PersParseResult (ParseResultD.ofState sd) := h.decls

end ConRon.Bridge.Frontend
