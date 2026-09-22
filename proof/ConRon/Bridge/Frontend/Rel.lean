/-
# `ConRon.Bridge.Frontend.Rel` — the parse-state relation

DESIGN §8.2's parser tier is one equation,

    denoteDecls (Arena.parse chunks) = parseChunks chunks   (exactness)

and the whole of this tier is the induction that proves it.  An induction over
a stream needs an invariant, and the invariant is this module: **the twin's
parse state denotes con-leche's, field for field**.

`Arena/Frontend/ExportC.lean`'s `StateD` is a field-for-field mirror of
`ConLeche/Frontend/ExportC.lean:82-134`'s — eighteen fields, in the same order,
with `NIdx`/`LIdx`/`EIdx` where con-leche has `Name`/`Level`/`Expr` — so the
relation is a field-for-field conjunction, and the four shapes it needs are:

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

**`PersStateD`** is the second half of what `Bridge/Checker/Capstone.lean`
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
-/
import ConRon.Bridge.Checker
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
theorem PersE_of_view {st : EStore} (hwf : StoreWF st)
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

One record for the six conjuncts every step of the parse carries, so that a
composition reads `h₁.trans h₂` rather than six `And.intro`s.  It is
`Bridge/StateOK.lean`'s `CheckOK.monoF` hypothesis, plus the scratch flag the
frontend tier needs and the Core tier does not.

The five frame conjuncts are what every caller needs and what nothing in the
frontend breaks: **the parse interns, and the ONE other thing it does is
compare two levels.**  It never enters the scratch tier (`Arena/Main.lean`
runs `internReservedPins` first and the fold's bracket has not started), never
writes a per-call memo and never touches the pin table — which is what makes
`PersStateD` free and what makes `Bridge/Checker/Capstone.lean`'s `FoldOK`
reachable at the post-parse state.

**The cache conjunct is a FRAME and not an equation** (task #97-P3-Frame).
Round one said `s'.caches = s.caches`, and that is false of the parse:
`registerProjOwners` (`Arena/Frontend/ExportC.lean:401`) calls `projRecOwners`
(`Arena/Frontend/ProjRec.lean:510-515`), which calls `structPartsCore?` and
`nativeParts?`, each of which computes its `isProp` field with
`Arena/Core.lean`'s `lvlEq?` — a cached verdict walk that probes `lvlEqC` and
on a miss writes `readLC` (twice, through `readLevelM`) and `lvlEqC`.  The
Rust does the same at the same three call sites, so the port is not at fault
and the statement was.  `Bridge/StateOK.lean`'s `CacheFrame` is the honest
clause: the record equation that names those two tables, plus their invariants
as implications.  A caller holding `CheckOK` — which is where the invariants
live — gets them back through `CheckOK.monoF`; a caller at `StateOK` does not
need them. -/

/-- con-leche: none — **the parse's frame**: the store only grew, the scratch
tier stayed as it was, the per-call memos and the pin table stood still, and
the per-declaration caches stood still up to the two tables a level comparison
writes. -/
structure ParseStep (s s' : AState) : Prop where
  ok : StateOK s'
  ext : Ext s.store s'.store
  scratch : s'.store.scratchOn = s.store.scratchOn
  memos : s'.memos = s.memos
  cframe : CacheFrame s s'
  pins : s'.pins = s.pins

theorem ParseStep.refl {s : AState} (hok : StateOK s) : ParseStep s s :=
  ⟨hok, Ext.refl _, rfl, rfl, CacheFrame.refl _, rfl⟩

theorem ParseStep.trans {a b c : AState} (h₁ : ParseStep a b) (h₂ : ParseStep b c) :
    ParseStep a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, by rw [h₂.scratch, h₁.scratch],
    by rw [h₂.memos, h₁.memos], h₁.cframe.trans h₂.cframe,
    by rw [h₂.pins, h₁.pins]⟩

/-- con-leche: none — the frame of a parse step that writes no
per-declaration table at all, which is every step but the owner census.  The
shape a proof reaches when it has the plain cache equation in hand. -/
theorem ParseStep.of_caches {s s' : AState} (hok : StateOK s')
    (hx : Ext s.store s'.store) (hsc : s'.store.scratchOn = s.store.scratchOn)
    (hm : s'.memos = s.memos) (hc : s'.caches = s.caches)
    (hp : s'.pins = s.pins) : ParseStep s s' :=
  ⟨hok, hx, hsc, hm, CacheFrame.of_eq hc hx, hp⟩

theorem ParseStep.of_eq {s s' : AState} (hok : StateOK s) (h : s' = s) :
    ParseStep s s' := by subst h; exact ParseStep.refl hok

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

theorem OptRel.some_right {α : Type u} {β : Type v} {R : α → β → Prop}
    {a : Option α} {b : Option β} {y : β} (h : OptRel R a b) (hb : b = some y) :
    ∃ x, a = some x ∧ R x y := by
  cases a with
  | none => rw [hb] at h; exact absurd h (by simp [OptRel])
  | some x => rw [hb] at h; exact ⟨x, rfl, h⟩

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

/-- con-leche: none — a `Std.HashMap` over HANDLES against one over the values
they denote.  Both directions, for `Bridge/StateOK.lean`'s `IFEnvOK` reason:
`hit` is what a read consumes, `cover` is what an arena extension preserves
(the naive "a miss at a handle that denotes `n` means a miss at `n`" is not). -/
structure MapRel {α : Type} {β : Type} (st : EStore) (R : α → β → Prop)
    (m : Std.HashMap NIdx α) (mc : Std.HashMap ConLeche.Name β) : Prop where
  hit : ∀ h a, m[h]? = some a →
    ∃ n b, denoteN st.ns h = some n ∧ mc[n]? = some b ∧ R a b
  cover : ∀ n b, mc[n]? = some b →
    ∃ h a, denoteN st.ns h = some n ∧ m[h]? = some a ∧ R a b

/-- con-leche: none — two EMPTY maps relate, whatever the relation is.  Five
of `StateD.init`'s eighteen fields are this (`Bridge/Frontend/Chunks.lean`'s
`StateD_init_run`). -/
theorem MapRel.empty {α β : Type} (st : EStore) (R : α → β → Prop) :
    MapRel st R (∅ : Std.HashMap NIdx α) (∅ : Std.HashMap ConLeche.Name β) where
  hit := by intro h a hk; simp at hk
  cover := by intro n b hn; simp at hn

/-- con-leche: none — **one entry, on both sides**, and the one place in this
module `denoteN_inj` is load-bearing: `hit` at a handle the insert missed has
to land on a KEY the insert missed, and two distinct handles denoting one name
would break exactly that.  Injectivity of the name store's denotation (task
#97a's `denoteN_inj`; DESIGN §8.3 makes exactness a soundness obligation) is
what rules it out, in both directions.

This is the lemma the six `noteDecl` arms, `registerProjOwners` and
`noteProjIota` all read: `MapRel.{mono,empty}` carry a map across an append
and start it, and this is the only thing that puts anything in one. -/
theorem MapRel.insert {α β : Type} {st : EStore} (hwf : StoreWF st)
    {R : α → β → Prop} {m : Std.HashMap NIdx α}
    {mc : Std.HashMap ConLeche.Name β} (h : MapRel st R m mc) {k : NIdx}
    {n : ConLeche.Name} (hk : denoteN st.ns k = some n) {a : α} {b : β}
    (hab : R a b) : MapRel st R (m.insert k a) (mc.insert n b) := by
  obtain ⟨rk, hrk⟩ := hwf
  refine ⟨?_, ?_⟩
  · intro i x hx
    rw [Std.HashMap.getElem?_insert] at hx
    by_cases hik : k = i
    · subst hik
      simp only [beq_self_eq_true, if_pos, Option.some.injEq] at hx
      subst hx
      exact ⟨n, b, hk, by simp, hab⟩
    · rw [if_neg (by simpa using hik)] at hx
      obtain ⟨n', b', hn', hb', hR⟩ := h.hit i x hx
      refine ⟨n', b', hn', ?_, hR⟩
      rw [Std.HashMap.getElem?_insert]
      by_cases hnn : n = n'
      · subst hnn
        exact absurd (denoteN_inj hrk.nsWF hk hn') hik
      · rw [if_neg (by simpa using hnn)]; exact hb'
  · intro n' b' hb'
    rw [Std.HashMap.getElem?_insert] at hb'
    by_cases hnn : n = n'
    · subst hnn
      simp only [beq_self_eq_true, if_pos, Option.some.injEq] at hb'
      subst hb'
      exact ⟨k, a, hk, by simp, hab⟩
    · rw [if_neg (by simpa using hnn)] at hb'
      obtain ⟨i, x, hi, hx, hR⟩ := h.cover n' b' hb'
      refine ⟨i, x, hi, ?_, hR⟩
      rw [Std.HashMap.getElem?_insert]
      by_cases hik : k = i
      · subst hik
        rw [hk] at hi
        simp only [Option.some.injEq] at hi
        exact absurd hi hnn
      · rw [if_neg (by simpa using hik)]; exact hx

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
  simp only [ConLeche.Frontend.IdTable.get?_empty]
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

/-! ## The frontend's own record denotations -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:85-104 ProjRecOwner — the
projection rewrite's owner record, field for field. -/
structure ProjRecOwnerRel (st : EStore) (o : ProjRecOwner)
    (oc : ConLeche.Frontend.ProjRecOwner) : Prop where
  T : denoteN st.ns o.T = some oc.T
  lps : denoteNList st.ns o.lps = some oc.lps
  nP : o.nP = oc.nP
  ctor : denoteN st.ns o.ctor = some oc.ctor
  nF : o.nF = oc.nF
  recName : denoteN st.ns o.recName = some oc.recName
  recLps : denoteNList st.ns o.recLps = some oc.recLps
  recType : denoteE st o.recType = some oc.recType
  numMotives : o.numMotives = oc.numMotives
  numMinors : o.numMinors = oc.numMinors

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:82-90 IndTypeRec — one
resolved type former of a parsed block. -/
structure MIndTypeRecRel (st : EStore) (t : MIndTypeRec)
    (tc : ConLeche.Frontend.InModel.IndTypeRec) : Prop where
  cv : denoteCV st t.cv = some tc.cv
  nP : t.nP = tc.nP
  nIdx : t.nIdx = tc.nIdx
  ctors : denoteNList st.ns t.ctors = some tc.ctors
  isRec : t.isRec = tc.isRec
  isReflexive : t.isReflexive = tc.isReflexive
  numNested : t.numNested = tc.numNested

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:92-97 IndCtorRec. -/
structure MIndCtorRecRel (st : EStore) (c : MIndCtorRec)
    (cc : ConLeche.Frontend.InModel.IndCtorRec) : Prop where
  cv : denoteCV st c.cv = some cc.cv
  nP : c.nP = cc.nP
  nF : c.nF = cc.nF

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:99-108 IndRecRec. -/
structure MIndRecRecRel (st : EStore) (r : MIndRecRec)
    (rc : ConLeche.Frontend.InModel.IndRecRec) : Prop where
  cv : denoteCV st r.cv = some rc.cv
  nP : r.nP = rc.nP
  nM : r.nM = rc.nM
  nm : r.nm = rc.nm
  nI : r.nI = rc.nI
  rules : denoteRules st r.rules = some rc.rules

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:111-115 BlockRec — a
parsed inductive block denotes con-leche's, member for member. -/
structure BlockRecRel (st : EStore) (b : BlockRec)
    (bc : ConLeche.Frontend.InModel.BlockRec) : Prop where
  types : ListRel (MIndTypeRecRel st) b.types bc.types
  ctors : ListRel (MIndCtorRecRel st) b.ctors bc.ctors
  recs : ListRel (MIndRecRecRel st) b.recs bc.recs

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:119-124 Ctx — what the
generator reads besides the block, related pointwise.  `tbl` and `blocks` are
partial and `heights` is total (con-leche's own default is `0`).

This is the relation `Bridge/Frontend/Modeller.lean`'s `ModellerRefines`
quantifies over, and it is the twin of `RefineOld/Frontend/IndSpecR.lean`'s
`Frontend.CtxRel`, which `conron.no_False_declaration` carries as `hmr`'s
third argument. -/
structure CtxRel (st : EStore) (c : Ctx) (cc : ConLeche.Frontend.InModel.Ctx) :
    Prop where
  tbl : ∀ h n, denoteN st.ns h = some n →
    OptRel (fun (p : List NIdx × EIdx) (q : List ConLeche.Name × Expr) =>
        denoteNList st.ns p.1 = some q.1 ∧ denoteE st p.2 = some q.2)
      (c.tbl h) (cc.tbl n)
  heights : ∀ h n, denoteN st.ns h = some n → c.heights h = cc.heights n
  blocks : ∀ h n, denoteN st.ns h = some n →
    OptRel (BlockRecRel st) (c.blocks h) (cc.blocks n)
  -- **the three COVER clauses** (task #97-P3-Frontend-2 round 2, finding 12):
  -- the three above say nothing about a name the store has never interned,
  -- and `ctxOf` answers `none`/`0` there — so without these the readback of
  -- the twin's context is not con-leche's context, and
  -- `inProcessModeller_refines` is not provable.  Same shape and same reason
  -- as `MapRel`'s `cover` beside its `hit`.
  tblCover : ∀ n q, cc.tbl n = some q → ∃ h, denoteN st.ns h = some n
  heightsCover : ∀ n, cc.heights n ≠ 0 → ∃ h, denoteN st.ns h = some n
  blocksCover : ∀ n b, cc.blocks n = some b → ∃ h, denoteN st.ns h = some n

/-! ## The parse state -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:82-134 StateD — **THE PARSE-STATE
RELATION**: the twin's parse state denotes con-leche's, field for field, in
the store `st`.

Eighteen clauses for eighteen fields.  The three stream-index tables go
through `IdTableRel`, the five handle-keyed maps through `MapRel`, the
declaration array through `denoteDeclArray`, and the five scalar/`Bool` fields
are plain equations — a `Nat` or a `Bool` names no handle, so task #97-P3-0
§5's finding 1 applies (`RelV`, no target store) and there is nothing to
denote. -/
structure StateDRel (st : EStore) (sd : StateD) (sc : ConLeche.Frontend.StateD) :
    Prop where
  names : IdTableRel (fun h n => denoteN st.ns h = some n) sd.names sc.names
  levels : IdTableRel (fun h u => denoteL st.ls h = some u) sd.levels sc.levels
  exprs : IdTableRel (fun h e => denoteE st h = some e) sd.exprs sc.exprs
  decls : denoteDeclArray st sd.decls = some sc.decls
  projOwners : MapRel st (ProjRecOwnerRel st) sd.projOwners sc.projOwners
  projLevels : MapRel st (fun l u => denoteL st.ls l = some u)
    sd.projLevels sc.projLevels
  projRewrites : denoteNList st.ns sd.projRewrites.toList
    = some sc.projRewrites.toList
  constTypes : MapRel st
    (fun (p : List NIdx × EIdx) (q : List ConLeche.Name × Expr) =>
      denoteNList st.ns p.1 = some q.1 ∧ denoteE st p.2 = some q.2)
    sd.constTypes sc.constTypes
  heights : MapRel st (fun (a b : Nat) => a = b) sd.heights sc.heights
  inModel : sd.inModel = sc.inModel
  inModelled : denoteNList st.ns sd.inModelled.toList = some sc.inModelled.toList
  genRecords : sd.genRecords = sc.genRecords
  genOwner : MapRel st (fun h n => denoteN st.ns h = some n) sd.genOwner sc.genOwner
  inModelGen : ListRel
    (fun (p : Nat × Array IDeclaration) (q : Nat × Array ConLeche.Declaration) =>
      p.1 = q.1 ∧ denoteDeclArray st p.2 = some q.2)
    sd.inModelGen.toList sc.inModelGen.toList
  indCount : sd.indCount = sc.indCount
  indBlocks : MapRel st (BlockRecRel st) sd.indBlocks sc.indBlocks
  inModelCensus : sd.inModelCensus = sc.inModelCensus
  inModelDeclined : ListRel
    (fun (p : NIdx × String) (q : ConLeche.Name × String) =>
      denoteN st.ns p.1 = some q.1 ∧ p.2 = q.2)
    sd.inModelDeclined.toList sc.inModelDeclined.toList

/-! ## The parse result -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:732-753 ParseResultD — the parse
RESULT relation: the seven fields `ParseResultD.ofState` copies out of the
state.  This is what DESIGN §8.2's exactness statement is about, and its
`decls` clause is the equation itself. -/
structure ParseResultRel (st : EStore) (r : ParseResultD)
    (rc : ConLeche.Frontend.ParseResultD) : Prop where
  decls : denoteDeclArray st r.decls = some rc.decls
  projRewrites : denoteNList st.ns r.projRewrites.toList
    = some rc.projRewrites.toList
  inModelled : denoteNList st.ns r.inModelled.toList = some rc.inModelled.toList
  genRecords : r.genRecords = rc.genRecords
  genOwner : MapRel st (fun h n => denoteN st.ns h = some n) r.genOwner rc.genOwner
  inModelGen : ListRel
    (fun (p : Nat × Array IDeclaration) (q : Nat × Array ConLeche.Declaration) =>
      p.1 = q.1 ∧ denoteDeclArray st p.2 = some q.2)
    r.inModelGen.toList rc.inModelGen.toList
  inModelDeclined : ListRel
    (fun (p : NIdx × String) (q : ConLeche.Name × String) =>
      denoteN st.ns p.1 = some q.1 ∧ p.2 = q.2)
    r.inModelDeclined.toList rc.inModelDeclined.toList

/-- con-leche: ConLeche/Frontend/ExportC.lean:761-763 ParseResultD.ofState —
the result relation is the state relation's seven clauses, read off.  The one
place the two records meet, and it is a projection. -/
theorem ParseResultRel.ofState {st : EStore} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (h : StateDRel st sd sc) :
    ParseResultRel st (ParseResultD.ofState sd)
      (ConLeche.Frontend.ParseResultD.ofState sc) :=
  { decls := h.decls, projRewrites := h.projRewrites, inModelled := h.inModelled,
    genRecords := h.genRecords, genOwner := h.genOwner, inModelGen := h.inModelGen,
    inModelDeclined := h.inModelDeclined }

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

theorem ListRel.mono {α : Type u} {β : Type v} {R R' : α → β → Prop}
    (hR : ∀ a b, R a b → R' a b) :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → ListRel R' as bs := by
  intro as bs h
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hR _ _ hab) ih

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

theorem MapRel.mono {α β : Type} {st st' : EStore} {R R' : α → β → Prop}
    (hx : Ext st st') (hR : ∀ a b, R a b → R' a b) {m : Std.HashMap NIdx α}
    {mc : Std.HashMap ConLeche.Name β} (h : MapRel st R m mc) :
    MapRel st' R' m mc where
  hit := by
    intro k a hk
    obtain ⟨n, b, hn, hb, hab⟩ := h.hit k a hk
    exact ⟨n, b, denoteN_ext hn hx, hb, hR _ _ hab⟩
  cover := by
    intro n b hn
    obtain ⟨k, a, hk, ha, hab⟩ := h.cover n b hn
    exact ⟨k, a, denoteN_ext hk hx, ha, hR _ _ hab⟩

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

theorem ProjRecOwnerRel.ext {st st' : EStore} (hx : Ext st st') {o : ProjRecOwner}
    {oc : ConLeche.Frontend.ProjRecOwner} (h : ProjRecOwnerRel st o oc) :
    ProjRecOwnerRel st' o oc where
  T := denoteN_ext h.T hx
  lps := denoteNListE_ext hx _ _ h.lps
  nP := h.nP
  ctor := denoteN_ext h.ctor hx
  nF := h.nF
  recName := denoteN_ext h.recName hx
  recLps := denoteNListE_ext hx _ _ h.recLps
  recType := denote_ext h.recType hx
  numMotives := h.numMotives
  numMinors := h.numMinors

theorem MIndTypeRecRel.ext {st st' : EStore} (hx : Ext st st') {t : MIndTypeRec}
    {tc : ConLeche.Frontend.InModel.IndTypeRec} (h : MIndTypeRecRel st t tc) :
    MIndTypeRecRel st' t tc where
  cv := denoteCV_ext h.cv hx
  nP := h.nP
  nIdx := h.nIdx
  ctors := denoteNListE_ext hx _ _ h.ctors
  isRec := h.isRec
  isReflexive := h.isReflexive
  numNested := h.numNested

theorem MIndCtorRecRel.ext {st st' : EStore} (hx : Ext st st') {c : MIndCtorRec}
    {cc : ConLeche.Frontend.InModel.IndCtorRec} (h : MIndCtorRecRel st c cc) :
    MIndCtorRecRel st' c cc where
  cv := denoteCV_ext h.cv hx
  nP := h.nP
  nF := h.nF

theorem MIndRecRecRel.ext {st st' : EStore} (hx : Ext st st') {r : MIndRecRec}
    {rc : ConLeche.Frontend.InModel.IndRecRec} (h : MIndRecRecRel st r rc) :
    MIndRecRecRel st' r rc where
  cv := denoteCV_ext h.cv hx
  nP := h.nP
  nM := h.nM
  nm := h.nm
  nI := h.nI
  rules := denoteRules_ext hx _ _ h.rules

theorem BlockRecRel.ext {st st' : EStore} (hx : Ext st st') {b : BlockRec}
    {bc : ConLeche.Frontend.InModel.BlockRec} (h : BlockRecRel st b bc) :
    BlockRecRel st' b bc where
  types := h.types.mono (fun _ _ => MIndTypeRecRel.ext hx)
  ctors := h.ctors.mono (fun _ _ => MIndCtorRecRel.ext hx)
  recs := h.recs.mono (fun _ _ => MIndRecRecRel.ext hx)

/-- con-leche: none — **the parse-state relation survives an append**: the
fact the streaming fold's induction rests on, and the reason a line's theorem
may say `StateDRel s'.store sd' sc'` while the next line's hypothesis is
`StateDRel s''.store sd' sc'`.  Eighteen clauses, one `Bridge/Rel.lean`
`…_ext` lemma each; the five scalar clauses are the hypothesis itself. -/
theorem StateDRel.ext {st st' : EStore} (hx : Ext st st') {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (h : StateDRel st sd sc) :
    StateDRel st' sd sc where
  names := h.names.mono (fun _ _ hd => denoteN_ext hd hx)
  levels := h.levels.mono (fun _ _ hd => denoteL_ext hd hx)
  exprs := h.exprs.mono (fun _ _ hd => denote_ext hd hx)
  decls := denoteDeclArray_ext hx h.decls
  projOwners := h.projOwners.mono hx (fun _ _ ho => ProjRecOwnerRel.ext hx ho)
  projLevels := h.projLevels.mono hx (fun _ _ hd => denoteL_ext hd hx)
  projRewrites := denoteNListE_ext hx _ _ h.projRewrites
  constTypes := h.constTypes.mono hx
    (fun _ _ hp => ⟨denoteNListE_ext hx _ _ hp.1, denote_ext hp.2 hx⟩)
  heights := h.heights.mono hx (fun _ _ hp => hp)
  inModel := h.inModel
  inModelled := denoteNListE_ext hx _ _ h.inModelled
  genRecords := h.genRecords
  genOwner := h.genOwner.mono hx (fun _ _ hd => denoteN_ext hd hx)
  inModelGen := h.inModelGen.mono
    (fun _ _ hp => ⟨hp.1, denoteDeclArray_ext hx hp.2⟩)
  indCount := h.indCount
  indBlocks := h.indBlocks.mono hx (fun _ _ hb => BlockRecRel.ext hx hb)
  inModelCensus := h.inModelCensus
  inModelDeclined := h.inModelDeclined.mono
    (fun _ _ hp => ⟨denoteN_ext hp.1 hx, hp.2⟩)

/-- con-leche: none — the same for the parse RESULT. -/
theorem ParseResultRel.ext {st st' : EStore} (hx : Ext st st') {r : ParseResultD}
    {rc : ConLeche.Frontend.ParseResultD} (h : ParseResultRel st r rc) :
    ParseResultRel st' r rc where
  decls := denoteDeclArray_ext hx h.decls
  projRewrites := denoteNListE_ext hx _ _ h.projRewrites
  inModelled := denoteNListE_ext hx _ _ h.inModelled
  genRecords := h.genRecords
  genOwner := h.genOwner.mono hx (fun _ _ hd => denoteN_ext hd hx)
  inModelGen := h.inModelGen.mono
    (fun _ _ hp => ⟨hp.1, denoteDeclArray_ext hx hp.2⟩)
  inModelDeclined := h.inModelDeclined.mono
    (fun _ _ hp => ⟨denoteN_ext hp.1 hx, hp.2⟩)

/-! ## Persistence

`Bridge/Checker/Capstone.lean`'s second frontend obligation: every handle the
parse holds is in the persistent tier.  `Bridge/Promote/Pers.lean`'s `Pers…`
vocabulary, lifted to the parse state — the clause that matters is the one the
FOLD reads, which is `decls` and nothing else; the three tables are carried so
that the induction has one invariant rather than two. -/

/-- con-leche: none — every declaration record the parse state holds is
persistent (`Bridge/Promote/Pers.lean`'s `PersDecl`).  This is the clause
`Bridge/Checker/Capstone.lean` names `hpd`. -/
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
