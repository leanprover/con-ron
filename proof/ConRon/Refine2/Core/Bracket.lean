/-
# `ConRon.Refine2.Core.Bracket` — the per-declaration bracket, for Theorem 2

**Task #97-P5-Bracket** (DESIGN.md §8.2).  `arena::core::{flush_caches,
enter_scratch, drop_scratch}` against `Arena/Core.lean`'s `flushCaches` /
`enterScratch` / `dropScratch`, and the ONE composite lemma the checker tier's
three bracketed steps — `check_decl_step`, `annot_step`, `check_pending` —
consume.

## Why this is one bracket lemma and not three `SimS`s

`Refine2/Shape.lean`'s module note lists the three primitives under `SimS`,
the total state-threading shape.  **`drop_scratch` cannot be a `SimS`**, and
neither can `enter_scratch`: `SimS` demands `Ext lst.store lst'.store` —
denotation preservation — and both ends of the bracket *un-decode* handles.
`enterScratch` replaces the scratch tier by the empty one, so a handle that
decoded through a live scratch tier stops decoding; `dropScratch` does the
same and turns the flag off as well.

What IS true is the bracket as a whole, and the side condition is the one
sentence of DESIGN §8.3's tier discipline:

> a bracket is entered at a declaration BOUNDARY — a store whose scratch tier
> is closed — and it leaves one behind.

`ScratchClosed st` below is that boundary, spelled as *`dropScratch` is a
fixpoint of the store*; `ext_bracket` is the lemma, and the shape is

    ScratchClosed a → StoreWF b → Ext a.enableScratch b → Ext a b.dropScratch

— the `Ext` the bracketed step owes, produced from the `Ext` its BODY
delivers.  `Ext` alone does not compose across the drop and cannot: a
persistent node whose child is a scratch handle denotes before the drop and
not after, and only the tier discipline rules that out.  That is why
`StoreWF b` — **the TWIN store's well-formedness, Theorem 1's invariant** —
is a hypothesis here.  Task #97-P5-Bracket's §1 in DESIGN.md is the finding
that goes with it; in one line: *Theorem 2's `Ext` conjunct is not a free
rider at the bracket, and the three bracketed statements are false without
this hypothesis.*

## What each primitive really claims

| primitive | relation and invariant | `Ext` |
|---|---|---|
| `flush_caches` | transported, caches empty on both sides | `Ext.refl` — the store is untouched |
| `enter_scratch` | transported, memos and scratch tier empty on both sides | only `Ext a a.enableScratch`, and only at a CLOSED `a` |
| `drop_scratch` | transported, caches and scratch tier empty on both sides | **none** — this is the un-decoding step |

So the three lemmas below hand back the twin's post-state EXPLICITLY rather
than existentially (`SimS` quantifies it), because the bracket has to name it
to chain the three store facts across it.

**Superseded (task #97-T2-LOCKSTEP).**  The paragraphs above describe the old
shape, where Theorem 2 carried `Ext`.  Theorem 2 is lockstep now: the three
primitives are the plain `SimS₀` lemmas at the end of this file, and
`ScratchClosed`/`ext_bracket` remain only as twin-store facts.
-/
import ConRon.Refine2.Specs
import ConRon.Arena.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn toFun sl_v)

/-! ## The declaration boundary

`dropScratch` is a fixpoint of the store: the flag is off AND the scratch
tier is literally empty.  Stated as the fixpoint rather than as four flag
equations because that is the form every proof below wants — one `rw` turns
a `dropScratch` fact into a fact about the store itself — and because it is
exactly what the previous bracket left behind. -/

/-- con-leche: none — the name store is at a declaration boundary. -/
def NScratchClosed (st : NStore) : Prop := st.dropScratch = st
/-- con-leche: none — the level store is at a declaration boundary. -/
def LScratchClosed (st : LStore) : Prop := st.dropScratch = st
/-- con-leche: none — the level-list store is at a declaration boundary. -/
def LsScratchClosed (st : LsStore) : Prop := st.dropScratch = st
/-- con-leche: none — **the arena is at a declaration boundary**: the scratch
tier is closed and empty, which is what the previous `dropScratch` left. -/
def ScratchClosed (st : EStore) : Prop := st.dropScratch = st

theorem ScratchClosed.lss {st : EStore} (h : ScratchClosed st) :
    LsScratchClosed st.lss := congrArg EStore.lss h

theorem LsScratchClosed.ls {st : LsStore} (h : LsScratchClosed st) :
    LScratchClosed st.ls := congrArg LsStore.ls h

theorem LScratchClosed.ns {st : LStore} (h : LScratchClosed st) :
    NScratchClosed st.ns := congrArg LStore.ns h

/-! ### It is what `StoreWF` plus a closed flag says

`Arena/WF.lean`'s `NWFAt.scrOff` / `LWFAt.scrOff` / `LsWFAt.scrOff` /
`EWFAt.scrOff` are *"the flag off means the tier is empty"* and the `sync`
fields carry the flag down through the four stores, so the boundary does not
have to be assumed separately from the twin store's well-formedness: it is
`StoreWF` and one flag. -/

theorem NScratchClosed.of_wf {st : NStore} (h : NStoreWF st)
    (hoff : st.scratchOn = false) : NScratchClosed st := by
  obtain ⟨rk, h⟩ := h
  have h1 : st.scr = NTables.empty := h.scrOff hoff
  obtain ⟨p, s, f⟩ := st
  subst h1; subst hoff; rfl

theorem LScratchClosed.of_wf {st : LStore} (h : LStoreWF st)
    (hoff : st.scratchOn = false) : LScratchClosed st := by
  obtain ⟨rk, h⟩ := h
  have hns : NScratchClosed st.ns :=
    NScratchClosed.of_wf h.ns (by rw [← h.sync]; exact hoff)
  have h1 : st.scr = LTables.empty := h.scrOff hoff
  show LStore.dropScratch st = st
  rw [LStore.dropScratch, show st.ns.dropScratch = st.ns from hns, h1.symm,
    hoff.symm]

theorem LsScratchClosed.of_wf {st : LsStore} (h : LsStoreWF st)
    (hoff : st.scratchOn = false) : LsScratchClosed st := by
  have hls : LScratchClosed st.ls :=
    LScratchClosed.of_wf h.ls (by rw [← h.sync]; exact hoff)
  have h1 : st.scr = LsTables.empty := h.scrOff hoff
  show LsStore.dropScratch st = st
  rw [LsStore.dropScratch, show st.ls.dropScratch = st.ls from hls, h1.symm,
    hoff.symm]

theorem ScratchClosed.of_wf {st : EStore} (h : StoreWF st)
    (hoff : st.scratchOn = false) : ScratchClosed st := by
  obtain ⟨rk, h⟩ := h
  have hlss : LsScratchClosed st.lss :=
    LsScratchClosed.of_wf h.lss (by rw [← h.sync]; exact hoff)
  have h1 : st.scr = ETables.empty := h.scrOff hoff
  show EStore.dropScratch st = st
  rw [EStore.dropScratch, show st.lss.dropScratch = st.lss from hlss, h1.symm,
    hoff.symm]


/-! ### The flag, and what denotes at a boundary

At a boundary the scratch tier answers `none` at every handle, so only a
PERSISTENT handle denotes.  That is the half of the bracket `Ext` that
`dropScratch` needs and the reason the side condition is about the store the
bracket is ENTERED at. -/

theorem NScratchClosed.off {st : NStore} (h : NScratchClosed st) :
    st.scratchOn = false := (congrArg NStore.scratchOn h).symm
theorem LScratchClosed.off {st : LStore} (h : LScratchClosed st) :
    st.scratchOn = false := (congrArg LStore.scratchOn h).symm
theorem LsScratchClosed.off {st : LsStore} (h : LsScratchClosed st) :
    st.scratchOn = false := (congrArg LsStore.scratchOn h).symm
theorem ScratchClosed.off {st : EStore} (h : ScratchClosed st) :
    st.scratchOn = false := (congrArg EStore.scratchOn h).symm

theorem NScratchClosed.pers {st : NStore} (h : NScratchClosed st) {i : NIdx}
    {x : ConLeche.Name} (hd : denoteN st i = some x) : i.isPersistent = true := by
  by_contra hp
  simp only [Bool.not_eq_true] at hp
  have hv : st.view i = none := by simp [NStore.view, hp, h.off]
  simp only [denoteN, denoteNAux, hv] at hd
  simp at hd

theorem LScratchClosed.pers {st : LStore} (h : LScratchClosed st) {i : LIdx}
    {x : ConLeche.Level} (hd : denoteL st i = some x) : i.isPersistent = true := by
  by_contra hp
  simp only [Bool.not_eq_true] at hp
  have hv : st.view i = none := by simp [LStore.view, hp, h.off]
  simp only [denoteL, denoteLAux, hv] at hd
  simp at hd

theorem LsScratchClosed.pers {st : LsStore} (h : LsScratchClosed st) {i : LsIdx}
    {x : List ConLeche.Level} (hd : denoteLs st i = some x) :
    i.isPersistent = true := by
  by_contra hp
  simp only [Bool.not_eq_true] at hp
  have hv : st.view i = none := by simp [LsStore.view, hp, h.off]
  simp only [denoteLs, hv] at hd
  simp at hd

theorem ScratchClosed.pers {st : EStore} (h : ScratchClosed st) {i : EIdx}
    {x : ConLeche.Expr} (hd : denoteE st i = some x) : i.isPersistent = true := by
  by_contra hp
  simp only [Bool.not_eq_true] at hp
  have hv : denoteE st i = none := h ▸ denoteE_dropScratch_scr st hp
  rw [hv] at hd
  simp at hd

/-! ## The bracket opened: `enterScratch` at a boundary

`Arena/WFProofs.lean`'s `denote…_enableScratch_eq` family says the two ends
of the bracket read back IDENTICALLY — the observation task #97-P3-Checker
paid for in `Bridge/Promote/Pers.lean` and the one that makes this side free.
At a boundary `st.dropScratch` is `st`, so opening the tier changes no
denotation at all and `Ext` is an equality rather than an implication. -/

theorem NScratchClosed.ext {st : NStore} (h : NScratchClosed st) :
    NExt st st.enableScratch := by
  intro i n hd
  rw [denoteN_enableScratch_eq, show st.dropScratch = st from h]; exact hd

theorem LScratchClosed.ext {st : LStore} (h : LScratchClosed st) :
    LExt st st.enableScratch := by
  refine ⟨h.ns.ext, ?_⟩
  intro i u hd
  rw [show st.enableScratch = st.enableScratch from rfl, denoteL_enableScratch_eq,
    show st.dropScratch = st from h]
  exact hd

theorem LsScratchClosed.ext {st : LsStore} (h : LsScratchClosed st) :
    LsExt st st.enableScratch := by
  refine ⟨h.ls.ext, ?_⟩
  intro i us hd
  rw [denoteLs_enableScratch_eq, show st.dropScratch = st from h]; exact hd

/-- con-leche: none — **the bracket opened**: at a declaration boundary
`enterScratch` preserves every denotation. -/
theorem ScratchClosed.ext {st : EStore} (h : ScratchClosed st) :
    Ext st st.enableScratch := by
  refine ⟨h.lss.ext, ?_⟩
  intro i e hd
  rw [denoteE_enableScratch_eq, show st.dropScratch = st from h]; exact hd

/-! ## The bracket closed: `dropScratch` after a body

This is the half that is NOT free, and the hypothesis is `StoreWF b` — the
TWIN store's well-formedness at the inner end of the bracket, which is
Theorem 1's invariant and which Theorem 2's `AStateRel`/`AStateInv` do not
carry.  It cannot be dropped: without the tier discipline a persistent node
may name a scratch child, and then it denotes before the drop and not after.
DESIGN §… task #97-P5-Bracket §1 is the finding. -/

theorem ext_dropScratch {a b : EStore} (hc : ScratchClosed a) (hwf : StoreWF b)
    (h : Ext a b) : Ext a b.dropScratch := by
  obtain ⟨rk, hwa⟩ := hwf
  have hwfE : StoreWF b := ⟨rk, hwa⟩
  have hlss : LsStoreWF b.lss := hwa.lss
  have hls : LStoreWF b.lss.ls := hlss.ls
  have hns : NStoreWF b.lss.ls.ns := by obtain ⟨rkl, hl⟩ := hls; exact hl.ns
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i n hd
    exact (NStore.dropScratch_spec hns).2.2 i n (hc.lss.ls.ns.pers hd)
      (h.lss.ls.ns i n hd)
  · intro i u hd
    exact (LStore.dropScratch_spec hls).2.2 i u (hc.lss.ls.pers hd)
      (h.lss.ls.lvl i u hd)
  · intro i us hd
    exact (LsStore.dropScratch_spec hlss).2.2 i us (hc.lss.pers hd)
      (h.lss.lst i us hd)
  · intro i e hd
    exact EStore.dropScratch_denote_pers hwfE (hc.pers hd) (h.expr i e hd)

/-- con-leche: none — **THE BRACKET, as an `Ext`.**  A step entered at a
declaration boundary, whose body delivers `Ext` from the opened store, hands
back `Ext` from the boundary — even though neither end of the bracket does on
its own.  This is the lemma the checker tier's three bracketed steps consume,
and DESIGN §8.2's `Ext` conjunct at those three statements is exactly it. -/
theorem ext_bracket {a b : EStore} (hc : ScratchClosed a) (hwf : StoreWF b)
    (h : Ext a.enableScratch b) : Ext a b.dropScratch :=
  ext_dropScratch hc hwf (Ext.trans hc.ext h)

/-! ## The tier reset, once

`arena::store::Tbl::reset` is `rows := Vec::new()` and `cons := reset_map`, so
a reset table is the twin's `Tbl.empty` at every clause of `TblRel` and
`TblInv`: two `rfl`s for the node and derived columns,
`Refine/HashMap2WF.lean`'s `RelOn_empty` / `KeysOk_of_nil` for the cons table,
and a vacuous `nodesP`.  Once here, twenty times below. -/

theorem tbl_reset_inv {A I D : Type} [DecidableEq A]
    {P : A → Prop}
    {hA : ron.hashmap.Hashable A} {eq2 : ron.hashmap.Eq2 A}
    {dupA : ron.hashmap.Dup A} {dupI : ron.hashmap.Dup I}
    {dupD : ron.hashmap.Dup D} {derDef : arena.store.DerDefault D}
    {rt rt' : arena.store.Tbl A I D} (hinv : Inv hA rt.cons)
    (h : arena.store.Tbl.reset hA eq2 dupA dupI dupD derDef rt = ok rt') :
    TblInv hA P rt' := by
  rw [arena.store.Tbl.reset] at h
  obtain ⟨hm, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rt' = ⟨alloc.vec.Vec.new (A × D), hm⟩ := (Result.ok_injective h).symm
  subst hst
  obtain ⟨hinv', hnil, -⟩ :=
    ConRon.Refine.HashMap2.clear_fit_refines hinv
      (by rw [arena.core_state.reset_map] at hhm; exact hhm)
  exact ⟨hinv', ConRon.Refine.HashMap2.KeysOk_of_nil hnil, by simp⟩

theorem tbl_reset_rel {A I D α ι δ ω : Type} [DecidableEq A] [BEq α] [Hashable α]
    {P : A → Prop} {absA : A → α} {absI : I → ι} {absD : D → δ} {obsD : δ → ω}
    {hA : ron.hashmap.Hashable A} {eq2 : ron.hashmap.Eq2 A}
    {dupA : ron.hashmap.Dup A} {dupI : ron.hashmap.Dup I}
    {dupD : ron.hashmap.Dup D} {derDef : arena.store.DerDefault D}
    {rt rt' : arena.store.Tbl A I D} (hinv : Inv hA rt.cons)
    (h : arena.store.Tbl.reset hA eq2 dupA dupI dupD derDef rt = ok rt') :
    TblRel P absA absI absD obsD rt' Tbl.empty := by
  rw [arena.store.Tbl.reset] at h
  obtain ⟨hm, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rt' = ⟨alloc.vec.Vec.new (A × D), hm⟩ := (Result.ok_injective h).symm
  subst hst
  obtain ⟨-, -, hnone⟩ :=
    ConRon.Refine.HashMap2.clear_fit_refines hinv
      (by rw [arena.core_state.reset_map] at hhm; exact hhm)
  exact ⟨rfl, rfl, ConRon.Refine.HashMap2.RelOn_empty hnone⟩

/-! ## The four tiers reset

`ETables::reset` and its three siblings are `Tbl::reset` at each constructor,
so each is `tbl_reset` per field and a record instance — the shape
`Refine2/Specs.lean`'s memo writes already use, and the reason the relations
are RECORDS. -/

theorem ntables_reset {rt rt' : arena.store.NTables}
    (hinv : NTablesInv rt) (h : arena.store.NTables.reset rt = ok rt') :
    NTablesRel rt' NTables.empty ∧ NTablesInv rt' := by
  rw [arena.store.NTables.reset] at h
  obtain ⟨t0, e0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t1, e1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t2, e2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rt' = ⟨t0, t1, t2⟩ :=
    (Result.ok_injective h).symm
  subst hst
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  exacts [tbl_reset_rel hinv.anons.inv e0,
    tbl_reset_rel hinv.strs.inv e1,
    tbl_reset_rel hinv.nums.inv e2,
    tbl_reset_inv hinv.anons.inv e0,
    tbl_reset_inv hinv.strs.inv e1,
    tbl_reset_inv hinv.nums.inv e2]

theorem ltables_reset {rt rt' : arena.store.LTables}
    (hinv : LTablesInv rt) (h : arena.store.LTables.reset rt = ok rt') :
    LTablesRel rt' LTables.empty ∧ LTablesInv rt' := by
  rw [arena.store.LTables.reset] at h
  obtain ⟨t0, e0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t1, e1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t2, e2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t3, e3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t4, e4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rt' = ⟨t0, t1, t2, t3, t4⟩ :=
    (Result.ok_injective h).symm
  subst hst
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  exacts [tbl_reset_rel hinv.zeros.inv e0,
    tbl_reset_rel hinv.succs.inv e1,
    tbl_reset_rel hinv.maxs.inv e2,
    tbl_reset_rel hinv.imaxs.inv e3,
    tbl_reset_rel hinv.params.inv e4,
    tbl_reset_inv hinv.zeros.inv e0,
    tbl_reset_inv hinv.succs.inv e1,
    tbl_reset_inv hinv.maxs.inv e2,
    tbl_reset_inv hinv.imaxs.inv e3,
    tbl_reset_inv hinv.params.inv e4]

theorem lstables_reset {rt rt' : arena.store.LsTables}
    (hinv : LsTablesInv rt) (h : arena.store.LsTables.reset rt = ok rt') :
    LsTablesRel rt' LsTables.empty ∧ LsTablesInv rt' := by
  rw [arena.store.LsTables.reset] at h
  obtain ⟨t0, e0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rt' = ⟨t0⟩ :=
    (Result.ok_injective h).symm
  subst hst
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  exacts [tbl_reset_rel hinv.lists.inv e0,
    tbl_reset_inv hinv.lists.inv e0]

theorem etables_reset {rt rt' : arena.store.ETables}
    (hinv : ETablesInv rt) (h : arena.store.ETables.reset rt = ok rt') :
    ETablesRel rt' ETables.empty ∧ ETablesInv rt' := by
  rw [arena.store.ETables.reset] at h
  obtain ⟨t0, e0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t1, e1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t2, e2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t3, e3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t4, e4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t5, e5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t6, e6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t7, e7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t8, e8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t9, e9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t10, e10, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rt' = ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ :=
    (Result.ok_injective h).symm
  subst hst
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  exacts [tbl_reset_rel hinv.bvars.inv e0,
    tbl_reset_rel hinv.fvars.inv e1,
    tbl_reset_rel hinv.sorts.inv e2,
    tbl_reset_rel hinv.consts.inv e3,
    tbl_reset_rel hinv.apps.inv e4,
    tbl_reset_rel hinv.lams.inv e5,
    tbl_reset_rel hinv.foralls.inv e6,
    tbl_reset_rel hinv.lets.inv e7,
    tbl_reset_rel hinv.lits.inv e8,
    tbl_reset_rel hinv.projs.inv e9,
    tbl_reset_rel hinv.bms.inv e10,
    tbl_reset_inv hinv.bvars.inv e0,
    tbl_reset_inv hinv.fvars.inv e1,
    tbl_reset_inv hinv.sorts.inv e2,
    tbl_reset_inv hinv.consts.inv e3,
    tbl_reset_inv hinv.apps.inv e4,
    tbl_reset_inv hinv.lams.inv e5,
    tbl_reset_inv hinv.foralls.inv e6,
    tbl_reset_inv hinv.lets.inv e7,
    tbl_reset_inv hinv.lits.inv e8,
    tbl_reset_inv hinv.projs.inv e9,
    tbl_reset_inv hinv.bms.inv e10]



/-! ## The two store states, and the moves between them (task #98-FREEZE)

A Rust store is OWNED (scratch off, read through the empty stand-in tier,
which is not `frozen`: the parse, the setup, between phase A's brackets) or
FROZEN (scratch on, its persistent tables moved into a `frozen` `PersTier`
that every read of it goes through: inside a declaration bracket, and a
phase-B worker for its whole life).  `freeze` moves the four tables out and
opens the scratch tiers empty; `thaw` puts a tier back and drops them;
`clear_scratch` empties the scratch tiers and touches nothing else.  The twin
has one store and no tier: its `enableScratch`/`dropScratch` are the scratch
halves alone, so the relation moves its READER at a freeze and a thaw — from
the owned store's stand-in to the tier handed out, and back. -/

/-- The persistent tier `freeze` moves out of a store: its four own
persistent tables, `frozen`. -/
def tierOf (ar : arena.store.EStore) : arena.store.PersTier :=
  { frozen := true, n := ar.lss.ls.ns.pers, l := ar.lss.ls.pers, ls := ar.lss.pers,
    e := ar.pers }

theorem nstore_freeze_eq {rs : arena.store.NStore} {t rs'}
    (h : arena.store.NStore.freeze rs = ok (t, rs')) :
    ∃ e s, arena.store.NTables.reset rs.scr = ok s ∧ t = rs.pers ∧
      rs' = { pers := e, scr := s, scratch_on := true } := by
  rw [arena.store.NStore.freeze] at h
  obtain ⟨e, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [core.mem.replace] at h
  obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp only [Prod.mk.injEq] at h'
  exact ⟨e, s, hs, h'.1.symm, h'.2.symm⟩

theorem lstore_freeze_eq {rs : arena.store.LStore} {t rs'}
    (h : arena.store.LStore.freeze rs = ok (t, rs')) :
    ∃ e s, arena.store.LTables.reset rs.scr = ok s ∧ t = rs.pers ∧
      rs' = { rs with pers := e, scr := s, scratch_on := true } := by
  rw [arena.store.LStore.freeze] at h
  obtain ⟨e, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [core.mem.replace] at h
  obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp only [Prod.mk.injEq] at h'
  exact ⟨e, s, hs, h'.1.symm, h'.2.symm⟩

theorem lsstore_freeze_eq {rs : arena.store.LsStore} {t rs'}
    (h : arena.store.LsStore.freeze rs = ok (t, rs')) :
    ∃ e s, arena.store.LsTables.reset rs.scr = ok s ∧ t = rs.pers ∧
      rs' = { rs with pers := e, scr := s, scratch_on := true } := by
  rw [arena.store.LsStore.freeze] at h
  obtain ⟨e, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [core.mem.replace] at h
  obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp only [Prod.mk.injEq] at h'
  exact ⟨e, s, hs, h'.1.symm, h'.2.symm⟩

/-- **`EStore::freeze` of an owned store**: it hands back the store's own four
tables as a `frozen` tier, and the frozen store read through that tier is
related to the twin store with its scratch tier opened — the persistent arm
is read through the tier now instead of the store, and it is the same four
tables.  `hpers`: the store was owned, read through a stand-in that is not
`frozen`. -/
theorem estore_freeze {pers} {rs : arena.store.EStore} {ls : EStore} {tier rs'}
    (hrel : StoreRel pers rs ls) (hinv : StoreInv pers rs) (hpers : pers.frozen = false)
    (h : arena.store.EStore.freeze rs = ok (tier, rs')) :
    tier = tierOf rs ∧ StoreRel tier rs' ls.enableScratch ∧ StoreInv tier rs' := by
  rw [arena.store.EStore.freeze] at h
  obtain ⟨⟨n, n1⟩, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨l, l1⟩, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨lt, ls1⟩, hls, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e0, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [core.mem.replace] at h
  obtain ⟨es, hes, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  obtain ⟨ne, ns, hns, rfl, rfl⟩ := nstore_freeze_eq hn
  obtain ⟨le, lsc, hlsc, rfl, rfl⟩ := lstore_freeze_eq hl
  obtain ⟨lse, lssc, hlssc, rfl, rfl⟩ := lsstore_freeze_eq hls
  have pN : rPersN pers rs.lss.ls.ns = rs.lss.ls.ns.pers := by unfold rPersN; rw [hpers]; rfl
  have pL : rPersL pers rs.lss.ls = rs.lss.ls.pers := by unfold rPersL; rw [hpers]; rfl
  have pLs : rPersLs pers rs.lss = rs.lss.pers := by unfold rPersLs; rw [hpers]; rfl
  have pE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hpers]; rfl
  obtain ⟨rN, iN⟩ := ntables_reset hinv.lss.lvl.ns.scrt hns
  obtain ⟨rL, iL⟩ := ltables_reset hinv.lss.lvl.scrt hlsc
  obtain ⟨rLs, iLs⟩ := lstables_reset hinv.lss.scrt hlssc
  obtain ⟨rE, iE⟩ := etables_reset hinv.scrt hes
  refine ⟨rfl, ⟨⟨⟨⟨?_, rN, rfl⟩, ?_, rL, rfl⟩, ?_, rLs, rfl⟩, ?_, rE, rfl⟩,
    ⟨⟨⟨⟨?_, iN, fun _ => rfl⟩, ?_, iL, fun _ => rfl⟩, ?_, iLs, fun _ => rfl⟩, ?_, iE,
      fun _ => rfl⟩⟩
  · show NTablesRel rs.lss.ls.ns.pers ls.lss.ls.ns.pers
    rw [← pN]; exact hrel.lss.lvl.ns.perst
  · show LTablesRel rs.lss.ls.pers ls.lss.ls.pers
    rw [← pL]; exact hrel.lss.lvl.perst
  · show LsTablesRel rs.lss.pers ls.lss.pers
    rw [← pLs]; exact hrel.lss.perst
  · show ETablesRel rs.pers ls.pers
    rw [← pE]; exact hrel.perst
  · show NTablesInv rs.lss.ls.ns.pers
    rw [← pN]; exact hinv.lss.lvl.ns.perst
  · show LTablesInv rs.lss.ls.pers
    rw [← pL]; exact hinv.lss.lvl.perst
  · show LsTablesInv rs.lss.pers
    rw [← pLs]; exact hinv.lss.perst
  · show ETablesInv rs.pers
    rw [← pE]; exact hinv.perst

/-- **`EStore::thaw` of a store read through a frozen tier**: the tier goes
back, and the owned store is related, through any stand-in that is not
`frozen`, to the twin store with its scratch tier dropped. -/
theorem estore_thaw {tier} {rs : arena.store.EStore} {ls : EStore} {rs'}
    (hrel : StoreRel tier rs ls) (hinv : StoreInv tier rs) (htf : tier.frozen = true)
    (h : arena.store.EStore.thaw rs tier = ok rs') {pers : arena.store.PersTier}
    (hpers : pers.frozen = false) :
    StoreRel pers rs' ls.dropScratch ∧ StoreInv pers rs' := by
  rw [arena.store.EStore.thaw] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨lt, hls, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨es, hes, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := (Result.ok_injective h).symm
  rw [arena.store.NStore.thaw] at hn
  obtain ⟨ns, hns, hn⟩ := ConRon.Refine.bind_eq_ok_iff.mp hn
  obtain rfl := (Result.ok_injective hn).symm
  rw [arena.store.LStore.thaw] at hl
  obtain ⟨lsc, hlsc, hl⟩ := ConRon.Refine.bind_eq_ok_iff.mp hl
  obtain rfl := (Result.ok_injective hl).symm
  rw [arena.store.LsStore.thaw] at hls
  obtain ⟨lssc, hlssc, hls⟩ := ConRon.Refine.bind_eq_ok_iff.mp hls
  obtain rfl := (Result.ok_injective hls).symm
  have pN : rPersN tier rs.lss.ls.ns = tier.n := by unfold rPersN; rw [htf]; rfl
  have pL : rPersL tier rs.lss.ls = tier.l := by unfold rPersL; rw [htf]; rfl
  have pLs : rPersLs tier rs.lss = tier.ls := by unfold rPersLs; rw [htf]; rfl
  have pE : rPersE tier rs = tier.e := by unfold rPersE; rw [htf]; rfl
  obtain ⟨rN, iN⟩ := ntables_reset hinv.lss.lvl.ns.scrt hns
  obtain ⟨rL, iL⟩ := ltables_reset hinv.lss.lvl.scrt hlsc
  obtain ⟨rLs, iLs⟩ := lstables_reset hinv.lss.scrt hlssc
  obtain ⟨rE, iE⟩ := etables_reset hinv.scrt hes
  have hoff : ∀ {b : Bool}, pers.frozen = true → b = true := fun h => by
    rw [hpers] at h; cases h
  refine ⟨⟨⟨⟨⟨?_, rN, rfl⟩, ?_, rL, rfl⟩, ?_, rLs, rfl⟩, ?_, rE, rfl⟩,
    ⟨⟨⟨⟨?_, iN, hoff⟩, ?_, iL, hoff⟩, ?_, iLs, hoff⟩, ?_, iE, hoff⟩⟩
  · show NTablesRel (rPersN pers _) ls.lss.ls.ns.pers
    unfold rPersN; rw [hpers]; rw [← pN]; exact hrel.lss.lvl.ns.perst
  · show LTablesRel (rPersL pers _) ls.lss.ls.pers
    unfold rPersL; rw [hpers]; rw [← pL]; exact hrel.lss.lvl.perst
  · show LsTablesRel (rPersLs pers _) ls.lss.pers
    unfold rPersLs; rw [hpers]; rw [← pLs]; exact hrel.lss.perst
  · show ETablesRel (rPersE pers _) ls.pers
    unfold rPersE; rw [hpers]; rw [← pE]; exact hrel.perst
  · show NTablesInv (rPersN pers _)
    unfold rPersN; rw [hpers]; rw [← pN]; exact hinv.lss.lvl.ns.perst
  · show LTablesInv (rPersL pers _)
    unfold rPersL; rw [hpers]; rw [← pL]; exact hinv.lss.lvl.perst
  · show LsTablesInv (rPersLs pers _)
    unfold rPersLs; rw [hpers]; rw [← pLs]; exact hinv.lss.perst
  · show ETablesInv (rPersE pers _)
    unfold rPersE; rw [hpers]; rw [← pE]; exact hinv.perst

/-- **`EStore::clear_scratch`**: the four scratch tiers emptied, the flags and
the persistent arm untouched — so, through the same tier, the store is related
to ANY twin store with the same persistent tables whose scratch tier is empty
and whose flags are the port's.  Both the record bracket's halves are this
lemma: opening against the twin's `enableScratch`, closing against its
`dropScratch` read with its scratch tier re-opened. -/
theorem estore_clear {tier} {rs : arena.store.EStore} {ls ls' : EStore} {rs'}
    (hrel : StoreRel tier rs ls) (hinv : StoreInv tier rs)
    (hpN : ls'.lss.ls.ns.pers = ls.lss.ls.ns.pers) (hpL : ls'.lss.ls.pers = ls.lss.ls.pers)
    (hpLs : ls'.lss.pers = ls.lss.pers) (hpE : ls'.pers = ls.pers)
    (hsN : ls'.lss.ls.ns.scr = NTables.empty) (hsL : ls'.lss.ls.scr = LTables.empty)
    (hsLs : ls'.lss.scr = LsTables.empty) (hsE : ls'.scr = ETables.empty)
    (hoN : ls'.lss.ls.ns.scratchOn = rs.lss.ls.ns.scratch_on)
    (hoL : ls'.lss.ls.scratchOn = rs.lss.ls.scratch_on)
    (hoLs : ls'.lss.scratchOn = rs.lss.scratch_on) (hoE : ls'.scratchOn = rs.scratch_on)
    (h : arena.store.EStore.clear_scratch rs = ok rs') :
    StoreRel tier rs' ls' ∧ StoreInv tier rs' := by
  rw [arena.store.EStore.clear_scratch] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨lt, hls, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨es, hes, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := (Result.ok_injective h).symm
  rw [arena.store.NStore.clear_scratch] at hn
  obtain ⟨ns, hns, hn⟩ := ConRon.Refine.bind_eq_ok_iff.mp hn
  obtain rfl := (Result.ok_injective hn).symm
  rw [arena.store.LStore.clear_scratch] at hl
  obtain ⟨lsc, hlsc, hl⟩ := ConRon.Refine.bind_eq_ok_iff.mp hl
  obtain rfl := (Result.ok_injective hl).symm
  rw [arena.store.LsStore.clear_scratch] at hls
  obtain ⟨lssc, hlssc, hls⟩ := ConRon.Refine.bind_eq_ok_iff.mp hls
  obtain rfl := (Result.ok_injective hls).symm
  obtain ⟨rN, iN⟩ := ntables_reset hinv.lss.lvl.ns.scrt hns
  obtain ⟨rL, iL⟩ := ltables_reset hinv.lss.lvl.scrt hlsc
  obtain ⟨rLs, iLs⟩ := lstables_reset hinv.lss.scrt hlssc
  obtain ⟨rE, iE⟩ := etables_reset hinv.scrt hes
  refine ⟨⟨⟨⟨⟨?_, ?_, hoN⟩, ?_, ?_, hoL⟩, ?_, ?_, hoLs⟩, ?_, ?_, hoE⟩,
    ⟨⟨⟨⟨hinv.lss.lvl.ns.perst, iN, hinv.lss.lvl.ns.frz⟩, hinv.lss.lvl.perst, iL,
      hinv.lss.lvl.frz⟩, hinv.lss.perst, iLs, hinv.lss.frz⟩, hinv.perst, iE, hinv.frz⟩⟩
  · rw [hpN]; exact hrel.lss.lvl.ns.perst
  · rw [hsN]; exact rN
  · rw [hpL]; exact hrel.lss.lvl.perst
  · rw [hsL]; exact rL
  · rw [hpLs]; exact hrel.lss.perst
  · rw [hsLs]; exact rLs
  · rw [hpE]; exact hrel.perst
  · rw [hsE]; exact rE

/-! ## The per-call memos and the per-declaration caches, reset

`arena::core_state::reset_map` is `HashMap2::clear_fit` (task #97-P6-1: the
bucket array is kept, the entries are not), so a reset table is `∅` for
`RelOn`, keeps `Inv` and has an empty slot list — the third is what the three
readback memos' value-well-formedness clauses of `CachesInv` need, and it is
why this is not simply `Refine2/Specs.lean`'s `memo_clear_step`. -/

theorem reset_map_rel {K K' V V' : Type} [DecidableEq K] [BEq K'] [Hashable K']
    {HashableInst : ron.hashmap.Hashable K} {m m' : ron.hashmap2.HashMap2 K V}
    {absK : K → K'} {absV : V → V'} (hinv : Inv HashableInst m)
    (h : arena.core_state.reset_map m = ok m') :
    RelOn (fun _ => True) m' (∅ : _root_.Std.HashMap K' V') absK absV := by
  rw [arena.core_state.reset_map] at h
  exact ConRon.Refine.HashMap2.RelOn_empty
    (ConRon.Refine.HashMap2.clear_fit_refines hinv h).2.2

theorem reset_map_inv {K V : Type} [DecidableEq K]
    {HashableInst : ron.hashmap.Hashable K} {m m' : ron.hashmap2.HashMap2 K V}
    (hinv : Inv HashableInst m) (h : arena.core_state.reset_map m = ok m') :
    Inv HashableInst m' := by
  rw [arena.core_state.reset_map] at h
  exact (ConRon.Refine.HashMap2.clear_fit_refines hinv h).1

theorem reset_map_nil {K V : Type} [DecidableEq K]
    {HashableInst : ron.hashmap.Hashable K} {m m' : ron.hashmap2.HashMap2 K V}
    (hinv : Inv HashableInst m) (h : arena.core_state.reset_map m = ok m') :
    sl_v m' = [] := by
  rw [arena.core_state.reset_map] at h
  exact (ConRon.Refine.HashMap2.clear_fit_refines hinv h).2.1

theorem caches_reset {rm rm' : arena.core_state.Caches} (hinv : CachesInv rm)
    (h : arena.core_state.Caches.reset rm = ok rm') :
    CachesRel rm' Caches.empty ∧ CachesInv rm' := by
  rw [arena.core_state.Caches.reset] at h
  obtain ⟨t0, e0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t1, e1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t2, e2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t3, e3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t4, e4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t5, e5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t6, e6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t7, e7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t8, e8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t9, e9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t10, e10, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t11, e11, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t12, e12, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t13, e13, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rm' = {
    whnf_core_c := t0,
    whnf_c := t1,
    infer_c := t2,
    infer_io_c := t3,
    annot_c := t4,
    defeq_c := t5,
    lvl_eq_c := t6,
    lvls_eq_c := t7,
    const_ty_c := t8,
    const_val_c := t9,
    rule_rhs_c := t10,
    read_l_c := t11,
    read_n_c := t12,
    read_ls_c := t13
  } := (Result.ok_injective h).symm
  subst hst
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  exacts [reset_map_rel hinv.whnfCoreC e0,
    reset_map_rel hinv.whnfC e1,
    reset_map_rel hinv.inferC e2,
    reset_map_rel hinv.inferIOC e3,
    reset_map_rel hinv.annotC e4,
    reset_map_rel hinv.defeqC e5,
    reset_map_rel hinv.lvlEqC e6,
    reset_map_rel hinv.lvlsEqC e7,
    reset_map_rel hinv.constTyC e8,
    reset_map_rel hinv.constValC e9,
    reset_map_rel hinv.ruleRhsC e10,
    reset_map_rel hinv.readLC e11,
    reset_map_rel hinv.readNC e12,
    reset_map_rel hinv.readLsC e13,
    reset_map_inv hinv.whnfCoreC e0,
    reset_map_inv hinv.whnfC e1,
    reset_map_inv hinv.inferC e2,
    reset_map_inv hinv.inferIOC e3,
    reset_map_inv hinv.annotC e4,
    reset_map_inv hinv.defeqC e5,
    reset_map_inv hinv.lvlEqC e6,
    reset_map_inv hinv.lvlsEqC e7,
    reset_map_inv hinv.constTyC e8,
    reset_map_inv hinv.constValC e9,
    reset_map_inv hinv.ruleRhsC e10,
    reset_map_inv hinv.readLC e11,
    reset_map_inv hinv.readNC e12,
    reset_map_inv hinv.readLsC e13,
    by intro p hp; rw [reset_map_nil hinv.readLC e11] at hp; simp at hp,
    by intro p hp; rw [reset_map_nil hinv.readNC e12] at hp; simp at hp,
    by intro p hp; rw [reset_map_nil hinv.readLsC e13] at hp; simp at hp]

theorem memos_reset {rm rm' : arena.monad.Memos} (hinv : MemosInv rm)
    (h : arena.monad.Memos.reset rm = ok rm') :
    MemosRel rm' Memos.empty ∧ MemosInv rm' := by
  rw [arena.monad.Memos.reset] at h
  obtain ⟨t0, e0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t1, e1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t2, e2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t3, e3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t4, e4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t5, e5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t6, e6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t7, e7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t8, e8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t9, e9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t10, e10, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t11, e11, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t12, e12, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rm' = { rm with
    inst1_c := t0,
    inst_l_c := t1,
    lift_c := t2,
    reset_c := t3,
    rename_c := t4,
    abs1_c := t5,
    lower_c := t6,
    inst1_l_c := t7,
    inst_lp_c := t8,
    bvar_b_c := t9,
    fvar_b_c := t10,
    inst_lp_l_c := t11,
    inst_lp_ls_c := t12
  } := (Result.ok_injective h).symm
  subst hst
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv.lpDefC, hinv.crfC⟩⟩
  exacts [reset_map_rel hinv.inst1C e0,
    reset_map_rel hinv.instLC e1,
    reset_map_rel hinv.liftC e2,
    reset_map_rel hinv.resetC e3,
    reset_map_rel hinv.renameC e4,
    reset_map_rel hinv.abs1C e5,
    reset_map_rel hinv.lowerC e6,
    reset_map_rel hinv.inst1LC e7,
    reset_map_rel hinv.instLPC e8,
    reset_map_rel hinv.bvarBC e9,
    reset_map_rel hinv.fvarBC e10,
    reset_map_rel hinv.instLPLC e11,
    reset_map_rel hinv.instLPLsC e12,
    reset_map_inv hinv.inst1C e0,
    reset_map_inv hinv.instLC e1,
    reset_map_inv hinv.liftC e2,
    reset_map_inv hinv.resetC e3,
    reset_map_inv hinv.renameC e4,
    reset_map_inv hinv.abs1C e5,
    reset_map_inv hinv.lowerC e6,
    reset_map_inv hinv.inst1LC e7,
    reset_map_inv hinv.instLPC e8,
    reset_map_inv hinv.bvarBC e9,
    reset_map_inv hinv.fvarBC e10,
    reset_map_inv hinv.instLPLC e11,
    reset_map_inv hinv.instLPLsC e12]


/-! ## The bracket in the lockstep shape (task #97-T2-LOCKSTEP step 1)

Theorem 2 is a lockstep refinement: the Rust and the twin run the same three
operations — `flush_caches`, `enter_scratch`, `drop_scratch` — from related
states, and each is a plain `SimS₀`.  Nothing about the twin's store is
carried: `ScratchClosed`, `BrOK`, `TwinWF` and `ext_bracket` existed only to
move `Ext`/`StoreWF` across the bracket, and those are Theorem 1's
(`Arena.checkDecl_bridge` concludes `StateOK`).  The checker lane moved to
these (task #97-T2-LOCKSTEP lane Checker), and the old explicit `_refines`
statements, `BrOK`, `TwinWF` and the two halves `bracket_open` /
`bracket_close` are deleted. -/

/-- **`flush_caches` ⊑ `flushCaches`**, lockstep. -/
theorem flush_caches_sim₀ {pers st lst st'}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.flush_caches st = ok st') :
    SimS₀ pers lst st' flushCaches := by
  rw [arena.core.flush_caches] at hrun
  obtain ⟨c, hc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with caches := c } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨hr, hi⟩ := caches_reset hinv.caches hc
  exact SimS₀.mk (lst' := { lst with caches := Caches.empty }) rfl
    { hrel with caches := hr } { hinv with caches := hi }

/-- **`enter_scratch` ⊑ `enterScratch`** (task #98-FREEZE): opening a bracket
FREEZES an owned store.  Both sides clear the memos and open an empty scratch
tier; the Rust hands out the store's own tables as a `frozen` tier, and the
relation moves to it — the reader the bracket's body runs at. -/
theorem enter_scratch_rel {pers st lst tier st'}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hrun : arena.core.enter_scratch st = ok (tier, st')) :
    tier = tierOf st.store ∧
      ∃ lst', (enterScratch : AM Unit).run lst = .ok ((), lst') ∧
        AStateRel₀ tier st' lst' ∧ AStateInv tier st' := by
  rw [arena.core.enter_scratch] at hrun
  obtain ⟨m, hm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨⟨t, e⟩, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have h' := Result.ok_injective hrun
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  obtain ⟨hmr, hmi⟩ := memos_reset hinv.memos hm
  obtain ⟨htier, hsr, hsi⟩ := estore_freeze hrel.store hinv.store hpers he
  exact ⟨htier, { lst with store := lst.store.enableScratch, memos := Memos.empty }, rfl,
    ⟨hsr, hmr, hrel.caches, hrel.pins⟩, ⟨hsi, hmi, hinv.caches⟩⟩

/-- **`drop_scratch` ⊑ `dropScratch`** (task #98-FREEZE): closing a bracket
THAWS the store with the tier that comes back.  Both sides drop the caches and
the scratch tier; the relation moves back from the tier to any stand-in that
is not `frozen`. -/
theorem drop_scratch_rel {tier st lst st'}
    (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st)
    (htf : tier.frozen = true)
    (hrun : arena.core.drop_scratch st tier = ok st') {pers : arena.store.PersTier}
    (hpers : pers.frozen = false) :
    SimS₀ pers lst st' dropScratch := by
  rw [arena.core.drop_scratch] at hrun
  obtain ⟨s1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { s1 with store := e } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨lf, hf, hr1, hi1⟩ := (flush_caches_sim₀ hrel hinv h1).apply
  obtain ⟨hsr, hsi⟩ := estore_thaw hr1.store hi1.store htf he hpers
  have hlf : lf = { lst with caches := Caches.empty } := by
    have : (flushCaches : AM Unit).run lst = .ok ((), { lst with caches := Caches.empty }) := rfl
    rw [this] at hf; cases hf; rfl
  subst hlf
  exact SimS₀.mk
    (lst' := { lst with store := lst.store.dropScratch, caches := Caches.empty }) rfl
    ⟨hsr, hr1.memos, hr1.caches, hr1.pins⟩ ⟨hsi, hi1.memos, hi1.caches⟩

/-- **The representation clause between two phase-B records** (task
#98-FREEZE): a worker's store stays frozen with an EMPTY scratch tier between
records, where the twin's is scratch-off; the Rust state is related to the
twin state with its scratch tier re-opened.  Nothing is interned there — the
next record opens with `enter_record`/`enterScratch` — so this is the same
data in two representations, not a fact about a run. -/
def AIdle (tier : arena.store.PersTier) (st : arena.monad.AState) (lst : AState) : Prop :=
  AStateRel₀ tier st { lst with store := lst.store.enableScratch }

/-- **`enter_record` ⊑ `enterScratch`** — a phase-B record's bracket, opened
on the frozen worker. -/
theorem enter_record_sim {tier st lst st'}
    (hidle : AIdle tier st lst) (hinv : AStateInv tier st)
    (hrun : arena.core.enter_record st = ok st') :
    SimS₀ tier lst st' enterScratch := by
  rw [arena.core.enter_record] at hrun
  obtain ⟨m, hm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with store := e, memos := m } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨hmr, hmi⟩ := memos_reset hinv.memos hm
  have hS := hidle.store
  obtain ⟨hsr, hsi⟩ := estore_clear (ls' := lst.store.enableScratch) hS hinv.store
    rfl rfl rfl rfl rfl rfl rfl rfl
    hS.lss.lvl.ns.scratchOn hS.lss.lvl.scratchOn hS.lss.scratchOn hS.scratchOn he
  exact SimS₀.mk
    (lst' := { lst with store := lst.store.enableScratch, memos := Memos.empty }) rfl
    ⟨hsr, hmr, hidle.caches, hidle.pins⟩ ⟨hsi, hmi, hinv.caches⟩

/-- **`leave_record` ⊑ `dropScratch`** — a phase-B record's bracket, closed
on the frozen worker, which stays frozen: the result is the idle clause. -/
theorem leave_record_rel {tier st lst st'}
    (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st)
    (htf : tier.frozen = true)
    (hrun : arena.core.leave_record st = ok st') :
    ∃ lst', (dropScratch : AM Unit).run lst = .ok ((), lst') ∧ AIdle tier st' lst' ∧
      AStateInv tier st' := by
  rw [arena.core.leave_record] at hrun
  obtain ⟨s1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { s1 with store := e } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨lf, hf, hr1, hi1⟩ := (flush_caches_sim₀ hrel hinv h1).apply
  have hlf : lf = { lst with caches := Caches.empty } := by
    have : (flushCaches : AM Unit).run lst = .ok ((), { lst with caches := Caches.empty }) := rfl
    rw [this] at hf; cases hf; rfl
  subst hlf
  -- the worker's scratch flags are up: its reader is the frozen tier
  have hN := hi1.store.lss.lvl.ns.frz htf
  have hL := hi1.store.lss.lvl.frz htf
  have hLs := hi1.store.lss.frz htf
  have hE := hi1.store.frz htf
  obtain ⟨hsr, hsi⟩ := estore_clear (ls' := lst.store.enableScratch) hr1.store hi1.store
    rfl rfl rfl rfl rfl rfl rfl rfl hN.symm hL.symm hLs.symm hE.symm he
  refine ⟨{ lst with store := lst.store.dropScratch, caches := Caches.empty }, rfl, ?_,
    ⟨hsi, hi1.memos, hi1.caches⟩⟩
  have hdd : (lst.store.dropScratch).enableScratch = lst.store.enableScratch := rfl
  exact ⟨by rw [hdd]; exact hsr, hr1.memos, hr1.caches, hr1.pins⟩

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.ext_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ext_bracket

/-- info: 'ConRon.Refine2.flush_caches_sim₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms flush_caches_sim₀

/-- info: 'ConRon.Refine2.enter_scratch_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms enter_scratch_rel

/-- info: 'ConRon.Refine2.drop_scratch_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms drop_scratch_rel

/-- info: 'ConRon.Refine2.enter_record_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms enter_record_sim

/-- info: 'ConRon.Refine2.leave_record_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms leave_record_rel

end ConRon.Refine2
