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
-/
import ConRon.Refine2.Specs

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



/-! ## The four stores, opened and closed

`enable_scratch` and `drop_scratch` differ in ONE bit — the flag they leave
behind — and in nothing else: both reset the scratch tier and touch neither
the persistent tier nor `shared_on`, so `rPersN`/`rPersL`/`rPersLs`/`rPersE`
are unchanged and the relation's persistent clause is carried across
untouched.  Eight lemmas, four lines of content each. -/

theorem nstore_enable {pers} {rs rs' : arena.store.NStore} {ls : NStore}
    (hrel : NStoreRel pers rs ls) (hinv : NStoreInv pers rs)
    (h : arena.store.NStore.enable_scratch rs = ok rs') :
    NStoreRel pers rs' ls.enableScratch ∧ NStoreInv pers rs' := by
  rw [arena.store.NStore.enable_scratch] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rs' = { rs with scr := t, scratch_on := true } :=
    (Result.ok_injective h).symm
  subst hst
  obtain ⟨hr, hi⟩ := ntables_reset hinv.scrt ht
  exact ⟨⟨hrel.perst, hr, rfl⟩, ⟨hinv.perst, hi⟩⟩

theorem lstore_enable {pers} {rs rs' : arena.store.LStore} {ls : LStore}
    (hrel : LStoreRel pers rs ls) (hinv : LStoreInv pers rs)
    (h : arena.store.LStore.enable_scratch rs = ok rs') :
    LStoreRel pers rs' ls.enableScratch ∧ LStoreInv pers rs' := by
  rw [arena.store.LStore.enable_scratch] at h
  obtain ⟨u, hu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rs' = { rs with ns := u, scr := t, scratch_on := true } :=
    (Result.ok_injective h).symm
  subst hst
  obtain ⟨hr, hi⟩ := ltables_reset hinv.scrt ht
  obtain ⟨hr2, hi2⟩ := nstore_enable hrel.ns hinv.ns hu
  exact ⟨⟨hr2, hrel.perst, hr, rfl⟩, ⟨hi2, hinv.perst, hi⟩⟩

theorem lsstore_enable {pers} {rs rs' : arena.store.LsStore} {ls : LsStore}
    (hrel : LsStoreRel pers rs ls) (hinv : LsStoreInv pers rs)
    (h : arena.store.LsStore.enable_scratch rs = ok rs') :
    LsStoreRel pers rs' ls.enableScratch ∧ LsStoreInv pers rs' := by
  rw [arena.store.LsStore.enable_scratch] at h
  obtain ⟨u, hu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rs' = { rs with ls := u, scr := t, scratch_on := true } :=
    (Result.ok_injective h).symm
  subst hst
  obtain ⟨hr, hi⟩ := lstables_reset hinv.scrt ht
  obtain ⟨hr2, hi2⟩ := lstore_enable hrel.lvl hinv.lvl hu
  exact ⟨⟨hr2, hrel.perst, hr, rfl⟩, ⟨hi2, hinv.perst, hi⟩⟩

theorem estore_enable {pers} {rs rs' : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) (hinv : StoreInv pers rs)
    (h : arena.store.EStore.enable_scratch rs = ok rs') :
    StoreRel pers rs' ls.enableScratch ∧ StoreInv pers rs' := by
  rw [arena.store.EStore.enable_scratch] at h
  obtain ⟨u, hu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rs' = { rs with lss := u, scr := t, scratch_on := true } :=
    (Result.ok_injective h).symm
  subst hst
  obtain ⟨hr, hi⟩ := etables_reset hinv.scrt ht
  obtain ⟨hr2, hi2⟩ := lsstore_enable hrel.lss hinv.lss hu
  exact ⟨⟨hr2, hrel.perst, hr, rfl⟩, ⟨hi2, hinv.perst, hi⟩⟩

theorem nstore_drop {pers} {rs rs' : arena.store.NStore} {ls : NStore}
    (hrel : NStoreRel pers rs ls) (hinv : NStoreInv pers rs)
    (h : arena.store.NStore.drop_scratch rs = ok rs') :
    NStoreRel pers rs' ls.dropScratch ∧ NStoreInv pers rs' := by
  rw [arena.store.NStore.drop_scratch] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rs' = { rs with scr := t, scratch_on := false } :=
    (Result.ok_injective h).symm
  subst hst
  obtain ⟨hr, hi⟩ := ntables_reset hinv.scrt ht
  exact ⟨⟨hrel.perst, hr, rfl⟩, ⟨hinv.perst, hi⟩⟩

theorem lstore_drop {pers} {rs rs' : arena.store.LStore} {ls : LStore}
    (hrel : LStoreRel pers rs ls) (hinv : LStoreInv pers rs)
    (h : arena.store.LStore.drop_scratch rs = ok rs') :
    LStoreRel pers rs' ls.dropScratch ∧ LStoreInv pers rs' := by
  rw [arena.store.LStore.drop_scratch] at h
  obtain ⟨u, hu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rs' = { rs with ns := u, scr := t, scratch_on := false } :=
    (Result.ok_injective h).symm
  subst hst
  obtain ⟨hr, hi⟩ := ltables_reset hinv.scrt ht
  obtain ⟨hr2, hi2⟩ := nstore_drop hrel.ns hinv.ns hu
  exact ⟨⟨hr2, hrel.perst, hr, rfl⟩, ⟨hi2, hinv.perst, hi⟩⟩

theorem lsstore_drop {pers} {rs rs' : arena.store.LsStore} {ls : LsStore}
    (hrel : LsStoreRel pers rs ls) (hinv : LsStoreInv pers rs)
    (h : arena.store.LsStore.drop_scratch rs = ok rs') :
    LsStoreRel pers rs' ls.dropScratch ∧ LsStoreInv pers rs' := by
  rw [arena.store.LsStore.drop_scratch] at h
  obtain ⟨u, hu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rs' = { rs with ls := u, scr := t, scratch_on := false } :=
    (Result.ok_injective h).symm
  subst hst
  obtain ⟨hr, hi⟩ := lstables_reset hinv.scrt ht
  obtain ⟨hr2, hi2⟩ := lstore_drop hrel.lvl hinv.lvl hu
  exact ⟨⟨hr2, hrel.perst, hr, rfl⟩, ⟨hi2, hinv.perst, hi⟩⟩

theorem estore_drop {pers} {rs rs' : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) (hinv : StoreInv pers rs)
    (h : arena.store.EStore.drop_scratch rs = ok rs') :
    StoreRel pers rs' ls.dropScratch ∧ StoreInv pers rs' := by
  rw [arena.store.EStore.drop_scratch] at h
  obtain ⟨u, hu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst : rs' = { rs with lss := u, scr := t, scratch_on := false } :=
    (Result.ok_injective h).symm
  subst hst
  obtain ⟨hr, hi⟩ := etables_reset hinv.scrt ht
  obtain ⟨hr2, hi2⟩ := lsstore_drop hrel.lss hinv.lss hu
  exact ⟨⟨hr2, hrel.perst, hr, rfl⟩, ⟨hi2, hinv.perst, hi⟩⟩



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
  have hst : rm' = {
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
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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



/-! ## The three primitives

Each hands the twin's post-state back EXPLICITLY — `SimS` quantifies it, and
the bracket has to name it to chain `ScratchClosed` / `StoreWF` / `Ext`
across the three steps.  `Ext` is deliberately NOT among the conclusions:
`flush_caches`' is `Ext.refl`, `enter_scratch`'s and `drop_scratch`'s are the
store-level lemmas above, under the side condition only the BRACKET has. -/

/-- **`flush_caches` ⊑ `flushCaches`** — the per-declaration cache drop.  The
store is untouched, so this one IS a `SimS` (`flush_caches_sim` below says
so); the explicit form is what the bracket uses. -/
theorem flush_caches_refines {pers st lst st'}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.flush_caches st = ok st') :
    (flushCaches : AM Unit).run lst = .ok ((), { lst with caches := Caches.empty }) ∧
      AStateRel pers st' { lst with caches := Caches.empty } ∧
      AStateInv pers st' := by
  rw [arena.core.flush_caches] at hrun
  obtain ⟨c, hc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with caches := c } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨hr, hi⟩ := caches_reset hinv.caches hc
  exact ⟨rfl, { hrel with caches := hr }, { hinv with caches := hi }⟩

/-- `flush_caches` in `Refine2/Shape.lean`'s own shape: it appends nothing, so
`Ext.refl` is the whole of its store claim. -/
theorem flush_caches_sim {pers st lst st'}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.flush_caches st = ok st') :
    SimS pers lst st' flushCaches := by
  obtain ⟨h1, h2, h3⟩ := flush_caches_refines hrel hinv hrun
  exact SimS.mk h1 h2 h3 (Ext.refl _)

/-- **`enter_scratch` ⊑ `enterScratch`** — the bracket opened: the per-call
memos cleared and the scratch tier turned on and emptied.

**Not a `SimS`.**  `SimS` demands `Ext lst.store lst'.store`, and opening the
tier un-decodes every handle the previous tier held; `ScratchClosed.ext` is
the `Ext` that IS true, and it is true only at a declaration boundary. -/
theorem enter_scratch_refines {pers st lst st'}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.enter_scratch st = ok st') :
    (enterScratch : AM Unit).run lst = .ok ((),
        { lst with store := lst.store.enableScratch, memos := Memos.empty }) ∧
      AStateRel pers st'
        { lst with store := lst.store.enableScratch, memos := Memos.empty } ∧
      AStateInv pers st' := by
  rw [arena.core.enter_scratch] at hrun
  obtain ⟨m, hm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with store := e, memos := m } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨hmr, hmi⟩ := memos_reset hinv.memos hm
  obtain ⟨hsr, hsi⟩ := estore_enable hrel.store hinv.store he
  exact ⟨rfl, { hrel with store := hsr, memos := hmr },
    { hinv with store := hsi, memos := hmi }⟩

/-- **`drop_scratch` ⊑ `dropScratch`** — the bracket closed: the caches
dropped and the scratch tier gone, in one operation so the two halves cannot
drift apart.

**Not a `SimS`, and this is the finding `Refine2/Shape.lean`'s module note
owes** (task #97-P5-Checker-2 §5, item 2): `Ext` is denotation preservation
and a dropped scratch handle no longer decodes, so there is no `Ext` here at
all.  What the bracket gets instead is `ext_bracket`, from the store the
bracket was ENTERED at. -/
theorem drop_scratch_refines {pers st lst st'}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.drop_scratch st = ok st') :
    (dropScratch : AM Unit).run lst = .ok ((),
        { lst with store := lst.store.dropScratch, caches := Caches.empty }) ∧
      AStateRel pers st'
        { lst with store := lst.store.dropScratch, caches := Caches.empty } ∧
      AStateInv pers st' := by
  rw [arena.core.drop_scratch] at hrun
  obtain ⟨s1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { s1 with store := e } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨-, hr1, hi1⟩ := flush_caches_refines hrel hinv h1
  obtain ⟨hsr, hsi⟩ := estore_drop hr1.store hi1.store he
  refine ⟨rfl, ?_, ?_⟩
  · exact { hr1 with store := hsr }
  · exact { hi1 with store := hsi }

end ConRon.Refine2
