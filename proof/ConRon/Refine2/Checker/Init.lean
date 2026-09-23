/-
# `ConRon.Refine2.Checker.Init` — Theorem 2 at the driver's START state

**Task #97-P5-Top** (task #97-COMPOSE's mismatch 2, `InitRel`).  Every
Theorem-2 lemma takes `AStateRel₀ pers st lst ∧ AStateInv pers st` and
concludes it for the post-state; nothing concluded it for the START state.
The binary makes that state as `AState::init(EStore::empty())` read through
`PersTier::empty()`, and the twin driver as `AState.init EStore.empty`.

`init_rel` below relates the two: the thirty-seven empty cons tables of the
four store tiers (`tbl_empty_rel`, one lemma for all of them — an empty `Tbl` is
an empty row vector and a fresh `HashMap2`), the thirteen per-call memos and
the fourteen per-declaration caches (fresh `HashMap2`s, related to `∅`), the
unfilled pin table (three word-0 handles and two empty vectors against the
twin's `Pins.empty`), and `StoreWF EStore.empty` (`Arena/WFProofs.lean`'s
`EStore.empty_wf`), and it also concludes `scratch_on = false`.

The `PersTier` argument is irrelevant here: with every `shared_on` down, the
relation reads the store's OWN persistent tier (`rPersE` and its three
siblings), never `pers`.
-/
import ConRon.Refine2.Promote.Intern

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn sl_v)

/-- **One empty cons table**: an empty row vector and a fresh `HashMap2`,
against the twin's `Tbl.empty`.  All thirty-seven tables of the four tiers are
this lemma. -/
private theorem tbl_empty_eq {A I D : Type}
    {hA : ron.hashmap.Hashable A} {e2 : ron.hashmap.Eq2 A} {dA : ron.hashmap.Dup A}
    {dI : ron.hashmap.Dup I} {dD : ron.hashmap.Dup D} {dd : arena.store.DerDefault D}
    {rt : arena.store.Tbl A I D}
    (h : arena.store.Tbl.empty hA e2 dA dI dD dd = ok rt) :
    ∃ hm, ron.hashmap2.HashMap2.new A I = ok hm ∧
      rt = { rows := alloc.vec.Vec.new (A × D), cons := hm } := by
  rw [arena.store.Tbl.empty] at h
  obtain ⟨hm, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨hm, hhm, (Result.ok_injective h).symm⟩

theorem tbl_empty_rel {A I D α ι δ ω : Type} [DecidableEq A] {_ : BEq α} {_ : Hashable α}
    {hA : ron.hashmap.Hashable A} {e2 : ron.hashmap.Eq2 A} {dA : ron.hashmap.Dup A}
    {dI : ron.hashmap.Dup I} {dD : ron.hashmap.Dup D} {dd : arena.store.DerDefault D}
    {P : A → Prop} {absA : A → α} {absI : I → ι} {absD : D → δ} {obsD : δ → ω}
    {rt : arena.store.Tbl A I D}
    (h : arena.store.Tbl.empty hA e2 dA dI dD dd = ok rt) :
    TblRel P absA absI absD obsD rt (Tbl.empty : Tbl α ι δ) := by
  obtain ⟨hm, hhm, rfl⟩ := tbl_empty_eq h
  obtain ⟨-, -, hnone⟩ :=
    ConRon.Refine.HashMap2.new_refines (HashableInst := hA) hhm
  exact ⟨rfl, rfl, ConRon.Refine.HashMap2.RelOn_empty hnone⟩

theorem tbl_empty_inv {A I D : Type} [DecidableEq A]
    {hA : ron.hashmap.Hashable A} {e2 : ron.hashmap.Eq2 A} {dA : ron.hashmap.Dup A}
    {dI : ron.hashmap.Dup I} {dD : ron.hashmap.Dup D} {dd : arena.store.DerDefault D}
    {P : A → Prop} {rt : arena.store.Tbl A I D}
    (h : arena.store.Tbl.empty hA e2 dA dI dD dd = ok rt) : TblInv hA P rt := by
  obtain ⟨hm, hhm, rfl⟩ := tbl_empty_eq h
  obtain ⟨hinv, hnil, -⟩ :=
    ConRon.Refine.HashMap2.new_refines (HashableInst := hA) hhm
  refine ⟨hinv, ConRon.Refine.HashMap2.KeysOk_of_nil hnil, ?_⟩
  intro p hp
  simp [alloc.vec.Vec.new] at hp

theorem ntables_empty {rt : arena.store.NTables}
    (h : arena.store.NTables.empty = ok rt) :
    NTablesRel rt NTables.empty ∧ NTablesInv rt := by
  rw [arena.store.NTables.empty] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t2, ht2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  subst h'
  exact ⟨⟨tbl_empty_rel ht, tbl_empty_rel ht1, tbl_empty_rel ht2⟩,
    ⟨tbl_empty_inv ht, tbl_empty_inv ht1, tbl_empty_inv ht2⟩⟩

theorem ltables_empty {rt : arena.store.LTables}
    (h : arena.store.LTables.empty = ok rt) :
    LTablesRel rt LTables.empty ∧ LTablesInv rt := by
  rw [arena.store.LTables.empty] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t2, ht2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t3, ht3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  subst h'
  exact ⟨⟨tbl_empty_rel ht, tbl_empty_rel ht1, tbl_empty_rel ht2, tbl_empty_rel ht2,
      tbl_empty_rel ht3⟩,
    ⟨tbl_empty_inv ht, tbl_empty_inv ht1, tbl_empty_inv ht2, tbl_empty_inv ht2,
      tbl_empty_inv ht3⟩⟩

theorem lstables_empty {rt : arena.store.LsTables}
    (h : arena.store.LsTables.empty = ok rt) :
    LsTablesRel rt LsTables.empty ∧ LsTablesInv rt := by
  rw [arena.store.LsTables.empty] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  subst h'
  exact ⟨⟨tbl_empty_rel ht⟩, ⟨tbl_empty_inv ht⟩⟩

theorem etables_empty {rt : arena.store.ETables}
    (h : arena.store.ETables.empty = ok rt) :
    ETablesRel rt ETables.empty ∧ ETablesInv rt := by
  rw [arena.store.ETables.empty] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t2, ht2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t3, ht3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t4, ht4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t5, ht5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t6, ht6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t7, ht7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t8, ht8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t9, ht9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  subst h'
  exact ⟨⟨tbl_empty_rel ht, tbl_empty_rel ht1, tbl_empty_rel ht2, tbl_empty_rel ht3,
      tbl_empty_rel ht4, tbl_empty_rel ht5, tbl_empty_rel ht5, tbl_empty_rel ht6,
      tbl_empty_rel ht7, tbl_empty_rel ht8, tbl_empty_rel ht9⟩,
    ⟨tbl_empty_inv ht, tbl_empty_inv ht1, tbl_empty_inv ht2, tbl_empty_inv ht3,
      tbl_empty_inv ht4, tbl_empty_inv ht5, tbl_empty_inv ht5, tbl_empty_inv ht6,
      tbl_empty_inv ht7, tbl_empty_inv ht8, tbl_empty_inv ht9⟩⟩

/-- The empty store, with every flag down.  `pers` is never read: the
relation's persistent arm is the store's own tier when `shared_on` is
`false`. -/
theorem estore_empty (pers : arena.store.PersTier) {rs : arena.store.EStore}
    (h : arena.store.EStore.empty = ok rs) :
    StoreRel pers rs EStore.empty ∧ StoreInv pers rs ∧ rs.scratch_on = false := by
  rw [arena.store.EStore.empty] at h
  obtain ⟨lss, hlss, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  subst h'
  rw [arena.store.LsStore.empty] at hlss
  obtain ⟨l, hl, hlss⟩ := ConRon.Refine.bind_eq_ok_iff.mp hlss
  obtain ⟨lt, hlt, hlss⟩ := ConRon.Refine.bind_eq_ok_iff.mp hlss
  have h' := Result.ok_injective hlss
  subst h'
  rw [arena.store.LStore.empty] at hl
  obtain ⟨n, hn, hl⟩ := ConRon.Refine.bind_eq_ok_iff.mp hl
  obtain ⟨lt2, hlt2, hl⟩ := ConRon.Refine.bind_eq_ok_iff.mp hl
  have h' := Result.ok_injective hl
  subst h'
  rw [arena.store.NStore.empty] at hn
  obtain ⟨nt, hnt, hn⟩ := ConRon.Refine.bind_eq_ok_iff.mp hn
  have h' := Result.ok_injective hn
  subst h'
  obtain ⟨hNR, hNI⟩ := ntables_empty hnt
  obtain ⟨hLR, hLI⟩ := ltables_empty hlt2
  obtain ⟨hLsR, hLsI⟩ := lstables_empty hlt
  obtain ⟨hER, hEI⟩ := etables_empty he
  refine ⟨⟨⟨⟨⟨hNR, hNR, rfl⟩, hLR, hLR, rfl⟩, hLsR, hLsR, rfl⟩, hER, hER, rfl⟩,
    ⟨⟨⟨⟨hNI, hNI⟩, hLI, hLI⟩, hLsI, hLsI⟩, hEI, hEI⟩, rfl⟩

theorem memos_empty {rm : arena.monad.Memos} (h : arena.monad.Memos.empty = ok rm) :
    MemosRel rm Memos.empty ∧ MemosInv rm := by
  rw [arena.monad.Memos.empty] at h
  obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m1, hm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m2, hm2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m3, hm3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  subst h'
  obtain ⟨i0, -, n0⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable) hm
  obtain ⟨i1, -, n1⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable) hm1
  obtain ⟨i2, -, n2⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.LIdx.Insts.Con_ron_coreRonHashmapHashable) hm2
  obtain ⟨i3, -, n3⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapHashable) hm3
  have r0 := fun {V' : Type} (absV : arena.handle.EIdx → V') =>
    ConRon.Refine.HashMap2.RelOn_empty (P := fun _ => True) (K' := EIdx × Nat)
      (absK := absEIdxNat) (absV := absV) n0
  exact ⟨⟨r0 _, r0 _, r0 _, r0 _, r0 _, r0 _, r0 _, r0 _, r0 _,
      ConRon.Refine.HashMap2.RelOn_empty n1, ConRon.Refine.HashMap2.RelOn_empty n1,
      ConRon.Refine.HashMap2.RelOn_empty n2, ConRon.Refine.HashMap2.RelOn_empty n3⟩,
    ⟨i0, i0, i0, i0, i0, i0, i0, i0, i0, i1, i1, i2, i3⟩⟩

theorem caches_empty {rc : arena.core_state.Caches}
    (h : arena.core_state.Caches.empty = ok rc) :
    CachesRel rc Caches.empty ∧ CachesInv rc := by
  rw [arena.core_state.Caches.empty] at h
  obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m1, hm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m2, hm2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m3, hm3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m4, hm4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m5, hm5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m6, hm6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m7, hm7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m8, hm8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  subst h'
  obtain ⟨i0, -, n0⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable) hm
  obtain ⟨i1, -, n1⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.core_state.EIdxPair.Insts.Con_ron_coreRonHashmapHashable) hm1
  obtain ⟨i2, -, n2⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.core_state.LIdxPair.Insts.Con_ron_coreRonHashmapHashable) hm2
  obtain ⟨i3, -, n3⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.core_state.LsIdxPair.Insts.Con_ron_coreRonHashmapHashable) hm3
  obtain ⟨i4, -, n4⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.core_state.NLsKey.Insts.Con_ron_coreRonHashmapHashable) hm4
  obtain ⟨i5, -, n5⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.core_state.NNLsKey.Insts.Con_ron_coreRonHashmapHashable) hm5
  obtain ⟨i6, s6, n6⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.LIdx.Insts.Con_ron_coreRonHashmapHashable) hm6
  obtain ⟨i7, s7, n7⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hm7
  obtain ⟨i8, s8, n8⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapHashable) hm8
  refine ⟨⟨ConRon.Refine.HashMap2.RelOn_empty n0, ConRon.Refine.HashMap2.RelOn_empty n0,
      ConRon.Refine.HashMap2.RelOn_empty n0, ConRon.Refine.HashMap2.RelOn_empty n0,
      ConRon.Refine.HashMap2.RelOn_empty n0, ConRon.Refine.HashMap2.RelOn_empty n1,
      ConRon.Refine.HashMap2.RelOn_empty n2, ConRon.Refine.HashMap2.RelOn_empty n3,
      ConRon.Refine.HashMap2.RelOn_empty n4, ConRon.Refine.HashMap2.RelOn_empty n4,
      ConRon.Refine.HashMap2.RelOn_empty n5, ConRon.Refine.HashMap2.RelOn_empty n6,
      ConRon.Refine.HashMap2.RelOn_empty n7, ConRon.Refine.HashMap2.RelOn_empty n8⟩,
    ⟨i0, i0, i0, i0, i0, i1, i2, i3, i4, i4, i5, i6, i7, i8, ?_, ?_, ?_⟩⟩
  · intro p hp; rw [s6] at hp; cases hp
  · intro p hp; rw [s7] at hp; cases hp
  · intro p hp; rw [s8] at hp; cases hp

/-- **`InitRel`, discharged** (task #97-COMPOSE's mismatch 2): the binary's
start state — `AState::init(EStore::empty())` read through
`PersTier::empty()` — is related to the twin driver's
`AState.init EStore.empty`, satisfies the Rust-side invariant, and has its
scratch tier closed. -/
theorem init_rel {pers : arena.store.PersTier} {est : arena.store.EStore}
    {st : arena.monad.AState}
    (hest : arena.store.EStore.empty = ok est)
    (hst : arena.monad.AState.init est = ok st) :
    AStateRel₀ pers st (AState.init EStore.empty) ∧ AStateInv pers st ∧
      st.store.scratch_on = false := by
  obtain ⟨hSR, hSI, hoff⟩ := estore_empty pers hest
  rw [arena.monad.AState.init] at hst
  obtain ⟨m, hm, hst⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst
  obtain ⟨c, hc, hst⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst
  obtain ⟨p, hp, hst⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst
  have h' := Result.ok_injective hst
  subst h'
  rw [arena.pins.Pins.empty] at hp
  simp only [arena.handle.LsIdx.of_word, arena.handle.LIdx.of_word,
    arena.handle.EIdx.of_word, bind_tc_ok] at hp
  have hp' := Result.ok_injective hp
  subst hp'
  obtain ⟨hMR, hMI⟩ := memos_empty hm
  obtain ⟨hCR, hCI⟩ := caches_empty hc
  exact ⟨⟨hSR, hMR, hCR, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩, ⟨hSI, hMI, hCI⟩,
    hoff⟩

/-- info: 'ConRon.Refine2.init_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms init_rel

end ConRon.Refine2
