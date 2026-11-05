/-
# `ConRon.Refine2.Core.Frame` — a scratch run's frame, at the relation

The twin's `scratchRun` ends a run with the persistent tables, the scratch flags and
the pins of the state it started from, and errors if the run grew a persistent array.
The Rust has the tier by `&` and saves and restores the flags and the pins
(`arena::promote::scratch_save`, `scratch_restore`).

At a frozen reader the relation reads the tier for the persistent arm, whatever the
store, so the two states the run began and ended at relate that arm to the same
tables: the arrays have the sizes they had, `frameFrom` puts back a related table,
and the restored flags and pins are the saved values on both sides.
-/
import ConRon.Refine2.Core.Bracket
import ConRon.Arena.Promote
import ConRon.Refine2.Dup

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- **`pins_dup` is the identity on the value.** -/
theorem pins_dup_val {p q : arena.pins.Pins} (h : arena.checker.pins_dup p = ok q) :
    q = p := by
  rw [arena.checker.pins_dup] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨li, hli, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := (Result.ok_injective h).symm
  subst h'
  have e1 : v = p.names := alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hv)
  have e2 : v1 = p.reserved := alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hv1)
  rw [e1, e2, dupId_lsidx _ _ hli, dupId_lidx _ _ hl, dupId_eidx _ _ he]

/-! ## The sizes -/

theorem TblRel.size_eq {A I D α ι δ ω : Type} [DecidableEq A] [BEq α] [Hashable α]
    {P : A → Prop} {absA : A → α} {absI : I → ι} {absD : D → δ} {obsD : δ → ω}
    {rt : arena.store.Tbl A I D} {a b : Tbl α ι δ}
    (ha : TblRel P absA absI absD obsD rt a) (hb : TblRel P absA absI absD obsD rt b) :
    a.size = b.size := by
  have h := congrArg List.length (ha.nodes.trans hb.nodes.symm)
  simpa [Tbl.size] using h

theorem NTablesRel.sizes_eq {rt a b} (ha : NTablesRel rt a) (hb : NTablesRel rt b) :
    a.sizes = b.sizes := by
  simp only [NTables.sizes]
  rw [ha.anons.size_eq hb.anons, ha.strs.size_eq hb.strs, ha.nums.size_eq hb.nums]

theorem LTablesRel.sizes_eq {rt a b} (ha : LTablesRel rt a) (hb : LTablesRel rt b) :
    a.sizes = b.sizes := by
  simp only [LTables.sizes]
  rw [ha.zeros.size_eq hb.zeros, ha.succs.size_eq hb.succs, ha.maxs.size_eq hb.maxs,
    ha.imaxs.size_eq hb.imaxs, ha.params.size_eq hb.params]

theorem LsTablesRel.sizes_eq {rt a b} (ha : LsTablesRel rt a) (hb : LsTablesRel rt b) :
    a.sizes = b.sizes := by
  simp only [LsTables.sizes]
  rw [ha.lists.size_eq hb.lists]

theorem ETablesRel.sizes_eq {rt a b} (ha : ETablesRel rt a) (hb : ETablesRel rt b) :
    a.sizes = b.sizes := by
  simp only [ETables.sizes]
  rw [ha.bvars.size_eq hb.bvars, ha.fvars.size_eq hb.fvars, ha.sorts.size_eq hb.sorts,
    ha.consts.size_eq hb.consts, ha.apps.size_eq hb.apps, ha.lams.size_eq hb.lams,
    ha.foralls.size_eq hb.foralls, ha.lets.size_eq hb.lets, ha.lits.size_eq hb.lits,
    ha.projs.size_eq hb.projs]

/-- **A run at a frozen reader grew no persistent array.** -/
theorem persSizes_eq {tier : arena.store.PersTier} {r₀ r₁ : arena.store.EStore} {a b : EStore}
    (htf : tier.frozen = true) (ha : StoreRel tier r₀ a) (hb : StoreRel tier r₁ b) :
    a.persSizes = b.persSizes := by
  have hE := ha.perst
  have hE' := hb.perst
  have hLs := ha.lss.perst
  have hLs' := hb.lss.perst
  have hL := ha.lss.lvl.perst
  have hL' := hb.lss.lvl.perst
  have hN := ha.lss.lvl.ns.perst
  have hN' := hb.lss.lvl.ns.perst
  simp only [rPersE, rPersLs, rPersL, rPersN, htf, ite_true] at hE hE' hLs hLs' hL hL' hN hN'
  simp only [EStore.persSizes]
  rw [hE.sizes_eq hE', hLs.sizes_eq hLs', hL.sizes_eq hL', hN.sizes_eq hN']

/-! ## The frame -/

/-- **The state a framed run ends in, related**: the persistent arm the state it began
at relates to the tier, the scratch arm and the caches and memos the state it ended at
relates, and the flags and pins the saved values. -/
theorem scratch_frame {tier : arena.store.PersTier} {st₀ st₁ st₂ : arena.monad.AState}
    {f : arena.promote.ScratchFrame} {lst₀ lst₁ : AState} (htf : tier.frozen = true)
    (h₀ : AStateRel₀ tier st₀ lst₀) (hi₀ : AStateInv tier st₀)
    (h₁ : AStateRel₀ tier st₁ lst₁) (hi₁ : AStateInv tier st₁)
    (hsave : arena.promote.scratch_save st₀ = ok f)
    (hres : arena.promote.scratch_restore st₁ f = ok st₂) :
    AStateRel₀ tier st₂ { lst₁ with store := lst₁.store.frameFrom lst₀.store, pins := lst₀.pins } ∧
      AStateInv tier st₂ := by
  rw [arena.promote.scratch_save] at hsave
  obtain ⟨p, hp, hsave⟩ := ConRon.Refine.bind_eq_ok_iff.mp hsave
  obtain rfl := pins_dup_val hp
  obtain rfl := (Result.ok_injective hsave).symm
  rw [arena.promote.scratch_restore] at hres
  obtain rfl := (Result.ok_injective hres).symm
  have hS₀ := h₀.store
  have hS₁ := h₁.store
  have hI₀ := hi₀.store
  have hI₁ := hi₁.store
  have e1 : ∀ s : arena.store.EStore, rPersE tier s = tier.e := fun s => by simp [rPersE, htf]
  have e2 : ∀ s : arena.store.LsStore, rPersLs tier s = tier.ls := fun s => by simp [rPersLs, htf]
  have e3 : ∀ s : arena.store.LStore, rPersL tier s = tier.l := fun s => by simp [rPersL, htf]
  have e4 : ∀ s : arena.store.NStore, rPersN tier s = tier.n := fun s => by simp [rPersN, htf]
  have r4 := hS₀.lss.lvl.ns.perst
  have r3 := hS₀.lss.lvl.perst
  have r2 := hS₀.lss.perst
  have r1 := hS₀.perst
  have i4 := hI₁.lss.lvl.ns.perst
  have i3 := hI₁.lss.lvl.perst
  have i2 := hI₁.lss.perst
  have i1 := hI₁.perst
  rw [e4] at r4 i4
  rw [e3] at r3 i3
  rw [e2] at r2 i2
  rw [e1] at r1 i1
  refine ⟨⟨⟨⟨⟨⟨?_, hS₁.lss.lvl.ns.scrt, hS₀.lss.lvl.ns.scratchOn⟩, ?_, hS₁.lss.lvl.scrt,
      hS₀.lss.lvl.scratchOn⟩, ?_, hS₁.lss.scrt, hS₀.lss.scratchOn⟩, ?_, hS₁.scrt, hS₀.scratchOn⟩,
      h₁.memos, h₁.caches, h₀.pins⟩,
    ⟨⟨⟨⟨⟨?_, hI₁.lss.lvl.ns.scrt, hI₀.lss.lvl.ns.frz⟩, ?_, hI₁.lss.lvl.scrt, hI₀.lss.lvl.frz⟩,
      ?_, hI₁.lss.scrt, hI₀.lss.frz⟩, ?_, hI₁.scrt, hI₀.frz⟩, hi₁.memos, hi₁.caches⟩⟩
  · rw [e4]; exact r4
  · rw [e3]; exact r3
  · rw [e2]; exact r2
  · rw [e1]; exact r1
  · rw [e4]; exact i4
  · rw [e3]; exact i3
  · rw [e2]; exact i2
  · rw [e1]; exact i1

/-- **`scratchRun` on an accepting run**: the sizes agree, so it answers what the run
did, at the framed state. -/
theorem scratchRun_ok {α : Type} {c : AM α} {tier : arena.store.PersTier}
    {st₀ st₁ : arena.monad.AState} {lst₀ lst₁ : AState} {a : α} (htf : tier.frozen = true)
    (h₀ : AStateRel₀ tier st₀ lst₀) (h₁ : AStateRel₀ tier st₁ lst₁)
    (hc : c.run lst₀ = .ok (a, lst₁)) :
    (scratchRun c).run lst₀ =
      .ok (a, { lst₁ with store := lst₁.store.frameFrom lst₀.store, pins := lst₀.pins }) := by
  have hc' : c lst₀ = .ok (a, lst₁) := hc
  show scratchRun c lst₀ = _
  unfold scratchRun
  rw [hc']
  simp only [persSizes_eq htf h₁.store h₀.store, BEq.rfl, ite_true]

/-- `scratchRun` on a failing run fails with what it failed with. -/
theorem scratchRun_err {α : Type} {c : AM α} {lst₀ : AState} {e : Arena.CheckError}
    (hc : c.run lst₀ = .error e) : (scratchRun c).run lst₀ = .error e := by
  have hc' : c lst₀ = .error e := hc
  show scratchRun c lst₀ = _
  unfold scratchRun
  rw [hc']

/-- The error a Rust failure maps to, through `scratchRun`. -/
theorem AErrSim.scratchRun {α : Type} {c : AM α} {lst₀ : AState}
    {e : kernel.core_types.CheckError} (h : AErrSim e (c.run lst₀)) :
    AErrSim e ((Arena.scratchRun c).run lst₀) := by
  intro k hk
  obtain ⟨le, hle, hl⟩ := h k hk
  exact ⟨le, scratchRun_err hle, hl⟩

end ConRon.Refine2
