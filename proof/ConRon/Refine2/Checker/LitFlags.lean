/-
# `ConRon.Refine2.Checker.LitFlags` — the literal flags of an index, related

`arena::env`'s literal-name readers (`lit_name_at`, `lits_stored`, `nat_lit_stored_by`,
`str_lit_stored_by`) against the twin's (`litNameAt`, `IFEnv.litsStored`,
`IFEnv.natLitStoredBy`, `IFEnv.strLitStoredBy`), and the push that recomputes the flags
with them (`ifenv_push` ⊑ `IFEnv.push`).  Lockstep: each Rust reader is the twin's, the
Rust's literal names being the twin's base's (`BaseRel.lits`) and its lookups the twin's
(`ifenv_find_abs`).
-/
import ConRon.Refine2.Checker.Shape
import ConRon.Refine2.Core.Arms.Delta

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The twin's push, field by field -/

theorem twin_push_idx (fe : IFEnv) (c : IConstantInfo) :
    (fe.push c).idx = fe.idx.insert c.name c := by unfold IFEnv.push; dsimp only; split <;> rfl
theorem twin_push_base (fe : IFEnv) (c : IConstantInfo) :
    (fe.push c).base = fe.base := by unfold IFEnv.push; dsimp only; split <;> rfl
theorem twin_push_env (fe : IFEnv) (c : IConstantInfo) :
    (fe.push c).env = ⟨c :: fe.env.consts, fe.env.tables⟩ := by unfold IFEnv.push; dsimp only; split <;> rfl
theorem twin_push_tbls (fe : IFEnv) (c : IConstantInfo) :
    (fe.push c).tbls = fe.tbls := by unfold IFEnv.push; dsimp only; split <;> rfl
theorem twin_popTemp_idx (fe : IFEnv) (n : NIdx) (prev : Option IConstantInfo) :
    (fe.popTemp n prev).idx = (match prev with
      | some r => fe.idx.insert n r
      | none => fe.idx.erase n) := rfl
theorem twin_popTemp_base (fe : IFEnv) (n : NIdx) (prev : Option IConstantInfo) :
    (fe.popTemp n prev).base = fe.base := rfl
theorem twin_popTemp_env (fe : IFEnv) (n : NIdx) (prev : Option IConstantInfo) :
    (fe.popTemp n prev).env = ⟨fe.env.consts.tail, fe.env.tables⟩ := rfl
theorem twin_popTemp_tbls (fe : IFEnv) (n : NIdx) (prev : Option IConstantInfo) :
    (fe.popTemp n prev).tbls = fe.tbls := rfl

/-- **`lit_name_at` ⊑ `litNameAt`**: the literal names from cursor `i` on, against `n`. -/
theorem lit_name_at_abs (lits : alloc.vec.Vec arena.handle.NIdx) (n : arena.handle.NIdx) :
    ∀ (k : Nat) (i : Std.Usize) {b : Bool}, lits.val.length - i.val = k →
      arena.env.lit_name_at lits n i = ok b →
      b = litNameAt (lits.val.map absNIdx) (absNIdx n) i.val := by
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [arena.env.lit_name_at.eq_def] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len lits by scalar_tac)] at h
    obtain rfl := (Result.ok_injective h).symm
    rw [litNameAt.eq_1, dite_eq_right (by simp; omega)]
  | succ k ih =>
    intro i b hk h
    rw [arena.env.lit_name_at.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len lits by scalar_tac)] at h
    have hlt : i.val < (lits.val.map absNIdx).length := by simp; omega
    rw [litNameAt.eq_1, dite_eq_left hlt]
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hmv := vec_index_some hm
    have hget : (lits.val.map absNIdx)[i.val] = absNIdx m := by
      have h1 : (lits.val.map absNIdx)[i.val]? = some (absNIdx m) := by
        rw [List.getElem?_map, hmv]; rfl
      rw [List.getElem?_eq_getElem hlt] at h1
      exact Option.some.inj h1
    rw [hget]
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hev := nidx_eq2_abs he
    cases e with
    | true =>
      obtain rfl := (Result.ok_injective h).symm
      rw [ite_eq_left (by rw [← hev])]
    | false =>
      rw [ite_eq_right (by rw [← hev]; simp)]
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      rw [← hi2v]
      exact ih i2 (by omega) h

/-- **`lits_stored` ⊑ `IFEnv.litsStored`**: the frozen index's literal names from cursor
`i` to `stop`, each probed with `ifenv_find`. -/
theorem lits_stored_abs {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hctx : CoreCtx pers rf lf) (stop : Std.Usize) :
    ∀ (k : Nat) (i : Std.Usize) {b : Bool}, stop.val - i.val = k →
      arena.env.lits_stored pers rf i stop = ok b → b = lf.litsStored i.val stop.val := by
  have hl : lf.base.lits = pers.env.lits.val.map absNIdx := hctx.base.lits
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [arena.env.lits_stored.eq_def] at h
    rw [ite_eq_left (show i ≥ stop by scalar_tac)] at h
    obtain rfl := (Result.ok_injective h).symm
    rw [IFEnv.litsStored.eq_1, ite_eq_left (by omega)]
  | succ k ih =>
    intro i b hk h
    rw [arena.env.lits_stored.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ stop by scalar_tac)] at h
    rw [IFEnv.litsStored.eq_1, ite_eq_right (by omega)]
    by_cases hlen : i.val < pers.env.lits.val.length
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len pers.env.lits by scalar_tac)] at h
      have hlen' : i.val < lf.base.lits.length := by rw [hl]; simpa using hlen
      rw [dite_eq_left hlen']
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnv := vec_index_some hn
      have hget : lf.base.lits[i.val] = absNIdx n := by
        have h1 : lf.base.lits[i.val]? = some (absNIdx n) := by
          rw [hl, List.getElem?_map, hnv]; rfl
        rw [List.getElem?_eq_getElem hlen'] at h1
        exact Option.some.inj h1
      obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hf := ifenv_find_abs hctx ho
      rw [hget, ← hf]
      cases o with
      | none => exact (Result.ok_injective h).symm
      | some c =>
        simp only [Option.map_some]
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        rw [← hi2v]
        exact ih i2 (by omega) h
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len pers.env.lits by scalar_tac)] at h
      have hlen' : ¬ i.val < lf.base.lits.length := by rw [hl]; simpa using hlen
      rw [dite_eq_right hlen']
      exact (Result.ok_injective h).symm

theorem nat_lit_count_val : arena.env.NAT_LIT_COUNT.val = NAT_LIT_COUNT := by
  unfold arena.env.NAT_LIT_COUNT; rfl

theorem str_lit_count_val : arena.env.STR_LIT_COUNT.val = STR_LIT_COUNT := by
  unfold arena.env.STR_LIT_COUNT; rfl

/-- **`nat_lit_stored_by` ⊑ `IFEnv.natLitStoredBy`.** -/
theorem nat_lit_stored_by_abs {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hctx : CoreCtx pers rf lf) {b : Bool}
    (h : arena.env.nat_lit_stored_by pers rf = ok b) : b = lf.natLitStoredBy := by
  rw [arena.env.nat_lit_stored_by] at h
  have := lits_stored_abs hctx _ _ 0#usize rfl h
  rw [nat_lit_count_val] at this
  exact this

/-- **`str_lit_stored_by` ⊑ `IFEnv.strLitStoredBy`.** -/
theorem str_lit_stored_by_abs {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hctx : CoreCtx pers rf lf) {b : Bool}
    (h : arena.env.str_lit_stored_by pers rf = ok b) : b = lf.strLitStoredBy := by
  rw [arena.env.str_lit_stored_by] at h
  obtain ⟨b0, hb0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h0 := nat_lit_stored_by_abs hctx hb0
  rw [IFEnv.strLitStoredBy, ← h0]
  cases b0 with
  | false => exact (Result.ok_injective h).symm
  | true =>
    simp only [Bool.true_and]
    have := lits_stored_abs hctx _ _ _ rfl h
    rw [nat_lit_count_val, str_lit_count_val] at this
    exact this

/-- The relation at other literal flags, the same on both sides. -/
theorem IFEnvRel.withFlags {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (h : IFEnvRel pers rf lf) (a b : Bool) :
    IFEnvRel pers { rf with «nat_lit» := a, str_lit := b } { lf with natLit := a, strLit := b } :=
  ⟨⟨h.idx, h.tbls, h.base, h.below, h.belowRec, h.baseOK, rfl, rfl⟩, h.env⟩

/-- **The flags' recomputation ⊑ the twin's**: `nat_lit_stored_by`, then `str_lit_stored_by`
at the layer with its new `Nat` flag, as the twin's `IFEnv.push` does. -/
theorem lit_flags_refines {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf) {b b1 : Bool}
    (hb : arena.env.nat_lit_stored_by pers rf = ok b)
    (hb1 : arena.env.str_lit_stored_by pers { rf with «nat_lit» := b } = ok b1) :
    IFEnvRel pers { rf with «nat_lit» := b, str_lit := b1 }
      (let fe2 := { lf with natLit := lf.natLitStoredBy }
       { fe2 with strLit := fe2.strLitStoredBy }) := by
  have hb' := nat_lit_stored_by_abs { hfe.toIFEnvRead with inv := hfinv } hb
  subst hb'
  have hrel2 : IFEnvRel pers { rf with «nat_lit» := lf.natLitStoredBy }
      { lf with natLit := lf.natLitStoredBy } :=
    ⟨⟨hfe.idx, hfe.tbls, hfe.base, hfe.below, hfe.belowRec, hfe.baseOK, rfl, hfe.strLit⟩,
      hfe.env⟩
  have hctx2 : CoreCtx pers _ _ := { hrel2.toIFEnvRead with inv := hfinv }
  have hb1' := str_lit_stored_by_abs hctx2 hb1
  subst hb1'
  exact hfe.withFlags _ _

/-- **`ifenv_push` ⊑ `IFEnv.push`, relation and invariant together**: the row and the list
(`ifenv_push_row_rel`), and the literal flags recomputed under the same condition, at a
literal name before string literals are expandable. -/
theorem ifenv_push_refines {pers : arena.store.PersTier} {rf rf' : arena.env.IFEnv} {lf : IFEnv}
    {ci : arena.env.IConstantInfo}
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (h : arena.env.ifenv_push pers rf ci = ok rf') :
    IFEnvRel pers rf' (lf.push (absIConstantInfo ci)) ∧ IFEnvInv rf' := by
  rw [arena.env.ifenv_push] at h
  obtain ⟨n, hn, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hname : absNIdx n = (absIConstantInfo ci).name := i_constant_info_name_abs hn
  obtain ⟨⟨pers1, re⟩, hre, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  dsimp only at h2
  obtain ⟨s, hs, h3⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
  obtain ⟨q, hq, h4⟩ := ConRon.Refine.bind_eq_ok_iff.mp h3
  obtain ⟨v, hv, h5⟩ := ConRon.Refine.bind_eq_ok_iff.mp h4
  have hre' : pers1 = pers ∧
      re = (!lf.strLit && litNameAt lf.base.lits (absIConstantInfo ci).name 0) := by
    rw [hfe.strLit, hfe.base.lits, ← hname]
    split at hre
    · rename_i hst
      simp only [Result.ok.injEq, Prod.mk.injEq] at hre
      obtain ⟨rfl, rfl⟩ := hre
      simp [hst]
    · rename_i hst
      obtain ⟨re1, hre1, hre⟩ := ConRon.Refine.bind_eq_ok_iff.mp hre
      simp only [Result.ok.injEq, Prod.mk.injEq] at hre
      obtain ⟨rfl, rfl⟩ := hre
      refine ⟨rfl, ?_⟩
      rw [lit_name_at_abs _ _ _ _ rfl hre1]
      simp [hst]
  obtain ⟨hrow, hinv⟩ := ifenv_push_row_rel hfe hfinv hs hn hq hv
  rw [hre'.1] at h5
  unfold IFEnv.push
  dsimp only
  cases hrv : re with
  | true =>
    rw [hrv] at h5
    rw [ite_eq_left (by rw [← hre'.2, hrv])]
    obtain ⟨b, hb, h6⟩ := ConRon.Refine.bind_eq_ok_iff.mp h5
    obtain ⟨b1, hb1, h7⟩ := ConRon.Refine.bind_eq_ok_iff.mp h6
    obtain rfl := (Result.ok_injective h7).symm
    exact ⟨lit_flags_refines hrow hinv hb hb1, hinv⟩
  | false =>
    rw [hrv] at h5
    rw [ite_eq_right (by rw [← hre'.2, hrv]; simp)]
    obtain rfl := (Result.ok_injective h5).symm
    exact ⟨hrow, hinv⟩

/-- **`ifenv_push_temp` is `ifenv_push`**, with the displaced row handed back: the same
binds in the same order, the insert's old row returned. -/
theorem ifenv_push_temp_push {pers : arena.store.PersTier} {rf rf1 : arena.env.IFEnv}
    {ci : arena.env.IConstantInfo} {prev : Option Std.U64}
    (h : arena.env.ifenv_push_temp pers rf ci = ok (prev, rf1)) :
    arena.env.ifenv_push pers rf ci = ok rf1 ∧
    ∃ n s hm v, arena.env.i_constant_info_name ci = ok n ∧
      lift (UScalar.cast .U64 (alloc.vec.Vec.len rf.env.consts)) = ok s ∧
      ron.hashmap2.HashMap2.insert arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
        arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 rf.idx n s = ok (prev, hm) ∧
      alloc.vec.Vec.push rf.env.consts ci = ok v ∧
      rf1.env = { rf.env with consts := v } ∧ rf1.idx = hm ∧ rf1.tbls = rf.tbls ∧
      rf1.base_below = rf.base_below ∧ rf1.base_below_rec = rf.base_below_rec := by
  rw [arena.env.ifenv_push_temp] at h
  obtain ⟨n, hn, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨pers1, re⟩, hre, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  dsimp only at h2
  obtain ⟨s, hs, h3⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
  obtain ⟨⟨pv, hm⟩, hq, h4⟩ := ConRon.Refine.bind_eq_ok_iff.mp h3
  obtain ⟨v, hv, h5⟩ := ConRon.Refine.bind_eq_ok_iff.mp h4
  have key : arena.env.ifenv_push pers rf ci = ok rf1 ∧ pv = prev ∧
      rf1.env = { rf.env with consts := v } ∧ rf1.idx = hm ∧ rf1.tbls = rf.tbls ∧
      rf1.base_below = rf.base_below ∧ rf1.base_below_rec = rf.base_below_rec := by
    cases re with
    | true =>
      simp only [ite_true] at h5
      obtain ⟨b, hb, h6⟩ := ConRon.Refine.bind_eq_ok_iff.mp h5
      obtain ⟨b1, hb1, h7⟩ := ConRon.Refine.bind_eq_ok_iff.mp h6
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h7)
      refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [arena.env.ifenv_push, hn, bind_ok, hre, bind_ok]
      simp only [Aeneas.Std.uncurry_apply_pair]
      rw [hs, bind_ok, hq, bind_ok]
      simp only [Aeneas.Std.uncurry_apply_pair]
      rw [hv, bind_ok, ite_eq_left trivial, hb, bind_ok, hb1, bind_ok]
    | false =>
      simp only [Bool.false_eq_true, ite_false] at h5
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h5)
      refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [arena.env.ifenv_push, hn, bind_ok, hre, bind_ok]
      simp only [Aeneas.Std.uncurry_apply_pair]
      rw [hs, bind_ok, hq, bind_ok]
      simp only [Aeneas.Std.uncurry_apply_pair]
      rw [hv, bind_ok]
      rfl
  obtain ⟨hpush, rfl, he, hi, ht, hb, hbr⟩ := key
  exact ⟨hpush, n, s, hm, v, hn, hs, hq, hv, he, hi, ht, hb, hbr⟩

/-- **`ifenv_set_flags` ⊑ `IFEnv.setFlags`**, at the flags of a related layer (the one the
temporary pushes started from, saved before them on both sides). -/
theorem ifenv_set_flags_refines {pers : arena.store.PersTier} {rf rf0 r : arena.env.IFEnv}
    {lf lf0 : IFEnv} (hfe : IFEnvRelI pers rf lf) (h0 : IFEnvRel pers rf0 lf0)
    (h : arena.env.ifenv_set_flags rf rf0.nat_lit rf0.str_lit = ok r) :
    IFEnvRelI pers r (lf.setFlags lf0.natLit lf0.strLit) := by
  rw [arena.env.ifenv_set_flags] at h
  obtain rfl := (Result.ok_injective h).symm
  rw [h0.natLit, h0.strLit]
  exact ⟨hfe.rel.withFlags _ _, hfe.inv⟩

namespace Lockstep

/-- `ifenv_push`: the constant pushed onto the layer. -/
@[lockstep] theorem ifenv_push_spec {pers : arena.store.PersTier} {rf lf} (hfe : IFEnvRelI pers rf lf)
    (ci : arena.env.IConstantInfo) :
    LSP (arena.env.ifenv_push pers rf ci)
      (fun r => IFEnvRelI pers r (lf.push (absIConstantInfo ci))) :=
  fun _ h => ifenv_push_refines hfe.rel hfe.inv h

/-- `ifenv_set_flags`: the flags of the layer a temporary extension started from. -/
@[lockstep] theorem ifenv_set_flags_spec {pers : arena.store.PersTier} {rf rf0 lf lf0}
    (hfe : IFEnvRelI pers rf lf) (h0 : IFEnvRelI pers rf0 lf0) :
    LSP (arena.env.ifenv_set_flags rf rf0.nat_lit rf0.str_lit)
      (fun r => IFEnvRelI pers r (lf.setFlags lf0.natLit lf0.strLit)) :=
  fun _ h => ifenv_set_flags_refines hfe h0.rel h

end Lockstep

end ConRon.Refine2
