/-
# `ConRon.Refine2.Checker.Jobs` — Theorem 2 for a record's job

`arena::stream_index`'s `record_check`, `record_job` and `arena::checker`'s `run_job`
against `Arena/StreamIndex.lean` and `Arena/Checker.lean`.

Every job runs on a worker's frozen store, read through the tier `freeze_tier` moved the store's tables and the
index into (`tierWith`).  A job's environment is the view of its position, an empty layer
over the frozen index (`stream_index_view_rel`), so `check_decl_refines` applies at it as at
any other layer.  Between two jobs a worker is `AIdle` (`Refine2/Core/Bracket.lean`).
-/
import ConRon.Refine2.Checker.Top
import ConRon.Refine2.Checker.StreamIndex

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The tier the driver freezes -/

/-- **The tier `freeze_tier` builds**: the store's four persistent tables, `frozen`, and
the stream index. -/
def tierWith (ar : arena.store.EStore) (ix : arena.stream_index.IStreamIndex) :
    arena.store.PersTier :=
  { frozen := true, n := ar.lss.ls.ns.pers, l := ar.lss.ls.pers, ls := ar.lss.pers,
    e := ar.pers, env := ix }

/-! ## A record's job -/

/-- A cast that fits, at an index read. -/
private theorem cast_val {i : Std.U64} {x : Std.Usize} (hi : i.val ≤ Std.Usize.max)
    (h : lift (UScalar.cast .Usize i) = (ok x : Result Std.Usize)) : x.val = i.val := by
  rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hi]
  exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective h).symm

/-- **`record_check` ⊑ `recordCheck`, accepting**: the `And` pin, then the record's check
at the view of its position. -/
theorem record_check_refines {tier st lst} {I : IStreamIndex}
    {mode : kernel.env.CheckMode} {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {k : Std.U64} {pd : arena.env.IDeclaration} {st'}
    (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st) (hI : StreamIndexRel tier.env I)
    (hk : k.val ≤ Std.Usize.max)
    (hrun : arena.stream_index.record_check tier st mode pins k pd = ok (.Ok (), st')) :
    ∃ lst', (recordCheck (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I (absU k)
        (absIDeclaration pd)).run lst = .ok ((), lst') ∧
      AStateRel₀ tier st' lst' ∧ AStateInv tier st' := by
  rw [arena.stream_index.record_check] at hrun
  obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS1 := and_pin_ok_refines hrel hinv h1
  cases r with
  | Err e => cases Result.ok_injective hrun
  | Ok b =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hS1.apply
    cases b with
    | false =>
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
    | true =>
      obtain ⟨w, hw, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hfe := stream_index_view_rel hI hk hw
      obtain ⟨⟨r1, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hS2 := check_decl_refines hrel1 hinv1 hfe.rel hfe.inv h2
      cases r1 with
      | Err e => cases Result.ok_injective hrun
      | Ok fe2 =>
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
        obtain ⟨v, lst2, hx2, -, hrel2, hinv2⟩ := hS2
        refine ⟨lst2, ?_, hrel2, hinv2⟩
        simp only [recordCheck, StateT.run_bind, hx1, except_ok_bind, id]
        simp only [↓reduceIte]
        rw [StateT.run_bind, hx2]
        rfl

/-- **`record_job` ⊑ `recordJob`, accepting**, between two idle worker states: the
bracket opened (`enter_record`), the check, the bracket closed (`leave_record`). -/
theorem record_job_refines {tier st lst} {I : IStreamIndex}
    {mode : kernel.env.CheckMode} {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {k : Std.U64} {pd : arena.env.IDeclaration} {st'}
    (hidle : AIdle tier st lst) (hinv : AStateInv tier st) (htf : tier.frozen = true)
    (hI : StreamIndexRel tier.env I) (hk : k.val ≤ Std.Usize.max)
    (hrun : arena.stream_index.record_job tier st mode pins k pd = ok (.Ok (), st')) :
    ∃ lst', (recordJob (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I (absU k)
        (absIDeclaration pd)).run lst = .ok ((), lst') ∧
      AIdle tier st' lst' ∧ AStateInv tier st' := by
  rw [arena.stream_index.record_job] at hrun
  obtain ⟨st1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (enter_record_sim hidle hinv h1).apply
  obtain ⟨⟨r, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨st3, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := record_check_refines hrel1 hinv1 hI hk h2
  obtain ⟨lst3, hx3, hidle3, hinv3⟩ := leave_record_rel hrel2 hinv2 htf h3
  refine ⟨lst3, ?_, hidle3, hinv3⟩
  simp only [recordJob, StateT.run_bind, hx1, except_ok_bind, hx2, hx3]

/-- **`run_job` ⊑ `runJob`, accepting**: job `k`, the record at position `k`'s job; a
position past the records is an error on both sides, so an accept never names one.
`hk`: the driver's index is a `usize` cast up. -/
theorem run_job_refines {tier st lst} {I : IStreamIndex}
    {mode : kernel.env.CheckMode} {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {k : Std.U64} {st'}
    (hidle : AIdle tier st lst) (hinv : AStateInv tier st) (htf : tier.frozen = true)
    (hI : StreamIndexRel tier.env I) (hk : k.val ≤ Std.Usize.max)
    (hrun : arena.checker.run_job tier st mode pins ds k = ok (.Ok (), st')) :
    k.val < ds.val.length ∧
    ∃ lst', runJob (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I
        (absIDeclL ds).toArray (absU k) lst = .ok (.ok (), lst') ∧
      AIdle tier st' lst' ∧ AStateInv tier st' := by
  rw [arena.checker.run_job] at hrun
  obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hiv := cast_val hk hi
  by_cases hb : i < alloc.vec.Vec.len ds
  · rw [ite_eq_left hb] at hrun
    have hb' : k.val < ds.val.length := by
      have := (Std.UScalar.lt_equiv _ _).mp hb
      rw [hiv] at this
      simpa using this
    obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hi2v := cast_val hk hi2
    obtain ⟨pd, hpd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hpdv : ds.val[k.val]? = some pd := by rw [← hi2v]; exact vec_index_some hpd
    obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases r with
    | Err e => cases Result.ok_injective hrun
    | Ok u =>
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
      cases u
      obtain ⟨lst1, hx1, hidle1, hinv1⟩ := record_job_refines hidle hinv htf hI hk h1
      refine ⟨hb', lst1, ?_, hidle1, hinv1⟩
      have hget : (absIDeclL ds).toArray[absU k]? = some (absIDeclaration pd) := by
        simp [absIDeclL, absU, hpdv]
      simp only [runJob, hget]
      rw [show recordJob _ _ I (absU k) (absIDeclaration pd) lst = .ok ((), lst1) from hx1]
  · rw [ite_eq_right hb] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun

end ConRon.Refine2
