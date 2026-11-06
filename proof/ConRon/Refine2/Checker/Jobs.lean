/-
# `ConRon.Refine2.Checker.Jobs` — Theorem 2 for the stream index's build and a record's job

`arena::stream_index`'s `stream_index_add`, `build_index`, `record_check`, `record_job` and
`arena::checker`'s `run_job` against `Arena/StreamIndex.lean` and `Arena/Checker.lean`.

The index is built on the driver's owned store, read through `pers`; every job runs on a
worker's frozen store, read through the tier `freeze_tier` moved the store's tables and the
index into (`tierWith`).  A job's environment is the view of its position, an empty layer
over the frozen index (`stream_index_view_rel`), so `check_decl_refines` applies at it as at
any other layer.  Between two jobs a worker is `AIdle` (`Refine2/Core/Bracket.lean`).
-/
import ConRon.Refine2.Checker.Top
import ConRon.Refine2.Checker.Install
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

/-! ## The index build -/

/-- A cast of a `Vec`'s length up to a `u64` is its value. -/
private theorem len_cast_val' {α : Type} {v : alloc.vec.Vec α} {s : Std.U64}
    (hs : lift (UScalar.cast .U64 (alloc.vec.Vec.len v)) = (ok s : Result Std.U64)) :
    s.val = v.val.length := by
  simp only [lift, Result.ok.injEq] at hs
  subst hs
  rw [usize_cast_u64_val']
  simp [alloc.vec.Vec.len]

/-- **`stream_index_add` ⊑ `IStreamIndex.add`, accepting**: the record's constants and
tables read off it (`decl_constants`, `decl_tables`), its first counter recorded, the
constants inserted from that counter on and the tables at the record's position. -/
theorem stream_index_add_refines {pers st lst} {ix ix' : arena.stream_index.IStreamIndex}
    {I : IStreamIndex} {pd : arena.env.IDeclaration} {st'}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hI : StreamIndexRel ix I)
    (hrun : arena.stream_index.stream_index_add pers st ix pd = ok (.Ok ix', st')) :
    ∃ I' lst', (I.add (absIDeclaration pd)).run lst = .ok (I', lst') ∧
      AStateRel₀ pers st' lst' ∧ AStateInv pers st' ∧ StreamIndexRel ix' I' := by
  rw [arena.stream_index.stream_index_add] at hrun
  obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS1 := decl_constants_refines hrel hinv h1
  cases r with
  | Err e => simp only at hrun; cases Result.ok_injective hrun
  | Ok cs =>
    simp only at hrun
    obtain ⟨⟨r1, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨L, lst1, hx1, hL, hrel1, hinv1⟩ := hS1
    have hS2 := decl_tables_refines hrel1 hinv1 h2
    cases r1 with
    | Err e => simp only at hrun; cases Result.ok_injective hrun
    | Ok ts =>
      simp only at hrun
      obtain ⟨Q, lst2, hx2, hQ, hrel2, hinv2⟩ := hS2
      obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hr2v := len_cast_val' hr2
      obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hvv : v.val = ix.firsts.val ++ [ix.next] := ConRon.Refine.vec_push_val hv
      obtain ⟨ix2, hix2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨ii, hii, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
      obtain ⟨hC, hN, hTb, hTm, hF⟩ := insert_consts_rel cs _ { ix with firsts := v } 0#usize
        I.base.idx (by simp) ⟨hI.consts.rows, hI.consts.len, hI.consts.inv, hI.consts.range⟩ hix2
      obtain ⟨hT, hCs, hIdx, hNx, hF2⟩ := insert_tables_rel r2 ts _ ix2 0#usize I.base.tbls
        (by simp) (by
          rw [show ix2.tables = ix.tables from hTb, show ix2.tbls = ix.tbls from hTm]
          exact ⟨fun n => by simp only [ixTbl]; rw [hTb, hTm]; exact hI.tables.rows n,
            by rw [hTm]; exact hI.tables.inv,
            fun n p hp => by rw [hTb]; rw [hTm] at hp; exact hI.tables.range n p hp⟩) hii
      refine ⟨_, lst2, ?_, hrel2, hinv2, ⟨?_, ?_, ?_, ?_⟩⟩
      · simp only [IStreamIndex.add, StateT.run_bind, hx1, hx2, except_ok_bind]
        rfl
      · -- the constants: unmoved by the table insertion
        rw [← hL]
        simp only [List.drop_zero] at hC
        have hC' := hC
        exact ⟨fun n => by simp only [ixRow]; rw [hCs, hIdx]; exact hC'.rows n,
          by rw [hCs, hNx]; exact hC'.len, by rw [hIdx]; exact hC'.inv,
          fun n c hc => by rw [hCs]; rw [hIdx] at hc; exact hC'.range n c hc⟩
      · simp only [List.drop_zero] at hT
        rw [← hQ]
        have hpos : absU r2 = I.firsts.size := by
          rw [absU, hr2v, ← Array.length_toList, hI.firsts, List.length_map]
        rw [← hpos]
        exact hT
      · simp only [Array.toList_push, hI.firsts, hF2, hF, hvv, List.map_append, List.map_cons,
          List.map_nil, hI.next]
      · simp only [List.drop_zero] at hN
        rw [← hL, ← hN, hNx, hI.next]

/-- **`build_index` ⊑ `buildIndexGo`, accepting**: the records from cursor `i` on, each
into the index, in order. -/
theorem build_index_refines {pers} (ds : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (m : Nat) {st lst} {ix ix' : arena.stream_index.IStreamIndex} {I : IStreamIndex}
      {i : Std.Usize} {st'} (k : Nat),
      ds.val.length - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st → StreamIndexRel ix I →
      arena.stream_index.build_index pers st ix ds i = ok (.Ok ix', st') →
      ∃ I' lst', buildIndexGo I k ((absIDeclL ds).drop i.val) lst = .ok (.ok I', lst') ∧
        AStateRel₀ pers st' lst' ∧ AStateInv pers st' ∧ StreamIndexRel ix' I' := by
  intro m
  induction m with
  | zero =>
    intro st lst ix ix' I i st' k hm hrel hinv hI hrun
    rw [arena.stream_index.build_index.eq_def] at hrun
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ds by scalar_tac)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
    rw [List.drop_eq_nil_of_le (by simp [absIDeclL]; omega)]
    exact ⟨I, lst, rfl, hrel, hinv, by cases (core.result.Result.Ok.inj ‹_›); exact hI⟩
  | succ m ih =>
    intro st lst ix ix' I i st' k hm hrel hinv hI hrun
    rw [arena.stream_index.build_index.eq_def] at hrun
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ds by scalar_tac)] at hrun
    have hlt : i.val < ds.val.length := by omega
    obtain ⟨pd, hpd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hpdv : ds.val[i.val]? = some pd := vec_index_some hpd
    obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases r with
    | Err e =>
      simp only at hrun
      obtain ⟨i3, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
    | Ok ix2 =>
      simp only at hrun
      obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi3v : i3.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi3
      obtain ⟨I2, lst1, hx1, hrel1, hinv1, hI2⟩ := stream_index_add_refines hrel hinv hI h1
      obtain ⟨I', lst', hx, hrel', hinv', hI'⟩ := ih (k + 1) (by omega) hrel1 hinv1 hI2 hrun
      refine ⟨I', lst', ?_, hrel', hinv', hI'⟩
      have hdrop : (absIDeclL ds).drop i.val =
          absIDeclaration pd :: (absIDeclL ds).drop i3.val := by
        rw [hi3v, absIDeclL, ← List.map_drop, ← List.map_drop,
          List.drop_eq_getElem_cons hlt, List.map_cons]
        rw [List.getElem?_eq_getElem hlt] at hpdv
        rw [Option.some_inj.mp hpdv]
      rw [hdrop, buildIndexGo]
      show (match (I.add (absIDeclaration pd)).run lst with
        | .ok (I'', s') => buildIndexGo I'' (k + 1) _ s'
        | .error e => .ok (.error (e, k), lst)) = _
      rw [hx1]
      exact hx

/-- **The driver's index build ⊑ `buildIndex`**: from the empty index. -/
theorem build_index_empty_refines {pers st lst} {ds : alloc.vec.Vec arena.env.IDeclaration}
    {ix : arena.stream_index.IStreamIndex} {st'}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.stream_index.build_index pers st ixEmpty ds 0#usize = ok (.Ok ix, st')) :
    ∃ I lst', buildIndex (absIDeclL ds).toArray lst = .ok (.ok I, lst') ∧
      AStateRel₀ pers st' lst' ∧ AStateInv pers st' ∧ StreamIndexRel ix I := by
  obtain ⟨I, lst', hx, h⟩ := build_index_refines ds _ 0 rfl hrel hinv ixEmpty_rel hrun
  exact ⟨I, lst', by simpa [buildIndex] using hx, h⟩

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
  | Err e => simp only at hrun; cases Result.ok_injective hrun
  | Ok b =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hS1.apply
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
    | true =>
      simp only [↓reduceIte] at hrun
      obtain ⟨w, hw, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hfe := stream_index_view_rel hI hk hw
      obtain ⟨⟨r1, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hS2 := check_decl_refines hrel1 hinv1 hfe.rel hfe.inv h2
      cases r1 with
      | Err e => simp only at hrun; cases Result.ok_injective hrun
      | Ok fe2 =>
        simp only at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
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
  rfl

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
    | Err e => simp only at hrun; cases Result.ok_injective hrun
    | Ok u =>
      simp only at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
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
