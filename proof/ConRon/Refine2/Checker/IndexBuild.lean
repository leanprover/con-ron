/-
# `ConRon.Refine2.Checker.IndexBuild` — Theorem 2 for the stream index's build

`arena::stream_index`'s `stream_index_add` and `build_index` against
`Arena/StreamIndex.lean`'s `IStreamIndex.add` and `buildIndex`.  The index is built on the
driver's owned store, read through `pers`, from what each record installs
(`decl_constants`, `decl_tables`: `Refine2/Checker/Install.lean`).
-/
import ConRon.Refine2.Checker.Install
import ConRon.Refine2.Checker.StreamIndex

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

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
  | Err e => cases Result.ok_injective hrun
  | Ok cs =>
    obtain ⟨⟨r1, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨L, lst1, hx1, hL, hrel1, hinv1⟩ := hS1
    have hS2 := decl_tables_refines hrel1 hinv1 h2
    cases r1 with
    | Err e => cases Result.ok_injective hrun
    | Ok ts =>
      obtain ⟨Q, lst2, hx2, hQ, hrel2, hinv2⟩ := hS2
      obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hr2v := len_cast_val' hr2
      obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hvv : v.val = ix.firsts.val ++ [ix.next] := ConRon.Refine.vec_push_val hv
      obtain ⟨ix2, hix2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨ii, hii, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hii', rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
      cases hii'
      obtain ⟨hC, hN, hTb, hTm, hF⟩ := insert_consts_rel cs _ { ix with firsts := v } 0#usize
        I.base.idx rfl ⟨hI.consts.rows, hI.consts.len, hI.consts.inv, hI.consts.range⟩ hix2
      obtain ⟨hT, hCs, hIdx, hNx, hF2⟩ := insert_tables_rel r2 ts _ ix2 0#usize I.base.tbls
        rfl (by
          exact ⟨fun n => by simp only [ixTbl]; rw [hTb, hTm]; exact hI.tables.rows n,
            by rw [hTm]; exact hI.tables.inv,
            fun n p hp => by rw [hTb]; rw [hTm] at hp; exact hI.tables.range n p hp⟩) hii
      let I' : IStreamIndex :=
        { base := { I.base with idx := (insertConsts I.base.idx I.next L).1,
                                tbls := insertTables I.base.tbls I.firsts.size Q }
          firsts := I.firsts.push I.next, next := (insertConsts I.base.idx I.next L).2 }
      refine ⟨I', lst2, ?_, hrel2, hinv2, ⟨?_, ?_, ?_, ?_⟩⟩
      · simp only [IStreamIndex.add, StateT.run_bind, hx1, hx2, except_ok_bind]
        rfl
      · -- the constants: unmoved by the table insertion
        show IxConsts _ (insertConsts I.base.idx I.next L).1
        simp only [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at hC
        rw [hI.next, hL]
        have hC' := hC
        exact ⟨fun n => by simp only [ixRow]; rw [hCs, hIdx]; exact hC'.rows n,
          by rw [hCs, hNx]; exact hC'.len, by rw [hIdx]; exact hC'.inv,
          fun n c hc => by rw [hCs]; rw [hIdx] at hc; exact hC'.range n c hc⟩
      · show IxTables _ (insertTables I.base.tbls I.firsts.size Q)
        simp only [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at hT
        have hpos : absU r2 = I.firsts.size := by
          rw [absU, hr2v, ← Array.length_toList, hI.firsts, List.length_map]
        rw [hQ, ← hpos]
        exact hT
      · show (I.firsts.push I.next).toList = _
        rw [Array.toList_push, hI.firsts, hF2, hF, hvv, hI.next]
        simp
      · show (insertConsts I.base.idx I.next L).2 = _
        simp only [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at hN
        rw [hI.next, hL, ← hN, hNx]

/-! ## The freeze -/

open Lockstep in
/-- `nat_lit_names` ⊑ `natLitNames`: three pin reads, the handles in order. -/
@[lockstep] theorem nat_lit_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxList a) (arena.env.nat_lit_names st) st lst natLitNames := by
  apply LSR.of_LS
  rw [arena.env.nat_lit_names, natLitNames]
  lockstep

open Lockstep in
/-- `str_lit_names` ⊑ `strLitNames`: the `Nat` names, then seven pin reads. -/
@[lockstep] theorem str_lit_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxList a) (arena.env.str_lit_names st) st lst strLitNames := by
  apply LSR.of_LS
  rw [arena.env.str_lit_names, strLitNames]
  lockstep

/-- **`lit_from` ⊑ `litFrom`**: the frozen index's counters of the literal names from cursor
`i` to `stop`; the counter is in range of the constant list, so `c + 1` does not overflow. -/
theorem lit_from_abs {ix : arena.stream_index.IStreamIndex}
    {idx : Std.HashMap NIdx (Nat × IConstantInfo)} (hC : IxConsts ix idx)
    (lits : alloc.vec.Vec arena.handle.NIdx) (stop : Std.Usize) :
    ∀ (m : Nat) (i : Std.Usize) {o : Option Std.U64}, stop.val - i.val = m →
      arena.env.lit_from ix.idx lits i stop = ok o →
      o.map absU = litFrom idx (lits.val.map absNIdx) i.val stop.val := by
  intro m
  induction m with
  | zero =>
    intro i o hm h
    rw [arena.env.lit_from.eq_def] at h
    rw [ite_eq_left (show i ≥ stop by scalar_tac)] at h
    obtain rfl := (Result.ok_injective h).symm
    rw [litFrom.eq_1, ite_eq_left (by omega)]
    rfl
  | succ m ih =>
    intro i o hm h
    rw [arena.env.lit_from.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ stop by scalar_tac)] at h
    rw [litFrom.eq_1, ite_eq_right (by omega)]
    by_cases hlen : i.val < lits.val.length
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len lits by scalar_tac)] at h
      have hlen' : i.val < (lits.val.map absNIdx).length := by simpa using hlen
      rw [dite_eq_left hlen']
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnv := vec_index_some hn
      have hget : (lits.val.map absNIdx)[i.val] = absNIdx n := by
        have h1 : (lits.val.map absNIdx)[i.val]? = some (absNIdx n) := by
          rw [List.getElem?_map, hnv]; rfl
        rw [List.getElem?_eq_getElem hlen'] at h1
        exact Option.some.inj h1
      rw [hget, ← hC.rows n]
      obtain ⟨g, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hgv := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hC.inv
        ConRon.Refine.HashMap2.KeysOk_true trivial hg
      unfold ixRow
      rw [← hgv]
      cases g with
      | none => exact congrArg (Option.map absU) (Result.ok_injective h).symm
      | some c =>
        have hc : c.val < ix.consts.val.length := hC.range n c hgv.symm
        obtain ⟨ci, hci⟩ : ∃ ci, ix.consts.val[c.val]? = some ci :=
          ⟨_, List.getElem?_eq_getElem hc⟩
        simp only [Option.bind_some, hci, Option.map_some]
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have ihr := ih i2 (by omega) hr
        rw [hi2v] at ihr
        rw [← ihr]
        cases r with
        | none => exact congrArg (Option.map absU) (Result.ok_injective h).symm
        | some k =>
          simp only [Option.map_some]
          have hlenmax : ix.consts.val.length ≤ Std.Usize.max := ix.consts.property
          obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hc1v : c1.val = c.val + 1 := by
            have := ConRon.Refine.HashMap.uscalar_add_eq hc1; exact this
          by_cases hk : c1 ≤ k
          · rw [ite_eq_left hk] at h
            obtain rfl := (Result.ok_injective h).symm
            rw [ite_eq_left (by simp only [absU]; scalar_tac)]
            rfl
          · rw [ite_eq_right hk] at h
            obtain rfl := (Result.ok_injective h).symm
            rw [ite_eq_right (by simp only [absU]; scalar_tac)]
            simp only [Option.map_some, absU, hc1v]
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len lits by scalar_tac)] at h
      have hlen' : ¬ i.val < (lits.val.map absNIdx).length := by simpa using hlen
      rw [dite_eq_right hlen']
      obtain rfl := (Result.ok_injective h).symm
      rfl

/-- **`stream_index_freeze` ⊑ `IStreamIndex.freeze`**: the literal names off the pin table,
the two thresholds over them; the rest of the index as it was. -/
theorem stream_index_freeze_refines {pers st lst} {ix ix' : arena.stream_index.IStreamIndex}
    {I : IStreamIndex}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hI : StreamIndexRel ix I)
    (h : arena.stream_index.stream_index_freeze st ix = ok (.Ok ix')) :
    ∃ F lst', I.freeze lst = .ok (F, lst') ∧ AStateRel₀ pers st lst' ∧
      StreamIndexRel ix' F ∧ FrozenRel ix' F := by
  rw [arena.stream_index.stream_index_freeze] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hls := str_lit_names_ls hrel hinv r hr
  cases r with
  | Err e => simp at h
  | Ok lits =>
    obtain ⟨b, lst', hb, rfl, hrel', -⟩ := hls
    obtain ⟨nf, hnf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨sf, hsf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp only [core.result.Result.Ok.injEq] at h'
    subst h'
    have hnfv := lit_from_abs hI.consts lits _ _ 0#usize rfl hnf
    have hsfv := lit_from_abs hI.consts lits _ _ 0#usize rfl hsf
    rw [nat_lit_count_val] at hnfv
    rw [str_lit_count_val] at hsfv
    let B : IFBase := { I.base with lits := absNIdxList lits }
    let F : IStreamIndex := { I with base := B
                                     natFrom := litFrom I.base.idx (absNIdxList lits) 0 NAT_LIT_COUNT
                                     strFrom := litFrom I.base.idx (absNIdxList lits) 0 STR_LIT_COUNT }
    refine ⟨F, lst', ?_, hrel',
      ⟨⟨fun n => hI.consts.rows n, hI.consts.len, hI.consts.inv, hI.consts.range⟩,
        ⟨fun n => hI.tables.rows n, hI.tables.inv, hI.tables.range⟩, hI.firsts, hI.next⟩,
      ⟨rfl, ?_, ?_⟩⟩
    · show (do let lits ← strLitNames; pure _ : AM IStreamIndex).run lst = _
      simp only [StateT.run_bind, hb]
      rfl
    · exact hnfv.symm
    · exact hsfv.symm

/-- **`build_index`'s loop ⊑ `buildIndexGo`, accepting**: the records from cursor `i` on,
each into the index, in order. -/
theorem build_index_loop_refines {pers} (ds : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (m : Nat) {st lst} {ix ix' : arena.stream_index.IStreamIndex} {I : IStreamIndex}
      {i : Std.Usize} {st'} (k : Nat),
      ds.val.length - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st → StreamIndexRel ix I →
      arena.stream_index.build_index_loop pers st ds ix i = ok (.Ok ix', st') →
      ∃ I' lst', buildIndexGo I k ((absIDeclL ds).drop i.val) lst = .ok (.ok I', lst') ∧
        AStateRel₀ pers st' lst' ∧ AStateInv pers st' ∧ StreamIndexRel ix' I' ∧
        FrozenRel ix' I' := by
  intro m
  induction m with
  | zero =>
    intro st lst ix ix' I i st' k hm hrel hinv hI hrun
    rw [arena.stream_index.build_index_loop.eq_def] at hrun
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ds by scalar_tac)] at hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases r with
    | Err e =>
      obtain ⟨i2, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
    | Ok fx =>
      obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
      cases h1
      obtain ⟨F, lst', hF, hrel', hIF, hFR⟩ := stream_index_freeze_refines hrel hinv hI hr
      rw [List.drop_eq_nil_of_le (by simp [absIDeclL]; omega)]
      refine ⟨F, lst', ?_, hrel', hinv, hIF, hFR⟩
      show (match I.freeze lst with
        | Except.ok (F, s') => Except.ok (Except.ok F, s')
        | Except.error e => Except.ok (Except.error (e, k), lst)) = _
      rw [show I.freeze lst = .ok (F, lst') from hF]
  | succ m ih =>
    intro st lst ix ix' I i st' k hm hrel hinv hI hrun
    rw [arena.stream_index.build_index_loop.eq_def] at hrun
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ds by scalar_tac)] at hrun
    have hlt : i.val < ds.val.length := by omega
    obtain ⟨pd, hpd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hpdv : ds.val[i.val]? = some pd := vec_index_some hpd
    obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases r with
    | Err e =>
      obtain ⟨i3, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
    | Ok ix2 =>
      obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi3v : i3.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi3
      obtain ⟨I2, lst1, hx1, hrel1, hinv1, hI2⟩ := stream_index_add_refines hrel hinv hI h1
      obtain ⟨I', lst', hx, hrel', hinv', hI', hF'⟩ := ih (k + 1) (by omega) hrel1 hinv1 hI2 hrun
      refine ⟨I', lst', ?_, hrel', hinv', hI', hF'⟩
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

/-- **`build_index` ⊑ `buildIndexGo`, accepting**: its loop, from cursor `i`. -/
theorem build_index_refines {pers} (ds : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (m : Nat) {st lst} {ix ix' : arena.stream_index.IStreamIndex} {I : IStreamIndex}
      {i : Std.Usize} {st'} (k : Nat),
      ds.val.length - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st → StreamIndexRel ix I →
      arena.stream_index.build_index pers st ix ds i = ok (.Ok ix', st') →
      ∃ I' lst', buildIndexGo I k ((absIDeclL ds).drop i.val) lst = .ok (.ok I', lst') ∧
        AStateRel₀ pers st' lst' ∧ AStateInv pers st' ∧ StreamIndexRel ix' I' ∧
        FrozenRel ix' I' :=
  fun m => build_index_loop_refines ds m

/-- **The driver's index build ⊑ `buildIndex`**: from the empty index. -/
theorem build_index_empty_refines {pers st lst} {ds : alloc.vec.Vec arena.env.IDeclaration}
    {ix : arena.stream_index.IStreamIndex} {st'}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.stream_index.build_index pers st ixEmpty ds 0#usize = ok (.Ok ix, st')) :
    ∃ I lst', buildIndex (absIDeclL ds).toArray lst = .ok (.ok I, lst') ∧
      AStateRel₀ pers st' lst' ∧ AStateInv pers st' ∧ StreamIndexRel ix I ∧ FrozenRel ix I := by
  obtain ⟨I, lst', hx, h⟩ := build_index_refines ds _ 0 rfl hrel hinv ixEmpty_rel hrun
  exact ⟨I, lst', by simpa [buildIndex] using hx, h⟩

end ConRon.Refine2
