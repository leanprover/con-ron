/-
# `ConRon.Refine2.Frontend.Olean.Records` — `olean/records.rs` against `Arena/Frontend/Olean/Records.lean`

**Task #142, Theorem 2.**  The record stream, through the stream parser's own builder
(`process_line_core_d_refines`): `decls_go` is an induction on the records left, `decls_of` the
`StateD` whose name and expression tables are the emitter's.  `read_tail_rel` is everything of
`read_oleans` past the closure's load, on one snapshot of the store.
-/
import ConRon.Refine2.Frontend.Olean.EmitBlocks

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.merge (merge_all)
open frontend.olean.records (table_of decls_go decls_go_loop decls_of first_absent first_absent_loop
  root_constants emit_merged)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend (StateD ParseResultD processLineCoreD)
open ConRon.Arena.Frontend.Olean (Emit Merged declsGo declsOf rootConstants mergeAll blocksOk emitAll)

/-! ## The tables -/

theorem table_of_rel {T α : Type} {A : T → α} {dense : alloc.vec.Vec T} {a : Array α}
    (hd : dense.val.map A = a.toList) {t} (h : table_of dense = ok t) :
    IdTableRel A t ({ dense := a } : ConLeche.Frontend.IdTable α) := by
  rw [table_of] at h
  peel h as m, hm
  cases Result.ok_injective h
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap.new_refines (HashableInst := hU64) hm
  exact ⟨hd, ConRon.Refine.HashMap.RelOn_empty hnone, hinv⟩

/-! ## The records -/

/-- **`decls_go` is `declsGo`**, position for position. -/
theorem decls_go_loop_rel {pers : arena.store.PersTier} {rst : arena.monad.AState}
    (out : alloc.vec.Vec frontend.scan_types.DeclRec) (hw : ∀ d ∈ out.val, DeclRecStrWF d) (K : Nat) :
    ∀ (st : frontend.export_c.StateD) (lsd : StateD) (k : Std.Usize) (lst : AState) (r st'),
      AStateRel₀ pers rst lst → AStateInv pers rst → StateDRel st lsd →
      out.val.length - k.val = K →
      decls_go_loop pers rst.store st out k = ok (r, st') →
      match r with
      | .Ok _ => ∃ lsd' lst', (declsGo k.val ((out.val.drop k.val).map absDeclRec) lsd).run lst =
          .ok (.ok lsd', lst') ∧ StateDRel st' lsd' ∧ AStateRel₀ pers rst lst' ∧ AStateInv pers rst
      | .Err p => StreamErrSim p ((declsGo k.val ((out.val.drop k.val).map absDeclRec) lsd).run lst) := by
  induction K with
  | zero =>
    intro st lsd k lst r st' hrel hinv hd hk h
    rw [decls_go_loop, ite_eq_right (not_lt_len hk)] at h
    cases Result.ok_injective h
    rw [drop_stop hk]
    exact ⟨lsd, lst, rfl, hd, hrel, hinv⟩
  | succ K ih =>
    intro st lsd k lst r st' hrel hinv hd hk h
    rw [decls_go_loop, ite_eq_left (lt_len hk)] at h
    peel h as dr, hdr
    peel h as q, hq
    obtain ⟨r1, st1⟩ := q
    have hwd : DeclRecStrWF dr := hw dr (by
      have := ConRon.Refine.ExprOps.vec_index_getElem? hdr
      exact List.mem_of_getElem? this)
    have hsim := process_line_core_d_refines hrel hinv hd ⟨⟩ hwd hq
    rw [idx_cons hdr, List.map_cons, declsGo]
    cases r1 with
    | Ok u =>
      obtain ⟨lsd1, lst1, hx, hd1, -, hrel1, hinv1⟩ := hsim
      rw [am_bind_ok hx]
      peel h as k1, hk1
      have := ih st1 lsd1 k1 lst1 r st' hrel1 hinv1 hd1 (by rw [usize_succ hk1]; omega) h
      rwa [usize_succ hk1] at this
    | Err e =>
      peel h as i1, hi1
      peel h as p, hp
      cases Result.ok_injective h
      obtain ⟨hline, herr, hver⟩ := line_err_to_check_refines hp
      have hiv : i1.val = k.val := Frontend.cast_u64_usize hi1
      cases e with
      | Err ce =>
        intro k' hk'
        rw [herr ce rfl] at hk'
        obtain ⟨le, hle, hkle⟩ := (hsim : AErrSim ce _) k' hk'
        exact Or.inr (Or.inl ⟨le, by rw [StateT.run_bind, hle]; rfl, hkle⟩)
      | Verdict v =>
        obtain ⟨lv, lst1, hx, hkk⟩ := hsim
        intro k' hk'
        rw [hver v lv rfl hkk] at hk'
        refine Or.inl ⟨_, lst1, ?_, hk'⟩
        rw [am_bind_ok hx, hline]
        show _ = Except.ok (Except.error (lv.toError, i1.val), lst1)
        rw [hiv]
        rfl

/-- **`decls_of` is `declsOf`.** -/
theorem decls_of_rel {pers : arena.store.PersTier} {rst : arena.monad.AState} {lst : AState}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    {em : frontend.olean.emit.Emit} {lem : Emit} (he : EmitRel em lem) {o}
    (h : decls_of pers rst.store em = ok o) :
    SimStreamRel ParseResultDRel pers lst (o, rst) (declsOf lem) := by
  rw [decls_of] at h
  peel h as t1, h1
  peel h as t2, h2
  peel h as t3, h3
  peel h as q, hq
  obtain ⟨r, st⟩ := q
  rw [decls_go] at hq
  have hd0 : StateDRel ⟨t1, t2, t3, alloc.vec.Vec.new arena.env.IDeclaration⟩
      ⟨{ dense := lem.names }, {}, { dense := lem.exprs }, #[]⟩ :=
    ⟨table_of_rel he.names h1, id_table_empty_rel h2, table_of_rel he.exprs h3, rfl⟩
  have hgo := decls_go_loop_rel em.out he.wf _ _ _ 0#usize lst r st hrel hinv hd0 rfl hq
  rw [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero, he.out] at hgo
  unfold SimStreamRel
  rw [declsOf]
  cases r with
  | Err e =>
    cases Result.ok_injective h
    show StreamErrSim _ _
    rw [StateT.run_bind]
    exact StreamErrSim.bind hgo _ (fun _ _ => rfl)
  | Ok u =>
    obtain ⟨lsd', lst', hx, hd', hrel', hinv'⟩ := hgo
    peel h as prd, hprd
    cases Result.ok_injective h
    refine ⟨_, lst', ?_, parse_result_of_state_refines hd' hprd, hrel', hinv'⟩
    rw [am_bind_ok hx]
    rfl

/-! ## The roots -/

/-- `first_absent`: the first name the merge does not hold, or the length. -/
theorem first_absent_rel {mg : frontend.olean.merge.Merged} {mg' : Merged} (hm : MergedRel mg mg')
    {cs : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize} (h : first_absent mg cs = ok i) :
    (∃ x, cs.val[i.val]? = some x ∧
        (cs.val.map absNIdx).find? (fun n => !mg'.map.contains n) = some (absNIdx x)) ∨
      (cs.val.length ≤ i.val ∧ (cs.val.map absNIdx).find? (fun n => !mg'.map.contains n) = none) := by
  rw [first_absent] at h
  have key : ∀ (k : Nat) (j : Std.Usize), cs.val.length - j.val = k →
      first_absent_loop mg cs j = ok i →
      (∃ x, cs.val[i.val]? = some x ∧
          ((cs.val.drop j.val).map absNIdx).find? (fun n => !mg'.map.contains n) = some (absNIdx x)) ∨
        (cs.val.length ≤ i.val ∧
          ((cs.val.drop j.val).map absNIdx).find? (fun n => !mg'.map.contains n) = none) := by
    intro k
    induction k with
    | zero =>
      intro j hk h
      rw [first_absent_loop, ite_eq_right (not_lt_len hk)] at h
      cases Result.ok_injective h
      refine Or.inr ⟨by omega, ?_⟩
      rw [drop_stop hk]
      rfl
    | succ k ih =>
      intro j hk h
      rw [first_absent_loop, ite_eq_left (lt_len hk)] at h
      peel h as n, hn
      peel h as b, hb
      rw [idx_cons hn, List.map_cons, List.find?_cons, ← mg_has_eq hm hb]
      cases b with
      | true =>
        rw [ite_eq_left rfl] at h
        peel h as j1, hj1
        have := ih j1 (by rw [usize_succ hj1]; omega) h
        rw [usize_succ hj1] at this
        simpa using this
      | false =>
        rw [ite_eq_right (by simp)] at h
        cases Result.ok_injective h
        exact Or.inl ⟨n, ConRon.Refine.ExprOps.vec_index_getElem? hn, rfl⟩
  simpa using key _ 0#usize rfl h

theorem PR.internal_tail {α β : Type} {R : α → β → Prop} {v : alloc.vec.Vec Std.U32} {x : AM β}
    (hx : FailsInt x) :
    PR R (Std.bind (kernel.core_types.internal v)
      (fun ce => ok (core.result.Result.Err ce) : kernel.core_types.CheckError → Result (core.result.Result α kernel.core_types.CheckError))) x := by
  intro o h s
  peel h as ce, hce
  rw [kernel.core_types.internal] at hce
  cases Result.ok_injective hce
  cases Result.ok_injective h
  intro k hk
  cases hk
  exact hx s

/-- The constants' relation. -/
def RootsRel (v : alloc.vec.Vec arena.handle.NIdx) (a : Array NIdx) : Prop :=
  v.val.map absNIdx = a.toList

/-- **`root_constants` is `rootConstants`.** -/
theorem root_constants_pr {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {mg : frontend.olean.merge.Merged} {mg' : Merged} (hm : MergedRel mg mg')
    {c : Option (alloc.vec.Vec arena.handle.NIdx)} {c' : Option (Array NIdx)}
    (hc : Option.Rel RootsRel c c') :
    PR RootsRel (root_constants pers ar mg c) (rootConstants mg' c') := by
  cases hc with
  | none =>
    rw [root_constants]
    refine PR.pure_step fun v hv => ?_
    exact PR.pure (by rw [RootsRel, nidx_vec_dup_val hv]; exact hm.order)
  | some ha =>
    rename_i cs cs'
    rw [root_constants]
    refine PR.pure_step fun i hi => ?_
    have hf := first_absent_rel hm hi
    have ea : cs'.find? (fun n => !mg'.map.contains n) =
        (cs.val.map absNIdx).find? (fun n => !mg'.map.contains n) := by
      rw [show cs.val.map absNIdx = cs'.toList from ha]
      simp
    rw [rootConstants, ea]
    rcases hf with ⟨x, hx, hfx⟩ | ⟨hle, hfn⟩
    · rw [hfx]
      have hlt : i.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
      rw [ite_eq_left (by simp [alloc.vec.Vec.len]; scalar_tac)]
      refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ =>
        PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ =>
        PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.internal_tail ?_
      fails_int
    · rw [hfn, ite_eq_right (by simp [alloc.vec.Vec.len]; scalar_tac)]
      refine PR.pure_step fun v hv => ?_
      exact PR.pure (by rw [RootsRel, nidx_vec_dup_val hv]; exact ha)

/-! ## The tail of the read -/

/-- **`emit_merged`**: the check, the roots, the walk. -/
theorem emit_merged_pr {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {ar : arena.store.EStore} {mg : frontend.olean.merge.Merged} {mg' : Merged}
    (hm : MergedRel mg mg') {c : Option (alloc.vec.Vec arena.handle.NIdx)} {c' : Option (Array NIdx)}
    (hc : Option.Rel RootsRel c c') :
    PR EmitRel (emit_merged pk pers ar mg c)
      (do
        blocksOk (absPins pk) mg'
        let cs ← rootConstants mg' c'
        emitAll (absPins pk) mg' cs) := by
  intro o h s
  rw [emit_merged] at h
  peel h as r, hr
  have h1 := blocks_ok_pr hm (pk := pk) (pers := pers) (ar := ar) r hr s
  cases r with
  | Err e =>
    cases Result.ok_injective h
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind h1 _
  | Ok u =>
    obtain ⟨b, hb, -⟩ := h1
    rw [am_bind_ok hb]
    peel h as r1, hr1
    have h2 := root_constants_pr hm hc (pers := pers) (ar := ar) r1 hr1 s
    cases r1 with
    | Err e =>
      cases Result.ok_injective h
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind h2 _
    | Ok cs =>
      obtain ⟨cs', hcs, hR⟩ := h2
      rw [am_bind_ok hcs]
      exact emit_all_rel hm hR o h s

/-- **Everything of `read_oleans` past the closure's load**, on one snapshot of the store: the
merge, the check, the walk and the records. -/
theorem read_tail_rel {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {rst : arena.monad.AState} {lst : AState} (hrel : AStateRel₀ pers rst lst)
    (hinv : AStateInv pers rst) {ls : alloc.vec.Vec frontend.olean.lazy.Loaded}
    {ls' : Array Arena.Frontend.Olean.Loaded} (hls : List.Forall₂ LoadedRel ls.val ls'.toList)
    {c : Option (alloc.vec.Vec arena.handle.NIdx)} {c' : Option (Array NIdx)}
    (hc : Option.Rel RootsRel c c') {o ar'}
    (h : (do
      let r2 ← merge_all pk pers rst.store ls
      match r2 with
      | core.result.Result.Ok m =>
        let r3 ← emit_merged pk pers rst.store m c
        match r3 with
        | core.result.Result.Ok em =>
          let r4 ← decls_of pers rst.store em
          ok (r4, rst.store)
        | core.result.Result.Err e => ok (core.result.Result.Err (e, 0#u64), rst.store)
      | core.result.Result.Err e => ok (core.result.Result.Err (e, 0#u64), rst.store)) = ok (o, ar')) :
    ar' = rst.store ∧ SimStreamRel ParseResultDRel pers lst (o, rst)
      (do
        let mg ← mergeAll (absPins pk) ls'
        blocksOk (absPins pk) mg
        let cs ← rootConstants mg c'
        declsOf (← emitAll (absPins pk) mg cs)) := by
  peel h as r2, hr2
  have h1 := merge_all_rel (st := rst) (lst := lst) pk hls hrel hinv r2 hr2
  cases r2 with
  | Err e =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    refine ⟨rfl, ?_⟩
    show StreamErrSim _ _
    rw [StateT.run_bind]
    exact StreamErrSim.of_throw h1
  | Ok m =>
    obtain ⟨mg', lst1, hx, hm, hrel1, hinv1⟩ := h1
    peel h as r3, hr3
    have h2 := emit_merged_pr hm hc (pk := pk) (pers := pers) (ar := rst.store) r3 hr3 lst1
    have e : (do
          blocksOk (absPins pk) mg'
          let cs ← rootConstants mg' c'
          declsOf (← emitAll (absPins pk) mg' cs)) =
        (do
          blocksOk (absPins pk) mg'
          let cs ← rootConstants mg' c'
          emitAll (absPins pk) mg' cs) >>= declsOf := by
      simp only [bind_assoc]
    unfold SimStreamRel
    rw [am_bind_ok hx]
    dsimp only
    rw [e]
    cases r3 with
    | Err e =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      refine ⟨rfl, ?_⟩
      show StreamErrSim _ _
      rw [StateT.run_bind]
      exact StreamErrSim.of_throw h2
    | Ok em =>
      obtain ⟨lem, hl, he⟩ := h2
      peel h as r4, hr4
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      refine ⟨rfl, ?_⟩
      rw [am_bind_ok hl]
      exact decls_of_rel hrel1 hinv1 he hr4

end ConRon.Refine2.Frontend.Olean
