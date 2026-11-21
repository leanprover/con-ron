/-
# `ConRon.Refine2.Frontend.Olean.Records` — `olean/records.rs` against `Arena/Frontend/Olean/Records.lean`

**Task #142, Theorem 2.**  The record stream, through the stream parser's own builder
(`process_line_core_d_refines`): `decls_go` is an induction on the records left, `decls_of` the
`StateD` whose name and expression tables are the emitter's.  `read_tail_rel` is everything of
`read_oleans` past the closure's load, on one snapshot of the store.
-/
import ConRon.Refine2.Frontend.Olean.EmitBlocks
import ConRon.Refine2.Frontend.Olean.Contract
import ConRon.Refine2.Frontend.Top

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.merge (merge_all)
open frontend.olean.records (table_of decls_go decls_go_loop decls_of first_absent first_absent_loop
  root_constants mod_refs mod_refs_loop)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend (StateD ParseResultD processLineCoreD)
open ConRon.Arena.Frontend.Olean (Emit Merged declsGo declsOf rootConstants mergeAll blocksOk emitAll)
open ConRon.Refine.HashMap2 (Inv RelOn toFun)

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

/-! ## A compared run's reads: the held constants and the homes -/

/-- **`held_constants`' loop is the twin's filter**, from position `i`. -/
theorem held_constants_loop_rel {mg : frontend.olean.merge.Merged} {mg' : Merged}
    (hm : MergedRel mg mg') (cs : alloc.vec.Vec arena.handle.NIdx) (K : Nat) :
    ∀ (out : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) {o}, cs.val.length - i.val = K →
      frontend.olean.records.held_constants_loop mg cs out i = ok o →
      o.val.map absNIdx = out.val.map absNIdx ++
        ((cs.val.drop i.val).map absNIdx).filter (mg'.map.contains ·) := by
  induction K with
  | zero =>
    intro out i o hk h
    rw [frontend.olean.records.held_constants_loop, ite_eq_right (not_lt_len hk)] at h
    cases Result.ok_injective h
    rw [drop_stop hk]
    simp
  | succ K ih =>
    intro out i o hk h
    rw [frontend.olean.records.held_constants_loop, ite_eq_left (lt_len hk)] at h
    peel h as n, hn
    peel h as b, hb
    peel h as out1, ho1
    peel h as i2, hi2
    have e := ih out1 i2 (by rw [usize_succ hi2]; omega) h
    rw [usize_succ hi2] at e
    rw [e, idx_cons hn, List.map_cons, List.filter_cons, ← mg_has_eq hm hb]
    cases b with
    | true =>
      rw [ite_eq_left rfl] at ho1
      peel ho1 as n1, hn1
      rw [nidx_dup2_ok hn1] at ho1
      rw [ConRon.Refine.vec_push_val ho1]
      simp
    | false =>
      rw [ite_eq_right (by simp)] at ho1
      cases Result.ok_injective ho1
      simp

/-- **`held_constants` is `heldConstants`**: the named constants the closure holds. -/
theorem held_constants_rel {mg : frontend.olean.merge.Merged} {mg' : Merged}
    (hm : MergedRel mg mg') {c : Option (alloc.vec.Vec arena.handle.NIdx)}
    {c' : Option (Array NIdx)} (hc : Option.Rel RootsRel c c') {o}
    (h : frontend.olean.records.held_constants mg c = ok o) :
    Option.Rel RootsRel o (Arena.Frontend.Olean.heldConstants mg' c') := by
  rw [frontend.olean.records.held_constants.eq_def] at h
  cases hc with
  | none =>
    cases Result.ok_injective h
    exact Option.Rel.none
  | some ha =>
    rename_i cs cs'
    peel h as out, hout
    cases Result.ok_injective h
    refine Option.Rel.some ?_
    have e := held_constants_loop_rel hm cs _ _ 0#usize rfl hout
    rw [RootsRel, e]
    simp only [show (alloc.vec.Vec.new arena.handle.NIdx).val = [] from rfl, List.map_nil,
      List.nil_append, show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero]
    rw [show cs.val.map absNIdx = cs'.toList from ha]
    simp

/-- The twin's step at one stored constant of module `m`. -/
@[reducible] def homeStep (m : NIdx) (h : Std.HashMap NIdx NIdx)
    (c : Arena.Frontend.Olean.CEntry) : Std.HashMap NIdx NIdx :=
  if h.contains c.c.name then h else h.insert c.c.name m

/-- One step of `homes_of`: the name kept where it has a home, else its module inserted. -/
theorem homes_step_rel {h : ron.hashmap2.HashMap2 arena.handle.NIdx arena.handle.NIdx}
    {h' : Std.HashMap NIdx NIdx} (hr : HomesRel h h') {n m : arena.handle.NIdx} {b : Bool}
    (hb : ron.hashmap2.HashMap2.contains_key arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 h n = ok b) {h1}
    (h2 : (if b then ok h else do
      let n ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 n
      let n1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 m
      let (_, h2) ← ron.hashmap2.HashMap2.insert arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
        arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 h n n1
      ok h2) = ok h1) :
    HomesRel h1 (if h'.contains (absNIdx n) then h' else h'.insert (absNIdx n) (absNIdx m)) := by
  have e1 := ConRon.Refine.HashMap2.contains_key_refines_gen nidx_eq2 hr.inv (anyNKeysOk _) trivial hb
  have hk := hr.map n trivial
  have eb : b = h'.contains (absNIdx n) := by
    rw [e1, Std.HashMap.contains_eq_isSome_getElem?, ← hk]
    cases ConRon.Refine.HashMap2.toFun h n <;> rfl
  subst eb
  cases hc : h'.contains (absNIdx n) with
  | true =>
    rw [hc, ite_eq_left rfl] at h2
    cases Result.ok_injective h2
    exact hr
  | false =>
    rw [hc, ite_eq_right (by simp)] at h2
    peel h2 as x, hx
    peel h2 as y, hy
    peel h2 as q, hq
    obtain ⟨old, map2⟩ := q
    cases Result.ok_injective h2
    rw [nidx_dup2_ok hx, nidx_dup2_ok hy] at hq
    have h3 := ConRon.Refine.HashMap2.Rel_insert_wf nidx_eq2 (fun _ _ _ _ he => absNIdx_inj he)
      hr.inv (anyNKeysOk _) hr.map trivial hq
    exact ⟨h3.1, (ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2 hr.inv (anyNKeysOk _) trivial hq).1⟩

/-- **`homes_of`'s inner loop**: module `i`'s constants from position `j`, the twin's fold. -/
theorem homes_inner_rel {ls : alloc.vec.Vec frontend.olean.lazy.Loaded} {i : Std.Usize}
    {l : frontend.olean.lazy.Loaded} {l' : Arena.Frontend.Olean.Loaded}
    (hl : ls.val[i.val]? = some l) (hrel : LoadedRel l l') (K : Nat) :
    ∀ (j : Std.Usize) (h : ron.hashmap2.HashMap2 arena.handle.NIdx arena.handle.NIdx)
      (h' : Std.HashMap NIdx NIdx) {o}, l.constants.val.length - j.val = K → HomesRel h h' →
      frontend.olean.records.homes_of_loop0_loop0 ls h i j = ok o →
      HomesRel o ((l'.constants.toList.drop j.val).foldl (homeStep l'.name) h') := by
  induction K with
  | zero =>
    intro j h h' o hk hr hx
    rw [frontend.olean.records.homes_of_loop0_loop0] at hx
    peel hx as l0, hl0
    rw [ConRon.Refine.ExprOps.vec_index_getElem? hl0] at hl
    cases Option.some.inj hl
    rw [ite_eq_right (not_lt_len hk)] at hx
    cases Result.ok_injective hx
    have hlen := hrel.constants.length_eq
    rw [List.drop_of_length_le (by simp at hlen ⊢; omega)]
    exact hr
  | succ K ih =>
    intro j h h' o hk hr hx
    rw [frontend.olean.records.homes_of_loop0_loop0] at hx
    peel hx as l0, hl0
    rw [ConRon.Refine.ExprOps.vec_index_getElem? hl0] at hl
    cases Option.some.inj hl
    rw [ite_eq_left (lt_len hk)] at hx
    peel hx as c, hc
    peel hx as b, hb
    peel hx as h1, hh1
    peel hx as j1, hj1
    obtain ⟨c', hc', hcr⟩ := forall₂_getElem? hrel.constants (ConRon.Refine.ExprOps.vec_index_getElem? hc)
    have hj : j.val < l'.constants.toList.length := (List.getElem?_eq_some_iff.mp hc').1
    have hd : l'.constants.toList.drop j.val = c' :: l'.constants.toList.drop (j.val + 1) := by
      rw [List.drop_eq_getElem_cons hj, (List.getElem?_eq_some_iff.mp hc').2]
    have hs := homes_step_rel hr hb hh1
    rw [hcr.1.«name», hrel.«name»] at hs
    have e := ih j1 h1 _ (by rw [usize_succ hj1]; omega) hs hx
    rw [usize_succ hj1] at e
    rw [hd, List.foldl_cons]
    exact e

/-- **`homes_of`'s outer loop**: the modules from position `i`, the twin's fold. -/
theorem homes_outer_rel {ls : alloc.vec.Vec frontend.olean.lazy.Loaded}
    {ls' : List Arena.Frontend.Olean.Loaded} (hls : List.Forall₂ LoadedRel ls.val ls') (K : Nat) :
    ∀ (i : Std.Usize) (h : ron.hashmap2.HashMap2 arena.handle.NIdx arena.handle.NIdx)
      (h' : Std.HashMap NIdx NIdx) {o}, ls.val.length - i.val = K → HomesRel h h' →
      frontend.olean.records.homes_of_loop0 ls h i = ok o →
      HomesRel o ((ls'.drop i.val).foldl
        (fun h l => l.constants.foldl (homeStep l.name) h) h') := by
  induction K with
  | zero =>
    intro i h h' o hk hr hx
    rw [frontend.olean.records.homes_of_loop0, ite_eq_right (not_lt_len hk)] at hx
    cases Result.ok_injective hx
    rw [List.drop_of_length_le (by have := hls.length_eq; omega)]
    exact hr
  | succ K ih =>
    intro i h h' o hk hr hx
    rw [frontend.olean.records.homes_of_loop0, ite_eq_left (lt_len hk)] at hx
    peel hx as h1, hh1
    peel hx as i2, hi2
    have hi : i.val < ls.val.length := by omega
    obtain ⟨l', hl', hlr⟩ := forall₂_getElem? hls (List.getElem?_eq_getElem hi)
    have e1 := homes_inner_rel (List.getElem?_eq_getElem hi) hlr _ 0#usize h h' rfl hr hh1
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e1
    have e := ih i2 h1 _ (by rw [usize_succ hi2]; omega) e1 hx
    rw [usize_succ hi2] at e
    have hj : i.val < ls'.length := (List.getElem?_eq_some_iff.mp hl').1
    rw [List.drop_eq_getElem_cons hj, (List.getElem?_eq_some_iff.mp hl').2, List.foldl_cons,
      ← Array.foldl_toList]
    exact e

/-- **`homes_of` is `homesOf`.** -/
theorem homes_of_rel {ls : alloc.vec.Vec frontend.olean.lazy.Loaded}
    {ls' : Array Arena.Frontend.Olean.Loaded} (hls : List.Forall₂ LoadedRel ls.val ls'.toList) {o}
    (h : frontend.olean.records.homes_of ls = ok o) :
    HomesRel o (Arena.Frontend.Olean.homesOf ls') := by
  rw [frontend.olean.records.homes_of] at h
  peel h as h0, hh0
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hh0
  have e := homes_outer_rel hls _ 0#usize h0 {} rfl
    ⟨ConRon.Refine.HashMap2.RelOn_empty hnone, hinv⟩ h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e
  rw [Arena.Frontend.Olean.homesOf, ← Array.foldl_toList]
  convert e using 2

/-- No homes asked for: the empty map. -/
theorem homes_new_rel {o} (h : ron.hashmap2.HashMap2.new arena.handle.NIdx arena.handle.NIdx = ok o) :
    HomesRel o {} := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) h
  exact ⟨ConRon.Refine.HashMap2.RelOn_empty hnone, hinv⟩

/-! ## The modules' references -/

/-- A module with its frontier moved out, as the twin's `modRefs` leaves it. -/
@[reducible] def clearFr (l : Arena.Frontend.Olean.Loaded) : Arena.Frontend.Olean.Loaded :=
  { l with frontier := {} }

/-- A module's reference, as the twin's `modRefs` takes it. -/
@[reducible] def refOf (l : Arena.Frontend.Olean.Loaded) : Arena.Frontend.Olean.ModRef :=
  ⟨l.name, l.frontier⟩

/-- Related lists, read pointwise. -/
theorem forall₂_of_getElem? {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (hlen : l.length = l'.length)
    (h : ∀ j (h2 : j < l'.length), ∃ x, l[j]? = some x ∧ R x l'[j]) : List.Forall₂ R l l' := by
  refine List.forall₂_iff_get.mpr ⟨hlen, fun j h1 h2 => ?_⟩
  obtain ⟨x, hx, hR⟩ := h j h2
  simp only [List.get_eq_getElem]
  rw [List.getElem?_eq_getElem h1] at hx
  cases Option.some.inj hx
  exact hR

/-- `mod_refs`' loop: the modules before `i` with their frontiers moved out into `out`. -/
theorem mod_refs_loop_rel (ls' : List Arena.Frontend.Olean.Loaded) :
    ∀ (k : Nat) (v : alloc.vec.Vec frontend.olean.lazy.Loaded)
      (out : alloc.vec.Vec frontend.olean.records.ModRef) (i : Std.Usize) {o},
      v.val.length - i.val = k → i.val ≤ v.val.length → v.val.length = ls'.length →
      out.val.length = i.val →
      (∀ j (h2 : j < ls'.length),
        ∃ x, v.val[j]? = some x ∧ LoadedRel x (if j < i.val then clearFr ls'[j] else ls'[j])) →
      (∀ j (h2 : j < ls'.length), j < i.val → ∃ x, out.val[j]? = some x ∧ ModRefRel x (refOf ls'[j])) →
      mod_refs_loop v out i = ok o →
      List.Forall₂ LoadedRel o.1.val (ls'.map clearFr) ∧
        List.Forall₂ ModRefRel o.2.val (ls'.map refOf) := by
  intro k
  induction k with
  | zero =>
    intro v out i o hk hle hlen hol hv hout h
    rw [mod_refs_loop, ite_eq_right (by scalar_tac)] at h
    have hl : ls'.length = i.val := by omega
    cases Result.ok_injective h
    refine ⟨forall₂_of_getElem? (by simp [hlen]) fun j h2 => ?_,
      forall₂_of_getElem? (by simp; omega) fun j h2 => ?_⟩
    · simp only [List.length_map] at h2
      obtain ⟨x, hx, hR⟩ := hv j h2
      rw [ite_eq_left (by omega)] at hR
      exact ⟨x, hx, by simpa using hR⟩
    · simp only [List.length_map] at h2
      obtain ⟨x, hx, hR⟩ := hout j h2 (by omega)
      exact ⟨x, hx, by simpa using hR⟩
  | succ k ih =>
    intro v out i o hk hle hlen hol hv hout h
    rw [mod_refs_loop, ite_eq_left (by scalar_tac)] at h
    have hlt : i.val < v.val.length := by omega
    peel h as q, hq
    obtain ⟨l, back⟩ := q
    have : Inhabited frontend.olean.lazy.Loaded := ⟨l⟩
    obtain ⟨-, hl, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hq
    peel h as f, hf
    simp only [core.mem.replace] at h
    peel h as l1, hl1
    obtain ⟨hidx1, rfl⟩ := vec_index_eq hl1
    peel h as n, hn
    cases nidx_dup2_ok hn
    peel h as out1, hout1
    peel h as i2, hi2
    have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
    have hli : LoadedRel l ls'[i.val] := by
      obtain ⟨x, hx, hR⟩ := hv i.val (by omega)
      rw [ite_eq_right (Nat.lt_irrefl _)] at hR
      rw [List.getElem?_eq_getElem hlt] at hx
      cases Option.some.inj hx
      rw [hl, getElem!_pos v.val i.val hlt]
      exact hR
    have hset : (alloc.vec.Vec.set v i { l with frontier := f }).val
        = v.val.set i.val { l with frontier := f } := by simp [alloc.vec.Vec.set]
    have hfr := frontier_empty_rel hf
    have hout1v := ConRon.Refine.vec_push_val hout1
    refine ih _ out1 i2 (by rw [hset, List.length_set]; omega) (by rw [hset, List.length_set]; omega)
      (by rw [hset, List.length_set]; exact hlen) (by rw [hout1v]; simp [hol, hi2v])
      (fun j h2 => ?_) (fun j h2 hj2 => ?_) h
    · rw [hset]
      by_cases hj : j = i.val
      · subst hj
        rw [List.getElem?_set_self hlt, ite_eq_left (by omega)]
        exact ⟨_, rfl, ⟨hli.name, hli.constants, hfr⟩⟩
      · rw [List.getElem?_set_ne (Ne.symm hj)]
        obtain ⟨x, hx, hR⟩ := hv j h2
        refine ⟨x, hx, ?_⟩
        by_cases hji : j < i.val
        · rw [ite_eq_left hji] at hR
          rw [ite_eq_left (by omega)]
          exact hR
        · rw [ite_eq_right hji] at hR
          rw [ite_eq_right (by omega)]
          exact hR
    · rw [hout1v]
      by_cases hj : j < i.val
      · obtain ⟨x, hx, hR⟩ := hout j h2 hj
        refine ⟨x, ?_, hR⟩
        rw [List.getElem?_append_left (by omega)]
        exact hx
      · have hj' : j = i.val := by omega
        subst hj'
        rw [List.getElem?_append_right (by omega)]
        simp only [hol, Nat.sub_self, List.getElem?_cons_zero]
        exact ⟨_, rfl, ⟨by simp [alloc.vec.Vec.set]; exact hli.name, hli.frontier⟩⟩

/-- **`mod_refs` is `modRefs`**: the frontiers moved out of the merge into the references. -/
theorem mod_refs_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {o} (h : mod_refs mg = ok o) :
    List.Forall₂ ModRefRel o.1.val (Arena.Frontend.Olean.modRefs mg').2.toList ∧
      MergedRel o.2 (Arena.Frontend.Olean.modRefs mg').1 := by
  rw [mod_refs] at h
  peel h as q, hq
  obtain ⟨v, out1⟩ := q
  cases Result.ok_injective h
  have hlen := hm.ls.length_eq
  have hnew : (alloc.vec.Vec.with_capacity frontend.olean.records.ModRef (alloc.vec.Vec.len mg.ls)).val
      = [] := by simp [alloc.vec.Vec.with_capacity, show (alloc.vec.Vec.new frontend.olean.records.ModRef).val = []
        from Slice.from_val _ _]
  obtain ⟨h1, h2⟩ := mod_refs_loop_rel mg'.ls.toList _ mg.ls _ 0#usize rfl (by simp) hlen
    (by rw [hnew]; rfl)
    (fun j h2 => by
      rw [ite_eq_right (by simp)]
      have hj : j < mg.ls.val.length := by omega
      exact ⟨_, List.getElem?_eq_getElem hj, (List.forall₂_iff_get.mp hm.ls).2 j hj h2⟩)
    (fun j _ hj => by simp at hj) hq
  refine ⟨by simpa [Arena.Frontend.Olean.modRefs] using h2, ⟨?_, hm.map, hm.inv, hm.order⟩⟩
  simpa [Arena.Frontend.Olean.modRefs] using h1

end ConRon.Refine2.Frontend.Olean
