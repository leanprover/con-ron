/-
# `ConRon.Refine2.Frontend.Olean.Group` — `olean/group.rs` against `Arena/Frontend/Olean/Group.lean`

**Task #166, Theorem 2.**  `merged_of_list` is `mergedOfList` (`MergedRel`); `group_parts`,
`group_emit` are equations; `block_steps` is `forM blockStep` (`PR`); `group_record` claims its
accept, as `record_of_entry` does (the records' error channel admits the scan's overflow).
`view::c_entry_dup`, `c_kind_dup`, `rules_dup` and `group::c_entry_dup` are the identity.
-/
import ConRon.Refine2.Frontend.Olean.Present

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.group (merged_of_list merged_of_list_loop group_parts group_emit block_steps
  block_steps_loop group_record group_record_loop0 group_record_loop1 group_record_loop2)
open frontend.olean.view (rules_dup rules_dup_loop c_kind_dup)
open frontend.olean.emit (block_tys block_ctors block_recs rec_map_of emit_block)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap (uscalar_add_eq)
open ConRon.Refine.HashMap2 (Inv toFun RelOn)
open ConLeche.Frontend.Olean (CEntryF CKindF)
open Arena.Frontend.Olean (mergedOfList groupParts groupEmit groupRecord blockStep blockTys
  blockCtors blockRecs recMapOf)

/-! ## The copies -/

/-- **`rules_dup` is the identity.** -/
theorem rules_dup_eq {rs r : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)}
    (h : rules_dup rs = ok r) : r = rs := by
  rw [rules_dup] at h
  refine vec_ext (dup_walk0 (L := fun i out => rules_dup_loop rs out i) ?_ h)
  intro i out o h
  rw [rules_dup_loop] at h
  by_cases hc : i < alloc.vec.Vec.len rs
  · rw [ite_eq_left hc] at h
    peel h as x, hx
    obtain ⟨n, k, e⟩ := x
    peel h as n1, hn1
    peel h as e1, he1
    peel h as o1, ho1
    peel h as j, hj
    rw [nidx_dup2_ok hn1, eidx_dup2_ok he1] at ho1
    exact Or.inr ⟨_, o1, j, ConRon.Refine.ExprOps.vec_index_getElem? hx,
      ConRon.Refine.vec_push_val ho1, add_one_usize hj, h⟩
  · rw [ite_eq_right hc] at h
    exact Or.inl ⟨len_le_of_not_lt hc, (Result.ok_injective h).symm⟩

/-- **`view::c_kind_dup` is the identity.** -/
theorem c_kind_dup_eq {k r : frontend.olean.spec.CKindF arena.handle.NIdx arena.handle.EIdx}
    (h : c_kind_dup k = ok r) : r = k := by
  unfold frontend.olean.view.c_kind_dup at h
  cases k with
  | Ax u => exact (Result.ok_injective h).symm
  | Defn v hh s =>
    peel h as e, he
    peel h as hr, hhr
    peel h as v1, hv1
    cases Result.ok_injective h
    rw [eidx_dup2_ok he, hints_dup_val hhr, ConRon.Refine.Expr.str_copy_eq hv1]
  | Thm v all =>
    peel h as e, he
    peel h as v1, hv1
    cases Result.ok_injective h
    rw [eidx_dup2_ok he, vec_ext (nidx_vec_dup_val hv1)]
  | Opaq v u =>
    peel h as e, he
    cases Result.ok_injective h
    rw [eidx_dup2_ok he]
  | Quot s =>
    peel h as v1, hv1
    cases Result.ok_injective h
    rw [ConRon.Refine.Expr.str_copy_eq hv1]
  | Induct np ni all cs nn ir iu irf =>
    peel h as v1, hv1
    peel h as v2, hv2
    cases Result.ok_injective h
    rw [vec_ext (nidx_vec_dup_val hv1), vec_ext (nidx_vec_dup_val hv2)]
  | Ctor ind ci np nf iu =>
    peel h as n, hn
    cases Result.ok_injective h
    rw [nidx_dup2_ok hn]
  | Recur all np ni nmo nmi rules k2 iu =>
    peel h as v1, hv1
    peel h as v2, hv2
    cases Result.ok_injective h
    rw [vec_ext (nidx_vec_dup_val hv1), rules_dup_eq hv2]

/-- **`view::c_entry_dup` is the identity.** -/
theorem view_c_entry_dup_eq {c r : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    (h : frontend.olean.view.c_entry_dup c = ok r) : r = c := by
  rw [frontend.olean.view.c_entry_dup] at h
  peel h as n, hn
  peel h as v, hv
  peel h as e, he
  peel h as k, hk
  cases Result.ok_injective h
  rw [nidx_dup2_ok hn, vec_ext (nidx_vec_dup_val hv), eidx_dup2_ok he, c_kind_dup_eq hk]

/-- **`group::c_entry_dup` is the identity.** -/
theorem c_entry_dup_eq {c r : frontend.olean.lazy.CEntry}
    (h : frontend.olean.group.c_entry_dup c = ok r) : r = c := by
  rw [frontend.olean.group.c_entry_dup] at h
  peel h as c1, hc1
  peel h as u, hu
  cases Result.ok_injective h
  rw [view_c_entry_dup_eq hc1, vec_ext (nidx_vec_dup_val hu)]

/-! ## A merge of a list -/

/-- The twin's step of `mergedOfList`. -/
def mergeStep (acc : Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array Arena.Frontend.Olean.CEntry)
    (c : Arena.Frontend.Olean.CEntry) :
    Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array Arena.Frontend.Olean.CEntry :=
  let (map, order, kept) := acc
  if map.contains c.c.name then acc
  else (map.insert c.c.name (0, kept.size), order.push c.c.name, kept.push c)

/-- What the loop's state says of the twin's. -/
structure ListMergeRel (s : ron.hashmap2.HashMap2 arena.handle.NIdx (Std.Usize × Std.Usize) ×
      alloc.vec.Vec arena.handle.NIdx × alloc.vec.Vec frontend.olean.lazy.CEntry)
    (t : Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array Arena.Frontend.Olean.CEntry) : Prop where
  map : RelOn anyN s.1 t.1 absNIdx absMgPos
  inv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable s.1
  order : s.2.1.val.map absNIdx = t.2.1.toList
  kept : List.Forall₂ CEntryRel s.2.2.val t.2.2.toList

/-- **`merged_of_list`'s loop is the twin's fold** on what is left of the list. -/
theorem merged_of_list_loop_rel {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs') :
    ∀ (k : Nat) (i : Std.Usize) map order kept t o, cs.val.length - i.val ≤ k →
      ListMergeRel (map, order, kept) t → merged_of_list_loop cs map order kept i = ok o →
      ListMergeRel o ((cs'.drop i.val).foldl mergeStep t) := by
  have hlen := hcs.length_eq
  intro k
  induction k with
  | zero =>
    intro i map order kept t o hk hr h
    rw [merged_of_list_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    exact hr
  | succ k ih =>
    intro i map order kept t o hk hr h
    rw [merged_of_list_loop] at h
    by_cases hi : i < alloc.vec.Vec.len cs
    · rw [ite_eq_left hi] at h
      have hlt : i.val < cs.val.length := by scalar_tac
      have hlt' : i.val < cs'.length := by omega
      peel h as c, hc
      obtain ⟨_, hce⟩ := List.getElem?_eq_some_iff.mp (ConRon.Refine.ExprOps.vec_index_getElem? hc)
      have hC : CEntryRel c cs'[i.val] := by
        rw [← hce]; exact (List.forall₂_iff_get.mp hcs).2 _ hlt hlt'
      rw [List.drop_eq_getElem_cons hlt', List.foldl_cons]
      peel h as n, hn
      rw [nidx_dup2_ok hn] at h
      peel h as b, hb
      have eb : b = t.1.contains (absNIdx c.c.name) := by
        have h1 := ConRon.Refine.HashMap2.contains_key_refines_gen nidx_eq2 hr.inv (anyNKeysOk _)
          trivial hb
        have hk := hr.map c.c.name trivial
        rw [h1, Std.HashMap.contains_eq_isSome_getElem?, ← hk]
        cases toFun map c.c.name <;> rfl
      have ename : absNIdx c.c.name = cs'[i.val].c.name := hC.1.«name»
      obtain ⟨tm, tor, tk⟩ := t
      obtain ⟨rm, ri, ro, rk⟩ := hr
      peel h as q, hq
      obtain ⟨map1, order1, kept1⟩ := q
      peel h as i2, hi2
      have hiv : i2.val = i.val + 1 := uscalar_add_eq hi2
      cases b with
      | true =>
        rw [ite_eq_left rfl] at hq
        cases Result.ok_injective hq
        have hS : mergeStep (tm, tor, tk) cs'[i.val] = (tm, tor, tk) := by
          simp only [mergeStep, ← ename, ← eb, ite_true]
        rw [hS]
        have := ih i2 _ _ _ (tm, tor, tk) o (by omega) ⟨rm, ri, ro, rk⟩ h
        rwa [hiv] at this
      | false =>
        rw [ite_eq_right Bool.false_ne_true] at hq
        peel hq as n1, hn1
        rw [nidx_dup2_ok hn1] at hq
        peel hq as p, hp
        obtain ⟨old, map2⟩ := p
        peel hq as o2, ho2
        peel hq as c1, hc1
        rw [c_entry_dup_eq hc1] at hq
        peel hq as k2, hk2
        cases Result.ok_injective hq
        have hins := ConRon.Refine.HashMap2.Rel_insert_wf nidx_eq2 (fun _ _ _ _ he => absNIdx_inj he)
          ri (anyNKeysOk _) rm trivial hp
        have hinv2 := (ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2 ri (anyNKeysOk _) trivial hp).1
        have hS : mergeStep (tm, tor, tk) cs'[i.val] =
            (tm.insert cs'[i.val].c.name (0, tk.size), tor.push cs'[i.val].c.name, tk.push cs'[i.val]) := by
          simp only [mergeStep, ← ename, ← eb, Bool.false_eq_true, ite_false]
        rw [hS]
        have hsz : tk.size = kept.val.length := by rw [← Array.length_toList, ← rk.length_eq]
        have m1 : RelOn anyN map1 (tm.insert cs'[i.val].c.name (0, tk.size)) absNIdx absMgPos := by
          rw [← ename, hsz]
          exact hins.1
        have m2 : order1.val.map absNIdx = (tor.push cs'[i.val].c.name).toList := by
          rw [ConRon.Refine.vec_push_val ho2, List.map_append, ro]
          simp [ename]
        have m3 : List.Forall₂ CEntryRel kept1.val (tk.push cs'[i.val]).toList := by
          rw [ConRon.Refine.vec_push_val hk2]
          simpa using List.rel_append rk (List.Forall₂.cons hC List.Forall₂.nil)
        have := ih i2 map1 order1 kept1
          (tm.insert cs'[i.val].c.name (0, tk.size), tor.push cs'[i.val].c.name, tk.push cs'[i.val]) o
          (by omega) ⟨m1, hinv2, m2, m3⟩ h
        rwa [hiv] at this
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      exact hr

/-- **`merged_of_list` is `mergedOfList`.** -/
theorem merged_of_list_rel {pk : frontend.olean.spec.OleanPins}
    {cs : alloc.vec.Vec frontend.olean.lazy.CEntry} {cs' : Array Arena.Frontend.Olean.CEntry}
    (hcs : List.Forall₂ CEntryRel cs.val cs'.toList) {mg : frontend.olean.merge.Merged}
    (h : merged_of_list pk cs = ok mg) : MergedRel mg (mergedOfList (absPins pk) cs') := by
  rw [merged_of_list] at h
  peel h as m0, hm0
  obtain ⟨hinv0, -, hnone⟩ := ConRon.Refine.HashMap2.with_capacity_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hm0
  peel h as q, hq
  obtain ⟨map1, order1, kept1⟩ := q
  have hL := merged_of_list_loop_rel hcs _ 0#usize m0 _ _ ({}, #[], #[]) _ (Nat.le_refl _)
    ⟨ConRon.Refine.HashMap2.RelOn_empty hnone, hinv0, by simp [alloc.vec.Vec.with_capacity],
      by simp [alloc.vec.Vec.with_capacity]⟩ hq
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hL
  peel h as n, hn
  rw [nidx_dup2_ok hn] at h
  peel h as f, hf
  peel h as ls1, hls1
  cases Result.ok_injective h
  have e : mergedOfList (absPins pk) cs' =
      let r := cs'.toList.foldl mergeStep ({}, #[], #[])
      (⟨#[Arena.Frontend.Olean.Loaded.mk (absPins pk).anon r.2.2 {}], r.1, r.2.1⟩ :
        Arena.Frontend.Olean.Merged) := by
    rw [mergedOfList, ← Array.foldl_toList]
    rfl
  rw [e]
  obtain ⟨rm, ri, ro, rk⟩ := hL
  refine ⟨?_, rm, ri, ro⟩
  rw [ConRon.Refine.vec_push_val hls1]
  simp only [alloc.vec.Vec.with_capacity]
  exact List.Forall₂.cons ⟨rfl, rk, frontier_empty_rel hf⟩ List.Forall₂.nil

/-! ## A group's parts and emission -/

/-- The parts, as the twin's lists. -/
@[reducible] def absParts (p : alloc.vec.Vec arena.handle.NIdx × alloc.vec.Vec arena.handle.NIdx ×
    alloc.vec.Vec arena.handle.NIdx) : List NIdx × List NIdx × List NIdx :=
  (p.1.val.map absNIdx, p.2.1.val.map absNIdx, p.2.2.val.map absNIdx)

/-- **`group_parts` is `groupParts`.** -/
theorem group_parts_eq {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {n : arena.handle.NIdx} {o} (h : group_parts mg n = ok o) :
    o.map absParts = groupParts mg' (absNIdx n) := by
  rw [group_parts] at h
  rw [groupParts]
  peel h as o1, h1
  have hg := mg_get_rel hm h1
  cases hg' : mg'.get (absNIdx n) with
  | none =>
    rw [hg'] at hg
    cases hg
    cases Result.ok_injective h; rfl
  | some c' =>
    rw [hg'] at hg
    cases hg with
    | @some c _ hc =>
    dsimp only at h ⊢
    have hk := hc.1.kind
    generalize c.c.kind = k at h hk
    generalize c'.c.kind = k' at hk ⊢
    cases k <;> cases k' <;> try exact (hk : False).elim
    case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
      obtain ⟨-, -, hall, -⟩ := hk
      have hall' : all.val.map absNIdx = all' := hall
      subst hall'
      peel h as tys, htys
      peel h as ctors, hctors
      peel h as rm, hrm
      peel h as recs, hrecs
      cases Result.ok_injective h
      have e1 := block_tys_rel hm htys
      have e2 := block_ctors_rel hm hctors
      have e3 := block_recs_rel hm (rec_map_of_rel hm hrm) hrecs
      rw [e1] at e2
      simp only [Option.map_some, absParts, e1, e2, e3]
    all_goals (cases Result.ok_injective h; rfl)

/-- **`group_emit` is `groupEmit`.** -/
theorem group_emit_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {tys ctors recs : alloc.vec.Vec arena.handle.NIdx}
    {em : frontend.olean.emit.Emit} (h : group_emit mg tys ctors recs = ok em) :
    EmitRel em (groupEmit mg' (tys.val.map absNIdx) (ctors.val.map absNIdx) (recs.val.map absNIdx)) := by
  rw [group_emit] at h
  peel h as hm0, hhm0
  exact emit_block_rel (emit_new_rel hhm0) hm h

/-- **`block_steps` is `forM blockStep`.** -/
theorem block_steps_pr {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {ar : arena.store.EStore} {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') (ns : alloc.vec.Vec arena.handle.NIdx) :
    PR (fun _ _ => True) (block_steps pk pers ar mg ns)
      ((ns.val.map absNIdx).forM (blockStep (absPins pk) mg')) := by
  rw [block_steps, forM_map]
  have := up_loop_pr (L := fun i => block_steps_loop pk pers ar mg ns i) ns
    (step := fun x => frontend.olean.emit.block_step pk pers ar mg x)
    (fun i => by rw [block_steps_loop]; rfl)
    (fun x => block_step_pr hm x) 0#usize
  simpa using this

/-- A loop that copies names onto the end of a list. -/
theorem copy_names_loop {v : alloc.vec.Vec arena.handle.NIdx}
    {L : alloc.vec.Vec arena.handle.NIdx → Std.Usize → Result (alloc.vec.Vec arena.handle.NIdx)}
    (hL : ∀ s i, L s i = if i < alloc.vec.Vec.len v then do
        let n ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice arena.handle.NIdx) v i
        let n1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 n
        let s1 ← alloc.vec.Vec.push s n1
        let i2 ← i + 1#usize
        L s1 i2
      else ok s)
    {s o : alloc.vec.Vec arena.handle.NIdx} (h : L s 0#usize = ok o) : o.val = s.val ++ v.val := by
  have := append_loop0 (src := v.val) (Ab := fun s : alloc.vec.Vec arena.handle.NIdx => s.val)
    (f := fun x => [x]) (loop := L) ?_ h
  · simpa [flatMap_single] using this
  · intro s i o h
    rw [hL] at h
    by_cases hi : i < alloc.vec.Vec.len v
    · right
      rw [ite_eq_left hi] at h
      peel h as x, hx
      peel h as x1, hx1
      rw [nidx_dup2_ok hx1] at h
      peel h as s1, hs1
      peel h as i1, hi1
      exact ⟨x, s1, i1, ConRon.Refine.ExprOps.vec_index_getElem? hx, ConRon.Refine.vec_push_val hs1,
        uscalar_add_eq hi1, h⟩
    · left
      rw [ite_eq_right hi] at h
      exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩

/-! ## A group's record -/

/-- **`group_record`'s accept is `groupRecord`.** -/
theorem group_record_ok {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    {n : arena.handle.NIdx} {d : arena.env.IDeclaration}
    (h : group_record pk pers st.store mg n = ok (.Ok d)) :
    ∃ lst', (groupRecord (absPins pk) mg' (absNIdx n)).run lst = .ok (absIDeclaration d, lst') ∧
      AStateRel₀ pers st lst' ∧ AStateInv pers st := by
  rw [group_record] at h
  rw [groupRecord]
  peel h as o, ho
  have hP := group_parts_eq hm ho
  cases o with
  | none => exact absurd h (not_ok_of_err (by err_any))
  | some p =>
    obtain ⟨tys, ctors, recs⟩ := p
    rw [← hP]
    dsimp only [Option.map_some, absParts] at h ⊢
    peel h as i1, -
    peel h as i3, -
    peel h as i5, -
    peel h as n1, hn1
    rw [nidx_dup2_ok hn1] at h
    peel h as ns1, hns1
    peel h as ns2, hns2
    peel h as ns3, hns3
    peel h as ns4, hns4
    have e4 : ns4.val = n :: (tys.val ++ ctors.val ++ recs.val) := by
      rw [copy_names_loop (fun s i => by rw [group_record_loop2]) hns4,
        copy_names_loop (fun s i => by rw [group_record_loop1]) hns3,
        copy_names_loop (fun s i => by rw [group_record_loop0]) hns2,
        ConRon.Refine.vec_push_val hns1]
      simp [alloc.vec.Vec.with_capacity]
    peel h as r, hr
    have hB := block_steps_pr (pk := pk) (pers := pers) (ar := st.store) hm ns4 r hr lst
    rw [e4] at hB
    simp only [List.map_cons, List.map_append] at hB
    cases r with
    | Err e => cases Result.ok_injective h
    | Ok u =>
      obtain ⟨_, hb, -⟩ := hB
      rw [am_bind_ok hb]
      dsimp only at h
      peel h as em, hem
      have he := group_emit_rel hm hem
      peel h as r1, hr1
      have hD := decls_of_rel hrel hinv he hr1
      cases r1 with
      | Err p => cases Result.ok_injective h
      | Ok pr =>
        obtain ⟨v, lst', hx, hv, hrel', hinv'⟩ := hD
        dsimp only at h
        rw [am_bind_ok hx]
        by_cases hl : alloc.vec.Vec.len pr.decls = 1#usize
        · rw [ite_eq_left hl] at h
          peel h as i7, hi7
          peel h as i8, hi8
          cases Result.ok_injective h
          refine ⟨lst', ?_, hrel', hinv'⟩
          have hl' : pr.decls.val.length = 1 := by
            have := congrArg UScalar.val hl
            simpa [alloc.vec.Vec.len] using this
          obtain ⟨x, hx1⟩ := List.length_eq_one_iff.mp hl'
          have hi := ConRon.Refine.ExprOps.vec_index_getElem? hi7
          rw [hx1] at hi
          cases (by simpa using hi : x = i7)
          have ev : v.decls = #[absIDeclaration i7] := by
            rw [hv.decls, absIDeclArr, hx1]; rfl
          simp only [ev, i_declaration_dup_abs hi8]
          rfl
        · rw [ite_eq_right hl] at h
          by_cases hl0 : alloc.vec.Vec.len pr.decls = 0#usize
          · rw [ite_eq_left hl0] at h
            exact absurd h (not_ok_of_err (by err_any))
          · rw [ite_eq_right hl0] at h
            exact absurd h (not_ok_of_err (by err_any))

end ConRon.Refine2.Frontend.Olean
