/-
# `ConRon.Refine2.Checker.Mates` — Theorem 2 for the solution a compared run builds

`arena::justify`'s driver-side pure helpers against `Arena/Justify.lean`: a block's names
(`block_names`, the twin's `block.map (·.name)`), the record mates (`mates_get`,
`mates_insert`, `record_mates`: `matesInsert`, `recordMatesGo`) and the solution itself
(`solution_of` ⊑ `solutionOf`): the solution's index by `StreamIndexRel`, the mates by
`SolRel`'s map relation.  No state is read; each lemma is a value equation or relation.
-/
import ConRon.Refine2.Checker.Justify
import ConRon.Refine2.Frontend.Olean.Records

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.Frontend (anyN anyNKeysOk)

/-- **The mates map against the twin's**: entry for entry at every key, well formed. -/
structure MatesMapRel (m : ron.hashmap2.HashMap2 arena.handle.NIdx (alloc.vec.Vec arena.handle.NIdx))
    (m' : Std.HashMap NIdx (List NIdx)) : Prop where
  map : ConRon.Refine.HashMap2.RelOn anyN m m' absNIdx absNIdxList
  inv : ConRon.Refine.HashMap2.Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable m

/-- `mates_get` ⊑ `getD _ []`. -/
theorem mates_get_val {m m' b v} (hr : MatesMapRel m m')
    (h : arena.justify.mates_get m b = ok v) : absNIdxList v = m'.getD (absNIdx b) [] := by
  rw [arena.justify.mates_get] at h
  obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e := ConRon.Refine.HashMap2.get_refines_gen nidx_eq2 hr.inv (anyNKeysOk _) trivial ho
  have hk := hr.map b trivial
  rw [← e] at hk
  rw [Std.HashMap.getD_eq_getD_getElem?, ← hk]
  cases o with
  | none =>
    cases Result.ok_injective h
    rfl
  | some x =>
    have := nidx_vec_dup_val h
    simp [absNIdxList, this]

/-- `block_names` ⊑ `block.map (·.name)`, from the cursor on, onto `out`. -/
theorem block_names_val (block : alloc.vec.Vec arena.env.IConstantInfo) :
    ∀ (K : Nat) (j : Std.Usize) (out r : alloc.vec.Vec arena.handle.NIdx),
      block.val.length - j.val = K → arena.justify.block_names block j out = ok r →
      absNIdxList r = absNIdxList out ++ ((block.val.drop j.val).map absIConstantInfo).map (·.name) := by
  intro K
  induction K with
  | zero =>
    intro j out r hk h
    rw [arena.justify.block_names.eq_def, ite_eq_left (show j ≥ alloc.vec.Vec.len block by
      scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by omega)]
    simp
  | succ K ih =>
    intro j out r hk h
    rw [arena.justify.block_names.eq_def, ite_eq_right (show ¬ j ≥ alloc.vec.Vec.len block by
      scalar_tac)] at h
    have hlt : j.val < block.val.length := by omega
    obtain ⟨ci, hci, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hciv : block.val[j.val]? = some ci := vec_index_some hci
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnv := i_constant_info_name_abs hn
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hout1v : out1.val = out.val ++ [n] := ConRon.Refine.vec_push_val hout1
    obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hj1v := ConRon.Refine.Nat.uadd_val hj1
    rw [ih j1 out1 r (by simp at hj1v; omega) h, hj1v]
    have hd : block.val.drop j.val = ci :: block.val.drop (j.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [List.getElem?_eq_some_iff.mp hciv |>.2]
    simp [absNIdxList, hout1v, hd, hnv]

/-- `mates_insert` ⊑ `matesInsert`, from the cursor on. -/
theorem mates_insert_rel (block : alloc.vec.Vec arena.env.IConstantInfo)
    (ns : alloc.vec.Vec arena.handle.NIdx) :
    ∀ (K : Nat) (j : Std.Usize) m m' o, block.val.length - j.val = K → MatesMapRel m m' →
      arena.justify.mates_insert m block ns j = ok o →
      MatesMapRel o (matesInsert m' (absNIdxList ns) ((block.val.drop j.val).map absIConstantInfo)) := by
  intro K
  induction K with
  | zero =>
    intro j m m' o hk hr h
    rw [arena.justify.mates_insert.eq_def, ite_eq_left (show j ≥ alloc.vec.Vec.len block by
      scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by omega)]
    exact hr
  | succ K ih =>
    intro j m m' o hk hr h
    rw [arena.justify.mates_insert.eq_def, ite_eq_right (show ¬ j ≥ alloc.vec.Vec.len block by
      scalar_tac)] at h
    have hlt : j.val < block.val.length := by omega
    obtain ⟨ci, hci, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hciv : block.val[j.val]? = some ci := vec_index_some hci
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := i_constant_info_name_abs hb
    obtain ⟨prev, hprev, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hprevv := mates_get_val hr hprev
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hvv := nidx_append_val ns _ prev 0#usize _ rfl hv
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨old, m1⟩ := q
    obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hj1v := ConRon.Refine.Nat.uadd_val hj1
    have h3 := ConRon.Refine.HashMap2.Rel_insert_wf nidx_eq2 (fun _ _ _ _ he => absNIdx_inj he)
      hr.inv (anyNKeysOk _) hr.map trivial hq
    have hinv1 := (ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2 hr.inv (anyNKeysOk _)
      trivial hq).1
    have := ih j1 m1 _ o (by simp at hj1v; omega) ⟨h3.1, hinv1⟩ h
    rw [hj1v] at this
    have hd : block.val.drop j.val = ci :: block.val.drop (j.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [List.getElem?_eq_some_iff.mp hciv |>.2]
    rw [hd, List.map_cons, matesInsert]
    have hvv' : absNIdxList v = nidxAppend (m'.getD (absIConstantInfo ci).name [])
        (absNIdxList ns) 0 (absNIdxList ns).length := by
      rw [← hbv, ← hprevv]
      simpa [absNIdxList, alloc.vec.Vec.len] using hvv
    rw [← hvv', ← hbv]
    exact this

/-- `record_mates` ⊑ `recordMatesGo`, from the cursor on. -/
theorem record_mates_rel (ds : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (K : Nat) (i : Std.Usize) m m' o, ds.val.length - i.val = K → MatesMapRel m m' →
      arena.justify.record_mates ds i m = ok o →
      MatesMapRel o (recordMatesGo m' ((ds.val.drop i.val).map absIDeclaration)) := by
  intro K
  induction K with
  | zero =>
    intro i m m' o hk hr h
    rw [arena.justify.record_mates, arena.justify.record_mates_loop.eq_def, ite_eq_left (show i ≥ alloc.vec.Vec.len ds by
      scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by omega)]
    exact hr
  | succ K ih =>
    intro i m m' o hk hr h
    rw [arena.justify.record_mates, arena.justify.record_mates_loop.eq_def, ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ds by
      scalar_tac)] at h
    have hlt : i.val < ds.val.length := by omega
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hdv : ds.val[i.val]? = some d := vec_index_some hd
    have hdrop : ds.val.drop i.val = d :: ds.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [List.getElem?_eq_some_iff.mp hdv |>.2]
    rw [hdrop, List.map_cons]
    cases d with
    | IndDecl block np =>
      simp only at h
      obtain ⟨ns, hns, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnsv := block_names_val block _ 0#usize _ ns rfl hns
      obtain ⟨m2, hm2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hr2 := mates_insert_rel block ns _ 0#usize m m' m2 rfl hr hm2
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi3v := ConRon.Refine.Nat.uadd_val hi3
      have := ih i3 m2 _ o (by simp at hi3v; omega) hr2 h
      rw [hi3v] at this
      simp only [absIDeclaration, recordMatesGo]
      have hns' : absNIdxList ns = (block.val.map absIConstantInfo).map (·.name) := by
        simpa [absNIdxList] using hnsv
      rw [← hns']
      simpa using this
    | AxiomDecl _ | DefnDecl _ _ _ | ThmDecl _ _ | OpaqueDecl _ _ | QuotDecl _ _ =>
      simp only at h
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi3v := ConRon.Refine.Nat.uadd_val hi3
      have := ih i3 m m' o (by simp at hi3v; omega) hr h
      rw [hi3v] at this
      simpa [absIDeclaration, recordMatesGo] using this

/-- **`solution_of` ⊑ `solutionOf`**: the solution stream's index, related, and the record mates
of the records the challenge's fold checks. -/
theorem solution_of_rel {ix : arena.stream_index.IStreamIndex} {I : IStreamIndex}
    (hI : StreamIndexRel ix I) {ds : alloc.vec.Vec arena.env.IDeclaration}
    {sol : arena.justify.Solution} (h : arena.justify.solution_of ix ds = ok sol) :
    SolRel sol (solutionOf I (absIDeclL ds)) := by
  rw [arena.justify.solution_of] at h
  obtain ⟨hm, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hm1, hhm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm
  have h0 : MatesMapRel hm ∅ := ⟨ConRon.Refine.HashMap2.RelOn_empty hnone, hinv⟩
  have hr := record_mates_rel ds _ 0#usize hm ∅ hm1 rfl h0 hhm1
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hr
  exact ⟨hI, hr.map, hr.inv⟩

end ConRon.Refine2
