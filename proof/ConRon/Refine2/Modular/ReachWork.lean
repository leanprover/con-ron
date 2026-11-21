/-
# `ConRon.Refine2.Modular.ReachWork` — `modular/reach.rs`: the worklist's pure helpers

**Task #166, Theorem 2.**  The store-free helpers of the reach's worklist and clash rule against
their twins (`Arena/Modular/Reach.lean`): each an equation under the abstraction (a `Vec` is its
list, a `HashMap2` keyed by handles the twin's `Std.HashSet` (`NSet`) or `Std.HashMap`
(`NMapRel`), the stack's live prefix reversed the twin's list (`StackRel`)).  `partner_reads`
and its folds run `needs_expr` on the state: they claim their accept.

**Casts.**  `pub_has` reads a load position back as a `usize`: the twin's load positions are
positions of its order (`IndexFits`), which fits a `usize`.  `clash_copy_list` reads a copy's
module the same way: its copies fit a `usize` (`CopyFits`), as every copy the index makes does.
-/
import ConRon.Refine2.Modular.ReachRel
import ConRon.Refine2.Frontend.Olean.Closure
import ConRon.Refine2.Modular.Graph
import ConRon.Refine2.Checker.Needs
import ConRon.Arena.Modular.Reach

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.modular.reach

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Refine2.Frontend.Olean
open ConRon.Refine.HashMap2 (Inv toFun)

/-! ## Handles -/

theorem nidx_dup2_eq (h : arena.handle.NIdx) :
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h = ok h := rfl

theorem drop_map_cons {α β : Type} {l : List α} {i : Nat} (hi : i < l.length) (f : α → β) :
    (l.drop i).map f = f l[i] :: (l.drop (i + 1)).map f := by
  rw [List.drop_eq_getElem_cons hi]; rfl

theorem usize_succ_val {i j : Std.Usize} (h : i + 1#usize = ok j) : j.val = i.val + 1 := by
  rw [ConRon.Refine.Nat.uadd_val h]; rfl

/-! ## The stack -/

/-- **`stack_push` pushes onto the twin's list.** -/
theorem stack_push_eq {stack : alloc.vec.Vec arena.handle.NIdx} {sp : Std.Usize} {l : List NIdx}
    {y : arena.handle.NIdx} {o} (h : StackRel absNIdx stack sp l) (hr : stack_push stack sp y = ok o) :
    StackRel absNIdx o.2 o.1 (absNIdx y :: l) := by
  rw [stack_push] at hr
  simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
  peel hr as st1, hst1
  peel hr as i1, hi1
  cases Result.ok_injective hr
  exact h.push hst1 hi1

theorem push_names_loop_eq (ys : alloc.vec.Vec arena.handle.NIdx)
    (seen : ron.hashmap2.HashMap2 arena.handle.NIdx Bool) (stack : alloc.vec.Vec arena.handle.NIdx)
      (sp i : Std.Usize) {S : Std.HashSet NIdx} {l : List NIdx} (hs : NSet seen S)
      (hl : StackRel absNIdx stack sp l) {o} (h : push_names_loop seen stack ys sp i = ok o) :
      NSet o.2.1 (Modular.pushNames S l ((ys.val.drop i.val).map absNIdx)).1 ∧
        StackRel absNIdx o.2.2 o.1 (Modular.pushNames S l ((ys.val.drop i.val).map absNIdx)).2 := by
  rw [push_names_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len ys
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 hs hb
    rw [List.drop_eq_getElem_cons hi, List.map_cons, Modular.pushNames]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      simp only [Aeneas.Std.bind_ok] at h
      peel h as i2, hi2
      have hv2 := usize_succ_val hi2
      have ih := push_names_loop_eq ys seen stack sp i2 hs hl h
      rw [usize_succ_val hi2] at ih
      have hT : S.contains (absNIdx ys.val[i.val]) = true := by rw [← eb]; exact cb
      simp only [hT, ↓reduceIte]
      exact ih
    · rw [ite_eq_right cb] at h
      have hT : S.contains (absNIdx ys.val[i.val]) = false := by rw [← eb]; simpa using cb
      peel h as q0, hq0
      obtain ⟨seen2, stack2, sp2⟩ := q0
      simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hq0
      peel hq0 as q, hq
      obtain ⟨old, seen3⟩ := q
      peel hq0 as q2, hq2
      obtain ⟨sp3, stack3⟩ := q2
      cases Result.ok_injective hq0
      peel h as i2, hi2
      have hv2 := usize_succ_val hi2
      have hs2 := SetRel.insert nidx_eq2 absNIdx_inj hs hq
      have hl2 := stack_push_eq hl hq2
      have ih := push_names_loop_eq ys seen2 stack2 sp2 i2 hs2 hl2 h
      rw [usize_succ_val hi2] at ih
      simp only [hT, Bool.false_eq_true, ↓reduceIte]
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨hs, hl⟩
termination_by ys.val.length - i.val
decreasing_by all_goals (have := lt_len hlt; omega)

/-- **`push_names` is `pushNames`.** -/
theorem push_names_eq {seen : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    {stack : alloc.vec.Vec arena.handle.NIdx} {sp : Std.Usize} {ys : alloc.vec.Vec arena.handle.NIdx}
    {S : Std.HashSet NIdx} {l : List NIdx} (hs : NSet seen S) (hl : StackRel absNIdx stack sp l) {o}
    (h : push_names seen stack sp ys = ok o) :
    NSet o.2.1 (Modular.pushNames S l (ys.val.map absNIdx)).1 ∧
      StackRel absNIdx o.2.2 o.1 (Modular.pushNames S l (ys.val.map absNIdx)).2 := by
  simpa using push_names_loop_eq ys seen stack sp 0#usize hs hl h

theorem pair_seconds_loop_eq (ps : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx))
    (out : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) {o}
      (h : pair_seconds_loop ps out i = ok o) :
      o.val.map absNIdx = out.val.map absNIdx ++ (ps.val.drop i.val).map (fun p => absNIdx p.2) := by
  rw [pair_seconds_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len ps
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as p, hp
    obtain ⟨_, rfl⟩ := vec_index_eq hp
    simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at h
    peel h as out1, hout1
    peel h as i2, hi2
    have hv2 := usize_succ_val hi2
    have ih := pair_seconds_loop_eq ps out1 i2 h
    rw [usize_succ_val hi2, ConRon.Refine.vec_push_val hout1] at ih
    rw [ih, List.drop_eq_getElem_cons hi]
    simp only [List.map_cons, List.map_append, List.append_assoc, List.map_nil, List.cons_append,
      List.nil_append, List.get_eq_getElem]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by ps.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`pair_seconds` is `ps.map (·.2)`.** -/
theorem pair_seconds_eq {ps : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)} {o}
    (h : pair_seconds ps = ok o) : o.val.map absNIdx = (ps.val.map absNN).map (·.2) := by
  rw [pair_seconds] at h
  have := pair_seconds_loop_eq ps _ 0#usize h
  simpa [List.map_map, Function.comp_def, alloc.vec.Vec.with_capacity] using this

/-! ## Sets -/

theorem set_add_all_loop_eq (ns : alloc.vec.Vec arena.handle.NIdx)
    (s : ron.hashmap2.HashMap2 arena.handle.NIdx Bool) (i : Std.Usize) {S : Std.HashSet NIdx}
      (hs : NSet s S) {o} (h : set_add_all_loop s ns i = ok o) :
      NSet o (((ns.val.drop i.val).map absNIdx).foldl (fun s n => s.insert n) S) := by
  rw [set_add_all_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len ns
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at h
    peel h as q, hq
    obtain ⟨old, s1⟩ := q
    peel h as i2, hi2
    have hv2 := usize_succ_val hi2
    have ih := set_add_all_loop_eq ns s1 i2 (SetRel.insert nidx_eq2 absNIdx_inj hs hq) h
    rw [usize_succ_val hi2] at ih
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact hs
termination_by ns.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`set_add_all` is the twin's fold of `insert`.** -/
theorem set_add_all_eq {s : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    {ns : alloc.vec.Vec arena.handle.NIdx} {S : Std.HashSet NIdx} (hs : NSet s S) {o}
    (h : set_add_all s ns = ok o) :
    NSet o ((ns.val.map absNIdx).foldl (fun s n => s.insert n) S) := by
  simpa using set_add_all_loop_eq ns s 0#usize hs h

theorem any_stored_loop_eq (stored : ron.hashmap2.HashMap2 arena.handle.NIdx Bool)
    (ns : alloc.vec.Vec arena.handle.NIdx) {S : Std.HashSet NIdx} (hs : NSet stored S)
    (i : Std.Usize) {o} (h : any_stored_loop stored ns i = ok o) :
      o = ((ns.val.drop i.val).map absNIdx).any S.contains := by
  rw [any_stored_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len ns
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 hs hb
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.any_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      cases Result.ok_injective h
      rw [← eb, cb]; rfl
    · rw [ite_eq_right cb] at h
      peel h as i2, hi2
      have hv2 := usize_succ_val hi2
      have ih := any_stored_loop_eq stored ns hs i2 h
      rw [usize_succ_val hi2] at ih
      rw [← eb, ih]; simp [cb]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by ns.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`any_stored` is `anyStored`.** -/
theorem any_stored_eq {stored : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    {ns : alloc.vec.Vec arena.handle.NIdx} {S : Std.HashSet NIdx} (hs : NSet stored S) {o}
    (h : any_stored stored ns = ok o) : o = Modular.anyStored S (ns.val.map absNIdx) := by
  rw [any_stored] at h
  simpa [Modular.anyStored] using any_stored_loop_eq stored ns hs 0#usize h

/-! ## The roots -/

theorem reach_roots_loop0_eq (own : ron.hashmap2.HashMap2 arena.handle.NIdx Bool)
    (roots : alloc.vec.Vec arena.handle.NIdx) {O : Std.HashSet NIdx} (ho : NSet own O)
    (out : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) {o}
      (h : reach_roots_loop0 own roots out i = ok o) :
      o.val.map absNIdx = out.val.map absNIdx ++ ((roots.val.drop i.val).map absNIdx).filter (!O.contains ·) := by
  rw [reach_roots_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len roots
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 ho hb
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.filter_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      simp only [Aeneas.Std.bind_ok] at h
      peel h as i2, hi2
      have hv2 := usize_succ_val hi2
      have ih := reach_roots_loop0_eq own roots ho out i2 h
      rw [usize_succ_val hi2] at ih
      have hT : O.contains (absNIdx roots.val[i.val]) = true := by rw [← eb]; exact cb
      simp only [hT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ih
    · rw [ite_eq_right cb] at h
      have hT : O.contains (absNIdx roots.val[i.val]) = false := by rw [← eb]; simpa using cb
      simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at h
      peel h as out1, hout1
      peel h as i2, hi2
      have hv2 := usize_succ_val hi2
      have ih := reach_roots_loop0_eq own roots ho out1 i2 h
      rw [usize_succ_val hi2, ConRon.Refine.vec_push_val hout1] at ih
      simp only [hT, Bool.not_false, ↓reduceIte]
      rw [ih]; simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by roots.val.length - i.val
decreasing_by all_goals (have := lt_len hlt; omega)

theorem reach_roots_loop1_eq (own : ron.hashmap2.HashMap2 arena.handle.NIdx Bool)
    (extra : alloc.vec.Vec arena.handle.NIdx) {O : Std.HashSet NIdx} (ho : NSet own O)
    (out : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) {o}
      (h : reach_roots_loop1 own extra out i = ok o) :
      o.val.map absNIdx = out.val.map absNIdx ++ ((extra.val.drop i.val).map absNIdx).filter (!O.contains ·) := by
  rw [reach_roots_loop1] at h
  by_cases hlt : i < alloc.vec.Vec.len extra
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 ho hb
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.filter_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      simp only [Aeneas.Std.bind_ok] at h
      peel h as i2, hi2
      have hv2 := usize_succ_val hi2
      have ih := reach_roots_loop1_eq own extra ho out i2 h
      rw [usize_succ_val hi2] at ih
      have hT : O.contains (absNIdx extra.val[i.val]) = true := by rw [← eb]; exact cb
      simp only [hT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ih
    · rw [ite_eq_right cb] at h
      have hT : O.contains (absNIdx extra.val[i.val]) = false := by rw [← eb]; simpa using cb
      simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at h
      peel h as out1, hout1
      peel h as i2, hi2
      have hv2 := usize_succ_val hi2
      have ih := reach_roots_loop1_eq own extra ho out1 i2 h
      rw [usize_succ_val hi2, ConRon.Refine.vec_push_val hout1] at ih
      simp only [hT, Bool.not_false, ↓reduceIte]
      rw [ih]; simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by extra.val.length - i.val
decreasing_by all_goals (have := lt_len hlt; omega)

/-- **`reach_roots` is `reachRoots`.** -/
theorem reach_roots_eq {own : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    {roots extra : alloc.vec.Vec arena.handle.NIdx} {O : Std.HashSet NIdx} (ho : NSet own O) {o}
    (h : reach_roots own roots extra = ok o) :
    o.val.map absNIdx = Modular.reachRoots O (roots.val.map absNIdx).toArray (extra.val.map absNIdx).toArray := by
  rw [reach_roots] at h
  peel h as i2, hi2
  peel h as out1, hout1
  have e1 := reach_roots_loop0_eq own roots ho _ 0#usize hout1
  have e2 := reach_roots_loop1_eq own extra ho out1 0#usize h
  rw [e2, e1]
  simp [Modular.reachRoots, alloc.vec.Vec.with_capacity]

theorem first_unloaded_loop_eq (wr : frontend.olean.index.WorkerReads)
    (rs : alloc.vec.Vec arena.handle.NIdx) {F : Std.HashMap NIdx ConLeche.Frontend.Olean.Copy}
    (hf : FirstRel wr.index.first F)
    (i : Std.Usize) {o} (h : first_unloaded_loop wr rs i = ok o) :
      (∀ j, o = some j → j.val < rs.val.length) ∧
      (o.bind fun j => (rs.val[j.val]?).map absNIdx) =
        ((rs.val.drop i.val).map absNIdx).find? (!F.contains ·) := by
  rw [first_unloaded_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len rs
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := hf.rel.contains_eq hb
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.find?_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      peel h as i2, hi2
      have hv2 := usize_succ_val hi2
      have ih := first_unloaded_loop_eq wr rs hf i2 h
      rw [usize_succ_val hi2] at ih
      have hT : F.contains (absNIdx rs.val[i.val]) = true := by rw [← eb]; exact cb
      simp only [hT, Bool.not_true]
      exact ih
    · rw [ite_eq_right cb] at h
      cases Result.ok_injective h
      have hT : F.contains (absNIdx rs.val[i.val]) = false := by rw [← eb]; simpa using cb
      refine ⟨fun j hj => by cases hj; exact hi, ?_⟩
      simp [hT, List.getElem?_eq_getElem hi]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by rs.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`first_unloaded` is the twin's `find?`**: the root it names, the first no loaded module holds. -/
theorem first_unloaded_eq {wr : frontend.olean.index.WorkerReads} {rs : alloc.vec.Vec arena.handle.NIdx}
    {F : Std.HashMap NIdx ConLeche.Frontend.Olean.Copy} (hf : FirstRel wr.index.first F) {o}
    (h : first_unloaded wr rs = ok o) :
    (∀ j, o = some j → j.val < rs.val.length) ∧
      (o.bind fun j => (rs.val[j.val]?).map absNIdx) = (rs.val.map absNIdx).find? (!F.contains ·) := by
  simpa using first_unloaded_loop_eq wr rs hf 0#usize h

/-! ## The public-import closure -/

/-- **`pub_has` is `pubHas`**, at a load position that fits a `usize`. -/
theorem pub_has_eq {wr : frontend.olean.index.WorkerReads} {wr' : Arena.Frontend.Olean.WorkerReads}
    (hw : WorkerReadsRel wr wr') (hfit : IndexFits wr'.loads) {env : Modular.ReachEnv}
    (he : env.wr = wr') {h : arena.handle.NIdx} {i : Std.U64} (hi : i.val ≤ Std.Usize.max) {o}
    (hr : pub_has wr h i = ok o) : o = Modular.pubHas env (absNIdx h) i.val := by
  rw [pub_has] at hr
  subst he
  peel hr as g, hg
  have eg := hw.loads.index.get_eq hg
  unfold Modular.pubHas
  cases g with
  | none =>
    cases Result.ok_injective hr
    rw [← eg]; rfl
  | some hi' =>
    rw [← eg]
    simp only [Option.map_some]
    have hlt : hi'.val < env.wr.loads.order.size := hfit _ _ eg.symm
    have hofit := (order_fits hw.loads)
    have hfit' : hi'.val ≤ Std.Usize.max := by omega
    dsimp only at hr
    peel hr as j, hj
    have ej : j.val = hi'.val := by rw [← Result.ok_injective hj]; exact ConRon.Refine2.Frontend.Olean.cast_usize_val hfit'
    have hpl : env.wr.pub.size = wr.pub_.val.length := by
      rw [← Array.length_toList, ← hw.pub, List.length_map]
    by_cases hl : j < alloc.vec.Vec.len wr.pub_
    · rw [ite_eq_left hl] at hr
      have hl' := lt_len hl
      peel hr as v, hv
      obtain ⟨_, rfl⟩ := vec_index_eq hv
      have eo := mod_set_has_eq (by omega) hr
      have hp : env.wr.pub[hi'.val]? = some (ConRon.Refine2.Frontend.absChunk wr.pub_.val[j.val]) := by
        rw [← ej, ← Array.getElem?_toList, ← hw.pub, List.getElem?_map, List.getElem?_eq_getElem hl']
        rfl
      rw [hp, eo]; rfl
    · rw [ite_eq_right hl] at hr
      cases Result.ok_injective hr
      have hp : env.wr.pub[hi'.val]? = none := by
        rw [Array.getElem?_eq_none]; have := not_lt_len hl; omega
      rw [hp]; rfl

/-! ## The clashing names' copies -/

/-- A clash's copy, its module and statement, as the twin's. -/
@[reducible] def absCopyStmt (p : arena.handle.NIdx × frontend.olean.spec.StmtRec) : NIdx × Arena.Frontend.Olean.StmtRec :=
  (absNIdx p.1, absStmtRec p.2)

/-- The twin's copy list of one clash. -/
@[reducible] def clashCopyListT (pk : Arena.Frontend.Olean.OleanPins) (wr' : Arena.Frontend.Olean.WorkerReads)
    (cl' : Arena.Frontend.Olean.Clash) : Array (NIdx × Arena.Frontend.Olean.StmtRec) :=
  cl'.copies.map fun (cp, cv, _) => (wr'.loads.nameAt pk cp.mod, cv)

theorem clash_copy_list_loop_eq {pk : frontend.olean.spec.OleanPins} {wr : frontend.olean.index.WorkerReads}
    {wr' : Arena.Frontend.Olean.WorkerReads} (hld : HeaderLoadsRel wr.loads wr'.loads)
    (v : alloc.vec.Vec (frontend.olean.index.Copy × frontend.olean.spec.StmtRec ×
      frontend.olean.spec.CKindF arena.handle.NIdx Unit))
    {V : List (ConLeche.Frontend.Olean.Copy × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit)}
    (hv : List.Forall₂ CopyInfoRel v.val V) (hfit : ∀ x ∈ v.val, CopyFits x.1)
    (out : alloc.vec.Vec (arena.handle.NIdx × frontend.olean.spec.StmtRec)) (i : Std.Usize) {o}
      (h : clash_copy_list_loop pk wr v out i = ok o) :
      o.val.map absCopyStmt = out.val.map absCopyStmt ++
        (V.drop i.val).map fun (cp, cv, _) => (wr'.loads.nameAt (absPins pk) cp.mod, cv) := by
  have hlen := List.Forall₂.length_eq hv
  rw [clash_copy_list_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len v
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    have hf := hfit _ (List.getElem_mem hi)
    have hr : CopyInfoRel v.val[i.val] (V[i.val]'(by omega)) := List.forall₂_iff_get.mp hv |>.2 _ hi _
    generalize v.val[i.val] = xv at h hf hr
    obtain ⟨c, sr, k⟩ := xv
    peel h as n, hn
    have en := header_loads_name_at_eq (pk := pk) hld hf.1 hn
    peel h as sr1, hsr1
    cases stmt_rec_dup_eq hsr1
    peel h as out1, hout1
    peel h as i2, hi2
    have hv2 := usize_succ_val hi2
    have ih := clash_copy_list_loop_eq hld v hv hfit out1 i2 h
    rw [usize_succ_val hi2, ConRon.Refine.vec_push_val hout1] at ih
    rw [ih, List.drop_eq_getElem_cons (by omega : i.val < V.length)]
    generalize V[i.val] = yv at hr ⊢
    obtain ⟨cp, cv, k'⟩ := yv
    obtain ⟨hc, hs, -⟩ := hr
    simp only at hc hs
    subst hc hs; simp [en]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by have := not_lt_len hlt; omega)]
    simp
termination_by v.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`clash_copy_list` is the twin's map of a clash's copies.** -/
theorem clash_copy_list_eq {pk : frontend.olean.spec.OleanPins} {wr : frontend.olean.index.WorkerReads}
    {wr' : Arena.Frontend.Olean.WorkerReads} (hld : HeaderLoadsRel wr.loads wr'.loads)
    {cl : frontend.olean.index.Clash} {cl' : Arena.Frontend.Olean.Clash} (hc : ClashRel cl cl')
    (hfit : ∀ x ∈ cl.copies.val, CopyFits x.1) {o} (h : clash_copy_list pk wr cl = ok o) :
    absCopies o = clashCopyListT (absPins pk) wr' cl' := by
  rw [clash_copy_list] at h
  have := clash_copy_list_loop_eq hld cl.copies hc.copies hfit _ 0#usize h
  apply Array.ext'
  simp only [clashCopyListT, Array.toList_map]
  rw [this]
  simp [alloc.vec.Vec.with_capacity]

/-- The twin's `clashCopiesOf`, from the `i`th clash on. -/
theorem clash_copies_of_loop_eq {pk : frontend.olean.spec.OleanPins} {wr : frontend.olean.index.WorkerReads}
    {wr' : Arena.Frontend.Olean.WorkerReads} (hw : WorkerReadsRel wr wr') (hfit : ClashesFit wr)
    (m : ron.hashmap2.HashMap2 arena.handle.NIdx (alloc.vec.Vec (arena.handle.NIdx × frontend.olean.spec.StmtRec)))
      {M : Std.HashMap NIdx (Array (NIdx × Arena.Frontend.Olean.StmtRec))} (hm : NMapRel absCopies m M)
      (i : Std.Usize) {o} (h : clash_copies_of_loop pk wr m i = ok o) :
      NMapRel absCopies o ((wr'.clashes.toList.drop i.val).foldl (fun m cl =>
        m.insert cl.name (clashCopyListT (absPins pk) wr' cl)) M) := by
  have hlen := List.Forall₂.length_eq hw.clashes
  rw [clash_copies_of_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len wr.clashes
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as c, hc
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    have hr : ClashRel wr.clashes.val[i.val] (wr'.clashes.toList[i.val]'(by omega)) :=
      List.forall₂_iff_get.mp hw.clashes |>.2 _ hi _
    simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at h
    peel h as v, hv
    have ev := clash_copy_list_eq hw.loads hr (hfit _ (List.getElem_mem hi)) hv
    peel h as q, hq
    obtain ⟨old, m1⟩ := q
    peel h as i2, hi2
    have hv2 := usize_succ_val hi2
    have hm1 := hm.insert hq
    rw [ev, hr.name] at hm1
    have ih := clash_copies_of_loop_eq hw hfit m1 hm1 i2 h
    rw [usize_succ_val hi2] at ih
    rw [List.drop_eq_getElem_cons (by omega : i.val < wr'.clashes.toList.length), List.foldl_cons]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by have := not_lt_len hlt; omega)]
    exact hm
termination_by wr.clashes.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`clash_copies_of` is `clashCopiesOf`.** -/
theorem clash_copies_of_eq {pk : frontend.olean.spec.OleanPins} {wr : frontend.olean.index.WorkerReads}
    {wr' : Arena.Frontend.Olean.WorkerReads} (hw : WorkerReadsRel wr wr') (hfit : ClashesFit wr) {o}
    (h : clash_copies_of pk wr = ok o) : NMapRel absCopies o (Modular.clashCopiesOf (absPins pk) wr') := by
  rw [clash_copies_of] at h
  peel h as m, hm
  have := clash_copies_of_loop_eq hw hfit m (M := {}) (NMapRel.new hm) 0#usize h
  simpa [Modular.clashCopiesOf, Array.foldl_toList] using this

/-! ## The partners' reads -/

/-- **The accept of a function that appends name pairs** to `acc`, on the state: the Rust's `Ok`
is a run of the twin from `A` (the twin's `acc`), in related states, the pairs related. -/
def PA (pers : arena.store.PersTier) (st : arena.monad.AState) (lst : AState)
    (acc : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx))
    (m : Result (core.result.Result Unit kernel.core_types.CheckError × arena.monad.AState ×
      alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)))
    (x : Array (NIdx × NIdx) → AM (Array (NIdx × NIdx))) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st → ∀ st' acc', m = ok (.Ok (), st', acc') →
    ∃ A' lst', (x (acc.val.map absNN).toArray).run lst = .ok (A', lst') ∧
      acc'.val.map absNN = A'.toList ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st'

theorem partner_reads_loop_eq (h : arena.handle.NIdx) (x : arena.needs.NeedsSt)
    (acc : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)) (i : Std.Usize) {o}
      (hr : partner_reads_loop acc h x i = ok o) :
      o.val.map absNN = acc.val.map absNN ++ (x.acc.val.drop i.val).map fun y => (absNIdx h, absNIdx y) := by
  rw [partner_reads_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len x.acc
  · rw [ite_eq_left hlt] at hr
    have hi := lt_len hlt
    simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
    peel hr as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel hr as acc1, hacc1
    peel hr as i2, hi2
    have hv2 := usize_succ_val hi2
    have ih := partner_reads_loop_eq h x acc1 i2 hr
    rw [usize_succ_val hi2, ConRon.Refine.vec_push_val hacc1] at ih
    rw [ih, drop_map_cons hi]
    simp
  · rw [ite_eq_right hlt] at hr
    cases Result.ok_injective hr
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by x.acc.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`partner_reads` is `partnerReads`.** -/
theorem partner_reads_ok {pers st lst} (acc : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx))
    (h : arena.handle.NIdx) (ty : arena.handle.EIdx) :
    PA pers st lst acc (partner_reads pers st acc h ty)
      (fun A => Modular.partnerReads A (absNIdx h) (absEIdx ty)) := by
  intro hrel hinv st' acc' hr
  rw [partner_reads] at hr
  peel hr as ns, hns
  have hN := needs_st_empty_spec ns hns
  peel hr as q, hq
  obtain ⟨r, st1⟩ := q
  have hL := needs_expr_ls hrel hinv hN ty r st1 hq
  cases r with
  | Err e => cases Result.ok_injective hr
  | Ok x =>
    obtain ⟨b, lst1, hx, hb, hrel1, hinv1⟩ := hL
    peel hr as acc1, hacc1
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    have ea := partner_reads_loop_eq h x acc 0#usize hacc1
    refine ⟨b.acc.foldl (fun A y => A.push (absNIdx h, y)) (acc.val.map absNN).toArray, lst1, ?_, ?_,
      hrel1, hinv1⟩
    · unfold Modular.partnerReads
      rw [am_bind_ok hx]; rfl
    · rw [ea, hb.acc]
      simp [absNIdxList, List.foldl_push_eq_append]

/-- The twin's step of `copiesPartners`. -/
@[reducible] def cpStep (acc : Array (NIdx × NIdx)) (p : NIdx × Arena.Frontend.Olean.StmtRec) :
    AM (Array (NIdx × NIdx)) :=
  Modular.partnerReads acc p.1 p.2.type

theorem copies_partners_loop_ok {pers} (cs : alloc.vec.Vec (arena.handle.NIdx × frontend.olean.spec.StmtRec))
    (st : arena.monad.AState) (lst : AState) (acc : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx))
      (i : Std.Usize) :
      PA pers st lst acc (copies_partners_loop pers st acc cs i)
        (fun A => ((cs.val.drop i.val).map absCopyStmt).foldlM cpStep A) := by
  intro hrel hinv st' acc' hr
  rw [copies_partners_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at hr
    have hi := lt_len hlt
    peel hr as p, hp
    obtain ⟨_, rfl⟩ := vec_index_eq hp
    beta_reduce
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldlM_cons]
    generalize cs.val[i.val] = xv at hr ⊢
    obtain ⟨n, sr⟩ := xv
    peel hr as q, hq
    obtain ⟨r, st1, acc1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective hr
    | Ok u =>
      obtain ⟨A1, lst1, hx1, hA1, hrel1, hinv1⟩ := partner_reads_ok acc n sr.ty hrel hinv st1 acc1 hq
      peel hr as i2, hi2
      have hv2 := usize_succ_val hi2
      obtain ⟨A2, lst2, hx2, hA2, hrel2, hinv2⟩ := copies_partners_loop_ok cs st1 lst1 acc1 i2 hrel1 hinv1 st' acc' hr
      rw [usize_succ_val hi2] at hx2
      refine ⟨A2, lst2, ?_, hA2, hrel2, hinv2⟩
      have e1 : (acc1.val.map absNN).toArray = A1 := by rw [hA1]
      rw [e1] at hx2
      exact (am_bind_ok hx1).trans hx2
  · rw [ite_eq_right hlt] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    refine ⟨(acc.val.map absNN).toArray, lst, ?_, by simp, hrel, hinv⟩
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by cs.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`copies_partners` is the twin's fold of `partnerReads`.** -/
theorem copies_partners_ok {pers st lst} (acc : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx))
    (cs : alloc.vec.Vec (arena.handle.NIdx × frontend.olean.spec.StmtRec)) :
    PA pers st lst acc (copies_partners pers st acc cs)
      (fun A => (absCopies cs).toList.foldlM cpStep A) := by
  intro hrel hinv st' acc' hr
  simpa using copies_partners_loop_ok cs st lst acc 0#usize hrel hinv st' acc' hr

/-- **`clash_partners_one` is `clashPartnersOne`.** -/
theorem clash_partners_one_ok {pers st lst} {env : frontend.modular.reach.ReachEnv} {env' : Modular.ReachEnv}
    (hc : NMapRel absCopies env.copies env'.copies)
    (acc : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)) (n : arena.handle.NIdx) :
    PA pers st lst acc (clash_partners_one pers st env acc n)
      (fun A => Modular.clashPartnersOne env' A (absNIdx n)) := by
  intro hrel hinv st' acc' hr
  rw [clash_partners_one] at hr
  peel hr as g, hg
  have eg := hc.get_eq hg
  unfold Modular.clashPartnersOne
  cases g with
  | none =>
    rw [← eg]
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    exact ⟨(acc.val.map absNN).toArray, lst, rfl, by simp, hrel, hinv⟩
  | some cs =>
    rw [← eg]
    exact copies_partners_ok acc cs hrel hinv st' acc' hr

theorem clash_partners_loop_ok {pers} {env : frontend.modular.reach.ReachEnv} {env' : Modular.ReachEnv}
    (hc : NMapRel absCopies env.copies env'.copies) (ns : alloc.vec.Vec arena.handle.NIdx)
    (st : arena.monad.AState) (lst : AState) (acc : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx))
      (i : Std.Usize) :
      PA pers st lst acc (clash_partners_loop pers st env acc ns i)
        (fun A => ((ns.val.drop i.val).map absNIdx).foldlM (Modular.clashPartnersOne env') A) := by
  intro hrel hinv st' acc' hr
  rw [clash_partners_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len ns
  · rw [ite_eq_left hlt] at hr
    have hi := lt_len hlt
    peel hr as p, hp
    obtain ⟨_, rfl⟩ := vec_index_eq hp
    peel hr as q, hq
    obtain ⟨r, st1, acc1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective hr
    | Ok u =>
      obtain ⟨A1, lst1, hx1, hA1, hrel1, hinv1⟩ := clash_partners_one_ok hc acc _ hrel hinv st1 acc1 hq
      peel hr as i2, hi2
      have hv2 := usize_succ_val hi2
      obtain ⟨A2, lst2, hx2, hA2, hrel2, hinv2⟩ :=
        clash_partners_loop_ok hc ns st1 lst1 acc1 i2 hrel1 hinv1 st' acc' hr
      rw [usize_succ_val hi2] at hx2
      refine ⟨A2, lst2, ?_, hA2, hrel2, hinv2⟩
      beta_reduce
      rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldlM_cons]
      have e1 : (acc1.val.map absNN).toArray = A1 := by rw [hA1]
      rw [e1] at hx2
      exact (am_bind_ok hx1).trans hx2
  · rw [ite_eq_right hlt] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    refine ⟨(acc.val.map absNN).toArray, lst, ?_, by simp, hrel, hinv⟩
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by ns.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`clash_partners` is `clashPartners`.** -/
theorem clash_partners_ok {pers st lst} {env : frontend.modular.reach.ReachEnv} {env' : Modular.ReachEnv}
    (hc : NMapRel absCopies env.copies env'.copies)
    (acc : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)) (ns : alloc.vec.Vec arena.handle.NIdx) :
    PA pers st lst acc (clash_partners pers st env acc ns)
      (fun A => Modular.clashPartners env' A (ns.val.map absNIdx)) := by
  intro hrel hinv st' acc' hr
  simpa [Modular.clashPartners] using clash_partners_loop_ok hc ns st lst acc 0#usize hrel hinv st' acc' hr

/-! ## Proof statuses -/

/-- **`status_is` is `statusIs`.** -/
theorem status_is_eq {p : frontend.modular.reach.ProofStatus} {yes : Bool} {o : Bool}
    (h : status_is p yes = ok o) : o = Modular.statusIs (absProofStatus p) yes := by
  cases p <;> cases Result.ok_injective h <;> simp [absProofStatus, Modular.statusIs]

/-! ## The worklist's start -/

/-- **`reach_log_init` is `ReachLog.init`.** -/
theorem reach_log_init_rel {rs : alloc.vec.Vec arena.handle.NIdx} {l}
    (h : reach_log_init rs = ok l) : ReachLogRel l (Modular.ReachLog.init (rs.val.map absNIdx)) := by
  rw [reach_log_init] at h
  peel h as m, hm
  have hs : NSet m (∅ : Std.HashSet NIdx) := by
    obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := hN) hm
    exact ⟨hinv, fun k => by rw [hnone]; simp⟩
  peel h as q, hq
  obtain ⟨sp, seen, stack⟩ := q
  have hp := push_names_eq hs (StackRel.empty absNIdx (alloc.vec.Vec.new arena.handle.NIdx)) hq
  cases Result.ok_injective h
  exact ⟨hp.1, hs, rfl, rfl, rfl, hp.2⟩

/-! ## The read order's records -/

/-- The twin's step of `inReadOrder`. -/
def irStep (L : Modular.ReachLog) (acc : Array IDeclaration × Array NIdx) (j : Nat) :
    Array IDeclaration × Array NIdx :=
  match L.ctx[j]?, L.homes[j]? with
  | some d, some h => (acc.1.push d, acc.2.push h)
  | _, _ => acc

theorem inReadOrder_eq (L : Modular.ReachLog) (o : Array Nat) :
    Modular.inReadOrder L o = o.foldl (irStep L) (#[], #[]) := rfl

theorem in_read_order_loop_eq (l : frontend.modular.reach.ReachLog) {L : Modular.ReachLog}
    (hl : ReachLogRel l L) (o : alloc.vec.Vec Std.U64) (ho : ∀ j ∈ o.val, j.val ≤ Std.Usize.max)
    (ctx : alloc.vec.Vec arena.env.IDeclaration) (homes : alloc.vec.Vec arena.handle.NIdx)
    (i : Std.Usize) {r} (h : in_read_order_loop l o ctx homes i = ok r) :
    (r.1.val.map absIDeclaration, r.2.val.map absNIdx) =
      (let p := ((o.val.drop i.val).map (·.val)).foldl (irStep L)
          ((ctx.val.map absIDeclaration).toArray, (homes.val.map absNIdx).toArray)
       (p.1.toList, p.2.toList)) := by
  rw [in_read_order_loop] at h
  have hc := congrArg List.length hl.ctx
  have hh := congrArg List.length hl.homes
  simp only [List.length_map, Array.length_toList] at hc hh
  by_cases hlt : i < alloc.vec.Vec.len o
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    have hfit := ho _ (List.getElem_mem hi)
    peel h as j, hj
    have ej : j.val = (o.val[i.val]).val := by rw [← Result.ok_injective hj]; exact ConRon.Refine2.Frontend.Olean.cast_usize_val hfit
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons]
    peel h as q, hq
    obtain ⟨ctx1, homes1⟩ := q
    peel h as i2, hi2
    have hv2 := usize_succ_val hi2
    have ih := in_read_order_loop_eq l hl o ho ctx1 homes1 i2 h
    rw [hv2] at ih
    rw [ih]
    by_cases h1 : j < alloc.vec.Vec.len l.ctx
    · rw [ite_eq_left h1] at hq
      have h1' := lt_len h1
      by_cases h2 : j < alloc.vec.Vec.len l.homes
      · rw [ite_eq_left h2] at hq
        have h2' := lt_len h2
        peel hq as d, hd
        obtain ⟨_, rfl⟩ := vec_index_eq hd
        peel hq as d1, hd1
        have ed := i_declaration_dup_abs hd1
        peel hq as ctx2, hctx2
        peel hq as n, hn
        obtain ⟨_, rfl⟩ := vec_index_eq hn
        simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hq
        peel hq as homes2, hhomes2
        cases Result.ok_injective hq
        have ec : L.ctx[(o.val[i.val]).val]? = some (absIDeclaration l.ctx.val[j.val]) := by
          rw [← ej, ← Array.getElem?_toList, ← hl.ctx, List.getElem?_map, List.getElem?_eq_getElem h1']
          rfl
        have eh : L.homes[(o.val[i.val]).val]? = some (absNIdx l.homes.val[j.val]) := by
          rw [← ej, ← Array.getElem?_toList, ← hl.homes, List.getElem?_map, List.getElem?_eq_getElem h2']
          rfl
        simp only [irStep, ec, eh, ConRon.Refine.vec_push_val hctx2, ConRon.Refine.vec_push_val hhomes2,
          List.map_append, List.map_cons, List.map_nil, ed]
        simp
      · rw [ite_eq_right h2] at hq
        cases Result.ok_injective hq
        have eh : L.homes[(o.val[i.val]).val]? = none := by
          rw [Array.getElem?_eq_none]; have := not_lt_len h2; omega
        simp only [irStep, eh]
        cases L.ctx[(o.val[i.val]).val]? <;> rfl
    · rw [ite_eq_right h1] at hq
      cases Result.ok_injective hq
      have ec : L.ctx[(o.val[i.val]).val]? = none := by
        rw [Array.getElem?_eq_none]; have := not_lt_len h1; omega
      simp only [irStep, ec]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by o.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`in_read_order` is `inReadOrder`**, at read-order positions that fit a `usize`. -/
theorem in_read_order_eq {l : frontend.modular.reach.ReachLog} {L : Modular.ReachLog}
    (hl : ReachLogRel l L) {o : alloc.vec.Vec Std.U64} (ho : ∀ j ∈ o.val, j.val ≤ Std.Usize.max) {r}
    (h : in_read_order l o = ok r) :
    r.1.val.map absIDeclaration = (Modular.inReadOrder L (o.val.map (·.val)).toArray).1.toList ∧
      r.2.val.map absNIdx = (Modular.inReadOrder L (o.val.map (·.val)).toArray).2.toList := by
  rw [in_read_order] at h
  have := in_read_order_loop_eq l hl o ho _ _ 0#usize h
  simp only [Prod.mk.injEq] at this
  rw [inReadOrder_eq]
  simpa [Array.foldl_toList, alloc.vec.Vec.with_capacity] using this

/-! ## A clash's spots -/

/-- A spot with its statement and kind, against the twin's. -/
def SpotInfoRel (x : frontend.modular.reach.Spot × frontend.olean.spec.StmtRec ×
      frontend.olean.spec.CKindF arena.handle.NIdx Unit)
    (y : Modular.Spot × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) : Prop :=
  absSpot x.1 = y.1 ∧ InfoRel x.2 y.2

/-- The twin's spot of one clash copy. -/
@[reducible] def clashSpotT (pk : Arena.Frontend.Olean.OleanPins) (W : Arena.Frontend.Olean.WorkerReads)
    (y : ConLeche.Frontend.Olean.Copy × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) :
    Option (Modular.Spot × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) :=
  (W.index.at y.1).map fun q => ((⟨⟨W.loads.nameAt pk y.1.mod, W.loads.levelAt y.1.mod⟩, q⟩ : Modular.Spot), y.2.1, y.2.2)

/-- **`clash_spot` is the twin's spot of a copy.** -/
theorem clash_spot_eq {pk : frontend.olean.spec.OleanPins} {wr : frontend.olean.index.WorkerReads}
    {W : Arena.Frontend.Olean.WorkerReads} (hw : WorkerReadsRel wr W)
    {x : frontend.olean.index.Copy × frontend.olean.spec.StmtRec × frontend.olean.spec.CKindF arena.handle.NIdx Unit}
    {y} (hx : CopyInfoRel x y) (hfit : CopyFits x.1) {o} (h : clash_spot pk wr x = ok o) :
    Option.Rel SpotInfoRel o (clashSpotT (absPins pk) W y) := by
  obtain ⟨c, sr, k⟩ := x
  obtain ⟨cp, cv, k'⟩ := y
  obtain ⟨hc, hs, hk⟩ := hx
  simp only at hc hs hk hfit
  subst hc hs
  rw [clash_spot] at h
  peel h as o1, ho1
  have e1 := name_index_at_eq hw.index hfit ho1
  rw [clashSpotT, ← e1]
  cases o1 with
  | none => cases Result.ok_injective h; exact .none
  | some q =>
    peel h as n, hn
    have en := header_loads_name_at_eq (pk := pk) hw.loads hfit.1 hn
    peel h as ol, hol
    have el := header_loads_level_at_eq hw.loads hfit.1 hol
    peel h as np, hnp
    cases name_position_dup_ok hnp
    peel h as sr1, hsr1
    cases stmt_rec_dup_eq hsr1
    peel h as k1, hk1
    cases c_kind_names_dup_eq hk1
    cases Result.ok_injective h
    exact .some ⟨by simp [absSpot, absPartKey, en, el], rfl, hk⟩

theorem clash_spots_loop_eq {pk : frontend.olean.spec.OleanPins} {wr : frontend.olean.index.WorkerReads}
    {W : Arena.Frontend.Olean.WorkerReads} (hw : WorkerReadsRel wr W)
    (v : alloc.vec.Vec (frontend.olean.index.Copy × frontend.olean.spec.StmtRec ×
      frontend.olean.spec.CKindF arena.handle.NIdx Unit))
    {V : List (ConLeche.Frontend.Olean.Copy × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit)}
    (hv : List.Forall₂ CopyInfoRel v.val V) (hfit : ∀ x ∈ v.val, CopyFits x.1)
    (out : alloc.vec.Vec (frontend.modular.reach.Spot × frontend.olean.spec.StmtRec ×
      frontend.olean.spec.CKindF arena.handle.NIdx Unit)) {O}
    (hout : List.Forall₂ SpotInfoRel out.val O) (i : Std.Usize) {o}
    (h : clash_spots_loop pk wr v out i = ok o) :
    List.Forall₂ SpotInfoRel o.val (O ++ (V.drop i.val).filterMap (clashSpotT (absPins pk) W)) := by
  have hlen := List.Forall₂.length_eq hv
  rw [clash_spots_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len v
  · rw [ite_eq_left hlt] at h
    have hi := lt_len hlt
    peel h as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    have hr : CopyInfoRel v.val[i.val] (V[i.val]'(by omega)) := List.forall₂_iff_get.mp hv |>.2 _ hi _
    peel h as o1, ho1
    have e1 := clash_spot_eq hw hr (hfit _ (List.getElem_mem hi)) ho1
    rw [List.drop_eq_getElem_cons (by omega : i.val < V.length), List.filterMap_cons]
    peel h as out1, hout1
    peel h as i2, hi2
    have hv2 := usize_succ_val hi2
    generalize clashSpotT (absPins pk) W V[i.val] = t at e1 ⊢
    cases e1 with
    | none =>
      cases Result.ok_injective hout1
      have ih := clash_spots_loop_eq hw v hv hfit out hout i2 h
      rw [hv2] at ih
      simpa using ih
    | some hab =>
      rename_i a b
      have hout' : List.Forall₂ SpotInfoRel out1.val (O ++ [b]) := by
        rw [ConRon.Refine.vec_push_val hout1]
        exact List.rel_append hout (List.Forall₂.cons hab .nil)
      have ih := clash_spots_loop_eq hw v hv hfit out1 hout' i2 h
      rw [hv2] at ih
      simpa using ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by have := not_lt_len hlt; omega)]
    simpa using hout
termination_by v.val.length - i.val
decreasing_by all_goals (have := lt_len hlt; omega)

/-- **`clash_spots` is `clashSpots`.** -/
theorem clash_spots_eq {pk : frontend.olean.spec.OleanPins} {wr : frontend.olean.index.WorkerReads}
    {env' : Modular.ReachEnv} (hw : WorkerReadsRel wr env'.wr)
    {cl : frontend.olean.index.Clash} {cl' : Arena.Frontend.Olean.Clash} (hc : ClashRel cl cl')
    (hfit : ∀ x ∈ cl.copies.val, CopyFits x.1) {o} (h : clash_spots pk wr cl = ok o) :
    List.Forall₂ SpotInfoRel o.val (Modular.clashSpots (absPins pk) env' cl') := by
  rw [clash_spots] at h
  have := clash_spots_loop_eq hw cl.copies hc.copies hfit _ (O := []) (by exact List.Forall₂.nil) 0#usize h
  simpa [Modular.clashSpots, clashSpotT] using this

end ConRon.Refine2.Modular
