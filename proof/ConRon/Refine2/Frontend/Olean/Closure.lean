/-
# `ConRon.Refine2.Frontend.Olean.Closure` — `olean/closure.rs`: the import walk

**Tasks #142, #143, Theorem 2.**  The import walk's steps (`import_on_path`, `walk_expand`,
`closure_order`'s pushes) against the twin's, and the stacks and sets the reader's walks
share.

**A stack** is a `Vec` and its top (`StackRel`): the live prefix, reversed, is the twin's list,
head on top; a popped slot stays until it is overwritten.
-/
import ConRon.Refine2.Frontend.Olean.Merge
import ConRon.Refine2.Frontend.Olean.Files
import ConRon.Arena.Frontend.Olean.Closure

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.closure

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine2 (AErrKind absAErrKind AErrSim)
open ConRon.Refine.HashMap2 (Inv toFun)
open ConRon.Refine2.Lockstep (LSP)

/-! ## The stacks -/

/-- **A stack**: the live prefix, reversed, is the twin's list. -/
def StackRel {α β : Type} (A : α → β) (stack : alloc.vec.Vec α) (sp : Std.Usize) (l : List β) : Prop :=
  sp.val ≤ stack.val.length ∧ (stack.val.take sp.val).reverse.map A = l

theorem StackRel.empty {α β : Type} (A : α → β) (stack : alloc.vec.Vec α) :
    StackRel A stack 0#usize [] :=
  ⟨by simp, by simp⟩

theorem StackRel.nil_of_zero {α β : Type} {A : α → β} {stack : alloc.vec.Vec α} {sp : Std.Usize}
    {l : List β} (h : StackRel A stack sp l) (h0 : ¬ sp > 0#usize) : l = [] := by
  have : ¬ (0#usize : Std.Usize).val < sp.val := h0
  have e : sp.val = 0 := by simpa using this
  rw [← h.2, e]; simp

/-- The top of a stack. -/
theorem StackRel.pop {α β : Type} {A : α → β} {stack : alloc.vec.Vec α} {sp sp1 : Std.Usize}
    {l : List β} (h : StackRel A stack sp l) (hpos : sp > 0#usize) (h1 : sp - 1#usize = ok sp1) :
    ∃ (hi : sp1.val < stack.val.length) (l' : List β), l = A stack.val[sp1.val] :: l' ∧
      StackRel A stack sp1 l' := by
  have hv := ConRon.Refine.HashMap.uscalar_sub_eq h1
  have hp : (0#usize : Std.Usize).val < sp.val := hpos
  have l1 : (1#usize : Std.Usize).val = 1 := by decide
  have l0 : (0#usize : Std.Usize).val = 0 := by decide
  rw [l1] at hv; rw [l0] at hp
  have hle := h.1
  have hi : sp1.val < stack.val.length := by omega
  have e : sp.val = sp1.val + 1 := by omega
  refine ⟨hi, (stack.val.take sp1.val).reverse.map A, ?_, by omega, rfl⟩
  rw [← h.2, e, List.take_succ_eq_append_getElem hi]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.map_cons]

theorem StackRel.exists_cons {α β : Type} {A : α → β} {stack : alloc.vec.Vec α} {sp : Std.Usize}
    {l : List β} (h : StackRel A stack sp l) (hpos : sp > 0#usize) : ∃ y l', l = y :: l' := by
  have hp : (0#usize : Std.Usize).val < sp.val := hpos
  have l0 : (0#usize : Std.Usize).val = 0 := by decide
  rw [l0] at hp
  have hle := h.1
  cases hl : l with
  | nil =>
    have := h.2
    rw [hl] at this
    simp only [List.map_eq_nil_iff, List.reverse_eq_nil_iff, List.take_eq_nil_iff] at this
    rcases this with h' | h'
    · omega
    · rw [h'] at hle; simp at hle; omega
  | cons y t => exact ⟨y, t, rfl⟩

/-- A push at the top: the slot overwritten, or the vector grown. -/
theorem StackRel.push {α β : Type} {A : α → β} {stack st1 : alloc.vec.Vec α} {sp i1 : Std.Usize}
    {l : List β} {x : α} (h : StackRel A stack sp l)
    (hs : (if sp < alloc.vec.Vec.len stack then do
        let (_, back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) stack sp
        ok (back x)
      else alloc.vec.Vec.push stack x) = ok st1)
    (hi : sp + 1#usize = ok i1) : StackRel A st1 i1 (A x :: l) := by
  have hv : i1.val = sp.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi]; rfl
  have hle := h.1
  have hd : st1.val.length ≥ sp.val + 1 ∧ st1.val.take (sp.val + 1) = stack.val.take sp.val ++ [x] := by
    by_cases hlt : sp < alloc.vec.Vec.len stack
    · rw [ite_eq_left hlt] at hs
      peel hs as p, hp
      obtain ⟨y, back⟩ := p
      have : Inhabited α := ⟨x⟩
      obtain ⟨hl, -, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hp
      cases Result.ok_injective hs
      have hl' : sp.val < stack.val.length := hl
      constructor
      · simp [alloc.vec.Vec.set]; omega
      · simp [alloc.vec.Vec.set, List.take_set]
        have n : (stack.val.take sp.val).length = sp.val := by simp; omega
        rw [List.take_succ_eq_append_getElem hl', List.set_append_right _ _ (by omega), n, Nat.sub_self]
        rfl
    · rw [ite_eq_right hlt] at hs
      have e : sp.val = stack.val.length := by
        have : ¬ sp.val < (alloc.vec.Vec.len stack).val := hlt
        rw [vec_len_val] at this; omega
      rw [ConRon.Refine.vec_push_val hs, e]
      simp
  refine ⟨by omega, ?_⟩
  rw [hv, hd.2, ← h.2]
  simp

/-- A walk's entry, as the twin's. -/
@[reducible] def absWEnt (p : arena.handle.NIdx × Bool) : NIdx × Bool := (absNIdx p.1, p.2)

/-- `walk_push`. -/
theorem walk_push_eq {stack : alloc.vec.Vec (arena.handle.NIdx × Bool)} {sp : Std.Usize}
    {l : List (NIdx × Bool)} {x i st1} (h : StackRel absWEnt stack sp l)
    (hr : walk_push stack sp x = ok (i, st1)) : StackRel absWEnt st1 i (absWEnt x :: l) := by
  rw [walk_push] at hr
  peel hr as t, ht
  peel hr as i1, hi1
  cases Result.ok_injective hr
  exact h.push ht hi1

/-! ## The sets -/

/-- `NIdx`'s table, as a set of the twin's handles. -/
abbrev NSet := SetRel arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable absNIdx

/-! ## A walk's output and its fuel -/

/-- The relation of a walk's output. -/
abbrev OutA (o : alloc.vec.Vec arena.handle.NIdx) (o' : _root_.Array NIdx) : Prop :=
  o.val.map absNIdx = o'.toList

theorem out_of_fuel_eq {T : Type} {r} (h : out_of_fuel T = ok r) :
    ∃ e, r = .Err e ∧ absAErrKind e = some .internal := by
  rw [out_of_fuel] at h
  exact (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) _ h

/-! ## The import walk -/

/-- An import's module, as the twin's. -/
@[reducible] def impMod (i : frontend.olean.spec.ImportF arena.handle.NIdx) : NIdx := absNIdx i.module

theorem import_on_path_loop_eq (imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))
    {seen done1 : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {s d : _root_.Std.HashSet NIdx}
    (hs : NSet seen s) (hd : NSet done1 d) (i : Std.Usize) {o}
    (h : import_on_path_loop imps seen done1 i = ok o) :
    o.map absNIdx = ((imps.val.drop i.val).map impMod).find? fun c => s.contains c && !d.contains c := by
  rw [import_on_path_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len imps
  · rw [ite_eq_left hlt] at h
    peel h as x, hx
    obtain ⟨hi, rfl⟩ := vec_index_eq hx
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 hs hb
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.find?_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      peel h as b1, hb1
      have eb1 := SetRel.contains_key nidx_eq2 hd hb1
      have hT : s.contains (impMod imps.val[i.val]) = true := by rw [← eb]; exact cb
      by_cases cb1 : b1 = true
      · rw [ite_eq_left cb1] at h
        peel h as i2, hi2
        have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
        have ih := import_on_path_loop_eq imps hs hd i2 h
        rw [hi2v] at ih
        have hD : d.contains (impMod imps.val[i.val]) = true := by rw [← eb1]; exact cb1
        simp only [hT, hD, Bool.not_true, Bool.and_false]
        exact ih
      · rw [ite_eq_right cb1] at h
        cases Result.ok_injective h
        have hD : d.contains (impMod imps.val[i.val]) = false := by rw [← eb1]; simpa using cb1
        simp [hT, hD]
    · rw [ite_eq_right cb] at h
      peel h as i2, hi2
      have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
      have ih := import_on_path_loop_eq imps hs hd i2 h
      rw [hi2v] at ih
      have hT : s.contains (impMod imps.val[i.val]) = false := by rw [← eb]; simpa using cb
      simp only [hT, Bool.false_and]
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hle : imps.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len imps).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le hle]; rfl
termination_by imps.val.length - i.val
decreasing_by
  all_goals
    have : i.val < (alloc.vec.Vec.len imps).val := hlt
    rw [vec_len_val] at this
    omega

/-- **`import_on_path` is `imps.find?`.** -/
theorem import_on_path_eq {imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {seen done1 : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {s d : _root_.Std.HashSet NIdx}
    (hs : NSet seen s) (hd : NSet done1 d) {o} (h : import_on_path imps seen done1 = ok o) :
    o.map absNIdx = (imps.val.map impMod).find? fun c => s.contains c && !d.contains c := by
  rw [import_on_path] at h
  simpa using import_on_path_loop_eq imps hs hd _ h

/-- The twin's children of an expansion. -/
@[reducible] def walkKids (s : _root_.Std.HashSet NIdx) (l : List NIdx) : List (NIdx × Bool) :=
  (l.filter (!s.contains ·)).map (·, false)

theorem walk_expand_loop_eq (stack : alloc.vec.Vec (arena.handle.NIdx × Bool))
    (imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))
    {seen : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {s' : _root_.Std.HashSet NIdx} (hs : NSet seen s')
    (s i : Std.Usize) {l : List (NIdx × Bool)} (hl : StackRel absWEnt stack s l) {o}
    (h : walk_expand_loop stack imps seen s i = ok o) :
    StackRel absWEnt o.2 o.1 (walkKids s' ((imps.val.take i.val).map impMod) ++ l) := by
  rw [walk_expand_loop] at h
  by_cases hp : i > 0#usize
  · rw [ite_eq_left hp] at h
    peel h as i1, hi1
    have hv := ConRon.Refine.HashMap.uscalar_sub_eq hi1
    have l1 : (1#usize : Std.Usize).val = 1 := by decide
    rw [l1] at hv
    have hp' : (0#usize : Std.Usize).val < i.val := hp
    have l0 : (0#usize : Std.Usize).val = 0 := by decide
    rw [l0] at hp'
    have e : i.val = i1.val + 1 := by omega
    peel h as x, hx
    obtain ⟨hb, rfl⟩ := vec_index_eq hx
    peel h as c, hc
    have ec := SetRel.contains_key nidx_eq2 hs hc
    have ek : walkKids s' ((imps.val.take (i1.val + 1)).map impMod) =
        walkKids s' ((imps.val.take i1.val).map impMod) ++ walkKids s' [impMod imps.val[i1.val]] := by
      rw [List.take_succ_eq_append_getElem hb, List.map_append, walkKids, List.filter_append,
        List.map_append]
      rfl
    rw [e, ek, List.append_assoc]
    by_cases cc : c = true
    · rw [ite_eq_left cc] at h
      have hf : s'.contains (impMod imps.val[i1.val]) = true := by rw [← ec]; exact cc
      have := walk_expand_loop_eq stack imps hs s i1 hl h
      simpa [walkKids, hf] using this
    · rw [ite_eq_right cc] at h
      have hf : s'.contains (impMod imps.val[i1.val]) = false := by rw [← ec]; simpa using cc
      peel h as n, hn
      cases nidx_dup2_ok hn
      peel h as q, hq
      obtain ⟨s1, st1⟩ := q
      have := walk_expand_loop_eq st1 imps hs s1 i1 (walk_push_eq hl hq) h
      simpa [walkKids, hf] using this
  · rw [ite_eq_right hp] at h
    cases Result.ok_injective h
    have : ¬ (0#usize : Std.Usize).val < i.val := hp
    have e : i.val = 0 := by simpa using this
    rw [e]
    simpa [walkKids] using hl
termination_by i.val
decreasing_by all_goals omega

/-- **`walk_expand` is `kids ++ (m, true) :: rest`.** -/
theorem walk_expand_eq {stack : alloc.vec.Vec (arena.handle.NIdx × Bool)}
    {imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {seen : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {s' : _root_.Std.HashSet NIdx} (hs : NSet seen s')
    {sp : Std.Usize} {m : arena.handle.NIdx} {l : List (NIdx × Bool)} (hl : StackRel absWEnt stack sp l) {o}
    (h : walk_expand stack sp m imps seen = ok o) :
    StackRel absWEnt o.2 o.1 (walkKids s' (imps.val.map impMod) ++ (absNIdx m, true) :: l) := by
  rw [walk_expand] at h
  peel h as n, hn
  cases nidx_dup2_ok hn
  peel h as q, hq
  obtain ⟨s1, st1⟩ := q
  have := walk_expand_loop_eq st1 imps hs s1 _ (walk_push_eq hl hq) h
  rwa [vec_len_val, List.take_length] at this

/-- `roots`, the last first, onto the walk's stack: `roots.head` on top. -/
theorem closure_order_loop_eq (roots : alloc.vec.Vec arena.handle.NIdx)
    (stack : alloc.vec.Vec (arena.handle.NIdx × Bool)) (sp i : Std.Usize) {l : List (NIdx × Bool)}
    (hl : StackRel absWEnt stack sp l) {o} (h : closure_order_loop roots stack sp i = ok o) :
    StackRel absWEnt o.1 o.2 ((roots.val.take i.val).map (fun r => (absNIdx r, false)) ++ l) := by
  rw [closure_order_loop] at h
  by_cases hp : i > 0#usize
  · rw [ite_eq_left hp] at h
    peel h as i1, hi1
    have hv := ConRon.Refine.HashMap.uscalar_sub_eq hi1
    have l1 : (1#usize : Std.Usize).val = 1 := by decide
    rw [l1] at hv
    have hp' : (0#usize : Std.Usize).val < i.val := hp
    have l0 : (0#usize : Std.Usize).val = 0 := by decide
    rw [l0] at hp'
    have e : i.val = i1.val + 1 := by omega
    peel h as x, hx
    obtain ⟨hb, rfl⟩ := vec_index_eq hx
    peel h as n, hn
    cases nidx_dup2_ok hn
    peel h as q, hq
    obtain ⟨sp1, st1⟩ := q
    have := closure_order_loop_eq roots st1 sp1 i1 (walk_push_eq hl hq) h
    rw [e, List.take_succ_eq_append_getElem hb, List.map_append, List.append_assoc]
    exact this
  · rw [ite_eq_right hp] at h
    cases Result.ok_injective h
    have : ¬ (0#usize : Std.Usize).val < i.val := hp
    have e : i.val = 0 := by simpa using this
    rw [e]
    simpa using hl
termination_by i.val
decreasing_by all_goals omega


end ConRon.Refine2.Frontend.Olean
