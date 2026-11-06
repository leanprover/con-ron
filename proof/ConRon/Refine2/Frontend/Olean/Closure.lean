/-
# `ConRon.Refine2.Frontend.Olean.Closure` — `olean/closure.rs`: what a constant mentions

**Task #142, Theorem 2.**  `consts_go` and `consts_of` against the twin's `constsGo` and
`constsOf`.  They read the store and no file, so both outcomes are claimed.

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
open ConRon.Arena.Frontend.Olean (constsGo constsOf addN outOfFuel entryDeps)
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

/-- `stack_push`. -/
theorem stack_push_eq {stack : alloc.vec.Vec arena.handle.EIdx} {sp : Std.Usize} {l : List EIdx}
    {x : arena.handle.EIdx} {i st1} (h : StackRel absEIdx stack sp l)
    (hr : stack_push stack sp x = ok (i, st1)) : StackRel absEIdx st1 i (absEIdx x :: l) := by
  rw [stack_push] at hr
  peel hr as t, ht
  peel hr as i1, hi1
  cases Result.ok_injective hr
  exact h.push ht hi1

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

/-- `EIdx`'s table, as a set of the twin's handles. -/
abbrev ESet := SetRel arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable absEIdx

/-- **`add_n` is `addN`.** -/
theorem add_n_eq {seen seen' : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    {sn : _root_.Std.HashSet NIdx} {out out' : alloc.vec.Vec arena.handle.NIdx} {o : Array NIdx}
    {n : arena.handle.NIdx} (hs : NSet seen sn) (ho : out.val.map absNIdx = o.toList)
    (h : add_n seen out n = ok (seen', out')) :
    NSet seen' (addN sn o (absNIdx n)).1 ∧ out'.val.map absNIdx = (addN sn o (absNIdx n)).2.toList := by
  rw [add_n] at h
  peel h as b, hb
  have eb := SetRel.contains_key nidx_eq2 hs hb
  by_cases hc : b = true
  · rw [ite_eq_left hc] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    simp only [addN, ← eb, hc, ↓reduceIte]
    exact ⟨hs, ho⟩
  · rw [ite_eq_right hc] at h
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as p, hp
    obtain ⟨_, seen1⟩ := p
    peel h as out1, ho1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    have ins := SetRel.insert nidx_eq2 absNIdx_inj hs hp
    have hf : sn.contains (absNIdx n) = false := by rw [← eb]; simpa using hc
    simp only [addN, hf, Bool.false_eq_true, ↓reduceIte]
    refine ⟨ins, ?_⟩
    rw [ConRon.Refine.vec_push_val ho1]
    simp [ho]

/-! ## The twin's walk, tag by tag -/

/-- The children of a node, as `constsGo` pushes them. -/
def kids : ENodeView → List EIdx
  | .app f a => [f, a]
  | .lam t b | .forallE t b => [t, b]
  | .letE t w b => [t, w, b]
  | .proj _ _ x => [x]
  | .fvar _ t => [t]
  | _ => []

section views
open ConRon.Refine2.Lockstep ConRon.Refine2

theorem kids_app (st : EStore) (i : EIdx) (hi : i.tag = ETag.app) :
    (st.view i).map kids = (st.viewApp i).map (fun p => [p.1, p.2]) := by
  rw [tagView_app _ _ hi, Option.map_map]; rfl

theorem kids_bind (st : EStore) (i : EIdx) (hi : ETag.isBind i.tag = true) :
    (st.view i).map kids = (st.viewBind i).map (fun p => [p.1, p.2]) := by
  rw [estore_view_of_bind st hi, Option.map_map]
  congr 1
  funext p
  have : i.tag = ETag.lam ∨ i.tag = ETag.forallE := by simpa [ETag.isBind] using hi
  rcases this with h | h <;> simp [kids, eBindView, h, ETag.lam, ETag.forallE]

theorem kids_let (st : EStore) (i : EIdx) (hi : i.tag = ETag.letE) :
    (st.view i).map kids = (st.viewLet i).map (fun p => [p.1, p.2.1, p.2.2]) := by
  have key : ∀ t : ETables, (t.get i).map kids = (t.getLet i).map (fun p => [p.1, p.2.1, p.2.2]) := by
    intro t
    simp only [ETables.get, ETables.getLet, hi, Option.map_map]
    simp (config := {decide := true}) only [ite_false, ite_true]
    cases t.lets.node? i.idxNat <;> rfl
  rw [EStore.view, EStore.viewLet]
  by_cases hp : i.isPersistent
  · rw [ite_eq_left hp, ite_eq_left hp, EStore.persGetLet]; exact key _
  · rw [ite_eq_right hp, ite_eq_right hp]
    by_cases hs : st.scratchOn
    · rw [ite_eq_left hs, ite_eq_left hs]; exact key _
    · rw [ite_eq_right hs, ite_eq_right hs]; rfl

theorem kids_proj (st : EStore) (i : EIdx) (hi : i.tag = ETag.proj) :
    (st.view i).map kids = (st.viewProj i).map (fun p => [p.2.2]) := by
  have key : ∀ t : ETables, (t.get i).map kids = (t.getProj i).map (fun p => [p.2.2]) := by
    intro t
    simp only [ETables.get, ETables.getProj, hi, Option.map_map]
    simp (config := {decide := true}) only [ite_false, ite_true]
    cases t.projs.node? i.idxNat <;> rfl
  rw [EStore.view, EStore.viewProj]
  by_cases hp : i.isPersistent
  · rw [ite_eq_left hp, ite_eq_left hp, EStore.persGetProj]; exact key _
  · rw [ite_eq_right hp, ite_eq_right hp]
    by_cases hs : st.scratchOn
    · rw [ite_eq_left hs, ite_eq_left hs]; exact key _
    · rw [ite_eq_right hs, ite_eq_right hs]; rfl

theorem kids_fvar (st : EStore) (i : EIdx) (hi : i.tag = ETag.fvar) :
    (st.view i).map kids = (st.viewFVarTy i).map (fun t => [t]) := by
  have key : ∀ t : ETables, (t.get i).map kids = (t.getFVarTy i).map (fun t => [t]) := by
    intro t
    simp only [ETables.get, ETables.getFVarTy, hi, Option.map_map]
    simp (config := {decide := true}) only [ite_false, ite_true]
    cases t.fvars.node? i.idxNat <;> rfl
  rw [EStore.view, EStore.viewFVarTy]
  by_cases hp : i.isPersistent
  · rw [ite_eq_left hp, ite_eq_left hp, EStore.persGetFVarTy]; exact key _
  · rw [ite_eq_right hp, ite_eq_right hp]
    by_cases hs : st.scratchOn
    · rw [ite_eq_left hs, ite_eq_left hs]; exact key _
    · rw [ite_eq_right hs, ite_eq_right hs]; rfl

theorem view_bind_run {δ : Type} (e : EIdx) (k : ENodeView → AM δ) (lst : AState) :
    (Arena.view e >>= k).run lst = match lst.store.view e with
      | some v => (k v).run lst
      | none => .error (Arena.CheckError.internal "arena: dangling expression handle") := by
  rw [StateT.run_bind, view_run_of]
  cases lst.store.view e <;> rfl

/-- The walk at a `const`. -/
theorem go_const_run {pk : Arena.Frontend.Olean.OleanPins} {f rest s sn o} {e : EIdx} (lst : AState)
    (ht : e.tag = ETag.const) :
    (constsGo pk (f + 1) (e :: rest) s sn o).run lst = match lst.store.viewConstName e with
      | some n => (constsGo pk f rest s (addN sn o n).1 (addN sn o n).2).run lst
      | none => .error (Arena.CheckError.internal "arena: dangling expression handle") := by
  rw [constsGo, ite_eq_left (by simp [ht])]
  rw [view_bind_run, tagView_const _ _ ht, EStore_viewConstName_eq]
  cases lst.store.viewConst e <;> rfl

/-- The walk at a `lit`. -/
theorem go_lit_run {pk : Arena.Frontend.Olean.OleanPins} {f rest s sn o} {e : EIdx} (lst : AState)
    (ht : e.tag = ETag.lit) :
    (constsGo pk (f + 1) (e :: rest) s sn o).run lst = match lst.store.viewLit e with
      | some (.natVal _) => (constsGo pk f rest s (addN sn o pk.nNat).1 (addN sn o pk.nNat).2).run lst
      | some (.strVal _) =>
        (constsGo pk f rest s
          (addN (addN sn o pk.nCharOfNat).1 (addN sn o pk.nCharOfNat).2 pk.nStringOfList).1
          (addN (addN sn o pk.nCharOfNat).1 (addN sn o pk.nCharOfNat).2 pk.nStringOfList).2).run lst
      | none => .error (Arena.CheckError.internal "arena: dangling expression handle") := by
  rw [constsGo, ite_eq_left (by simp [ht])]
  rw [view_bind_run, tagView_lit _ _ ht]
  cases lst.store.viewLit e with
  | none => rfl
  | some l => cases l <;> rfl

/-- The walk at a leaf, or a node visited. -/
theorem go_skip {pk : Arena.Frontend.Olean.OleanPins} {f rest s sn o} {e : EIdx}
    (h1 : e.tag ≠ ETag.const) (h2 : e.tag ≠ ETag.lit)
    (h3 : (e.tag == ETag.bvar || e.tag == ETag.sort || s.contains e) = true) :
    constsGo pk (f + 1) (e :: rest) s sn o = constsGo pk f rest s sn o := by
  rw [constsGo, ite_eq_right (by simp [h1, h2]), ite_eq_left h3]

/-- The walk at a first visit of a tag past `proj`. -/
theorem go_past {pk : Arena.Frontend.Olean.OleanPins} {f rest s sn o} {e : EIdx}
    (h1 : e.tag ≠ ETag.const) (h2 : e.tag ≠ ETag.lit)
    (h3 : ¬ (e.tag == ETag.bvar || e.tag == ETag.sort || s.contains e) = true)
    (h4 : ETag.proj < e.tag) :
    constsGo pk (f + 1) (e :: rest) s sn o = constsGo pk f rest (s.insert e) sn o := by
  rw [constsGo, ite_eq_right (by simp [h1, h2]), ite_eq_right h3]
  dsimp only
  rw [ite_eq_left h4]

/-- The walk at a first visit of a compound node. -/
theorem go_comp_run {pk : Arena.Frontend.Olean.OleanPins} {f rest s sn o} {e : EIdx} (lst : AState)
    (h1 : e.tag ≠ ETag.const) (h2 : e.tag ≠ ETag.lit)
    (h3 : ¬ (e.tag == ETag.bvar || e.tag == ETag.sort || s.contains e) = true)
    (h4 : ¬ ETag.proj < e.tag) :
    (constsGo pk (f + 1) (e :: rest) s sn o).run lst = match (lst.store.view e).map kids with
      | some ks => (constsGo pk f (ks ++ rest) (s.insert e) sn o).run lst
      | none => .error (Arena.CheckError.internal "arena: dangling expression handle") := by
  rw [constsGo, ite_eq_right (by simp [h1, h2]), ite_eq_right h3]
  dsimp only
  rw [ite_eq_right h4, view_bind_run]
  cases lst.store.view e with
  | none => rfl
  | some v => cases v <;> rfl

/-! ## The tags -/

theorem abs_const : ConRon.Refine2.absU32 arena.handle.ETAG_CONST = ETag.const := by unfold arena.handle.ETAG_CONST; decide
theorem abs_lit : ConRon.Refine2.absU32 arena.handle.ETAG_LIT = ETag.lit := by unfold arena.handle.ETAG_LIT; decide
theorem abs_bvar : ConRon.Refine2.absU32 arena.handle.ETAG_BVAR = ETag.bvar := by unfold arena.handle.ETAG_BVAR; decide
theorem abs_sort : ConRon.Refine2.absU32 arena.handle.ETAG_SORT = ETag.sort := by unfold arena.handle.ETAG_SORT; decide
theorem abs_app : ConRon.Refine2.absU32 arena.handle.ETAG_APP = ETag.app := by unfold arena.handle.ETAG_APP; decide
theorem abs_lam : ConRon.Refine2.absU32 arena.handle.ETAG_LAM = ETag.lam := by unfold arena.handle.ETAG_LAM; decide
theorem abs_forallE : ConRon.Refine2.absU32 arena.handle.ETAG_FORALL_E = ETag.forallE := by unfold arena.handle.ETAG_FORALL_E; decide
theorem abs_letE : ConRon.Refine2.absU32 arena.handle.ETAG_LET_E = ETag.letE := by unfold arena.handle.ETAG_LET_E; decide
theorem abs_proj : ConRon.Refine2.absU32 arena.handle.ETAG_PROJ = ETag.proj := by unfold arena.handle.ETAG_PROJ; decide
theorem abs_fvar : ConRon.Refine2.absU32 arena.handle.ETAG_FVAR = ETag.fvar := by unfold arena.handle.ETAG_FVAR; decide

theorem tag_ne {t x : Std.U32} {k : UInt32} (hx : ConRon.Refine2.absU32 x = k) (h : ¬ t = x) : ConRon.Refine2.absU32 t ≠ k := by
  rw [← hx]; exact fun he => h (ConRon.Refine2.absU32_inj he)

/-! ## `consts_children` -/

/-- What `consts_children` claims, at the twin's children of the view. -/
def ChildOut (l : List EIdx) (V : Option (List EIdx))
    (o : core.result.Result Std.Usize kernel.core_types.CheckError × alloc.vec.Vec arena.handle.EIdx) : Prop :=
  match o.1 with
  | .Ok s => ∃ ks, V = some ks ∧ StackRel absEIdx o.2 s (ks ++ l)
  | .Err ce => absAErrKind ce = some .internal ∧ V = none

theorem dangling_arm {l : List EIdx} {stack o}
    (h : (do let r ← arena.monad.fail_dangling_e Std.Usize; ok (r, stack)) = ok o) :
    ChildOut l none o := by
  peel h as r, hr
  obtain ⟨v, rfl⟩ := fail_dangling_e_spec _ _ hr
  cases Result.ok_injective h
  exact ⟨rfl, rfl⟩

/-- **`consts_children`, at a tag no further than `proj`.** -/
theorem consts_children_eq {pers : arena.store.PersTier} {ar : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers ar ls) {stack sp} {l : List EIdx} {e : arena.handle.EIdx} {t : Std.U32} {o}
    (hs : StackRel absEIdx stack sp l) (ht : (absEIdx e).tag = ConRon.Refine2.absU32 t)
    (h : consts_children pers ar stack sp e t = ok o) :
    t = arena.handle.ETAG_APP ∨ t = arena.handle.ETAG_LAM ∨ t = arena.handle.ETAG_FORALL_E ∨
      t = arena.handle.ETAG_LET_E ∨ t = arena.handle.ETAG_PROJ ∨ t = arena.handle.ETAG_FVAR →
    ChildOut l ((ls.view (absEIdx e)).map kids) o := by
  intro hany
  rw [consts_children] at h
  by_cases c1 : t = arena.handle.ETAG_APP
  · rw [ite_eq_left c1] at h
    peel h as q, hq
    rw [kids_app _ _ (by rw [ht, c1, abs_app]), estore_view_app_abs hrel hq]
    cases q with
    | none => exact dangling_arm h
    | some p =>
      obtain ⟨f, a⟩ := p
      dsimp only at h
      peel h as p1, h1
      obtain ⟨s1, st1⟩ := p1
      peel h as p2, h2
      obtain ⟨s2, st2⟩ := p2
      cases Result.ok_injective h
      exact ⟨_, rfl, stack_push_eq (stack_push_eq hs h1) h2⟩
  rw [ite_eq_right c1] at h
  by_cases c2 : t = arena.handle.ETAG_LAM
  · rw [ite_eq_left c2] at h
    peel h as q, hq
    have hb : ETag.isBind (absEIdx e).tag = true := by rw [ht, c2, abs_lam]; rfl
    rw [kids_bind _ _ hb, estore_view_bind_abs hrel hb hq]
    cases q with
    | none => exact dangling_arm h
    | some p =>
      obtain ⟨f, a⟩ := p
      dsimp only at h
      peel h as p1, h1
      obtain ⟨s1, st1⟩ := p1
      peel h as p2, h2
      obtain ⟨s2, st2⟩ := p2
      cases Result.ok_injective h
      exact ⟨_, rfl, stack_push_eq (stack_push_eq hs h1) h2⟩
  rw [ite_eq_right c2] at h
  by_cases c3 : t = arena.handle.ETAG_FORALL_E
  · rw [ite_eq_left c3] at h
    peel h as q, hq
    have hb : ETag.isBind (absEIdx e).tag = true := by rw [ht, c3, abs_forallE]; rfl
    rw [kids_bind _ _ hb, estore_view_bind_abs hrel hb hq]
    cases q with
    | none => exact dangling_arm h
    | some p =>
      obtain ⟨f, a⟩ := p
      dsimp only at h
      peel h as p1, h1
      obtain ⟨s1, st1⟩ := p1
      peel h as p2, h2
      obtain ⟨s2, st2⟩ := p2
      cases Result.ok_injective h
      exact ⟨_, rfl, stack_push_eq (stack_push_eq hs h1) h2⟩
  rw [ite_eq_right c3] at h
  by_cases c4 : t = arena.handle.ETAG_LET_E
  · rw [ite_eq_left c4] at h
    peel h as q, hq
    rw [kids_let _ _ (by rw [ht, c4, abs_letE]), estore_view_let_abs hrel hq]
    cases q with
    | none => exact dangling_arm h
    | some p =>
      obtain ⟨f, v, a⟩ := p
      dsimp only at h
      peel h as p1, h1
      obtain ⟨s1, st1⟩ := p1
      peel h as p2, h2
      obtain ⟨s2, st2⟩ := p2
      peel h as p3, h3
      obtain ⟨s3, st3⟩ := p3
      cases Result.ok_injective h
      exact ⟨_, rfl, stack_push_eq (stack_push_eq (stack_push_eq hs h1) h2) h3⟩
  rw [ite_eq_right c4] at h
  by_cases c5 : t = arena.handle.ETAG_PROJ
  · rw [ite_eq_left c5] at h
    peel h as q, hq
    rw [kids_proj _ _ (by rw [ht, c5, abs_proj]), estore_view_proj_abs hrel hq]
    cases q with
    | none => exact dangling_arm h
    | some p =>
      obtain ⟨_, _, x⟩ := p
      dsimp only at h
      peel h as p1, h1
      obtain ⟨s1, st1⟩ := p1
      cases Result.ok_injective h
      exact ⟨_, rfl, stack_push_eq hs h1⟩
  rw [ite_eq_right c5] at h
  have c6 : t = arena.handle.ETAG_FVAR := by
    rcases hany with h' | h' | h' | h' | h' | h'
    · exact absurd h' c1
    · exact absurd h' c2
    · exact absurd h' c3
    · exact absurd h' c4
    · exact absurd h' c5
    · exact h'
  rw [ite_eq_left c6] at h
  peel h as q, hq
  rw [kids_fvar _ _ (by rw [ht, c6, abs_fvar]), estore_view_fvar_ty_abs hrel hq]
  cases q with
  | none => exact dangling_arm h
  | some ty =>
    dsimp only at h
    peel h as p1, h1
    obtain ⟨s1, st1⟩ := p1
    cases Result.ok_injective h
    exact ⟨_, rfl, stack_push_eq hs h1⟩

/-- **`consts_children`, past `proj`**: nothing pushed. -/
theorem consts_children_past {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {stack sp} {e : arena.handle.EIdx} {t : Std.U32} {o}
    (ht : ETag.proj < ConRon.Refine2.absU32 t)
    (h : consts_children pers ar stack sp e t = ok o) : o = (.Ok sp, stack) := by
  rw [consts_children] at h
  have ne : ∀ {x : Std.U32}, ¬ ETag.proj < ConRon.Refine2.absU32 x → ¬ t = x := by
    rintro x hx rfl; exact hx ht
  rw [ite_eq_right (ne (x := arena.handle.ETAG_APP) (by rw [abs_app]; decide)),
    ite_eq_right (ne (x := arena.handle.ETAG_LAM) (by rw [abs_lam]; decide)),
    ite_eq_right (ne (x := arena.handle.ETAG_FORALL_E) (by rw [abs_forallE]; decide)),
    ite_eq_right (ne (x := arena.handle.ETAG_LET_E) (by rw [abs_letE]; decide)),
    ite_eq_right (ne (x := arena.handle.ETAG_PROJ) (by rw [abs_proj]; decide)),
    ite_eq_right (ne (x := arena.handle.ETAG_FVAR) (by rw [abs_fvar]; decide))] at h
  exact (Result.ok_injective h).symm

/-! ## `consts_go` -/

/-- What `consts_children`'s reuse of the work space leaves. -/
structure WorkInv (w : ConstsWork) : Prop where
  seen : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable w.seen
  seenN : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable w.seen_n

/-- **What a read of the store with the work space claims**: `Ok` is a run of the twin, which
leaves the state as it was, and `Err` a failure at the same kind. -/
def WOut {α β : Type} (R : α → β → Prop) (x : AM β) (lst : AState)
    (r : core.result.Result α kernel.core_types.CheckError) (w : ConstsWork) : Prop :=
  match r with
  | .Ok a => ∃ b, x.run lst = .ok (b, lst) ∧ R a b ∧ WorkInv w
  | .Err e => AErrSim e (x.run lst)

theorem WOut.of_run {α β : Type} {R : α → β → Prop} {x y : AM β} {lst r w}
    (h : WOut R y lst r w) (e : x.run lst = y.run lst) : WOut (α := α) R x lst r w := by
  cases r with
  | Ok a => obtain ⟨b, hb, hr, hw⟩ := h; exact ⟨b, e.trans hb, hr, hw⟩
  | Err c => intro k hk; rw [e]; exact h k hk

/-- The relation of a walk's output. -/
abbrev OutA (o : alloc.vec.Vec arena.handle.NIdx) (o' : _root_.Array NIdx) : Prop :=
  o.val.map absNIdx = o'.toList

theorem out_of_fuel_eq {T : Type} {r} (h : out_of_fuel T = ok r) :
    ∃ e, r = .Err e ∧ absAErrKind e = some .internal := by
  rw [out_of_fuel] at h
  exact (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) _ h

theorem internal_sim {γ : Type} {e : kernel.core_types.CheckError} {m : String}
    (he : absAErrKind e = some .internal) :
    AErrSim e (.error (Arena.CheckError.internal m) : Except Arena.CheckError γ) :=
  twin_err_of_kind rfl he rfl

theorem dangling_e_sim {T : Type} {r} (h : arena.monad.fail_dangling_e T = ok r) :
    ∃ e, r = .Err e ∧ absAErrKind e = some .internal := by
  obtain ⟨v, rfl⟩ := fail_dangling_e_spec _ _ h
  exact ⟨_, rfl, rfl⟩

/-- **The walk's loop against `constsGo`.** -/
theorem consts_go_loop_eq {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} (hrel : AStateRel₀ pers st lst)
    (f : Nat) (w : ConstsWork) (sp : Std.Usize) (out : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64)
    (l : List EIdx) (s : _root_.Std.HashSet EIdx) (sn : _root_.Std.HashSet NIdx) (o' : _root_.Array NIdx)
    (hf : fuel.val = f) (hl : StackRel absEIdx w.stack sp l) (hs : ESet w.seen s) (hn : NSet w.seen_n sn)
    (ho : OutA out o') {r w'} (h : consts_go_loop pk pers st.store w sp out fuel = ok (r, w')) :
    WOut OutA (constsGo (absPins pk) f l s sn o') lst r w' := by
  rw [consts_go_loop] at h
  by_cases hsp : sp > 0#usize
  swap
  · rw [ite_eq_right hsp] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    have hnil := hl.nil_of_zero hsp
    subst hnil
    have e : constsGo (absPins pk) f [] s sn o' = pure o' := by rw [constsGo]
    rw [e]
    exact ⟨o', rfl, ho, hs.inv, hn.inv⟩
  rw [ite_eq_left hsp] at h
  by_cases h0 : fuel = 0#u64
  · rw [ite_eq_left h0] at h
    have hf0 : f = 0 := by rw [← hf, h0]; rfl
    subst hf0
    peel h as r0, hr0
    obtain ⟨c, rfl, hk⟩ := out_of_fuel_eq hr0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    obtain ⟨y, l', rfl⟩ := hl.exists_cons hsp
    have e : constsGo (absPins pk) 0 (y :: l') s sn o' = outOfFuel := by rw [constsGo]
    rw [e]
    exact internal_sim hk
  rw [ite_eq_right h0] at h
  peel h as fuel1, hfuel1
  peel h as sp1, hsp1
  peel h as e, he
  peel h as e1, he1
  cases eidx_dup2_ok he1
  peel h as t, ht
  obtain ⟨hi, l', rfl, hl'⟩ := hl.pop hsp hsp1
  obtain ⟨hei, rfl⟩ := vec_index_eq he
  generalize hE : w.stack.val[sp1.val] = e at *
  have hfv : fuel1.val = f - 1 := by
    rw [ConRon.Refine.HashMap.uscalar_sub_eq hfuel1, hf]; rfl
  have hfp : f ≠ 0 := by
    intro hz
    apply h0
    apply UScalar.eq_of_val_eq
    rw [hf, hz]; rfl
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hfv' : fuel1.val = f' := by rw [hfv]; rfl
  have htag : (absEIdx e).tag = ConRon.Refine2.absU32 t := eidx_tag_abs ht
  have hstore := hrel.store
  by_cases c1 : t = arena.handle.ETAG_CONST
  · rw [ite_eq_left c1] at h
    peel h as q, hq
    have hrun := go_const_run (pk := absPins pk) (f := f') (rest := l') (s := s) (sn := sn) (o := o') lst
      (e := absEIdx e) (by rw [htag, c1, abs_const])
    rw [estore_view_const_name_abs hstore hq] at hrun
    cases q with
    | none =>
      peel h as r0, hr0
      obtain ⟨c, rfl, hk⟩ := dangling_e_sim hr0
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      show AErrSim c _
      rw [hrun]
      exact internal_sim hk
    | some n =>
      dsimp only at h
      peel h as p, hp
      obtain ⟨hm, out1⟩ := p
      obtain ⟨h1, h2⟩ := add_n_eq hn ho hp
      exact (consts_go_loop_eq hrel f' { w with seen_n := hm } sp1 out1 fuel1 l' s _ _ hfv' hl' hs h1 h2 h).of_run hrun
  rw [ite_eq_right c1] at h
  have ne1 : (absEIdx e).tag ≠ ETag.const := by rw [htag]; exact tag_ne abs_const c1
  by_cases c2 : t = arena.handle.ETAG_LIT
  · rw [ite_eq_left c2] at h
    peel h as q, hq
    have hrun := go_lit_run (pk := absPins pk) (f := f') (rest := l') (s := s) (sn := sn) (o := o') lst
      (e := absEIdx e) (by rw [htag, c2, abs_lit])
    rw [ConRon.Refine2.Lockstep.PB.estore_view_lit_abs hstore hq] at hrun
    cases q with
    | none =>
      peel h as r0, hr0
      obtain ⟨c, rfl, hk⟩ := dangling_e_sim hr0
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      show AErrSim c _
      rw [hrun]
      exact internal_sim hk
    | some v =>
      cases v with
      | NatVal k =>
        dsimp only at h
        peel h as p, hp
        obtain ⟨hm, out1⟩ := p
        obtain ⟨h1, h2⟩ := add_n_eq hn ho hp
        exact (consts_go_loop_eq hrel f' { w with seen_n := hm } sp1 out1 fuel1 l' s _ _ hfv' hl' hs h1 h2 h).of_run hrun
      | StrVal k =>
        dsimp only at h
        peel h as p, hp
        obtain ⟨hm, out1⟩ := p
        obtain ⟨h1, h2⟩ := add_n_eq hn ho hp
        peel h as p2, hp2
        obtain ⟨hm2, out2⟩ := p2
        obtain ⟨h3, h4⟩ := add_n_eq h1 h2 hp2
        exact (consts_go_loop_eq hrel f' { w with seen_n := hm2 } sp1 out2 fuel1 l' s _ _ hfv' hl' hs h3 h4 h).of_run hrun
  rw [ite_eq_right c2] at h
  have ne2 : (absEIdx e).tag ≠ ETag.lit := by rw [htag]; exact tag_ne abs_lit c2
  by_cases c3 : t = arena.handle.ETAG_BVAR
  · rw [ite_eq_left c3] at h
    rw [go_skip ne1 ne2 (by simp [htag, c3, abs_bvar])]
    exact consts_go_loop_eq hrel f' w sp1 _ fuel1 l' s _ _ hfv' hl' hs hn ho h
  rw [ite_eq_right c3] at h
  have ne3 : (absEIdx e).tag ≠ ETag.bvar := by rw [htag]; exact tag_ne abs_bvar c3
  by_cases c4 : t = arena.handle.ETAG_SORT
  · rw [ite_eq_left c4] at h
    rw [go_skip ne1 ne2 (by simp [htag, c4, abs_sort])]
    exact consts_go_loop_eq hrel f' w sp1 _ fuel1 l' s _ _ hfv' hl' hs hn ho h
  rw [ite_eq_right c4] at h
  have ne4 : (absEIdx e).tag ≠ ETag.sort := by rw [htag]; exact tag_ne abs_sort c4
  peel h as b, hb
  have eb := SetRel.contains_key eidx_eq2 hs hb
  by_cases cb : b = true
  · rw [ite_eq_left cb] at h
    rw [go_skip ne1 ne2 (by simp [← eb, cb])]
    exact consts_go_loop_eq hrel f' w sp1 _ fuel1 l' s _ _ hfv' hl' hs hn ho h
  rw [ite_eq_right cb] at h
  have h3 : ¬ ((absEIdx e).tag == ETag.bvar || (absEIdx e).tag == ETag.sort || s.contains (absEIdx e)) = true := by
    simp [ne3, ne4, ← eb, cb]
  peel h as e2, he2
  cases eidx_dup2_ok he2
  peel h as p, hp
  obtain ⟨_, hm⟩ := p
  have ins := SetRel.insert eidx_eq2 absEIdx_inj hs hp
  peel h as p2, hp2
  obtain ⟨r2, v⟩ := p2
  by_cases cp : ETag.proj < ConRon.Refine2.absU32 t
  · cases consts_children_past cp hp2
    rw [go_past ne1 ne2 h3 (by rw [htag]; exact cp)]
    exact consts_go_loop_eq hrel f' { w with stack := w.stack, seen := hm } sp1 _ fuel1 l' _ _ _ hfv' hl' ins hn ho h
  have hany : t = arena.handle.ETAG_APP ∨ t = arena.handle.ETAG_LAM ∨ t = arena.handle.ETAG_FORALL_E ∨
      t = arena.handle.ETAG_LET_E ∨ t = arena.handle.ETAG_PROJ ∨ t = arena.handle.ETAG_FVAR := by
    have hv : ¬ 9 < t.val := by
      intro hg
      apply cp
      show ETag.proj.toNat < (ConRon.Refine2.absU32 t).toNat
      rw [ConRon.Refine2.absU32_toNat]; exact hg
    have v : ∀ {x : Std.U32} {k : Nat}, x.val = k → t.val = k → t = x := fun hx ht =>
      UScalar.eq_of_val_eq (ht.trans hx.symm)
    have hc1 : ¬ t.val = 3 := fun he => c1 (v (by unfold arena.handle.ETAG_CONST; rfl) he)
    have hc2 : ¬ t.val = 8 := fun he => c2 (v (by unfold arena.handle.ETAG_LIT; rfl) he)
    have hc3 : ¬ t.val = 0 := fun he => c3 (v (by unfold arena.handle.ETAG_BVAR; rfl) he)
    have hc4 : ¬ t.val = 2 := fun he => c4 (v (by unfold arena.handle.ETAG_SORT; rfl) he)
    have : t.val = 4 ∨ t.val = 5 ∨ t.val = 6 ∨ t.val = 7 ∨ t.val = 9 ∨ t.val = 1 := by omega
    rcases this with he | he | he | he | he | he
    · exact .inl (v (by unfold arena.handle.ETAG_APP; rfl) he)
    · exact .inr (.inl (v (by unfold arena.handle.ETAG_LAM; rfl) he))
    · exact .inr (.inr (.inl (v (by unfold arena.handle.ETAG_FORALL_E; rfl) he)))
    · exact .inr (.inr (.inr (.inl (v (by unfold arena.handle.ETAG_LET_E; rfl) he))))
    · exact .inr (.inr (.inr (.inr (.inl (v (by unfold arena.handle.ETAG_PROJ; rfl) he)))))
    · exact .inr (.inr (.inr (.inr (.inr (v (by unfold arena.handle.ETAG_FVAR; rfl) he)))))
  have hC := consts_children_eq hstore hl' htag hp2 hany
  have hrun := go_comp_run (pk := absPins pk) (f := f') (rest := l') (s := s) (sn := sn) (o := o') lst
    ne1 ne2 h3 (by rw [htag]; exact cp)
  cases r2 with
  | Err x =>
    obtain ⟨hk, hV⟩ := hC
    cases Result.ok_injective h
    show AErrSim x _
    rw [hrun, hV]
    exact internal_sim hk
  | Ok s1 =>
    obtain ⟨ks, hV, hs1⟩ := hC
    rw [hV] at hrun
    exact (consts_go_loop_eq hrel f' { w with stack := v, seen := hm } s1 _ fuel1 _ _ _ _ hfv' hs1 ins hn ho h).of_run hrun
termination_by f
decreasing_by all_goals omega

/-- **`consts_go` is `constsGo`.** -/
theorem consts_go_eq {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} (hrel : AStateRel₀ pers st lst)
    {w : ConstsWork} {sp : Std.Usize} {out : alloc.vec.Vec arena.handle.NIdx}
    {l : List EIdx} {s : _root_.Std.HashSet EIdx} {sn : _root_.Std.HashSet NIdx} {o' : _root_.Array NIdx}
    (hl : StackRel absEIdx w.stack sp l) (hs : ESet w.seen s) (hn : NSet w.seen_n sn)
    (ho : OutA out o') {r w'} (h : consts_go pk pers st.store w sp out = ok (r, w')) :
    WOut OutA (constsGo (absPins pk) ConLeche.Frontend.Olean.closureFuel l s sn o') lst r w' := by
  rw [consts_go] at h
  peel h as fuel, hfuel
  exact consts_go_loop_eq hrel _ w sp out fuel l s sn o' (closure_fuel_val hfuel) hl hs hn ho h

/-- `es`, the last first, onto a stack: `es.head` on top. -/
theorem consts_of_loop_eq (v es : alloc.vec.Vec arena.handle.EIdx) (sp i : Std.Usize) {l : List EIdx} {o}
    (hl : StackRel absEIdx v sp l) (h : consts_of_loop v es sp i = ok o) :
    StackRel absEIdx o.1 o.2 ((es.val.take i.val).map absEIdx ++ l) := by
  rw [consts_of_loop] at h
  by_cases hp : i > 0#usize
  · rw [ite_eq_left hp] at h
    peel h as i1, hi1
    have hv := ConRon.Refine.HashMap.uscalar_sub_eq hi1
    have l1 : (1#usize : Std.Usize).val = 1 := by decide
    rw [l1] at hv
    have hp' : (0#usize : Std.Usize).val < i.val := hp
    have l0 : (0#usize : Std.Usize).val = 0 := by decide
    rw [l0] at hp'
    peel h as e, he
    obtain ⟨hb, rfl⟩ := vec_index_eq he
    peel h as e1, he1
    cases eidx_dup2_ok he1
    peel h as q, hq
    obtain ⟨sp1, v1⟩ := q
    have e : i.val = i1.val + 1 := by omega
    have := consts_of_loop_eq v1 es sp1 i1 (stack_push_eq hl hq) h
    rw [e, List.take_succ_eq_append_getElem hb, List.map_append, List.append_assoc]
    exact this
  · rw [ite_eq_right hp] at h
    cases Result.ok_injective h
    have : ¬ (0#usize : Std.Usize).val < i.val := hp
    have e : i.val = 0 := by simpa using this
    rw [e]
    simpa using hl
termination_by i.val
decreasing_by omega

theorem eidx_new_eset {m : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {n : Nat}
    (hinv : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable m) (hnone : ∀ k, toFun m k = none) :
    ESet m (_root_.Std.HashSet.emptyWithCapacity n) :=
  ⟨hinv, fun k => by rw [hnone]; simp⟩

theorem nidx_new_nset {m : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {n : Nat}
    (hinv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable m) (hnone : ∀ k, toFun m k = none) :
    NSet m (_root_.Std.HashSet.emptyWithCapacity n) :=
  ⟨hinv, fun k => by rw [hnone]; simp⟩

/-- **`consts_of` is `constsOf`**, both sets emptied by their `clear`. -/
theorem consts_of_eq {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} (hrel : AStateRel₀ pers st lst)
    {w : ConstsWork} {es : alloc.vec.Vec arena.handle.EIdx} (hw : WorkInv w) {r w'}
    (h : consts_of pk pers st.store w es = ok (r, w')) :
    WOut OutA (constsOf (absPins pk) (es.val.map absEIdx)) lst r w' := by
  rw [consts_of] at h
  peel h as hm, hhm
  peel h as hm1, hhm1
  peel h as q, hq
  obtain ⟨v, sp⟩ := q
  obtain ⟨i1, -, i2⟩ := ConRon.Refine.HashMap2.clear_refines hw.seen hhm
  obtain ⟨i3, -, i4⟩ := ConRon.Refine.HashMap2.clear_refines hw.seenN hhm1
  have hS := consts_of_loop_eq _ es _ _ (StackRel.empty absEIdx w.stack) hq
  rw [show (alloc.vec.Vec.len es).val = es.val.length from vec_len_val es, List.take_length, List.append_nil] at hS
  exact consts_go_eq hrel hS (eidx_new_eset i1 i2) (nidx_new_nset i3 i4) (by simp [OutA, alloc.vec.Vec.new]) h

/-! ## A constant's dependencies -/

abbrev RuleR := RuleRel (N := arena.handle.NIdx) absNIdx (E := arena.handle.EIdx) absEIdx ValRel

theorem c_entry_deps_loop_eq (out : alloc.vec.Vec arena.handle.EIdx)
    (rules : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)) (i : Std.Usize)
    {L : List (NIdx × Nat × EIdx)} (hr : List.Forall₂ RuleR (rules.val.drop i.val) L) {o}
    (h : c_entry_deps_loop out rules i = ok o) :
    o.val.map absEIdx = out.val.map absEIdx ++ L.map (·.2.2) := by
  rw [c_entry_deps_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len rules
  · rw [ite_eq_left hlt] at h
    peel h as t, ht
    obtain ⟨hi, rfl⟩ := vec_index_eq ht
    rw [List.drop_eq_getElem_cons hi] at hr
    cases hr with
    | cons hab hrest =>
      peel h as e1, he1
      cases eidx_dup2_ok he1
      peel h as out1, ho1
      peel h as i2, hi2
      have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
      rw [← hi2v] at hrest
      have := c_entry_deps_loop_eq out1 rules i2 hrest h
      rw [this, ConRon.Refine.vec_push_val ho1]
      simp [hab.2.2]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hle : rules.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len rules).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le hle] at hr
    cases hr
    simp
termination_by rules.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len rules).val := hlt
  rw [vec_len_val] at this
  omega

/-- **`c_entry_deps` is `entryDeps`.** -/
theorem c_entry_deps_eq {c : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    {c' : ConLeche.Frontend.Olean.CEntryF NIdx EIdx} (hc : EntryRel absNIdx absEIdx ValRel c c') {o}
    (h : c_entry_deps c = ok o) : o.val.map absEIdx = entryDeps c' := by
  rw [c_entry_deps] at h
  peel h as e, he
  cases eidx_dup2_ok he
  peel h as out, ho
  have ev := ConRon.Refine.vec_push_val ho
  have ev' : out.val.map absEIdx = [c'.type] := by
    rw [ev]; simp [alloc.vec.Vec.new, hc.type]
  have hk := hc.kind
  obtain ⟨n', l', ty', k'⟩ := c'
  rw [entryDeps]
  cases hck : c.kind <;> cases k' <;> rw [hck] at hk h <;> try exact hk.elim
  case Ax.ax => cases Result.ok_injective h; exact ev'
  case Quot.quot => cases Result.ok_injective h; exact ev'
  case Induct.induct => cases Result.ok_injective h; exact ev'
  case Ctor.ctor => cases Result.ok_injective h; exact ev'
  case Defn.defn =>
    peel h as e1, he1
    cases eidx_dup2_ok he1
    rw [ConRon.Refine.vec_push_val h, List.map_append, ev']
    simp only [List.map_cons, List.map_nil]
    rw [hk.1]; rfl
  case Thm.thm =>
    peel h as e1, he1
    cases eidx_dup2_ok he1
    rw [ConRon.Refine.vec_push_val h, List.map_append, ev']
    simp only [List.map_cons, List.map_nil]
    rw [hk.1]; rfl
  case Opaq.opaq =>
    peel h as e1, he1
    cases eidx_dup2_ok he1
    rw [ConRon.Refine.vec_push_val h, List.map_append, ev']
    simp only [List.map_cons, List.map_nil]
    rw [hk.1]; rfl
  case Recur.recur =>
    have := c_entry_deps_loop_eq out _ _ (by simpa using hk.2.2.2.2.2.1) h
    rw [this, ev']; rfl

/-- **`c_entry_of_read` is `CEntry.ofRead`.** -/
theorem c_entry_of_read_eq {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} (hrel : AStateRel₀ pers st lst)
    {w : ConstsWork} (hw : WorkInv w)
    {c : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    {c' : ConLeche.Frontend.Olean.CEntryF NIdx EIdx} (hc : EntryRel absNIdx absEIdx ValRel c c') {r w'}
    (h : c_entry_of_read pk pers st.store w c = ok (r, w')) :
    WOut CEntryRel (Arena.Frontend.Olean.CEntry.ofRead (absPins pk) c') lst r w' := by
  rw [c_entry_of_read] at h
  peel h as es, hes
  peel h as q, hq
  obtain ⟨r1, w1⟩ := q
  have hO := consts_of_eq hrel hw hq
  rw [c_entry_deps_eq hc hes] at hO
  have e : ∀ l1, (Arena.Frontend.Olean.CEntry.ofRead (absPins pk) c').run l1 =
      ((constsOf (absPins pk) (entryDeps c') >>= fun u => pure { c := c', uses := u }) : AM _).run l1 :=
    fun _ => rfl
  cases r1 with
  | Ok uses =>
    obtain ⟨u', hu, hr, hw1⟩ := hO
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    refine ⟨{ c := c', uses := u' }, ?_, ⟨hc, hr⟩, hw1⟩
    rw [e, am_bind_ok hu]
    rfl
  | Err x =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    show AErrSim x _
    rw [e, StateT.run_bind]
    exact AErrSim.bind hO _

/-- The loop of `entries_of_read`. -/
theorem entries_of_read_loop_eq {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} (hrel : AStateRel₀ pers st lst)
    (w : ConstsWork) (cs : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx))
    (out : alloc.vec.Vec CEntry) (i : Std.Usize)
    {L : List (ConLeche.Frontend.Olean.CEntryF NIdx EIdx)} (hw : WorkInv w)
    (hr : List.Forall₂ (EntryRel absNIdx absEIdx ValRel) (cs.val.drop i.val) L)
    {acc : List Arena.Frontend.Olean.CEntry} (ho : List.Forall₂ CEntryRel out.val acc) {r w'}
    (h : entries_of_read_loop pk pers st.store w cs out i = ok (r, w')) :
    WOut (fun (o : alloc.vec.Vec CEntry) (ys : List Arena.Frontend.Olean.CEntry) =>
        List.Forall₂ CEntryRel o.val (acc ++ ys))
      (L.mapM (Arena.Frontend.Olean.CEntry.ofRead (absPins pk))) lst r w' := by
  rw [entries_of_read_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    peel h as q, hq
    obtain ⟨cf, back⟩ := q
    have hi : i.val < cs.val.length := by
      have : i.val < (alloc.vec.Vec.len cs).val := hlt
      rwa [vec_len_val] at this
    have : Inhabited (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx) := ⟨cs.val[i.val]⟩
    obtain ⟨-, hcf, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hq
    have hcf' : cf = cs.val[i.val] := by rw [hcf]; simp [hi]
    subst hcf'
    rw [List.drop_eq_getElem_cons hi] at hr
    cases hr with
    | @cons _ y _ L' hab hrest =>
      peel h as n, -
      peel h as e, -
      dsimp only at h
      peel h as p, hp
      obtain ⟨r1, w1⟩ := p
      have hE := c_entry_of_read_eq hrel hw hab hp
      rw [List.mapM_cons]
      cases r1 with
      | Err x =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
        show AErrSim x _
        rw [StateT.run_bind]
        exact AErrSim.bind hE _
      | Ok a =>
        obtain ⟨b, hb, hR, hw1⟩ := hE
        peel h as out1, ho1
        peel h as i2, hi2
        have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
        have hd : ∀ x, ((cs.set i x).val).drop i2.val = cs.val.drop (i.val + 1) := by
          intro x
          rw [hi2v]
          simp [alloc.vec.Vec.set, List.drop_set]
        have ho' : List.Forall₂ CEntryRel out1.val (acc ++ [b]) := by
          rw [ConRon.Refine.vec_push_val ho1]
          exact List.rel_append ho (.cons hR .nil)
        have ih := entries_of_read_loop_eq hrel w1 _ out1 i2 hw1 (by rw [hd]; exact hrest) ho' h
        have e2 : ((Arena.Frontend.Olean.CEntry.ofRead (absPins pk) y >>= fun a =>
            L'.mapM (Arena.Frontend.Olean.CEntry.ofRead (absPins pk)) >>= fun t => pure (a :: t)) : AM _).run lst =
            ((L'.mapM (Arena.Frontend.Olean.CEntry.ofRead (absPins pk)) >>= fun t => pure (b :: t)) : AM _).run lst :=
          am_bind_ok hb
        refine WOut.of_run ?_ e2
        cases r with
        | Err x =>
          show AErrSim x _
          rw [StateT.run_bind]
          exact AErrSim.bind ih _
        | Ok o =>
          obtain ⟨ys, hys, hF, hwz⟩ := ih
          refine ⟨b :: ys, ?_, ?_, hwz⟩
          · rw [am_bind_ok hys]; rfl
          · simpa using hF
  · rw [ite_eq_right hlt] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    have hle : cs.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len cs).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le hle] at hr
    cases hr
    exact ⟨[], rfl, by simpa using ho, hw⟩
termination_by cs.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len cs).val := hlt
  rw [vec_len_val] at this
  simp only [alloc.vec.Vec.set] at *
  simp [hi2v] at *
  omega

/-- **`entries_of_read` is `d.constants.mapM CEntry.ofRead`**, the constants as a list. -/
theorem entries_of_read_eq {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} (hrel : AStateRel₀ pers st lst)
    {w : ConstsWork} {d : frontend.olean.spec.ModDecoded}
    {L : List (ConLeche.Frontend.Olean.CEntryF NIdx EIdx)} (hw : WorkInv w)
    (hr : List.Forall₂ (EntryRel absNIdx absEIdx ValRel) d.constants.val L) {r w'}
    (h : entries_of_read pk pers st.store w d = ok (r, w')) :
    WOut (fun (o : alloc.vec.Vec CEntry) (ys : List Arena.Frontend.Olean.CEntry) =>
        List.Forall₂ CEntryRel o.val ys)
      (L.mapM (Arena.Frontend.Olean.CEntry.ofRead (absPins pk))) lst r w' := by
  rw [entries_of_read] at h
  have := entries_of_read_loop_eq hrel w d.constants _ _ (acc := []) hw (by simpa using hr) (.nil) h
  simpa using this

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

end views

end ConRon.Refine2.Frontend.Olean
