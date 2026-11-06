/-
# `ConRon.Refine2.Frontend.Olean.Merge` — `olean/merge.rs` against `Arena/Frontend/Olean/Merge.lean`

**Task #142, Theorem 2.**  A stored constant (`CEntryRel`), a loaded module (`LoadedRel`),
the merge (`MergedRel`: the map's positions by `RelOn`, with the table's `Inv`).

The merge reads the store and does not change it, and neither does the twin's: `CR` is the
judgement of such a read, with the state relation a premise so that a bind threads it, and
`CRM` the same with the merge threaded beside it.  A Rust index out of range is a Rust
`fail` and no obligation, which is why `mg_get` answers the twin's `Merged.get`.
-/
import ConRon.Refine2.Frontend.Olean.Skel

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.merge (mg_get mg_has is_prop_body is_prop_body_loop is_prop_head
  is_prop_head_loop is_prop_drop is_prop_drop_loop is_prop_tail is_prop_cheap subsumes
  merge_conflict merge_entry merge_module merge_module_loop merge_all merge_all_loop)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap2 (Inv RelOn toFun)
open ConRon.Arena.Frontend.Olean (isPropBody isPropHead isPropDrop isPropCheap)

/-! ## The relations -/

/-- A recursor's rule, handles against the twin's. -/
abbrev RuleR := RuleRel (N := arena.handle.NIdx) absNIdx (E := arena.handle.EIdx) absEIdx ValRel

/-- **`lazy::CEntry` against the twin's.** -/
def CEntryRel (c : frontend.olean.lazy.CEntry) (c' : Arena.Frontend.Olean.CEntry) : Prop :=
  EntryRel absNIdx absEIdx ValRel c.c c'.c ∧ c.uses.val.map absNIdx = c'.uses.toList

/-- **`sparse::Table` against upstream's `Table`**: the same keys, ascending, and
the values abstracted. -/
structure TableRel {T α : Type} (A : T → α) (t : frontend.olean.sparse.Table T)
    (t' : ConLeche.Frontend.Olean.Table α) : Prop where
  keys : t.keys.val.map (·.val) = t'.keys.toList
  vals : t.vals.val.map A = t'.vals.toList

/-- **`sparse::Frontier` against the twin's**: the four tables. -/
structure FrontierRel (b : frontend.olean.sparse.Frontier) (b' : Arena.Frontend.Olean.Frontier) :
    Prop where
  names : TableRel absNIdx b.names b'.names
  levels : TableRel absLIdx b.levels b'.levels
  lists : TableRel absLsIdx b.lists b'.lists
  exprs : TableRel absEIdx b.exprs b'.exprs

/-- `table_empty` is upstream's empty table. -/
theorem table_empty_rel {T α : Type} {A : T → α} {t}
    (h : frontend.olean.sparse.table_empty T = ok t) : TableRel A t {} := by
  rw [frontend.olean.sparse.table_empty] at h
  cases Result.ok_injective h
  exact ⟨by simp [show (alloc.vec.Vec.new Std.U64).val = [] from Slice.from_val _ _],
    by simp [show (alloc.vec.Vec.new T).val = [] from Slice.from_val _ _]⟩

/-- `frontier_empty` is the twin's empty frontier. -/
theorem frontier_empty_rel {b} (h : frontend.olean.sparse.frontier_empty = ok b) : FrontierRel b {} := by
  rw [frontend.olean.sparse.frontier_empty] at h
  peel h as t, ht
  peel h as t1, ht1
  peel h as t2, ht2
  peel h as t3, ht3
  cases Result.ok_injective h
  exact ⟨table_empty_rel ht, table_empty_rel ht1, table_empty_rel ht2, table_empty_rel ht3⟩

/-- `lazy::Loaded` against the twin's. -/
structure LoadedRel (l : frontend.olean.lazy.Loaded) (l' : Arena.Frontend.Olean.Loaded) :
    Prop where
  «name» : absNIdx l.name = l'.name
  constants : List.Forall₂ CEntryRel l.constants.val l'.constants.toList
  frontier : FrontierRel l.frontier l'.frontier

/-- A position in the merge. -/
@[reducible] def absMgPos (p : Std.Usize × Std.Usize) : Nat × Nat := (p.1.val, p.2.val)

/-- **`merge::Merged` against the twin's.** -/
structure MergedRel (mg : frontend.olean.merge.Merged) (mg' : Arena.Frontend.Olean.Merged) :
    Prop where
  ls : List.Forall₂ LoadedRel mg.ls.val mg'.ls.toList
  map : RelOn anyN mg.map mg'.map absNIdx absMgPos
  inv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable mg.map
  order : mg.order.val.map absNIdx = mg'.order.toList

/-! ## The merge's reads, without a store -/

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {i : Nat} {x : α} (hi : l[i]? = some x) :
    ∃ y, l'[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hab _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using hi)

/-- **`mg_get` is `Merged.get`**: the map's answer, and the Rust's index in range. -/
theorem mg_get_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {n : arena.handle.NIdx} {o : Option frontend.olean.lazy.CEntry}
    (h : mg_get mg n = ok o) : Option.Rel CEntryRel o (mg'.get (absNIdx n)) := by
  rw [mg_get] at h
  peel h as o1, h1
  have hk := hm.map n trivial
  rw [← nidx_get hm.inv h1] at hk
  rw [Arena.Frontend.Olean.Merged.get, ← hk]
  cases o1 with
  | none => cases Result.ok_injective h; exact .none
  | some p =>
    obtain ⟨i, j⟩ := p
    dsimp only at h
    peel h as l, hl
    peel h as c, hc
    cases Result.ok_injective h
    obtain ⟨l', hl', hlr⟩ := forall₂_getElem? hm.ls (ConRon.Refine.ExprOps.vec_index_getElem? hl)
    obtain ⟨c', hc', hcr⟩ := forall₂_getElem? (LoadedRel.constants hlr)
      (ConRon.Refine.ExprOps.vec_index_getElem? hc)
    have e1 : mg'.ls[i.val]? = some l' := by simpa using hl'
    have e2 : l'.constants[j.val]? = some c' := by simpa using hc'
    simp only [Option.map, absMgPos, e1, Option.bind_some, e2]
    exact .some hcr

/-- `mg_has` is `mg.map.contains`. -/
theorem mg_has_eq {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {n : arena.handle.NIdx} {b : Bool} (h : mg_has mg n = ok b) :
    b = mg'.map.contains (absNIdx n) := by
  rw [mg_has] at h
  have h1 := ConRon.Refine.HashMap2.contains_key_refines_gen nidx_eq2 hm.inv (anyNKeysOk _) trivial h
  have hk := hm.map n trivial
  rw [h1, Std.HashMap.contains_eq_isSome_getElem?, ← hk]
  cases toFun mg.map n <;> rfl

/-! ## `CR`: a read of the store with `CheckError` -/

/-- **The lockstep judgement of a read of the store**: the Rust's `m` over `st.store`, and
the twin's `x`, which leaves a related state. -/
def CR {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result α kernel.core_types.CheckError)) (x : AM β) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ o, m = ok o →
      match o with
      | .Ok a => ∃ b lst', x.run lst = .ok (b, lst') ∧ R a b ∧
          AStateRel₀ pers st lst' ∧ AStateInv pers st
      | .Err e => AErrSim e (x.run lst)

/-- The Rust `Ok` against the twin's `pure`. -/
theorem CR.pure {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {a : α} {b : β} (hR : R a b) :
    CR pers R st lst (ok (.Ok a)) (Pure.pure b) := by
  intro hrel hinv o h
  cases Result.ok_injective h
  exact ⟨b, lst, rfl, hR, hrel, hinv⟩

/-- A step of the Rust alone. -/
theorem CR.pure_step {α β γ : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError)}
    {x : AM β} (h : ∀ a, f = ok a → CR pers R st lst (k a) x) :
    CR pers R st lst (Std.bind f k) x := by
  intro hrel hinv o hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 hrel hinv o h2

/-- **The bind of two reads.** -/
theorem CR.bind {α₁ β₁ α β : Type} {pers : arena.store.PersTier} {R₁ : α₁ → β₁ → Prop}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result α₁ kernel.core_types.CheckError)}
    {k : core.result.Result α₁ kernel.core_types.CheckError →
      Result (core.result.Result α kernel.core_types.CheckError)}
    {x : AM β₁} {g : β₁ → AM β}
    (hf : CR pers R₁ st lst f x)
    (he : ∀ e, k (.Err e) = ok (.Err e))
    (hk : ∀ a b lst1, R₁ a b → CR pers R st lst1 (k (.Ok a)) (g b)) :
    CR pers R st lst (Std.bind f k) (x >>= g) := by
  intro hrel hinv o hm
  obtain ⟨r, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf hrel hinv r hf1
  cases r with
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := h1
    rw [am_bind_ok hx]
    exact hk a b lst1 hR hrel1 hinv1 o hk1
  | Err e =>
    rw [he e] at hk1
    cases Result.ok_injective hk1
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind h1 _

/-- `Arena.view`'s run, on a store that has the node or does not. -/
theorem view_run_some {lst : AState} {e : EIdx} {v : ENodeView} (h : lst.store.view e = some v) :
    (Arena.view e).run lst = .ok (v, lst) := by
  show ((match lst.store.view e with
          | some v => (Pure.pure v : AM ENodeView)
          | none => Arena.fail (.internal "arena: dangling expression handle")).run lst) = _
  rw [h]; rfl

theorem view_run_none {lst : AState} {e : EIdx} (h : lst.store.view e = none) :
    (Arena.view e).run lst = .error (.internal "arena: dangling expression handle") := by
  show ((match lst.store.view e with
          | some v => (Pure.pure v : AM ENodeView)
          | none => Arena.fail (.internal "arena: dangling expression handle")).run lst) = _
  rw [h]; rfl

/-- **`EStore::view` and the Rust's dangling arm**, against the twin's `view`. -/
theorem CR.view {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {e : arena.handle.EIdx}
    {k : Option arena.store.ENodeView → Result (core.result.Result α kernel.core_types.CheckError)}
    {g : ENodeView → AM β}
    (hn : k none = arena.monad.fail_dangling_e α)
    (hs : ∀ v, CR pers R st lst (k (some v)) (g (absENodeView v))) :
    CR pers R st lst (Std.bind (arena.store.EStore.view st.store pers e) k)
      (Arena.view (absEIdx e) >>= g) := by
  intro hrel hinv o hm
  obtain ⟨q, hq, hk⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hv := estore_view_abs hrel.store hq
  cases q with
  | none =>
    rw [hn] at hk
    obtain ⟨w, rfl⟩ := Lockstep.fail_dangling_e_spec α o hk
    show AErrSim _ _
    rw [StateT.run_bind, view_run_none hv]
    intro k' hk'
    cases hk'
    exact ⟨_, rfl, rfl⟩
  | some v =>
    rw [am_bind_ok (view_run_some hv)]
    exact hs v hrel hinv o hk


/-! ## The telescope walks -/

/-- `CLOSURE_FUEL` is `closureFuel`. -/
theorem closure_fuel_val {x : Std.U64} (h : frontend.olean.closure.CLOSURE_FUEL = ok x) :
    x.val = ConLeche.Frontend.Olean.closureFuel := by
  rw [frontend.olean.closure.CLOSURE_FUEL] at h
  have := (ConRon.Refine.Nat.ushiftLeftI_val h).2
  rw [this]; decide

theorem fuel_pred {f f1 : Std.U64} (h : f - 1#u64 = ok f1) : f1.val = f.val - 1 := by
  have he := UScalar.sub_equiv f 1#u64
  rw [h] at he
  simp only [Result.match.ok] at he
  have := he.2.1
  have h1 : (1#u64).val = 1 := rfl
  omega

theorem is_prop_body_cr {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (n : Nat) : ∀ (e : arena.handle.EIdx) (fuel : Std.U64), fuel.val = n →
      CR pers (EqA absEIdx) st lst (is_prop_body_loop pers st.store e fuel)
        (isPropBody n (absEIdx e)) := by
  induction n with
  | zero =>
    intro e fuel hf
    rw [is_prop_body_loop, ite_eq_right_iff.mpr (fun hc => absurd hc (by scalar_tac))]
    exact CR.pure rfl
  | succ n ih =>
    intro e fuel hf
    rw [is_prop_body_loop, ite_eq_left (by scalar_tac), isPropBody]
    refine CR.pure_step fun fuel1 h1 => ?_
    refine CR.view rfl fun v => ?_
    cases v <;> first
      | exact ih _ fuel1 (by rw [fuel_pred h1, hf]; rfl)
      | exact CR.pure rfl

theorem is_prop_body_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (ty : arena.handle.EIdx) :
    CR pers (EqA absEIdx) st lst (is_prop_body pers st.store ty)
      (isPropBody ConLeche.Frontend.Olean.closureFuel (absEIdx ty)) := by
  rw [is_prop_body]
  refine CR.pure_step fun e he => CR.pure_step fun fuel hf => ?_
  rw [eidx_dup2_ok he]
  exact is_prop_body_cr _ _ _ (closure_fuel_val hf)

/-- `is_prop_head`'s answer. -/
@[reducible] def absHead (p : Option (arena.handle.NIdx × Std.U64)) : Option (NIdx × Nat) :=
  p.map fun q => (absNIdx q.1, q.2.val)

theorem is_prop_head_cr {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (n : Nat) : ∀ (e : arena.handle.EIdx) (k fuel : Std.U64), fuel.val = n →
      CR pers (EqA absHead) st lst (is_prop_head_loop pers st.store e k fuel)
        (isPropHead n (absEIdx e) k.val) := by
  induction n with
  | zero =>
    intro e k fuel hf
    rw [is_prop_head_loop, ite_eq_right_iff.mpr (fun hc => absurd hc (by scalar_tac))]
    exact CR.pure rfl
  | succ n ih =>
    intro e k fuel hf
    rw [is_prop_head_loop, ite_eq_left (by scalar_tac), isPropHead]
    refine CR.pure_step fun fuel1 h1 => ?_
    refine CR.view rfl fun v => ?_
    cases v with
    | App f a =>
      refine CR.pure_step fun k1 hk1 => ?_
      have hk := ConRon.Refine.Nat.uadd_val hk1
      have h1' : (1#u64).val = 1 := rfl
      rw [h1'] at hk
      show CR _ _ _ _ _ (isPropHead n (absEIdx f) (k.val + 1))
      rw [← hk]
      exact ih _ _ fuel1 (by rw [fuel_pred h1, hf]; rfl)
    | _ => exact CR.pure rfl

theorem is_prop_head_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (e : arena.handle.EIdx) :
    CR pers (EqA absHead) st lst (is_prop_head pers st.store e)
      (isPropHead ConLeche.Frontend.Olean.closureFuel (absEIdx e) 0) := by
  rw [is_prop_head]
  refine CR.pure_step fun x hx => CR.pure_step fun fuel hf => ?_
  rw [eidx_dup2_ok hx]
  exact is_prop_head_cr _ _ 0#u64 _ (closure_fuel_val hf)

theorem is_prop_drop_cr {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (n : Nat) : ∀ (e : arena.handle.EIdx) (k : Std.U64), k.val = n →
      CR pers (EqA (Option.map absEIdx)) st lst (is_prop_drop_loop pers st.store e k)
        (isPropDrop n (absEIdx e)) := by
  induction n with
  | zero =>
    intro e k hf
    rw [is_prop_drop_loop, ite_eq_right_iff.mpr (fun hc => absurd hc (by scalar_tac))]
    exact CR.pure rfl
  | succ n ih =>
    intro e k hf
    rw [is_prop_drop_loop, ite_eq_left (by scalar_tac), isPropDrop]
    refine CR.pure_step fun k1 h1 => ?_
    refine CR.view rfl fun v => ?_
    cases v <;> first
      | exact ih _ k1 (by rw [fuel_pred h1, hf]; rfl)
      | exact CR.pure rfl

theorem is_prop_drop_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (e : arena.handle.EIdx) (k : Std.U64) :
    CR pers (EqA (Option.map absEIdx)) st lst (is_prop_drop pers st.store e k)
      (isPropDrop k.val (absEIdx e)) := by
  rw [is_prop_drop]
  refine CR.pure_step fun x hx => ?_
  rw [eidx_dup2_ok hx]
  exact is_prop_drop_cr _ _ _ rfl

theorem lidx_eq2_beq {a b : arena.handle.LIdx} {o : Bool}
    (h : arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absLIdx a == absLIdx b) := by
  rw [arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absLIdx a ≠ absLIdx b := fun hc => hab (absLIdx_inj hc)
    simp [h1, h2]

/-- The end of the twin's `isPropCheap`: `is_prop_tail`. -/
def isPropTail (pk : Arena.Frontend.Olean.OleanPins) (ty : EIdx) (k : Nat) : AM Bool := do
  match ← isPropDrop k ty with
  | none => pure false
  | some x =>
    match ← Arena.view x with
    | .sort u => pure (u == pk.zero)
    | _ => pure false

theorem is_prop_tail_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) (ty : arena.handle.EIdx) (k : Std.U64) :
    CR pers Eq st lst (is_prop_tail pk pers st.store ty k)
      (isPropTail (absPins pk) (absEIdx ty) k.val) := by
  rw [is_prop_tail, isPropTail]
  refine CR.bind (is_prop_drop_rel ty k) (fun _ => rfl) fun a b lst1 hab => ?_
  cases hab
  cases a with
  | none => exact CR.pure rfl
  | some x =>
    refine CR.view rfl fun v => ?_
    cases v with
    | «Sort» u =>
      refine CR.pure_step fun b hb => ?_
      rw [lidx_eq2_beq hb]
      exact CR.pure rfl
    | _ => exact CR.pure rfl

theorem is_prop_cheap_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) {mg : frontend.olean.merge.Merged}
    {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg') (ty : arena.handle.EIdx) :
    CR pers Eq st lst (is_prop_cheap pk pers st.store mg ty)
      (isPropCheap (absPins pk) mg' (absEIdx ty)) := by
  rw [is_prop_cheap, isPropCheap]
  refine CR.bind (is_prop_body_rel ty) (fun _ => rfl) fun b b' lst1 hb => ?_
  cases hb
  refine CR.bind (is_prop_head_rel b) (fun _ => rfl) fun o o' lst2 ho => ?_
  cases ho
  cases o with
  | none => exact CR.pure rfl
  | some p =>
    obtain ⟨n, k⟩ := p
    refine CR.pure_step fun o1 h1 => ?_
    have hr := mg_get_rel hm h1
    dsimp only [absHead, Option.map]
    cases hg : mg'.get (absNIdx n) with
    | none =>
      rw [hg] at hr
      cases hr
      exact CR.pure rfl
    | some d' =>
      rw [hg] at hr
      cases hr with
      | some hd =>
        have e : absEIdx _ = d'.c.type := hd.1.type
        dsimp only
        rw [← e]
        exact is_prop_tail_rel pk _ k

/-! ## `subsumes` -/

theorem nidx_list_eq_loop_val (a b : alloc.vec.Vec arena.handle.NIdx)
    (hlen : a.val.length = b.val.length) (k : Nat) :
    ∀ (i : Std.Usize) (o : Bool), a.val.length - i.val = k →
      frontend.olean.module.nidx_list_eq_loop a b i = ok o →
      o = ((a.val.drop i.val).map absNIdx == (b.val.drop i.val).map absNIdx) := by
  induction k with
  | zero =>
    intro i o hk h
    rw [frontend.olean.module.nidx_list_eq_loop, ite_eq_right_iff.mpr (fun hc => absurd hc (by scalar_tac))] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]; rfl
  | succ k ih =>
    intro i o hk h
    rw [frontend.olean.module.nidx_list_eq_loop, ite_eq_left (by scalar_tac)] at h
    peel h as x, hx
    peel h as y, hy
    peel h as b1, hb1
    obtain ⟨hl1, e1⟩ := List.getElem?_eq_some_iff.mp (ConRon.Refine.ExprOps.vec_index_getElem? hx)
    obtain ⟨hl2, e2⟩ := List.getElem?_eq_some_iff.mp (ConRon.Refine.ExprOps.vec_index_getElem? hy)
    rw [List.drop_eq_getElem_cons hl1, List.drop_eq_getElem_cons hl2, e1, e2]
    simp only [List.map_cons, List.cons_beq_cons]
    rw [← nidx_eq2_abs hb1]
    cases b1 with
    | false =>
      cases Result.ok_injective h
      rfl
    | true =>
      rw [ite_eq_left rfl] at h
      peel h as i2, hi2
      have hi := ConRon.Refine.Nat.uadd_val hi2
      have h1' : (1#usize).val = 1 := rfl
      rw [h1'] at hi
      rw [ih i2 o (by omega) h, hi]
      rfl

/-- **`nidx_list_eq` is `==` on the handles.** -/
theorem nidx_list_eq_abs {a b : alloc.vec.Vec arena.handle.NIdx} {o : Bool}
    (h : frontend.olean.module.nidx_list_eq a b = ok o) :
    o = (a.val.map absNIdx == b.val.map absNIdx) := by
  rw [frontend.olean.module.nidx_list_eq] at h
  by_cases hl : a.val.length = b.val.length
  · rw [ite_eq_right (by simpa [alloc.vec.Vec.len] using hl)] at h
    have := nidx_list_eq_loop_val a b hl _ 0#usize o rfl h
    simpa using this
  · rw [ite_eq_left (by simpa [alloc.vec.Vec.len] using hl)] at h
    cases Result.ok_injective h
    symm
    rw [beq_eq_false_iff_ne]
    intro hc
    exact hl (by simpa using congrArg List.length hc)

/-- **`subsumes` is the twin's.** -/
theorem subsumes_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) {mg : frontend.olean.merge.Merged}
    {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    {c1 c2 : frontend.olean.lazy.CEntry} {c1' c2' : Arena.Frontend.Olean.CEntry}
    (h1 : CEntryRel c1 c1') (h2 : CEntryRel c2 c2') :
    CR pers Eq st lst (subsumes pk pers st.store mg c1 c2)
      (Arena.Frontend.Olean.subsumes (absPins pk) mg' c1' c2') := by
  rw [subsumes, Arena.Frontend.Olean.subsumes]
  have hn := h2.1.«name»
  have hty := h1.1.type
  have hk1 := h1.1.kind
  have hk2 := h2.1.kind
  refine CR.pure_step fun b hb => ?_
  have e1 : (c1'.c.name == c2'.c.name) = b := by rw [nidx_eq2_abs hb, h1.1.«name», hn]
  rw [e1]
  cases b with
  | false => exact CR.pure rfl
  | true =>
    rw [ite_eq_left rfl]
    refine CR.pure_step fun b1 hb1 => ?_
    have e2 : (c1'.c.type == c2'.c.type) = b1 := by rw [eidx_eq2_abs hb1, hty, h2.1.type]
    rw [Bool.true_and, e2]
    cases b1 with
    | false => exact CR.pure rfl
    | true =>
      rw [ite_eq_left rfl]
      refine CR.pure_step fun b2 hb2 => ?_
      have e3 : (c1'.c.levelParams == c2'.c.levelParams) = b2 := by
        rw [nidx_list_eq_abs hb2]
        exact congrArg₂ _ h1.1.levelParams.symm h2.1.levelParams.symm
      rw [Bool.true_and, e3]
      cases b2 with
      | false => exact CR.pure rfl
      | true =>
        rw [ite_eq_left rfl, ite_eq_left rfl]
        rw [← hty, ← hn]
        generalize c1.c.kind = k1 at hk1 ⊢
        generalize c1'.c.kind = k1' at hk1 ⊢
        generalize c2.c.kind = k2 at hk2 ⊢
        generalize c2'.c.kind = k2' at hk2 ⊢
        cases k1 <;> cases k1' <;> try exact (hk1 : False).elim
        case Ax.ax u1 u1' =>
          cases k2 <;> cases k2' <;> try first | exact (hk2 : False).elim | exact CR.pure rfl
          case Ax.ax u2 u2' =>
            cases (hk1 : u1 = u1')
            cases (hk2 : u2 = u2')
            cases u1 <;> cases u2 <;> first
              | exact CR.pure rfl
              | exact is_prop_cheap_rel pk hm _
        case Thm.thm v a v' a' =>
          have ha : a.val.map absNIdx = a' := hk1.2
          cases k2 <;> cases k2' <;> try first | exact (hk2 : False).elim | exact CR.pure rfl
          case Ax.ax u2 u2' =>
            cases (hk2 : u2 = u2')
            subst ha
            dsimp only
            by_cases hl : a.val.length = 1
            · have hi : a.len = 1#usize := UScalar.eq_of_val_eq (by simpa [alloc.vec.Vec.len] using hl)
              obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
              rw [ite_eq_left hi]
              refine CR.pure_step fun n hn => CR.pure_step fun b3 hb3 => ?_
              have hnx := ConRon.Refine.ExprOps.vec_index_getElem? hn
              rw [hx] at hnx
              cases (by simpa using hnx : x = n)
              have e : (List.map absNIdx a.val == [absNIdx c2.c.name]) = b3 := by
                rw [nidx_eq2_abs hb3, hx]; simp
              rw [e]
              cases b3 <;> cases u2 <;> exact CR.pure rfl
            · rw [ite_eq_right (fun hi => hl (by
                have := congrArg UScalar.val hi
                simpa [alloc.vec.Vec.len] using this))]
              have e : (List.map absNIdx a.val == [absNIdx c2.c.name]) = false := by
                rw [beq_eq_false_iff_ne]
                intro hc
                exact hl (by simpa using congrArg List.length hc)
              rw [e]
              exact CR.pure rfl
          case Thm.thm w d w' d' =>
            have hd : d.val.map absNIdx = d' := hk2.2
            refine CR.pure_step fun b3 hb3 => ?_
            rw [nidx_list_eq_abs hb3, ha, hd]
            exact CR.pure rfl
        all_goals exact CR.pure rfl

/-! ## The conflict -/

theorem readName_run_some {lst : AState} {n : NIdx} {x : ConLeche.Name}
    (h : denoteN lst.store.ns n = some x) : (Arena.readName n).run lst = .ok (x, lst) := by
  show ((match denoteN lst.store.ns n with
          | some x => (Pure.pure x : AM ConLeche.Name)
          | none => Arena.fail (.internal "arena: dangling name handle")).run lst) = _
  rw [h]; rfl

theorem readName_run_none {lst : AState} {n : NIdx} (h : denoteN lst.store.ns n = none) :
    (Arena.readName n).run lst = .error (.internal "arena: dangling name handle") := by
  show ((match denoteN lst.store.ns n with
          | some x => (Pure.pure x : AM ConLeche.Name)
          | none => Arena.fail (.internal "arena: dangling name handle")).run lst) = _
  rw [h]; rfl

/-- **`merge_conflict` fails as the twin's message does**: the read's failure, or `invalid`. -/
theorem merge_conflict_err {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {β : Type} (msg : ConLeche.Name → String) (hrel : AStateRel₀ pers st lst)
    {n : arena.handle.NIdx} {o} (h : merge_conflict pers st.store n = ok o) :
    ∃ e, o = .Err e ∧
      AErrSim e ((Arena.readName (absNIdx n) >>= fun x =>
        (Arena.fail (.invalid (msg x)) : AM β)).run lst) := by
  rw [merge_conflict] at h
  peel h as r, hr
  have hR := env_read_name_abs hrel.store hr
  rw [StateT.run_bind]
  cases hd : denoteN lst.store.ns (absNIdx n) with
  | none =>
    rw [hd] at hR
    obtain ⟨e, rfl, hk⟩ := hR
    cases Result.ok_injective h
    rw [readName_run_none hd]
    refine ⟨e, rfl, fun k hk' => ?_⟩
    rw [hk] at hk'
    cases hk'
    exact ⟨_, rfl, rfl⟩
  | some x =>
    rw [hd] at hR
    obtain ⟨y, rfl, -⟩ := hR
    peel h as s, -
    peel h as v, -
    peel h as v1, -
    peel h as t, -
    peel h as ce, hce
    cases Result.ok_injective h
    rw [kernel.core_types.invalid] at hce
    cases Result.ok_injective hce
    rw [readName_run_some hd]
    refine ⟨_, rfl, fun k hk' => ?_⟩
    cases hk'
    exact ⟨_, rfl, rfl⟩

/-! ## `CRM`: a read of the store that threads the merge -/

/-- **The merge's step**: the twin's `Merged` is related, and holds the modules `ls'` still. -/
def CRM (pers : arena.store.PersTier) (ls' : Array Arena.Frontend.Olean.Loaded)
    (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result Unit kernel.core_types.CheckError × frontend.olean.merge.Merged))
    (x : AM Arena.Frontend.Olean.Merged) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ o mg2, m = ok (o, mg2) →
      match o with
      | .Ok _ => ∃ b lst', x.run lst = .ok (b, lst') ∧ MergedRel mg2 b ∧ b.ls = ls' ∧
          AStateRel₀ pers st lst' ∧ AStateInv pers st
      | .Err e => AErrSim e (x.run lst)

theorem CRM.pure {pers : arena.store.PersTier} {ls' : Array Arena.Frontend.Olean.Loaded}
    {st : arena.monad.AState} {lst : AState} {mg2 : frontend.olean.merge.Merged}
    {b : Arena.Frontend.Olean.Merged} (hR : MergedRel mg2 b) (hb : b.ls = ls') :
    CRM pers ls' st lst (ok (.Ok (), mg2)) (Pure.pure b) := by
  intro hrel hinv o mg3 h
  cases Result.ok_injective h
  exact ⟨b, lst, rfl, hR, hb, hrel, hinv⟩

theorem CRM.pure_step {γ : Type} {pers : arena.store.PersTier}
    {ls' : Array Arena.Frontend.Olean.Loaded}
    {st : arena.monad.AState} {lst : AState} {f : Result γ}
    {k : γ → Result (core.result.Result Unit kernel.core_types.CheckError × frontend.olean.merge.Merged)}
    {x : AM Arena.Frontend.Olean.Merged} (h : ∀ a, f = ok a → CRM pers ls' st lst (k a) x) :
    CRM pers ls' st lst (Std.bind f k) x := by
  intro hrel hinv o mg2 hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 hrel hinv o mg2 h2

/-- A read, then a step. -/
theorem CRM.bind_cr {α β : Type} {pers : arena.store.PersTier}
    {ls' : Array Arena.Frontend.Olean.Loaded} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result α kernel.core_types.CheckError)}
    {k : core.result.Result α kernel.core_types.CheckError →
      Result (core.result.Result Unit kernel.core_types.CheckError × frontend.olean.merge.Merged)}
    {x : AM β} {g : β → AM Arena.Frontend.Olean.Merged}
    (hf : CR pers R st lst f x)
    (he : ∀ e, ∃ mg2, k (.Err e) = ok (.Err e, mg2))
    (hk : ∀ a b lst1, R a b → CRM pers ls' st lst1 (k (.Ok a)) (g b)) :
    CRM pers ls' st lst (Std.bind f k) (x >>= g) := by
  intro hrel hinv o mg2 hm
  obtain ⟨r, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf hrel hinv r hf1
  cases r with
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := h1
    rw [am_bind_ok hx]
    exact hk a b lst1 hR hrel1 hinv1 o mg2 hk1
  | Err e =>
    obtain ⟨mg3, he3⟩ := he e
    rw [he3] at hk1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hk1)
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind h1 _

/-- Two steps. -/
theorem CRM.bind {pers : arena.store.PersTier} {ls' : Array Arena.Frontend.Olean.Loaded}
    {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result Unit kernel.core_types.CheckError × frontend.olean.merge.Merged)}
    {k : core.result.Result Unit kernel.core_types.CheckError × frontend.olean.merge.Merged →
      Result (core.result.Result Unit kernel.core_types.CheckError × frontend.olean.merge.Merged)}
    {x : AM Arena.Frontend.Olean.Merged} {g : Arena.Frontend.Olean.Merged → AM Arena.Frontend.Olean.Merged}
    (hf : CRM pers ls' st lst f x)
    (he : ∀ e mg1, k (.Err e, mg1) = ok (.Err e, mg1))
    (hk : ∀ u mg1 b lst1, MergedRel mg1 b → b.ls = ls' → CRM pers ls' st lst1 (k (.Ok u, mg1)) (g b)) :
    CRM pers ls' st lst (Std.bind f k) (x >>= g) := by
  intro hrel hinv o mg2 hm
  obtain ⟨⟨r, mg1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf hrel hinv r mg1 hf1
  cases r with
  | Ok u =>
    obtain ⟨b, lst1, hx, hR, hb, hrel1, hinv1⟩ := h1
    rw [am_bind_ok hx]
    exact hk u mg1 b lst1 hR hb hrel1 hinv1 o mg2 hk1
  | Err e =>
    rw [he e mg1] at hk1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hk1)
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind h1 _

/-! ## `merge_entry` -/

/-- The merge's map, one insert further. -/
theorem merged_insert {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {n : arena.handle.NIdx} {p : Std.Usize × Std.Usize} {old map2}
    (h : ron.hashmap2.HashMap2.insert arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 mg.map n p = ok (old, map2)) :
    RelOn anyN map2 (mg'.map.insert (absNIdx n) (absMgPos p)) absNIdx absMgPos ∧
      Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable map2 := by
  have h1 := ConRon.Refine.HashMap2.Rel_insert_wf nidx_eq2 (fun _ _ _ _ he => absNIdx_inj he)
    hm.inv (anyNKeysOk _) hm.map trivial h
  exact ⟨h1.1, (ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2 hm.inv (anyNKeysOk _) trivial h).1⟩

/-- **Merge one constant.**  The twin's `c'` is the `i`-th of its module `m`, by position,
as the Rust reads it. -/
theorem merge_entry_crm {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) {ls' : Array Arena.Frontend.Olean.Loaded}
    {mg : frontend.olean.merge.Merged} {lmg : Arena.Frontend.Olean.Merged} (hm : MergedRel mg lmg)
    (hls : lmg.ls = ls') {m i : Std.Usize} {c' : Arena.Frontend.Olean.CEntry}
    (hc : ∀ l', ls'[m.val]? = some l' → l'.constants[i.val]? = some c') :
    CRM pers ls' st lst (merge_entry pk pers st.store mg m i)
      (Arena.Frontend.Olean.mergeEntry (absPins pk) lmg m.val i.val c') := by
  rw [merge_entry, Arena.Frontend.Olean.mergeEntry]
  refine CRM.pure_step fun l hl => CRM.pure_step fun c hcc => CRM.pure_step fun n hn => ?_
  rw [nidx_dup2_ok hn]
  obtain ⟨l', hl1, hlr⟩ := forall₂_getElem? hm.ls (ConRon.Refine.ExprOps.vec_index_getElem? hl)
  obtain ⟨c'', hc1, hcr⟩ := forall₂_getElem? (LoadedRel.constants hlr)
    (ConRon.Refine.ExprOps.vec_index_getElem? hcc)
  have hl2 : ls'[m.val]? = some l' := by rw [← hls]; simpa using hl1
  have hc2 := hc l' hl2
  rw [show l'.constants[i.val]? = some c'' by simpa using hc1] at hc2
  cases Option.some.inj hc2
  have hname : absNIdx c.c.name = c'.c.name := hcr.1.«name»
  rw [← hname]
  refine CRM.pure_step fun o ho => ?_
  have hg := mg_get_rel hm ho
  cases hlg : lmg.get (absNIdx c.c.name) with
  | none =>
    rw [hlg] at hg
    cases hg
    refine CRM.pure_step fun n1 hn1 => ?_
    rw [nidx_dup2_ok hn1]
    refine CRM.pure_step fun q hq => CRM.pure_step fun v hv => ?_
    obtain ⟨old, map2⟩ := q
    obtain ⟨h1, h2⟩ := merged_insert hm hq
    refine CRM.pure ⟨hm.ls, h1, h2, ?_⟩ hls
    rw [ConRon.Refine.vec_push_val hv, List.map_append, hm.order]
    simp
  | some prev' =>
    rw [hlg] at hg
    cases hg with
    | some hp =>
      refine CRM.pure_step fun c1 hc1' => ?_
      have e1 := ConRon.Refine.ExprOps.vec_index_getElem? hc1'
      rw [ConRon.Refine.ExprOps.vec_index_getElem? hcc] at e1
      cases Option.some.inj e1
      refine CRM.bind_cr (subsumes_rel pk hm hcr hp) (fun _ => ⟨_, rfl⟩) fun a b lst1 hab => ?_
      cases hab
      cases a with
      | true =>
        refine CRM.pure_step fun q hq => ?_
        obtain ⟨old, map2⟩ := q
        obtain ⟨h1, h2⟩ := merged_insert hm hq
        exact CRM.pure ⟨hm.ls, h1, h2, hm.order⟩ hls
      | false =>
        refine CRM.bind_cr (subsumes_rel pk hm hp hcr) (fun _ => ⟨_, rfl⟩) fun a b lst2 hab => ?_
        cases hab
        cases a with
        | true => exact CRM.pure hm hls
        | false =>
          intro hrel hinv o2 mg3 h
          peel h as r2, hr2
          obtain ⟨e, rfl, he⟩ := merge_conflict_err (β := Arena.Frontend.Olean.Merged)
            (fun x => toString "two modules store different constants named " ++ toString x) hrel hr2
          cases Result.ok_injective h
          exact he

/-! ## The loops -/

/-- `for i in [0:n]` over a list's elements with their positions. -/
def ixFold {m : Type → Type} [Monad m] {α β : Type} (f : Nat → α → β → m β) :
    List α → Nat → β → m β
  | [], _, b => pure b
  | a :: l, i, b => f i a b >>= ixFold f l (i + 1)

/-- **`for i in [0:a.size]`, as a fold over the array's elements.** -/
theorem forIn_range_ixFold {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (a : Array α) (f : Nat → α → β → m β) (init : β) :
    forIn' [:a.size] init (fun i (hi : i ∈ [:a.size]) r => do
        let r' ← f i (a[i]'hi.2.1) r
        pure PUnit.unit
        pure (ForInStep.yield r')) = ixFold f a.toList 0 init := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  have key : ∀ (k i : Nat) (b : β) (hik : i + k = a.size),
      forIn' (List.range' i k 1) b (fun j (hj : j ∈ List.range' i k 1) r => do
          let r' ← f j (a[j]'(by have := (List.mem_range'_1.mp hj).2; omega)) r
          pure (ForInStep.yield r')) = ixFold f (a.toList.drop i) i b := by
    intro k
    induction k with
    | zero =>
      intro i b hk
      rw [List.drop_eq_nil_of_le (by simpa using (by omega : a.size ≤ i))]
      rfl
    | succ k ih =>
      intro i b hk
      have hi : i < a.toList.length := by simpa using (by omega : i < a.size)
      change forIn' (i :: List.range' (i + 1) k 1) b _ = _
      rw [List.forIn'_cons, List.drop_eq_getElem_cons hi]
      simp only [ixFold, bind_assoc, pure_bind]
      refine congrArg (f i a[i] b >>= ·) (funext fun r => ?_)
      exact ih (i + 1) r (by omega)
  have := key a.size 0 init (by omega)
  simpa [Std.Legacy.Range.size] using this

/-- The twin's constants of module `m`, folded. -/
abbrev mergeMod (pk : Arena.Frontend.Olean.OleanPins) (m : Nat) (l : Arena.Frontend.Olean.Loaded)
    (mg : Arena.Frontend.Olean.Merged) : AM Arena.Frontend.Olean.Merged :=
  ixFold (fun i c r => Arena.Frontend.Olean.mergeEntry pk r m i c) l.constants.toList 0 mg

/-- **`mergeAll`, as two folds.** -/
theorem mergeAll_eq (pk : Arena.Frontend.Olean.OleanPins) (ls : Array Arena.Frontend.Olean.Loaded) :
    Arena.Frontend.Olean.mergeAll pk ls = ixFold (mergeMod pk) ls.toList 0 { ls } := by
  rw [Arena.Frontend.Olean.mergeAll]
  refine (bind_pure _).trans ?_
  refine Eq.trans ?_ (forIn_range_ixFold ls (mergeMod pk) { ls })
  refine congrArg _ (funext fun m => funext fun hm => funext fun r => ?_)
  exact congrArg (· >>= _)
    (forIn_range_ixFold (ls[m]'hm.2.1).constants
      (fun i c r => Arena.Frontend.Olean.mergeEntry pk r m i c) r)

theorem merge_module_loop_crm {pers : arena.store.PersTier} {st : arena.monad.AState}
    (pk : frontend.olean.spec.OleanPins) {ls' : Array Arena.Frontend.Olean.Loaded}
    {l' : Arena.Frontend.Olean.Loaded} {m n : Std.Usize} (hl : ls'[m.val]? = some l')
    (hn : n.val = l'.constants.size) (k : Nat) :
    ∀ (mg : frontend.olean.merge.Merged) (lmg : Arena.Frontend.Olean.Merged) (i : Std.Usize)
      (lst : AState), MergedRel mg lmg → lmg.ls = ls' → n.val - i.val = k →
      CRM pers ls' st lst (merge_module_loop pk pers st.store mg m n i)
        (ixFold (fun i c r => Arena.Frontend.Olean.mergeEntry (absPins pk) r m.val i c)
          (l'.constants.toList.drop i.val) i.val lmg) := by
  induction k with
  | zero =>
    intro mg lmg i lst hm hls hk
    rw [merge_module_loop, ite_eq_right_iff.mpr (fun hc => absurd hc (by scalar_tac))]
    rw [List.drop_eq_nil_of_le (by simpa using (by omega : l'.constants.size ≤ i.val)), ixFold]
    exact CRM.pure hm hls
  | succ k ih =>
    intro mg lmg i lst hm hls hk
    have hi : i.val < l'.constants.toList.length := by simpa using (by omega : i.val < l'.constants.size)
    rw [merge_module_loop, ite_eq_left (by scalar_tac), List.drop_eq_getElem_cons hi, ixFold]
    refine CRM.bind (merge_entry_crm pk hm hls fun l1 h1 => ?_) (fun _ _ => rfl) ?_
    · rw [hl] at h1
      cases Option.some.inj h1
      simp
    · intro u mg1 b lst1 hb hb2
      refine CRM.pure_step fun i1 hi1 => ?_
      have hu := ConRon.Refine.Nat.uadd_val hi1
      have h1' : (1#usize).val = 1 := rfl
      rw [h1'] at hu
      rw [← hu]
      exact ih mg1 b i1 lst1 hb hb2 (by omega)

theorem merge_module_crm {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) {ls' : Array Arena.Frontend.Olean.Loaded}
    {l' : Arena.Frontend.Olean.Loaded} {m : Std.Usize} (hl : ls'[m.val]? = some l')
    {mg : frontend.olean.merge.Merged} {lmg : Arena.Frontend.Olean.Merged} (hm : MergedRel mg lmg)
    (hls : lmg.ls = ls') :
    CRM pers ls' st lst (merge_module pk pers st.store mg m) (mergeMod (absPins pk) m.val l' lmg) := by
  rw [merge_module]
  refine CRM.pure_step fun l hl0 => ?_
  obtain ⟨l1, hl1, hlr⟩ := forall₂_getElem? hm.ls (ConRon.Refine.ExprOps.vec_index_getElem? hl0)
  rw [show ls'[m.val]? = some l1 by rw [← hls]; simpa using hl1] at hl
  cases Option.some.inj hl
  refine merge_module_loop_crm pk (by rw [← hls]; simpa using hl1) ?_ _ mg lmg 0#usize lst hm hls rfl
  have := (LoadedRel.constants hlr).length_eq
  simpa [alloc.vec.Vec.len] using this

theorem merge_all_loop_cr {pers : arena.store.PersTier} {st : arena.monad.AState}
    (pk : frontend.olean.spec.OleanPins) {ls' : Array Arena.Frontend.Olean.Loaded} {n : Std.Usize}
    (hn : n.val = ls'.size) (k : Nat) :
    ∀ (mg : frontend.olean.merge.Merged) (lmg : Arena.Frontend.Olean.Merged) (m : Std.Usize)
      (lst : AState), MergedRel mg lmg → lmg.ls = ls' → n.val - m.val = k →
      CR pers MergedRel st lst (merge_all_loop pk pers st.store n mg m)
        (ixFold (mergeMod (absPins pk)) (ls'.toList.drop m.val) m.val lmg) := by
  induction k with
  | zero =>
    intro mg lmg m lst hm hls hk
    rw [merge_all_loop, ite_eq_right_iff.mpr (fun hc => absurd hc (by scalar_tac))]
    rw [List.drop_eq_nil_of_le (by simpa using (by omega : ls'.size ≤ m.val)), ixFold]
    exact CR.pure hm
  | succ k ih =>
    intro mg lmg m lst hm hls hk
    have hi : m.val < ls'.toList.length := by simpa using (by omega : m.val < ls'.size)
    rw [merge_all_loop, ite_eq_left (by scalar_tac), List.drop_eq_getElem_cons hi]
    intro hrel hinv o h
    peel h as q, hq
    obtain ⟨r, mg1⟩ := q
    have h1 := merge_module_crm pk (l' := ls'.toList[m.val]) (by simp) hm hls hrel hinv r mg1 hq
    rw [ixFold]
    cases r with
    | Err e =>
      cases Result.ok_injective h
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind h1 _
    | Ok u =>
      obtain ⟨b, lst1, hx, hb, hb2, hrel1, hinv1⟩ := h1
      rw [am_bind_ok hx]
      peel h as m1, hm1
      have hu := ConRon.Refine.Nat.uadd_val hm1
      have h1' : (1#usize).val = 1 := rfl
      rw [h1'] at hu
      rw [← hu]
      exact ih mg1 b m1 lst1 hb hb2 (by omega) hrel1 hinv1 o h

/-- **`merge_all` is `mergeAll`.** -/
theorem merge_all_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) {ls : alloc.vec.Vec frontend.olean.lazy.Loaded}
    {ls' : Array Arena.Frontend.Olean.Loaded} (hls : List.Forall₂ LoadedRel ls.val ls'.toList) :
    CR pers MergedRel st lst (merge_all pk pers st.store ls)
      (Arena.Frontend.Olean.mergeAll (absPins pk) ls') := by
  rw [merge_all, mergeAll_eq]
  refine CR.pure_step fun hm0 h0 => ?_
  obtain ⟨hinv0, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) h0
  refine merge_all_loop_cr pk ?_ _ _ { ls := ls' } 0#usize lst
    ⟨hls, ConRon.Refine.HashMap2.RelOn_empty hnone, hinv0, rfl⟩ rfl rfl
  have := hls.length_eq
  simpa [alloc.vec.Vec.len] using this

end ConRon.Refine2.Frontend.Olean
