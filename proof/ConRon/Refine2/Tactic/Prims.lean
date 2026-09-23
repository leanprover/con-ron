/-
# `ConRon.Refine2.Tactic.Prims` — the `@[lockstep]` primitive correspondences

Task #97-T2-TACTIC.  One lemma per Rust/twin primitive pair, in the judgement
shape `Tactic/Lockstep.lean` steps with.  Each is the existing `Specs.lean` /
`ExprOps/*.lean` lemma restated over `AStateRel₀` (the lockstep relation), so
where the existing proof only reads `hrel.store` / `hrel.memos` the proof
below is that proof with `AStateRel₀`.

**The seven interns are `sorry` here, and as stated they are FALSE until the
D2 twin fix lands** (task #97-T2-AUDIT §4: the Rust skips the persistent
probe when a child is in the scratch tier, the twin always probes, so on a
store that is not `StoreWF` the two can answer different handles).  Under
`AStateRel₀` the existing lemmas need `hchild`, a fact about the twin store
no lockstep context carries.  They are stated with `AStateRel₀`, `AStateInv`
and nothing else because that is the statement the migration's intern slice
proves once the twin mirrors the `sk` skip; `intern_e_bind_i_ls` also waits
on finding 15 (`internLamIE`'s capacity test before the probe).  Nothing
outside the `Tactic/Sample*.lean` measurements may use them; `#print axioms`
on each sample shows `sorryAx` exactly through these.
-/
import ConRon.Refine2.Tactic.Lockstep
import ConRon.Refine2.Specs
import ConRon.Refine2.ExprOps.Pure

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

attribute [lockstep_simp] absENodeView Option.map_some Option.map_none absU

/-! ## Condition correspondences (`lockstep_simp`) -/

@[lockstep_simp] theorem absU32_beq_lam (t : Std.U32) :
    (absU32 t == ETag.lam) = decide (t = arena.handle.ETAG_LAM) := by
  rw [← etag_lam_abs]
  by_cases h : t = arena.handle.ETAG_LAM
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_LAM := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_forallE (t : Std.U32) :
    (absU32 t == ETag.forallE) = decide (t = arena.handle.ETAG_FORALL_E) := by
  rw [← etag_forallE_abs]
  by_cases h : t = arena.handle.ETAG_FORALL_E
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_FORALL_E := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_sort (t : Std.U32) :
    (absU32 t == ETag.sort) = decide (t = arena.handle.ETAG_SORT) := by
  rw [← etag_sort_abs]
  by_cases h : t = arena.handle.ETAG_SORT
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_SORT := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_app (t : Std.U32) :
    (absU32 t == ETag.app) = decide (t = arena.handle.ETAG_APP) := by
  rw [← etag_app_abs]
  by_cases h : t = arena.handle.ETAG_APP
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_APP := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_bvar (t : Std.U32) :
    (absU32 t == ETag.bvar) = decide (t = arena.handle.ETAG_BVAR) := by
  rw [← etag_bvar_abs]
  by_cases h : t = arena.handle.ETAG_BVAR
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_BVAR := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_letE (t : Std.U32) :
    (absU32 t == ETag.letE) = decide (t = arena.handle.ETAG_LET_E) := by
  rw [← etag_letE_abs]
  by_cases h : t = arena.handle.ETAG_LET_E
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_LET_E := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_proj (t : Std.U32) :
    (absU32 t == ETag.proj) = decide (t = arena.handle.ETAG_PROJ) := by
  rw [← etag_proj_abs]
  by_cases h : t = arena.handle.ETAG_PROJ
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_PROJ := fun hc => h (absU32_inj hc)
    simp [h, this]

attribute [lockstep_simp] etag_sort_abs etag_app_abs etag_bvar_abs etag_letE_abs etag_proj_abs

@[lockstep_simp] theorem isBind_forallE : ETag.isBind ETag.forallE = true := rfl
@[lockstep_simp] theorem isBind_lam : ETag.isBind ETag.lam = true := rfl

attribute [lockstep_simp] decide_eq_true_eq etag_forallE_abs etag_lam_abs absBindM beq_self_eq_true

/-! ## Rust-only steps -/

@[lockstep] theorem dup2_eidx (h : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_eidx _ _ he

@[lockstep] theorem fail_spec (T : Type) (e : kernel.core_types.CheckError) :
    LSP (arena.monad.fail T e) (fun r => r = .Err e) :=
  fun r hr => fail_run hr

@[lockstep] theorem eidx_nat_key_spec (h : arena.handle.EIdx) (d : Std.U64) :
    LSP (arena.monad.eidx_nat_key h d) (fun k => absEIdxNat k = (absEIdx h, absU d)) :=
  fun _ hk => eidx_nat_key_abs hk

@[lockstep] theorem uscalar_sub {ty} (x y : Std.UScalar ty) :
    LSP (x - y) (fun z => z.val = x.val - y.val ∧ y.val ≤ x.val) := by
  intro z h
  have := ConRon.Refine.Nat.usub_val h
  exact ⟨this.2, this.1⟩

@[lockstep] theorem uscalar_add {ty} (x y : Std.UScalar ty) :
    LSP (x + y) (fun z => z.val = x.val + y.val) :=
  fun _ h => ConRon.Refine.Nat.uadd_val h

attribute [lockstep_simp] absEIdxListFrom absOptE

@[lockstep] theorem eidx_tag_spec (i : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.tag i) (fun t => (absEIdx i).tag = absU32 t) :=
  fun _ h => eidx_tag_abs h

@[lockstep] theorem vec_index_spec {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) :
    LSP (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i)
      (fun x => ∃ hb : i.val < v.val.length, x = v.val[i.val]) := by
  intro x h
  obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt h
  exact ⟨hb, hx.symm⟩

@[lockstep] theorem fail_dangling_e_spec (T : Type) :
    LSP (arena.monad.fail_dangling_e T) (fun r => ∃ v, r = .Err (.Internal v)) := by
  intro r h
  rw [arena.monad.fail_dangling_e] at h
  obtain ⟨s, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨v, fail_run h⟩

@[lockstep] theorem vec_push_spec {α : Type} (v : alloc.vec.Vec α) (x : α) :
    LSP (alloc.vec.Vec.push v x) (fun w => w.val = v.val ++ [x]) :=
  fun _ h => ConRon.Refine.vec_push_val h

@[lockstep] theorem e_tag_is_bind_spec (t : Std.U32) :
    LSP (arena.handle.e_tag_is_bind t) (fun b => b = ETag.isBind (absU32 t)) := by
  intro b h
  rw [arena.handle.e_tag_is_bind] at h
  simp only [ETag.isBind, absU32_beq_lam, absU32_beq_forallE]
  split at h
  · cases Result.ok_injective h; simp [*]
  · cases Result.ok_injective h; simp [*]

@[lockstep] theorem bvar_of_data_spec (w : Std.U64) :
    LSP (kernel.expr.bvar_of_data w) (fun r => r.val = w.val / 65536 % 32768) :=
  fun _ h => ConRon.Refine.Expr.bvar_of_data_val h

@[lockstep] theorem sat_range_spec :
    LSP kernel.expr.sat_range (fun r => r.val = ConLeche.satRange) :=
  fun _ h => ConRon.Refine.Expr.sat_range_val h

/-! ## Reads -/

/-- A Rust store read against a twin read of the same store field. -/
theorem LSV.of_store_read {α β : Type} {pers st lst} {m : Result α} {x : AM β}
    {A : α → β} {F : EStore → β} (hx : ∀ l : AState, x.run l = .ok (F l.store, l))
    (hr : ∀ a, m = ok a → F lst.store = A a)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSV pers (fun a b => b = A a) m st lst x := by
  intro a ha
  exact ⟨_, lst, hx lst, (hr a ha).symm ▸ rfl, hrel, hinv⟩

@[lockstep] theorem view_app_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absPairE a) (arena.monad.view_app pers st h) st lst
      (Arena.viewApp (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewApp (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by rw [arena.monad.view_app] at hr; exact estore_view_app_abs hrel.store hr)
    hrel hinv

@[lockstep] theorem view_bvar_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absU a) (arena.monad.view_bvar pers st h) st lst
      (Arena.viewBVar (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewBVar (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by rw [arena.monad.view_bvar] at hr; exact estore_view_bvar_abs hrel.store hr)
    hrel hinv

@[lockstep] theorem view_let_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absLetT a) (arena.monad.view_let pers st h) st lst
      (Arena.viewLet (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewLet (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by rw [arena.monad.view_let] at hr; exact estore_view_let_abs hrel.store hr)
    hrel hinv

@[lockstep] theorem view_proj_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absProjT a) (arena.monad.view_proj pers st h) st lst
      (Arena.viewProj (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewProj (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by rw [arena.monad.view_proj] at hr; exact estore_view_proj_abs hrel.store hr)
    hrel hinv

@[lockstep] theorem view_bind_i_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx)
    (hbind : ETag.isBind (absEIdx h).tag = true) :
    LSV pers (fun a b => b = Option.map absBindI a) (arena.monad.view_bind_i pers st h) st lst
      (Arena.viewBindI (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewBindI (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by
      rw [arena.monad.view_bind_i] at hr; exact estore_view_bind_i_abs hrel.store hbind hr)
    hrel hinv

/-- `derived_e` against `derivedE`: the word, up to its hash (`derObsE`), read
as the three fields every reader uses. -/
@[lockstep] theorem derived_e_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun (d : Std.U64) (w : UInt64) =>
        (ConLeche.bvarOfData w).toNat = d.val / 65536 % 32768)
      (arena.monad.derived_e pers st h) st lst (derivedE (absEIdx h)) := by
  intro d hd
  refine ⟨_, lst, rfl, ?_, hrel, hinv⟩
  rw [arena.monad.derived_e] at hd
  exact (derObsE_fields (estore_derived_abs hrel.store hd)).1

attribute [lockstep_simp] absPairE absLetT absProjT absBindI


/-- `arena::monad::view_sort` against `Arena.viewSort`. -/
@[lockstep] theorem view_sort_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absLIdx a) (arena.monad.view_sort pers st h) st lst
      (Arena.viewSort (absEIdx h)) := by
  intro o hrun
  refine ⟨_, lst, rfl, ?_, hrel, hinv⟩
  rw [arena.monad.view_sort] at hrun
  exact estore_view_sort_abs hrel.store hrun

/-- `arena::monad::view_bind` against `Arena.viewBind`, at a binder tag. -/
@[lockstep] theorem view_bind_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx)
    (hbind : ETag.isBind (absEIdx h).tag = true) :
    LSV pers (fun a b => b = Option.map absBindM a) (arena.monad.view_bind pers st h) st lst
      (Arena.viewBind (absEIdx h)) := by
  intro o hrun
  refine ⟨_, lst, rfl, ?_, hrel, hinv⟩
  rw [arena.monad.view_bind] at hrun
  exact estore_view_bind_abs hrel.store hbind hrun


/-- `arena::monad::view` against `Arena.view` (`view_run` over `AStateRel₀`). -/
@[lockstep] theorem view_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absENodeView a) (arena.monad.view pers st h) st lst
      (Arena.view (absEIdx h)) := by
  intro o hrun
  rw [arena.monad.view] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hqa := estore_view_abs hrel.store hq
  have hrunL : (Arena.view (absEIdx h)).run lst
      = (match lst.store.view (absEIdx h) with
         | some v => Except.ok (v, lst)
         | none => Except.error (Arena.CheckError.internal
             "arena: dangling expression handle")) := by
    show ((match lst.store.view (absEIdx h) with
            | some v => (pure v : AM ENodeView)
            | none => Arena.fail
                (.internal "arena: dangling expression handle")).run lst) = _
    cases lst.store.view (absEIdx h) <;> rfl
  cases hqc : q with
  | none =>
    rw [hqc] at hrun
    obtain ⟨s, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 : core.result.Result.Err
        (kernel.core_types.CheckError.Internal v) = o := Result.ok_injective hrun
    subst h2
    refine AErrSim.internal (s := "arena: dangling expression handle") ?_
    rw [hrunL, hqa, hqc]
    rfl
  | some v =>
    rw [hqc] at hrun
    have h2 : core.result.Result.Ok v = o := Result.ok_injective hrun
    subst h2
    refine ⟨absENodeView v, lst, ?_, rfl, hrel, hinv⟩
    rw [hrunL, hqa, hqc]
    rfl

/-- `inst_list_cutoff` against the twin's inline `derivedE` read: the Rust's
boolean is the twin's test on the word it reads. -/
@[lockstep] theorem inst_list_cutoff_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) (k : Std.U64) :
    LSV pers (fun (o : Bool) (d : UInt64) =>
        o = (decide ((ConLeche.bvarOfData d).toNat < ConLeche.satRange) &&
          decide ((ConLeche.bvarOfData d).toNat ≤ absU k)))
      (arena.expr_ops.inst_list_cutoff pers st h k) st lst (derivedE (absEIdx h)) := by
  intro o hrun
  refine ⟨lst.store.derived (absEIdx h), lst, rfl, ?_, hrel, hinv⟩
  rw [arena.expr_ops.inst_list_cutoff] at hrun
  obtain ⟨der, hder, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨sr, hsr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.monad.derived_e] at hder
  obtain ⟨hbv, -, -⟩ := derObsE_fields (estore_derived_abs hrel.store hder)
  have hbb := ConRon.Refine.Expr.bvar_of_data_val hb
  have hsrv := ConRon.Refine.Expr.sat_range_val hsr
  have hbn : (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat = b.val := by
    rw [hbv, hbb]
  split at hrun <;> rename_i hlt <;> simp only [Result.ok.injEq] at hrun <;> rw [← hrun]
  · have h1 : (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat
        < ConLeche.satRange := by rw [hbn, ← hsrv]; exact hlt
    simp only [h1, decide_true, Bool.true_and]
    have h2 : ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat ≤ absU k)
        = (b ≤ k) := by
      rw [hbn]
      exact propext ⟨fun x => by scalar_tac, fun x => by scalar_tac⟩
    simp only [h2]
  · have h1 : ¬ ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat
        < ConLeche.satRange) := by rw [hbn, ← hsrv]; simpa using hlt
    simp [h1]

/-! ## Memo get / set (`lift` shown; the other twelve are the same four lines) -/

@[lockstep] theorem lift_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.lift_get st k) st lst
      (Arena.liftGet (absEIdxNat k)) := by
  intro o hrun
  refine ⟨_, lst, ?_, rfl, hrel, hinv⟩
  rw [arena.monad.lift_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.liftC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.liftC k trivial
  show (Arena.liftGet (absEIdxNat k)).run lst = _
  rw [show (Arena.liftGet (absEIdxNat k)).run lst
        = .ok (lst.memos.liftC[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

@[lockstep] theorem lift_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) (r : arena.handle.EIdx) :
    LSW pers (arena.monad.lift_set st k r) lst
      (Arena.liftSet (absEIdxNat k) (absEIdx r)) := by
  intro st' hrun
  rw [arena.monad.lift_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with lift_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.liftC
    hrel.memos.liftC hp
  exact ⟨(), _, rfl, trivial, { hrel with memos := { hrel.memos with liftC := h1 } },
    { hinv with memos := { hinv.memos with liftC := h2 } }⟩

@[lockstep] theorem inst1_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.inst1_get st k) st lst
      (Arena.inst1Get (absEIdxNat k)) := by
  intro o hrun
  refine ⟨_, lst, ?_, rfl, hrel, hinv⟩
  rw [arena.monad.inst1_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.inst1C
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.inst1C k trivial
  show (Arena.inst1Get (absEIdxNat k)).run lst = _
  rw [show (Arena.inst1Get (absEIdxNat k)).run lst
        = .ok (lst.memos.inst1C[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

@[lockstep] theorem inst1_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) (r : arena.handle.EIdx) :
    LSW pers (arena.monad.inst1_set st k r) lst
      (Arena.inst1Set (absEIdxNat k) (absEIdx r)) := by
  intro st' hrun
  rw [arena.monad.inst1_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with inst1_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.inst1C
    hrel.memos.inst1C hp
  exact ⟨(), _, rfl, trivial, { hrel with memos := { hrel.memos with inst1C := h1 } },
    { hinv with memos := { hinv.memos with inst1C := h2 } }⟩

/-! ## Interns — pending D2 (see the module note) -/

@[lockstep] theorem intern_e_bvar_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (i : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_bvar pers st i) lst
      (Arena.internBVarE (absU i)) := by
  sorry

@[lockstep] theorem intern_e_app_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f a : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_app pers st f a) lst
      (Arena.internAppE (absEIdx f) (absEIdx a)) := by
  sorry

@[lockstep] theorem intern_e_lam_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_lam pers st t b m) lst
      (Arena.internLamE (absEIdx t) (absEIdx b) (ConRon.Refine.absBinderMeta m)) := by
  sorry

@[lockstep] theorem intern_e_forall_e_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_forall_e pers st t b m) lst
      (Arena.internForallEE (absEIdx t) (absEIdx b) (ConRon.Refine.absBinderMeta m)) := by
  sorry

@[lockstep] theorem intern_e_let_e_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t v b : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_let_e pers st t v b) lst
      (Arena.internLetEE (absEIdx t) (absEIdx v) (absEIdx b)) := by
  sorry

@[lockstep] theorem intern_e_bind_i_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t : Std.U32) (ty b : arena.handle.EIdx) (m : arena.handle.BMIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_bind_i pers st t ty b m) lst
      (Arena.internBindIE (absU32 t) (absEIdx ty) (absEIdx b) (absBMIdx m)) := by
  sorry

@[lockstep] theorem intern_e_proj_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (i : Std.U64) (s : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_proj pers st n i s) lst
      (Arena.internProjE (absNIdx n) (absU i) (absEIdx s)) := by
  sorry

end ConRon.Refine2.Lockstep
