/-
# `ConRon.Refine2.Tactic.Prims` — the `@[lockstep]` primitive correspondences

Task #97-T2-TACTIC.  One lemma per Rust/twin primitive pair, in the judgement
shape `Tactic/Lockstep.lean` steps with.  Each is the existing `Specs.lean` /
`ExprOps/*.lean` lemma restated over `AStateRel₀` (the lockstep relation), so
where the existing proof only reads `hrel.store` / `hrel.memos` the proof
below is that proof with `AStateRel₀`.

**The interns are `sorry` here, on purpose.**  Under `AStateRel₀` an intern's
lockstep statement is TRUE only after the D2 twin fix (task #97-T2-AUDIT §4:
the Rust skips the persistent probe when a child is scratch, the twin always
probes); until then the existing lemma needs `hchild`, which is a fact about
the twin store no lockstep context carries.  They are restated with
`AStateRel₀`, `AStateInv` and nothing else, which is the statement the Specs
slice of the migration will prove.  `#print axioms` on each sample therefore
shows `sorryAx` exactly through these.
-/
import ConRon.Refine2.Tactic.Lockstep
import ConRon.Refine2.ExprOps.Mut

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

/-! ## Reads -/

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

@[lockstep] theorem intern_e_proj_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (i : Std.U64) (s : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_proj pers st n i s) lst
      (Arena.internProjE (absNIdx n) (absU i) (absEIdx s)) := by
  sorry

end ConRon.Refine2.Lockstep
