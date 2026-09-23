/-
# `ConRon.Refine2.Tactic.Prims` — the `@[lockstep]` primitive correspondences

Task #97-T2-TACTIC.  One lemma per Rust/twin primitive pair, in the judgement
shape `Tactic/Lockstep.lean` steps with.  Each is the existing `Specs.lean` /
`ExprOps/*.lean` lemma restated over `AStateRel₀` (the lockstep relation), so
where the existing proof only reads `hrel.store` / `hrel.memos` the proof
below is that proof with `AStateRel₀`.

**The interns.**  Task #97-T2-TACTIC left the seven expression interns
`sorry`: they were false until the D2 twin fix (task #97-T2-AUDIT §4).  Since
the foundation's intern slice (task #97-T2-LOCKSTEP slice 3) they are the
`Refine2/Specs.lean` `intern_*_run₀` lemmas in `LS` form (task #97-P5-Core
round 5, which also added `fvar`, `sort`, `const`, `lit`, the level node, the
level list and `intern_level`).  **`intern_e_lam_ls` / `intern_e_forall_e_ls`
stay `sorry`**, and only because of their statement (task #97-T2-LOCKSTEP D6):
`intern_e_{lam,forall_e}_run₀` need `PropWhenWF m.pw` of the Rust INPUT datum
(the `bms` cons key is a `PropWhen`, so `TblRel` is `RelOn PropWhenWF`), which
these two statements do not ask for; `intern_e_{lam,forall_e}_wf_ls` are the
same pairs with that premise, proved, and registered first.
-/
import ConRon.Refine2.Tactic.Lockstep
import ConRon.Refine2.Specs
import ConRon.Refine2.ExprOps.Pure
import ConRon.Refine.ExprOpsMeta

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
-- the other three tag constants (the Inductives Modeled lane met `etag_const_abs`
-- missing; task #97-T2-TACTIC round 2)
attribute [lockstep_simp] etag_const_abs etag_fvar_abs etag_lit_abs

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

/-! ### The `ExprOps` tier's vector abstractions (task #97-T2-LOCKSTEP lane ExprOps) -/

@[lockstep_simp] theorem absSz_val (x : Std.Usize) : absSz x = x.val := rfl

attribute [lockstep_simp] absEIdxArr_size

@[lockstep_simp] theorem absEIdxArr_getElem (v : alloc.vec.Vec arena.handle.EIdx) (k : Nat)
    (h : k < (absEIdxArr v).size) :
    (absEIdxArr v)[k] = absEIdx (v.val[k]'(by simpa using h)) := by
  simp [absEIdxArr]


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

end ConRon.Refine2.Lockstep

namespace ConRon.Refine2

open ConRon.Arena

/-! ## Representation facts the `ExprOps` walks read (task #97-T2-LOCKSTEP lane ExprOps)

Kind 1 of task #97-T2-AUDIT §2: well-formedness of the RUST values a read
answers (a binder datum's `PropWhen`, a readback level), from `AStateInv`
alone.  Moved here from `ExprOps/Mut.lean`, which now imports this file. -/

theorem etables_get_bm_wf {rt : arena.store.ETables} (hinv : ETablesInv rt)
    {m : arena.handle.BMIdx} {o : Option kernel.expr.BinderMeta}
    (h : arena.store.ETables.get_bm rt m = ok o) :
    ∀ bm, o = some bm → ConRon.Refine.PropWhenWF bm.pw := by
  rw [arena.store.ETables.get_bm] at h
  obtain ⟨n, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hwf := tbl_node_wf hinv.bms hp
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option kernel.expr.BinderMeta) = o := Result.ok_injective h
    subst h2
    intro bm hbm; cases hbm
  | some r =>
    rw [hpc] at h hwf
    obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some bm = o := Result.ok_injective h
    subst h2
    rw [ConRon.Refine.PropWhen.dup_eq hpw] at hbm
    have h3 : bm = ⟨r.pw⟩ := by
      rw [kernel.expr.binder_meta] at hbm
      exact (Result.ok_injective hbm).symm
    subst h3
    intro bm' hbm'
    simp only [Option.some.injEq] at hbm'
    subst hbm'
    exact hwf r rfl

theorem estore_view_bm_wf {pers rs} (hinv : StoreInv pers rs)
    {m : arena.handle.BMIdx} {o}
    (h : arena.store.EStore.view_bm rs pers m = ok o) :
    ∀ bm, o = some bm → ConRon.Refine.PropWhenWF bm.pw := by
  rw [arena.store.EStore.view_bm] at h
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · rw [arena.store.EStore.pers_get_bm] at h
    have h3 : arena.store.ETables.get_bm (rPersE pers rs) m = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_bm_wf hinv.perst h3
  · split at h
    · exact etables_get_bm_wf hinv.scrt h
    · have h2 : (none : Option kernel.expr.BinderMeta) = o := Result.ok_injective h
      subst h2
      intro bm hbm; cases hbm

/-- At a non-binder tag `view` is `ETables.get`, which answers no binder
view. -/
theorem view_nonbind_bmOf {st : EStore} {i : EIdx} (hnb : ETag.isBind i.tag = false)
    {v : ENodeView} (hv : st.view i = some v) : v.bmOf = none := by
  rw [EStore.view, if_neg (by rw [hnb]; simp)] at hv
  split at hv
  · exact ETables.bmOf_get hv
  · split at hv
    · exact ETables.bmOf_get hv
    · cases hv

/-- **A binder view's datum is well formed** — `bms`' `TblInv`, read through
`view`.  The non-binder branch cannot produce a binder view, which the TWIN
says: `ETables.get` answers no binder view (`ETables.bmOf_get`). -/
theorem estore_view_bind_wf {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs) {i : arena.handle.EIdx} {o}
    (h : arena.store.EStore.view rs pers i = ok o) {ty b : arena.handle.EIdx}
    {m : kernel.expr.BinderMeta}
    (hv : o = some (.Lam ty b m) ∨ o = some (.ForallE ty b m)) :
    ConRon.Refine.PropWhenWF m.pw := by
  have habs := estore_view_abs hrel h
  rw [arena.store.EStore.view] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have htg := eidx_tag_abs ht
  have hib := etag_isBind_abs hbb
  split at h <;> rename_i hbv
  · obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases hqc : q with
    | none =>
      rw [hqc] at h
      have h2 : (none : Option arena.store.ENodeView) = o := Result.ok_injective h
      subst h2
      rcases hv with hv | hv <;> cases hv
    | some tt =>
      rw [hqc] at h
      obtain ⟨ty', bo', mm⟩ := tt
      obtain ⟨ev, hev, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some ev = o := Result.ok_injective h
      subst h2
      have hmm : m = mm := by
        rw [arena.store.e_bind_view] at hev
        split at hev
        · have := Result.ok_injective hev
          rcases hv with hv | hv <;> rw [← this] at hv <;>
            simp only [Option.some.injEq, reduceCtorEq] at hv
          exact (arena.store.ENodeView.Lam.inj hv).2.2.symm
        · have := Result.ok_injective hev
          rcases hv with hv | hv <;> rw [← this] at hv <;>
            simp only [Option.some.injEq, reduceCtorEq] at hv
          exact (arena.store.ENodeView.ForallE.inj hv).2.2.symm
      subst hmm
      rw [hqc] at hq
      rw [arena.store.EStore.view_bind] at hq
      obtain ⟨o1, -, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
      cases ho1 : o1 with
      | none =>
        rw [ho1] at hq
        have := Result.ok_injective hq
        cases this
      | some t3 =>
        rw [ho1] at hq
        obtain ⟨e1, e2, bmi⟩ := t3
        obtain ⟨o2, ho2, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
        cases ho2c : o2 with
        | none =>
          rw [ho2c] at hq
          have := Result.ok_injective hq
          cases this
        | some m2 =>
          rw [ho2c] at hq ho2
          have h3 := Result.ok_injective hq
          simp only [Option.some.injEq, Prod.mk.injEq] at h3
          rw [← h3.2.2]
          exact estore_view_bm_wf hinv ho2 m2 rfl
  · -- the non-binder branch: the twin view is `ETables.get`, which answers no
    -- binder view
    exfalso
    have hnb : ETag.isBind (absEIdx i).tag = false := by
      rw [htg, hib]; simpa using hbv
    rcases hv with hv | hv <;> subst hv <;>
      exact absurd (view_nonbind_bmOf hnb habs) (by simp [absENodeView, ENodeView.bmOf])

theorem read_level_m_wf {pers st} (hinv : AStateInv pers st) {h : arena.handle.LIdx}
    {o} (hrun : arena.monad.read_level_m pers st h = ok o) :
    (∀ l, o.1 = .Ok l → ConRon.Refine.LevelWF l) ∧ o.2.store = st.store := by
  rw [arena.monad.read_level_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lidx_eq2 hinv.caches.readLC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hto
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok n, st) = o := Result.ok_injective hrun
    rw [← ho]
    have hne : n = x := by
      rw [ConRon.Refine.level_dup_eq] at hn; exact (Result.ok_injective hn).symm
    refine ⟨fun l hl => ?_, rfl⟩
    simp only [core.result.Result.Ok.injEq] at hl
    rw [← hl, hne]
    exact hinv.caches.readLVals (h, x) (ConRon.Refine.HashMap.lookupK_mem hto.symm)
  | none =>
    rw [hrc] at hrun
    obtain ⟨ls0, hls0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ls] at hls0
    have hls2 : ls0 = st.store.lss.ls := (Result.ok_injective hls0).symm
    subst hls2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hdw := denote_l_wf hinv.store.lss.lvl hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact ⟨(by intro l hl; cases hl), rfl⟩
    | some x =>
      rw [hvc] at hrun hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨l3, hl3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hl3e : l3 = x := by
        rw [ConRon.Refine.level_dup_eq] at hl3; exact (Result.ok_injective hl3).symm
      have ho := Result.ok_injective hrun
      rw [← ho]
      have hx3 : ConRon.Refine.LevelWF l3 := by rw [hl3e]; exact hdw x rfl
      refine ⟨fun l hl => ?_, rfl⟩
      simp only [core.result.Result.Ok.injEq] at hl
      first | (rw [← hl]; exact hdw x rfl) | (rw [← hl]; exact hx3) | (rw [hl] at hx3; exact hx3)

theorem read_levels_m_wf {pers st} (hinv : AStateInv pers st) {h : arena.handle.LsIdx}
    {o} (hrun : arena.monad.read_levels_m pers st h = ok o) :
    (∀ l, o.1 = .Ok l → ConRon.Refine.LevelsWF l) ∧ o.2.store = st.store := by
  rw [arena.monad.read_levels_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lsidx_eq2 hinv.caches.readLsC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hto
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok n, st) = o := Result.ok_injective hrun
    rw [← ho]
    refine ⟨fun l hl => ?_, rfl⟩
    simp only [core.result.Result.Ok.injEq] at hl
    rw [← hl]
    intro u hu
    rw [level_list_dup_val hn] at hu
    exact hinv.caches.readLsVals (h, x) (ConRon.Refine.HashMap.lookupK_mem hto.symm) u hu
  | none =>
    rw [hrc] at hrun
    obtain ⟨ls0, hls0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ls_s] at hls0
    have hls2 : ls0 = st.store.lss := (Result.ok_injective hls0).symm
    subst hls2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hdw := denote_ls_wf hinv.store.lss hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact ⟨(by intro l hl; cases hl), rfl⟩
    | some x =>
      rw [hvc] at hrun hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨l3, hl3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have ho := Result.ok_injective hrun
      rw [← ho]
      refine ⟨fun l hl => ?_, rfl⟩
      simp only [core.result.Result.Ok.injEq] at hl
      rw [← hl]; exact hdw x rfl

/-- A name read back is well formed, and the port's store does not move. -/
theorem read_name_m_wf {pers st} (hinv : AStateInv pers st) {h : arena.handle.NIdx}
    {o} (hrun : arena.monad.read_name_m pers st h = ok o) :
    (∀ n, o.1 = .Ok n → ConRon.Refine.NameWF n) ∧ o.2.store = st.store := by
  rw [arena.monad.read_name_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hinv.caches.readNC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hto
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok n, st) = o := Result.ok_injective hrun
    rw [← ho]
    have hne : n = x := (Result.ok_injective (by rw [← hn]; simp)).symm
    refine ⟨fun l hl => ?_, rfl⟩
    simp only [core.result.Result.Ok.injEq] at hl
    rw [← hl, hne]
    exact hinv.caches.readNVals (h, x) (ConRon.Refine.HashMap.lookupK_mem hto.symm)
  | none =>
    rw [hrc] at hrun
    obtain ⟨ns, hns, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ns] at hns
    have hns2 : ns = st.store.lss.ls.ns := (Result.ok_injective hns).symm
    subst hns2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hdw := denote_n_wf hinv.store.lss.lvl.ns hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact ⟨(by intro l hl; cases hl), rfl⟩
    | some x =>
      rw [hvc] at hrun hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨n2, hn2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have ho := Result.ok_injective hrun
      rw [← ho]
      refine ⟨fun l hl => ?_, rfl⟩
      simp only [core.result.Result.Ok.injEq] at hl
      rw [← hl]; exact hdw x rfl

theorem read_names_m_from_wf {pers} {ks : alloc.vec.Vec arena.handle.NIdx} :
    ∀ k {st : arena.monad.AState} {lst : AState}, AStateRel₀ pers st lst →
      AStateInv pers st → ∀ (i : Std.Usize) (out : alloc.vec.Vec kernel.name.Name),
      ks.length - i.val ≤ k → (∀ n ∈ out.val, ConRon.Refine.NameWF n) → ∀ {o},
      arena.monad.read_names_m_from pers st ks i out = ok o →
      (∀ v, o.1 = .Ok v → ∀ n ∈ v.val, ConRon.Refine.NameWF n) ∧
        o.2.store = st.store := by
  intro k
  induction k with
  | zero =>
    intro st lst hrel hinv i out hk hout o hrun
    rw [arena.monad.read_names_m_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
      Result.ok_injective hrun
    rw [← ho]
    refine ⟨fun v hv => ?_, rfl⟩
    simp only [core.result.Result.Ok.injEq] at hv
    rw [← hv]; exact hout
  | succ k ih =>
    intro st lst hrel hinv i out hk hout o hrun
    rw [arena.monad.read_names_m_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
        Result.ok_injective hrun
      rw [← ho]
      refine ⟨fun v hv => ?_, rfl⟩
      simp only [core.result.Result.Ok.injEq] at hv
      rw [← hv]; exact hout
    · rename_i hlt
      obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r, st1⟩ := p1
      have hstep := read_name_m_run₀ hrel hinv hp1
      have hw := read_name_m_wf hinv hp1
      cases hrc : r with
      | Err e =>
        simp only [hrc] at hrun
        have ho : ((core.result.Result.Err e : core.result.Result _ _), st1) = o :=
          Result.ok_injective hrun
        rw [← ho]
        exact ⟨(by intro v hv; cases hv), hw.2⟩
      | Ok x =>
        rw [hrc] at hstep hw
        simp only [hrc] at hrun
        obtain ⟨lst1, -, hrel1, hinv1⟩ := hstep
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hout1v : out1.val = out.val ++ [x] := ConRon.Refine.vec_push_val hout1
        have hih := ih hrel1 hinv1 i2 out1 (by scalar_tac) (by
          intro nn hnn
          rw [hout1v] at hnn
          rcases List.mem_append.mp hnn with hnn | hnn
          · exact hout nn hnn
          · rw [List.mem_singleton.mp hnn]; exact hw.1 x rfl) hrun
        exact ⟨hih.1, hih.2.trans hw.2⟩

end ConRon.Refine2

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

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
        (ConLeche.bvarOfData w).toNat = d.val / 65536 % 32768 ∧
        (ConLeche.fvarOfData w).toNat = d.val / 2 % 32768 ∧
        ConLeche.lpOfData w = decide (d.val % 2 = 1))
      (arena.monad.derived_e pers st h) st lst (derivedE (absEIdx h)) := by
  intro d hd
  refine ⟨_, lst, rfl, ?_, hrel, hinv⟩
  rw [arena.monad.derived_e] at hd
  exact derObsE_fields (estore_derived_abs hrel.store hd)

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

/-- The datum `view_bind` answers is well formed (kind 1, from `AStateInv`). -/
theorem view_bind_meta_wf {pers st} (hinv : AStateInv pers st) {h : arena.handle.EIdx}
    {ty b : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    (hrun : arena.monad.view_bind pers st h = ok (some (ty, b, m))) :
    ConRon.Refine.PropWhenWF m.pw := by
  rw [arena.monad.view_bind, arena.store.EStore.view_bind] at hrun
  obtain ⟨o1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  cases ho1 : o1 with
  | none => rw [ho1] at hrun; cases Result.ok_injective hrun
  | some t3 =>
    rw [ho1] at hrun
    obtain ⟨e1, e2, bmi⟩ := t3
    obtain ⟨o2, ho2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases ho2c : o2 with
    | none => rw [ho2c] at hrun; cases Result.ok_injective hrun
    | some m2 =>
      rw [ho2c] at hrun ho2
      have h3 := Result.ok_injective hrun
      simp only [Option.some.injEq, Prod.mk.injEq] at h3
      rw [← h3.2.2]
      exact estore_view_bm_wf hinv.store ho2 m2 rfl

/-- `arena::monad::view_bind` against `Arena.viewBind`, at a binder tag; the
datum it answers is well formed (the `PropWhenWF` an intern of a rebuilt binder
needs). -/
@[lockstep] theorem view_bind_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx)
    (hbind : ETag.isBind (absEIdx h).tag = true) :
    LSV pers (fun a b => (∀ t, a = some t → ConRon.Refine.PropWhenWF t.2.2.pw) ∧
        b = Option.map absBindM a) (arena.monad.view_bind pers st h) st lst
      (Arena.viewBind (absEIdx h)) := by
  intro o hrun
  refine ⟨_, lst, rfl, ⟨fun t ht => ?_, ?_⟩, hrel, hinv⟩
  · subst ht
    obtain ⟨ty, b, m⟩ := t
    exact view_bind_meta_wf hinv hrun
  · rw [arena.monad.view_bind] at hrun
    exact estore_view_bind_abs hrel.store hbind hrun


/-- What a caller of `view` may assume of the RUST view beyond its abstraction
(kind 1: from `AStateInv`): a binder's datum is well formed. -/
def EViewMetaWF : arena.store.ENodeView → Prop
  | .Lam _ _ m => ConRon.Refine.PropWhenWF m.pw
  | .ForallE _ _ m => ConRon.Refine.PropWhenWF m.pw
  | _ => True

theorem view_meta_wf {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.EIdx} {v : arena.store.ENodeView}
    (hq : arena.store.EStore.view st.store pers h = ok (some v)) : EViewMetaWF v := by
  cases v with
  | Lam ty b m => exact estore_view_bind_wf hrel.store hinv.store hq (Or.inl rfl)
  | ForallE ty b m => exact estore_view_bind_wf hrel.store hinv.store hq (Or.inr rfl)
  | _ => trivial

/-- `arena::monad::view` against `Arena.view` (`view_run` over `AStateRel₀`); the
Rust view's binder datum is well formed (`EViewMetaWF`). -/
@[lockstep] theorem view_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSR pers (fun a b => EViewMetaWF a ∧ b = absENodeView a) (arena.monad.view pers st h) st lst
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
    refine ⟨absENodeView v, lst, ?_, ⟨view_meta_wf hrel hinv (hqc ▸ hq), rfl⟩, hrel, hinv⟩
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

/-! ## Primitive pairs of the `ExprOps` walks (task #97-T2-LOCKSTEP lane ExprOps) -/

/-! ## Converters -/

theorem LSV.ofSimR {α β : Type} {A : α → β} {pers st lst} {m : Result α} {x : AM β}
    (h : ∀ a, m = ok a → SimR A lst a x) (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) : LSV pers (fun a b => b = A a) m st lst x := by
  intro a ha; exact ⟨_, lst, h a ha, rfl, hrel, hinv⟩

/-! ## Handle equality and duplication -/

@[lockstep] theorem eidx_eq2_spec (a b : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun c => c = (absEIdx a == absEIdx b)) := by
  intro c h
  have := eidx_eq2 a b c trivial trivial h
  subst this
  by_cases hab : a = b
  · subst hab; simp
  · have : absEIdx a ≠ absEIdx b := fun hh => hab (absEIdx_inj hh)
    simp [hab, this]

@[lockstep] theorem lidx_eq2_spec (a b : arena.handle.LIdx) :
    LSP (arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun c => c = (absLIdx a == absLIdx b)) := by
  intro c h
  have := lidx_eq2 a b c trivial trivial h
  subst this
  by_cases hab : a = b
  · subst hab; simp
  · have : absLIdx a ≠ absLIdx b := fun hh => hab (absLIdx_inj hh)
    simp [hab, this]

@[lockstep] theorem lsidx_eq2_spec (a b : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun c => c = (absLsIdx a == absLsIdx b)) := by
  intro c h
  have := lsidx_eq2 a b c trivial trivial h
  subst this
  by_cases hab : a = b
  · subst hab; simp
  · have : absLsIdx a ≠ absLsIdx b := fun hh => hab (absLsIdx_inj hh)
    simp [hab, this]

@[lockstep] theorem dup2_lidx (h : arena.handle.LIdx) :
    LSP (arena.handle.LIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_lidx _ _ he

@[lockstep] theorem dup2_lsidx (h : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_lsidx _ _ he

@[lockstep] theorem dup2_nidx (h : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_nidx _ _ he

/-! ## The derived word's `lp` bit -/

@[lockstep] theorem lp_of_data_spec (w : Std.U64) :
    LSP (kernel.expr.lp_of_data w) (fun b => b = decide (w.val % 2 = 1)) := by
  intro b h
  rw [ConRon.Refine.Expr.lp_of_data_val h]
  by_cases hw : w.val % 2 = 1 <;> simp [hw]

/-! ## The `instLP` memos -/

@[lockstep] theorem inst_lp_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.inst_lp_get st k) st lst
      (Arena.instLPGet (absEIdxNat k)) :=
  LSV.ofSimR (fun _ h => inst_lp_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem inst_lp_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) (r : arena.handle.EIdx) :
    LSW pers (arena.monad.inst_lp_set st k r) lst (Arena.instLPSet (absEIdxNat k) (absEIdx r)) :=
  LSW.ofSimS₀ fun _ h => inst_lp_set_run₀ hrel hinv h

@[lockstep] theorem inst_lp_l_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.handle.LIdx) :
    LSV pers (fun a b => b = Option.map absLIdx a) (arena.monad.inst_lp_l_get st k) st lst
      (Arena.instLPLGet (absLIdx k)) :=
  LSV.ofSimR (fun _ h => inst_lp_l_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem inst_lp_l_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k r : arena.handle.LIdx) :
    LSW pers (arena.monad.inst_lp_l_set st k r) lst (Arena.instLPLSet (absLIdx k) (absLIdx r)) :=
  LSW.ofSimS₀ fun _ h => inst_lp_l_set_run₀ hrel hinv h

@[lockstep] theorem inst_lp_ls_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.handle.LsIdx) :
    LSV pers (fun a b => b = Option.map absLsIdx a) (arena.monad.inst_lp_ls_get st k) st lst
      (Arena.instLPLsGet (absLsIdx k)) :=
  LSV.ofSimR (fun _ h => inst_lp_ls_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem inst_lp_ls_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k r : arena.handle.LsIdx) :
    LSW pers (arena.monad.inst_lp_ls_set st k r) lst
      (Arena.instLPLsSet (absLsIdx k) (absLsIdx r)) :=
  LSW.ofSimS₀ fun _ h => inst_lp_ls_set_run₀ hrel hinv h

@[lockstep] theorem inst_lp_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.inst_lp_clear st) lst Arena.instLPClear :=
  LSW.ofSimS₀ fun _ h => inst_lp_clear_run₀ hrel hinv h


/-! ## Level readbacks, the level substitution, level interns -/

theorem LS.ofSim₀WF {α β : Type} {A : α → β} {P : α → Prop} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β}
    (h : ∀ o, m = ok o → Sim₀ A pers lst o x)
    (hP : ∀ o, m = ok o → ∀ a, o.1 = .Ok a → P a) :
    LS pers (fun a b => P a ∧ b = A a) m lst x := by
  intro o st' hm
  have := h _ hm
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨lst', hx, h1, h2⟩ := this
    exact ⟨_, lst', hx, ⟨hP _ hm a rfl, rfl⟩, h1, h2⟩

@[lockstep] theorem read_level_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LIdx) :
    LS pers (fun a b => ConRon.Refine.LevelWF a ∧ b = ConRon.Refine.absLevel a)
      (arena.monad.read_level_m pers st h) lst (Arena.readLevelM (absLIdx h)) :=
  LS.ofSim₀WF (fun _ hr => read_level_m_run₀ hrel hinv hr)
    (fun _ hr a ha => (read_level_m_wf hinv hr).1 a ha)

@[lockstep] theorem read_levels_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LsIdx) :
    LS pers (fun a b => ConRon.Refine.LevelsWF a ∧ b = ConRon.Refine.absLevels a)
      (arena.monad.read_levels_m pers st h) lst (Arena.readLevelsM (absLsIdx h)) :=
  LS.ofSim₀WF (fun _ hr => read_levels_m_run₀ hrel hinv hr)
    (fun _ hr a ha => (read_levels_m_wf hinv hr).1 a ha)

theorem read_names_m_wf₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {ks : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.monad.read_names_m pers st ks = ok o) :
    ∀ v, o.1 = .Ok v → ∀ n ∈ v.val, ConRon.Refine.NameWF n := by
  rw [arena.monad.read_names_m] at hrun
  exact (read_names_m_from_wf ks.length hrel hinv 0#usize
    (alloc.vec.Vec.new kernel.name.Name) (by scalar_tac)
    (by intro n hn; exact absurd hn (by simp [alloc.vec.Vec.new])) hrun).1

@[lockstep] theorem read_names_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ks : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => (∀ n ∈ a.val, ConRon.Refine.NameWF n) ∧ b = ConRon.Refine.absNames a)
      (arena.monad.read_names_m pers st ks) lst (Arena.readNamesM (ks.val.map absNIdx)) :=
  LS.ofSim₀WF (fun _ hr => read_names_m_run₀ hrel hinv hr)
    (fun _ hr a ha => read_names_m_wf₀ hrel hinv hr a ha)

@[lockstep] theorem level_subst_spec {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} {l : kernel.level.Level}
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k) (hus : ∀ v ∈ us.val, ConRon.Refine.LevelWF v)
    (hl : ConRon.Refine.LevelWF l) :
    LSP (kernel.level.subst ks us l) (fun r => ConRon.Refine.LevelWF r ∧
      ConRon.Refine.absLevel r = ConLeche.Level.subst (ConRon.Refine.absNames ks)
        (ConRon.Refine.absLevels us) (ConRon.Refine.absLevel l)) := by
  intro r h
  obtain ⟨h1, h2⟩ := ConRon.Refine.Level.subst_use h hl hks hus
  exact ⟨h2, h1⟩

@[lockstep] theorem subst_level_list_spec {ks : alloc.vec.Vec kernel.name.Name}
    {us vs : alloc.vec.Vec kernel.level.Level}
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k) (hus : ∀ v ∈ us.val, ConRon.Refine.LevelWF v)
    (hvs : ConRon.Refine.LevelsWF vs) :
    LSP (arena.expr_ops.subst_level_list ks us vs) (fun r => ConRon.Refine.LevelsWF r ∧
      ConRon.Refine.absLevels r = substLevelList (ConRon.Refine.absNames ks)
        (ConRon.Refine.absLevels us) (ConRon.Refine.absLevels vs)) := by
  intro r h
  exact ⟨subst_level_list_wf hks hus hvs h, ExprOps.subst_level_list_refines hks hus hvs h⟩

@[lockstep] theorem intern_levels_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (l : alloc.vec.Vec kernel.level.Level)
    (hwf : ConRon.Refine.LevelsWF l) :
    LS pers (fun a b => b = absLsIdx a) (arena.monad.intern_levels pers st l) lst
      (Arena.internLevels (ConRon.Refine.absLevels l)) :=
  LS.ofSim₀ fun _ h => intern_levels_run₀ hrel hinv hwf h


/-! ## Binder data -/

@[lockstep] theorem subst_pw_spec {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} {pw : kernel.prop_when.PropWhen}
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k) (hus : ∀ v ∈ us.val, ConRon.Refine.LevelWF v)
    (hpw : ConRon.Refine.PropWhenWF pw) :
    LSP (kernel.level.subst_pw ks us pw) (fun r => ConRon.Refine.PropWhenWF r ∧
      ConRon.Refine.absPropWhen r = ConLeche.Level.substPW (ConRon.Refine.absNames ks)
        (ConRon.Refine.absLevels us) (ConRon.Refine.absPropWhen pw)) := by
  intro r h
  obtain ⟨h1, h2⟩ := ConRon.Refine.ExprOps.subst_pw_refines hks hus hpw h
  exact ⟨h2, h1⟩

@[lockstep] theorem binder_meta_spec (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.expr.binder_meta pw) (fun m => m = { pw := pw }) := by
  intro m h; rw [kernel.expr.binder_meta] at h; exact (Result.ok_injective h).symm

@[lockstep] theorem binder_meta_beq_spec {a b : kernel.expr.BinderMeta}
    (ha : ConRon.Refine.PropWhenWF a.pw) (hb : ConRon.Refine.PropWhenWF b.pw) :
    LSP (kernel.expr.binder_meta_beq a b)
      (fun c => c = (ConRon.Refine.absBinderMeta a == ConRon.Refine.absBinderMeta b)) := by
  intro c h
  rw [ConRon.Refine.Expr.binder_meta_beq_refines ha hb h]
  rfl

attribute [lockstep_simp] ConRon.Refine.absBinderMeta

/-! ## The state-free helpers of `ExprOps/Pure.lean`, as Rust-only steps -/

attribute [lockstep_simp] ExprOps.absEIdxL ExprOps.absFvlL ExprOps.absBinderL
  ConRon.Refine.absLevels ConRon.Refine.absNames

@[lockstep_simp] theorem vec_new_val' {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl
@[lockstep_simp] theorem vec_with_capacity_val' {α : Type} (n : Std.Usize) :
    (alloc.vec.Vec.with_capacity α n).val = [] := rfl
@[lockstep_simp] theorem usize_zero_val' : ((0#usize : Std.Usize)).val = 0 := rfl

-- The twin's nested `do` blocks, flattened so that its next action is at the head.
attribute [lockstep_simp] bind_assoc

/-- The twin's `if` in callee position (`let y ← if c then x else y`), pushed to
the head so that it is decided like any other twin test. -/
@[lockstep_simp] theorem twin_ite_bind {α β : Type} {c : Prop} [Decidable c] (x y : AM α)
    (f : α → AM β) : ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  by_cases h : c <;> simp [h]

@[lockstep_simp] theorem twin_pure_bind' {α β : Type} (a : α) (f : α → AM β) :
    ((pure a : AM α) >>= f) = f a := pure_bind a f

attribute [lockstep_simp] List.reverse_append List.reverse_cons List.reverse_nil List.reverse_singleton
attribute [lockstep_simp] List.map_append List.map_cons List.map_nil List.drop_zero
  List.nil_append List.cons_append List.singleton_append List.append_nil

@[lockstep] theorem cons_eidx_spec (a : arena.handle.EIdx) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.expr_ops.cons_eidx a xs)
      (fun r => ExprOps.absEIdxL r = absEIdx a :: ExprOps.absEIdxL xs) :=
  fun _ h => ExprOps.cons_eidx_refines h

/-- `snoc_eidx_of` is the twin's `Array.push` (the accumulators' push order). -/
@[lockstep] theorem snoc_eidx_of_spec (xs : alloc.vec.Vec arena.handle.EIdx) (y : arena.handle.EIdx) :
    LSP (arena.expr_ops.snoc_eidx_of xs y)
      (fun r => absEIdxArr r = (absEIdxArr xs).push (absEIdx y)) := by
  intro r h
  have := ExprOps.snoc_eidx_of_refines h
  simp only [ExprOps.absEIdxL] at this
  simp only [absEIdxArr, this, List.push_toArray]

@[lockstep] theorem eidx_take_beq_spec (args want : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.expr_ops.eidx_take_beq args want)
      (fun r => r = ((ExprOps.absEIdxL args).take (ExprOps.absEIdxL want).length ==
        ExprOps.absEIdxL want)) := by
  intro r h
  have := ExprOps.eidx_take_beq_refines h
  cases r <;> simp_all

/-- `bne` of two machine words is `bne` of their values. -/
@[lockstep_simp] theorem u64_bne_val (a b : Std.U64) : (a != b) = (a.val != b.val) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
  exact ⟨fun h hv => h (Std.UScalar.eq_of_val_eq hv), fun h hab => h (by rw [hab])⟩

@[lockstep_simp] theorem u64_zero_val' : ((0#u64 : Std.U64)).val = 0 := rfl

attribute [lockstep_simp] id_eq

@[lockstep] theorem cons_binder_spec (ty : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (xs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    LSP (arena.expr_ops.cons_binder ty m xs)
      (fun r => ExprOps.absBinderL r =
        (absEIdx ty, ConRon.Refine.absBinderMeta m) :: ExprOps.absBinderL xs) :=
  fun _ h => ExprOps.cons_binder_refines h

@[lockstep] theorem binder_copy_from_spec
    (xs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (i : Std.Usize)
    (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    LSP (arena.expr_ops.binder_copy_from xs i out)
      (fun r => ExprOps.absBinderL r = ExprOps.absBinderL out ++ (ExprOps.absBinderL xs).drop i.val) :=
  fun _ h => ExprOps.binder_copy_from_refines h

/-- `take_eidx_n` (the prefix at a `u64` count) against `takeEidx` at that count. -/
@[lockstep] theorem take_eidx_n_spec (xs : alloc.vec.Vec arena.handle.EIdx) (c : Std.U64) :
    LSP (arena.expr_ops.take_eidx_n xs c)
      (fun r => absEIdxArr r = takeEidx (absEIdxArr xs) c.val) := by
  intro r h
  have := ExprOps.take_eidx_n_refines h
  apply Array.ext'
  rw [takeEidx, ExprOps.eidxCopyUpto_toList (absEIdxArr xs) c.val c.val 0 #[] (by omega)]
  simp only [absEIdxArr, List.toList_toArray] at this ⊢
  simpa [ExprOps.absEIdxL] using this

@[lockstep] theorem fvl_copy_from_spec (xs : alloc.vec.Vec (Std.U64 × arena.handle.EIdx))
    (i : Std.Usize) (out : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) :
    LSP (arena.expr_ops.fvl_copy_from xs i out)
      (fun r => ExprOps.absFvlL r = ExprOps.absFvlL out ++ (ExprOps.absFvlL xs).drop i.val) :=
  fun _ h => ExprOps.fvl_copy_from_refines h

@[lockstep] theorem fvl_append_spec (x y : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) :
    LSP (arena.expr_ops.fvl_append x y)
      (fun r => ExprOps.absFvlL r = ExprOps.absFvlL x ++ ExprOps.absFvlL y) :=
  fun _ h => ExprOps.fvl_append_refines h

theorem leafMem_app' (l1 l2 : List (Nat × EIdx)) (i : Nat) (t : EIdx) :
    leafMem (l1 ++ l2) i t = (leafMem l1 i t || leafMem l2 i t) := by
  induction l1 with
  | nil => simp [leafMem]
  | cons p r ih =>
    rw [List.cons_append, ExprOps.leafMem_cons, ExprOps.leafMem_cons, ih, Bool.or_assoc]

/-- **`leafMem` is order blind**, which is what makes `fvar_leaves_go`'s
push-order deviation (the accumulator is the twin's list reversed) sound at its
one reader, `leaves_sub_go`. -/
@[lockstep_simp] theorem leafMem_reverse (l : List (Nat × EIdx)) (i : Nat) (t : EIdx) :
    leafMem l.reverse i t = leafMem l i t := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    rw [List.reverse_cons, leafMem_app', ih, ExprOps.leafMem_cons, ExprOps.leafMem_cons,
      leafMem, Bool.or_false, Bool.or_comm]

@[lockstep] theorem leaf_mem_spec (bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx))
    (idx : Std.U64) (ty : arena.handle.EIdx) :
    LSP (arena.expr_ops.leaf_mem bl idx ty)
      (fun r => r = leafMem (ExprOps.absFvlL bl) (absU idx) (absEIdx ty)) :=
  fun _ h => (ExprOps.leaf_mem_refines h).symm

@[lockstep] theorem expr_ptr_beq_spec (a b : arena.handle.EIdx) :
    LSP (arena.expr_ops.expr_ptr_beq a b) (fun r => r = exprPtrBEq (absEIdx a) (absEIdx b)) :=
  fun _ h => (ExprOps.expr_ptr_beq_refines h).symm

/-! ### Tag tests the `ExprOps` walks make (suffix `_eo`: the Core lane has its own copies) -/

@[lockstep_simp] theorem absU32_beq_fvar_eo (t : Std.U32) :
    (absU32 t == ETag.fvar) = decide (t = arena.handle.ETAG_FVAR) := by
  rw [← etag_fvar_abs]
  by_cases h : t = arena.handle.ETAG_FVAR
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_FVAR := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_const_eo (t : Std.U32) :
    (absU32 t == ETag.const) = decide (t = arena.handle.ETAG_CONST) := by
  rw [← etag_const_abs]
  by_cases h : t = arena.handle.ETAG_CONST
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_CONST := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_lit_eo (t : Std.U32) :
    (absU32 t == ETag.lit) = decide (t = arena.handle.ETAG_LIT) := by
  rw [← etag_lit_abs]
  by_cases h : t = arena.handle.ETAG_LIT
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_LIT := fun hc => h (absU32_inj hc)
    simp [h, this]

attribute [lockstep_simp] etag_fvar_abs etag_const_abs etag_lit_abs

/-! ## More reads and Rust-only steps of the `ExprOps` walks -/

@[lockstep] theorem view_fvar_ty_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.view_fvar_ty pers st h) st lst
      (Arena.viewFVarTy (absEIdx h)) :=
  LSV.ofSimR (fun _ hr => view_fvar_ty_run₀ hrel hr) hrel hinv

@[lockstep] theorem view_fvar_idx_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absU a) (arena.monad.view_fvar_idx pers st h) st lst
      (Arena.viewFVarIdx (absEIdx h)) :=
  LSV.ofSimR (fun _ hr => view_fvar_idx_run₀ hrel hr) hrel hinv

@[lockstep] theorem derived_l_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LIdx) :
    LSV pers (fun (a : arena.store.LDer) (b : LDer) => b.hasParam = a.has_param)
      (arena.monad.derived_l pers st h) st lst (Arena.derivedL (absLIdx h)) := by
  intro a ha
  obtain ⟨v, hx, hobs⟩ := derived_l_run₀ hrel ha
  exact ⟨v, lst, hx, hobs, hrel, hinv⟩

@[lockstep] theorem fvar_of_data_spec (w : Std.U64) :
    LSP (kernel.expr.fvar_of_data w) (fun r => r.val = w.val / 2 % 32768) :=
  fun _ h => ConRon.Refine.Expr.fvar_of_data_val h

/-- The public `AOut₀` statement of a read-only function from its `LSR`. -/
theorem LSR.toAOut₀ {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β} {o}
    (h : LSR pers (fun a b => b = A a) m st lst x) (hm : m = ok o) :
    AOut₀ A pers o st (x.run lst) := by
  have := h o hm
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨b, lst', hx, rfl, h1, h2⟩ := this
    exact ⟨lst', hx, h1, h2⟩

/-- A total Rust READ in the `LS` judgement (the `LSV` twin of `LSR.of_LS`). -/
theorem LSV.ofLS {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result α} {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : LS pers R (m >>= fun a => ok (.Ok a, st)) lst x) : LSV pers R m st lst x := by
  intro a hm
  exact h (.Ok a) st (by rw [hm, Aeneas.Std.bind_tc_ok])

/-- The public `SimR`-shaped statement of a total read from its `LSV`, when the
twin action leaves the state alone. -/
theorem LSV.toAOut₀ {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {m : Result α} {st : arena.monad.AState} {lst : AState} {x : AM β} {a : α}
    (h : LSV pers (fun a b => b = A a) m st lst x) (hm : m = ok a) :
    ∃ lst', x.run lst = .ok (A a, lst') ∧ AStateRel₀ pers st lst' ∧ AStateInv pers st := by
  obtain ⟨b, lst', hx, rfl, h1, h2⟩ := h a hm
  exact ⟨lst', hx, h1, h2⟩

/-! ### The three walk-local memos (`ExprOps/Pure.lean`'s relations) -/

@[lockstep] theorem wscoped_memo_get_spec {memo : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} (hm : ExprOps.WMemoRel memo lm) (k : arena.monad.EIdxNat) :
    LSP (arena.expr_ops.wscoped_memo_get memo k) (fun o => o = lm[absEIdxNat k]?) :=
  fun _ h => (ExprOps.wscoped_memo_get_refines hm.2 ConRon.Refine.HashMap2.KeysOk_true hm.1 h).symm

@[lockstep] theorem wscoped_memo_set_spec {memo : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} (hm : ExprOps.WMemoRel memo lm) (k : arena.monad.EIdxNat)
    (r : Bool) :
    LSP (arena.expr_ops.wscoped_memo_set memo k r)
      (fun m' => ExprOps.WMemoRel m' (lm.insert (absEIdxNat k) r)) := by
  intro m' h
  obtain ⟨h1, h2, -⟩ :=
    ExprOps.wscoped_memo_set_refines hm.2 ConRon.Refine.HashMap2.KeysOk_true hm.1 h
  exact ⟨h1, h2⟩

@[lockstep] theorem leaves_sub_get_spec {memo : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} (hm : ExprOps.LMemoRel memo lm) (k : arena.handle.EIdx) :
    LSP (arena.expr_ops.leaves_sub_get memo k) (fun o => o = lm[absEIdx k]?) :=
  fun _ h => (ExprOps.leaves_sub_get_refines hm.2 ConRon.Refine.HashMap2.KeysOk_true hm.1 h).symm

@[lockstep] theorem leaves_sub_set_spec {memo : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} (hm : ExprOps.LMemoRel memo lm) (k : arena.handle.EIdx)
    (r : Bool) :
    LSP (arena.expr_ops.leaves_sub_set memo k r)
      (fun m' => ExprOps.LMemoRel m' (lm.insert (absEIdx k) r)) := by
  intro m' h
  obtain ⟨h1, h2, -⟩ :=
    ExprOps.leaves_sub_set_refines hm.2 ConRon.Refine.HashMap2.KeysOk_true hm.1 h
  exact ⟨h1, h2⟩

@[lockstep] theorem fvl_seen_spec {seen : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashMap EIdx Unit} (hs : ExprOps.SeenRel seen ls) (k : arena.handle.EIdx) :
    LSP (arena.expr_ops.fvl_seen seen k) (fun b => b = (ls[absEIdx k]?).isSome) := by
  intro b h
  rw [ExprOps.fvl_seen_refines hs.2 ConRon.Refine.HashMap2.KeysOk_true hs.1 h,
    Std.HashMap.contains_eq_isSome_getElem?]

@[lockstep] theorem fvl_record_spec {seen : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashMap EIdx Unit} (hs : ExprOps.SeenRel seen ls) (k : arena.handle.EIdx) :
    LSP (arena.expr_ops.fvl_record seen k)
      (fun m' => ExprOps.SeenRel m' (ls.insert (absEIdx k) ())) := by
  intro m' h
  obtain ⟨h1, h2, -⟩ :=
    ExprOps.fvl_record_refines hs.2 ConRon.Refine.HashMap2.KeysOk_true hs.1 h
  exact ⟨h1, h2⟩

@[lockstep] theorem hashmap2_new_eidxnat_spec :
    LSP (ron.hashmap2.HashMap2.new arena.monad.EIdxNat Bool) (fun m => ExprOps.WMemoRel m ∅) := by
  intro m h
  obtain ⟨hnInv, -, hnNone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable) h
  exact ⟨ConRon.Refine.HashMap2.RelOn_empty hnNone, hnInv⟩

@[lockstep] theorem hashmap2_new_eidx_spec :
    LSP (ron.hashmap2.HashMap2.new arena.handle.EIdx Bool)
      (fun m => ExprOps.LMemoRel m ∅ ∧ ExprOps.SeenRel m ∅) := by
  intro m h
  obtain ⟨hnInv, -, hnNone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable) h
  exact ⟨⟨ConRon.Refine.HashMap2.RelOn_empty hnNone, hnInv⟩,
    ⟨ConRon.Refine.HashMap2.RelOn_empty hnNone, hnInv⟩⟩

/-! ### Casts and the `never` datum -/

@[lockstep] theorem lift_cast_u64_of_usize (x : Std.Usize) :
    LSP (lift (Std.UScalar.cast .U64 x)) (fun r => r.val = x.val) := by
  intro r h
  simp only [lift, Result.ok.injEq] at h
  subst h
  rw [Std.UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt ?_
  have h1 : x.val ≤ Std.Usize.max := by scalar_tac
  have hmax : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
    simp only [Std.Usize.max, Std.Usize.numBits, Std.UScalarTy.Usize_numBits_eq]
  have h64 : 2 ^ System.Platform.numBits ≤ 2 ^ 64 := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  have : Std.UScalarTy.U64.numBits = 64 := rfl
  rw [this]
  have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  omega

@[lockstep] theorem lift_cast_usize_of_u64 (x : Std.U64) :
    LSP (lift (Std.UScalar.cast .Usize x)) (fun r => r.val = x.val ∨ Std.Usize.max < x.val) := by
  intro r h
  simp only [lift, Result.ok.injEq] at h
  subst h
  by_cases hx : x.val ≤ Std.Usize.max
  · left
    rw [Std.UScalar.cast_val_eq, Std.UScalarTy.Usize_numBits_eq]
    refine Nat.mod_eq_of_lt ?_
    have hmax : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
      simp only [Std.Usize.max, Std.Usize.numBits, Std.UScalarTy.Usize_numBits_eq]
    have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
    omega
  · right; omega

@[lockstep] theorem max_u64_spec (a b : Std.U64) :
    LSP (kernel.expr.max_u64 a b) (fun r => r.val = max a.val b.val) := by
  intro r h
  rw [kernel.expr.max_u64] at h
  split at h <;> (have := Result.ok_injective h; subst this) <;> scalar_tac

/-- `kernel::expr_ops::sub_nat`: `Nat` subtraction (truncated at `0`). -/
@[lockstep] theorem sub_nat_spec (a b : Std.U64) :
    LSP (kernel.expr_ops.sub_nat a b) (fun r => r.val = a.val - b.val) := by
  intro r h
  rw [kernel.expr_ops.sub_nat] at h
  split at h
  · exact (ConRon.Refine.Nat.usub_val h).2
  · simp only [Result.ok.injEq] at h
    rw [← h]
    show (0 : Nat) = a.val - b.val
    scalar_tac

@[lockstep] theorem never_spec :
    LSP kernel.prop_when.never (fun r => ConRon.Refine.PropWhenWF r ∧
      ConRon.Refine.absPropWhen r = ConLeche.PropWhen.never) := by
  intro r h
  exact ⟨ConRon.Refine.PropWhenWF.never h,
    ConRon.Refine.PropWhen.absPropWhen_never (ConRon.Refine.PropWhen.never_shape h).2⟩

@[lockstep] theorem last_eidx_spec (xs : alloc.vec.Vec arena.handle.EIdx) (k : Std.Usize) :
    LSP (arena.expr_ops.last_eidx xs k)
      (fun r => absEIdxArr r = lastEidx (absEIdxArr xs) k.val) := by
  intro r h
  have := ExprOps.last_eidx_refines h
  simp only [ExprOps.absEIdxArr, ExprOps.absEIdxL] at this
  apply Array.ext'
  simp only [absEIdxArr, List.toList_toArray] at this ⊢
  rw [← this]

/-- `arena::monad::intern_e` (the view dispatcher) against `internE`, under the
view's own well-formedness (the literal's payload, the binder's datum). -/
@[lockstep] theorem intern_e_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.ENodeView)
    (hlit : ∀ l, v = .Lit l → ConRon.Refine.LiteralWF l)
    (hpw : ∀ ty b m, v = .Lam ty b m ∨ v = .ForallE ty b m → ConRon.Refine.PropWhenWF m.pw) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e pers st v) lst
      (Arena.internE (absENodeView v)) :=
  LS.ofSim₀ fun _ h => intern_e_run₀ hrel hinv v hlit hpw h

/-! ### The remaining memo probes, writes and clears (from `Specs.lean`'s `₀` lemmas) -/

@[lockstep] theorem inst1_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.inst1_clear st) lst Arena.inst1Clear :=
  LSW.ofSimS₀ fun _ h => inst1_clear_run₀ hrel hinv h

@[lockstep] theorem inst_l_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.inst_l_get st k) st lst
      (Arena.instLGet (absEIdxNat k)) :=
  LSV.ofSimR (fun _ h => inst_l_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem inst_l_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) (r : arena.handle.EIdx) :
    LSW pers (arena.monad.inst_l_set st k r) lst (Arena.instLSet (absEIdxNat k) (absEIdx r)) :=
  LSW.ofSimS₀ fun _ h => inst_l_set_run₀ hrel hinv h

@[lockstep] theorem inst_l_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.inst_l_clear st) lst Arena.instLClear :=
  LSW.ofSimS₀ fun _ h => inst_l_clear_run₀ hrel hinv h

@[lockstep] theorem lift_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.lift_clear st) lst Arena.liftClear :=
  LSW.ofSimS₀ fun _ h => lift_clear_run₀ hrel hinv h

@[lockstep] theorem reset_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.reset_get st k) st lst
      (Arena.resetGet (absEIdxNat k)) :=
  LSV.ofSimR (fun _ h => reset_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem reset_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) (r : arena.handle.EIdx) :
    LSW pers (arena.monad.reset_set st k r) lst (Arena.resetSet (absEIdxNat k) (absEIdx r)) :=
  LSW.ofSimS₀ fun _ h => reset_set_run₀ hrel hinv h

@[lockstep] theorem reset_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.reset_clear st) lst Arena.resetClear :=
  LSW.ofSimS₀ fun _ h => reset_clear_run₀ hrel hinv h

@[lockstep] theorem rename_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.rename_get st k) st lst
      (Arena.renameGet (absEIdxNat k)) :=
  LSV.ofSimR (fun _ h => rename_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem rename_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) (r : arena.handle.EIdx) :
    LSW pers (arena.monad.rename_set st k r) lst (Arena.renameSet (absEIdxNat k) (absEIdx r)) :=
  LSW.ofSimS₀ fun _ h => rename_set_run₀ hrel hinv h

@[lockstep] theorem rename_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.rename_clear st) lst Arena.renameClear :=
  LSW.ofSimS₀ fun _ h => rename_clear_run₀ hrel hinv h

@[lockstep] theorem abs1_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.abs1_get st k) st lst
      (Arena.abs1Get (absEIdxNat k)) :=
  LSV.ofSimR (fun _ h => abs1_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem abs1_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) (r : arena.handle.EIdx) :
    LSW pers (arena.monad.abs1_set st k r) lst (Arena.abs1Set (absEIdxNat k) (absEIdx r)) :=
  LSW.ofSimS₀ fun _ h => abs1_set_run₀ hrel hinv h

@[lockstep] theorem abs1_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.abs1_clear st) lst Arena.abs1Clear :=
  LSW.ofSimS₀ fun _ h => abs1_clear_run₀ hrel hinv h

@[lockstep] theorem lower_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.lower_get st k) st lst
      (Arena.lowerGet (absEIdxNat k)) :=
  LSV.ofSimR (fun _ h => lower_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem lower_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) (r : arena.handle.EIdx) :
    LSW pers (arena.monad.lower_set st k r) lst (Arena.lowerSet (absEIdxNat k) (absEIdx r)) :=
  LSW.ofSimS₀ fun _ h => lower_set_run₀ hrel hinv h

@[lockstep] theorem lower_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.lower_clear st) lst Arena.lowerClear :=
  LSW.ofSimS₀ fun _ h => lower_clear_run₀ hrel hinv h

@[lockstep] theorem inst1_l_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) :
    LSV pers (fun a b => b = Option.map absEIdx a) (arena.monad.inst1_l_get st k) st lst
      (Arena.inst1LGet (absEIdxNat k)) :=
  LSV.ofSimR (fun _ h => inst1_l_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem inst1_l_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.monad.EIdxNat) (r : arena.handle.EIdx) :
    LSW pers (arena.monad.inst1_l_set st k r) lst (Arena.inst1LSet (absEIdxNat k) (absEIdx r)) :=
  LSW.ofSimS₀ fun _ h => inst1_l_set_run₀ hrel hinv h

@[lockstep] theorem inst1_l_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.inst1_l_clear st) lst Arena.inst1LClear :=
  LSW.ofSimS₀ fun _ h => inst1_l_clear_run₀ hrel hinv h

@[lockstep] theorem bvar_b_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absU a) (arena.monad.bvar_b_get st k) st lst
      (Arena.bvarBGet (absEIdx k)) :=
  LSV.ofSimR (fun _ h => bvar_b_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem bvar_b_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.handle.EIdx) (r : Std.U64) :
    LSW pers (arena.monad.bvar_b_set st k r) lst (Arena.bvarBSet (absEIdx k) (absU r)) :=
  LSW.ofSimS₀ fun _ h => bvar_b_set_run₀ hrel hinv h

@[lockstep] theorem bvar_b_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.bvar_b_clear st) lst Arena.bvarBClear :=
  LSW.ofSimS₀ fun _ h => bvar_b_clear_run₀ hrel hinv h

@[lockstep] theorem fvar_b_get_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absU a) (arena.monad.fvar_b_get st k) st lst
      (Arena.fvarBGet (absEIdx k)) :=
  LSV.ofSimR (fun _ h => fvar_b_get_run₀ hrel hinv h) hrel hinv

@[lockstep] theorem fvar_b_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.handle.EIdx) (r : Std.U64) :
    LSW pers (arena.monad.fvar_b_set st k r) lst (Arena.fvarBSet (absEIdx k) (absU r)) :=
  LSW.ofSimS₀ fun _ h => fvar_b_set_run₀ hrel hinv h

@[lockstep] theorem fvar_b_clear_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSW pers (arena.monad.fvar_b_clear st) lst Arena.fvarBClear :=
  LSW.ofSimS₀ fun _ h => fvar_b_clear_run₀ hrel hinv h

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

/-! ## Interns (see the module note) -/

@[lockstep] theorem intern_e_bvar_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (i : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_bvar pers st i) lst
      (Arena.internBVarE (absU i)) :=
  LS.ofSim₀ fun _ h => intern_e_bvar_run₀ hrel hinv i h

@[lockstep] theorem intern_e_app_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f a : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_app pers st f a) lst
      (Arena.internAppE (absEIdx f) (absEIdx a)) :=
  LS.ofSim₀ fun _ h => intern_e_app_run₀ hrel hinv f a h

/-- `intern_e_lam` with its datum's `PropWhenWF` in context: the `₀` lemma.
Registered BEFORE the `sorry` statement below, so `lockstep` tries it first. -/
@[lockstep] theorem intern_e_lam_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t b : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (hpw : ConRon.Refine.PropWhenWF m.pw) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_lam pers st t b m) lst
      (Arena.internLamE (absEIdx t) (absEIdx b) (ConRon.Refine.absBinderMeta m)) :=
  LS.ofSim₀ fun _ h => intern_e_lam_run₀ hrel hinv t b m hpw h

/-- `intern_e_forall_e` with its datum's `PropWhenWF` in context. -/
@[lockstep] theorem intern_e_forall_e_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t b : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (hpw : ConRon.Refine.PropWhenWF m.pw) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_forall_e pers st t b m) lst
      (Arena.internForallEE (absEIdx t) (absEIdx b) (ConRon.Refine.absBinderMeta m)) :=
  LS.ofSim₀ fun _ h => intern_e_forall_e_run₀ hrel hinv t b m hpw h

@[lockstep] theorem intern_e_lam_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_lam pers st t b m) lst
      (Arena.internLamE (absEIdx t) (absEIdx b) (ConRon.Refine.absBinderMeta m)) :=
  sorry

@[lockstep] theorem intern_e_forall_e_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_forall_e pers st t b m) lst
      (Arena.internForallEE (absEIdx t) (absEIdx b) (ConRon.Refine.absBinderMeta m)) :=
  sorry

@[lockstep] theorem intern_e_let_e_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t v b : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_let_e pers st t v b) lst
      (Arena.internLetEE (absEIdx t) (absEIdx v) (absEIdx b)) :=
  LS.ofSim₀ fun _ h => intern_e_let_e_run₀ hrel hinv t v b h

@[lockstep] theorem intern_e_bind_i_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t : Std.U32) (ty b : arena.handle.EIdx) (m : arena.handle.BMIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_bind_i pers st t ty b m) lst
      (Arena.internBindIE (absU32 t) (absEIdx ty) (absEIdx b) (absBMIdx m)) :=
  LS.ofSim₀ fun _ h => intern_e_bind_i_run₀ hrel hinv t ty b m h

@[lockstep] theorem intern_e_proj_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (i : Std.U64) (s : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_proj pers st n i s) lst
      (Arena.internProjE (absNIdx n) (absU i) (absEIdx s)) :=
  LS.ofSim₀ fun _ h => intern_e_proj_run₀ hrel hinv n i s h

@[lockstep] theorem intern_e_fvar_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (idx : Std.U64) (ty : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_fvar pers st idx ty) lst
      (Arena.internFVarE (absU idx) (absEIdx ty)) :=
  LS.ofSim₀ fun _ h => intern_e_fvar_run₀ hrel hinv idx ty h

@[lockstep] theorem intern_e_sort_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (u : arena.handle.LIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_sort pers st u) lst
      (Arena.internSortE (absLIdx u)) :=
  LS.ofSim₀ fun _ h => intern_e_sort_run₀ hrel hinv u h

@[lockstep] theorem intern_e_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (us : arena.handle.LsIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_const pers st n us) lst
      (Arena.internConstE (absNIdx n) (absLsIdx us)) :=
  LS.ofSim₀ fun _ h => intern_e_const_run₀ hrel hinv n us h

@[lockstep] theorem intern_e_lit_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (l : kernel.expr.Literal) (hwf : ConRon.Refine.LiteralWF l) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_lit pers st l) lst
      (Arena.internLitE (ConRon.Refine.absLiteral l)) :=
  LS.ofSim₀ fun _ h => intern_e_lit_run₀ hrel hinv l hwf h

@[lockstep] theorem intern_l_node_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.LNodeView) :
    LS pers (fun a b => b = absLIdx a) (arena.monad.intern_l_node pers st v) lst
      (Arena.internLNode (absLNodeView v)) :=
  LS.ofSim₀ fun _ h => intern_l_node_run₀ hrel hinv v h

@[lockstep] theorem intern_ls_node_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : alloc.vec.Vec arena.handle.LIdx) :
    LS pers (fun a b => b = absLsIdx a) (arena.monad.intern_ls_node pers st v) lst
      (Arena.internLsNode (absLsNodeView v)) :=
  LS.ofSim₀ fun _ h => intern_ls_node_run₀ hrel hinv v h

@[lockstep] theorem intern_level_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (l : kernel.level.Level) (hwf : ConRon.Refine.LevelWF l) :
    LS pers (fun a b => b = absLIdx a) (arena.monad.intern_level pers st l) lst
      (Arena.internLevel (ConRon.Refine.absLevel l)) :=
  LS.ofSim₀ fun _ h => intern_level_run₀ hrel hinv hwf h

/-! ## Extension alternatives (task #97-T2-LOCKSTEP lane ExprOps)

Added as `macro_rules` rather than edits of the core's alternatives: a later
`macro_rules` is tried first, and falls back to the core's on failure. -/

namespace ConRon.Refine2.Lockstep

/-- The ExprOps walks' error arms: the `uncurry` repack must close outright
(`done`), and the Aeneas `let (st1, body) ← let (r2, st3) := y; …` shape is
reduced whole. -/
macro_rules
  | `(tactic| lockstep_errarm) => `(tactic| first
      | exact errArm_ok
      | (show ErrArm (ok _ >>= _) _; rw [bind_tc_ok]; exact errArm_ok)
      | (apply errArm_of_eq; simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]; try rfl; done)
      | (intro o st2 h; simp only [Aeneas.Std.uncurry_apply_pair, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at h; all_goals first | exact h.1.symm | exact h.symm)
      | (simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]; exact errArm_ok)
      | (intro o st2 h; simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair, Result.ok.injEq,
          Prod.mk.injEq] at h; obtain ⟨h1, -⟩ := h; exact h1.symm))

open Lean Elab Tactic in
/-- Fails unless the goal mentions a `==` (keeps the `beq_iff_eq` alternative
below off every other side goal: `simp_all` over a large context is dear). -/
elab "lockstep_guard_beq" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  unless t.containsConst (· == ``BEq.beq) do
    throwError "lockstep_guard_beq: no `==` in the goal"

/-- A twin test on a `==` of a decoded field (`(fvarOfData b).toNat == 0`) that
the Rust decided on its machine word: the decode facts in the context, the
`BEq` read as `=`, then arithmetic. -/
macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (lockstep_guard_beq; simp_all only [lockstep_simp, beq_iff_eq]; scalar_tac))

open Lean Meta Elab Tactic in
/-- A premise that is one part of a syntactic conjunction in the context (a
fresh walk memo's `LMemoRel a ∅ ∧ SeenRel a ∅`), matched at reducible
transparency, no case split. -/
elab "lockstep_and_part" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    -- the parts of a syntactic conjunction, as proof terms
    let rec parts (e t : Expr) (fuel : Nat) : List Expr :=
      match fuel, t.consumeMData with
      | f + 1, .app (.app (.const ``And _) a) b =>
        mkApp3 (mkConst ``And.left) a b e :: mkApp3 (mkConst ``And.right) a b e ::
          (parts (mkApp3 (mkConst ``And.left) a b e) a f ++
           parts (mkApp3 (mkConst ``And.right) a b e) b f)
      | _, _ => []
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      for (p : Expr) in parts d.toExpr t 4 do
        if ← withReducible (isDefEq (← inferType p) tgt) then
          g.assign p
          replaceMainGoal []
          return
    throwError "lockstep_and_part: no conjunct matches"

macro_rules
  | `(tactic| lockstep_side_ext) => `(tactic| lockstep_and_part)

end ConRon.Refine2.Lockstep
