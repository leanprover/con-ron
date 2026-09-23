/-
# `ConRon.Refine2.Core.LS.PrimsG` — region G's primitive pairs (the annotation pass)

Task #97-P5-Core round 5, region G.  The `@[lockstep]` pairs the annotation
bodies (`annotate_body` and its binder loops) step through that no earlier
file provides: the binder stack's abstraction, the level read and its
zero-ness, the handle equalities, the `usize → u64` cast, and one pending
intern prim (`ifenv_find_proj`, which interns the projection table's
reserved name).
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PG

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## Abstractions -/

/-- The annotation loops' binder stack (`Vec<(EIdx, BinderMeta)>`, pushed
outermost first) as the twin's `Array (EIdx × BinderMeta)`. -/
def absStk (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    Array (EIdx × ConLeche.BinderMeta) :=
  (v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).toArray


/-! The containers normalise to `List.toArray (List.map …)`. -/

theorem absStk_eq (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    absStk v = (v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).toArray := rfl

theorem absEIdxArr_eq (v : alloc.vec.Vec arena.handle.EIdx) :
    absEIdxArr v = (v.val.map absEIdx).toArray := rfl

theorem absStk_size (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    (absStk v).size = v.val.length := by
  simp [absStk]

theorem vec_new_val {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl

theorem vec_len_abs {α : Type} (v : alloc.vec.Vec α) :
    absSz (alloc.vec.Vec.len v) = v.val.length := by
  simp [absSz]

theorem vec_len_val' {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.len v).val = v.val.length := by
  simp

@[lockstep_simp] theorem absBinderMeta_pw (m : kernel.expr.BinderMeta) :
    (ConRon.Refine.absBinderMeta m).pw = ConRon.Refine.absPropWhen m.pw := rfl

@[lockstep_simp] theorem absBinderMeta_mk (pw : kernel.prop_when.PropWhen) :
    ConRon.Refine.absBinderMeta { pw } = ⟨ConRon.Refine.absPropWhen pw⟩ := rfl

/-- The binder stack's index, as a twin fact about the twin's `stk[j]!`. -/
theorem stk_index_twin (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (i : Std.Usize) :
    LSP (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        (arena.handle.EIdx × kernel.expr.BinderMeta)) v i)
      (fun x => TwinEq ((absStk v)[i.val]!) (absEIdx x.1, ConRon.Refine.absBinderMeta x.2)) := by
  intro x h
  obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt h
  show _ = _
  simp [absStk, hb, ← hx]

@[lockstep_simp] theorem peel_fuel_val : (arena.core.PEEL_FUEL).val = peelFuel := by
  rw [arena.core.PEEL_FUEL, Arena.peelFuel]; rfl

/-! ## Rust-only steps -/

 theorem dup2_nidx (n : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 n) (fun m => m = n) :=
  fun _ hm => dupId_nidx _ _ hm

 theorem prop_when_dup_spec (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.prop_when.dup pw) (fun r => r = pw) :=
  fun _ h => ConRon.Refine.PropWhen.dup_eq h

 theorem binder_meta_dup_spec (m : kernel.expr.BinderMeta) :
    LSP (kernel.expr.binder_meta_dup m) (fun r => r = m) :=
  fun _ h => ConRon.Refine.Expr.binder_meta_dup_eq h

 theorem binder_meta_spec (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.expr.binder_meta pw) (fun r => r = { pw }) := by
  intro r h
  rw [kernel.expr.binder_meta] at h
  exact (Result.ok_injective h).symm

 theorem usize_cast_u64_spec (x : Std.Usize) :
    LSP (lift (Std.UScalar.cast .U64 x)) (fun r => r.val = x.val) := by
  intro r h
  cases Result.ok_injective h
  exact usize_cast_u64_val' x

 theorem eidx_eq2_spec (a b : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun c => c = (absEIdx a == absEIdx b)) := by
  intro c h
  rw [arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  by_cases hab : a.word = b.word
  · have : absEIdx a = absEIdx b := by simp [absEIdx, hab]
    simp [hab, this]
  · have : absEIdx a ≠ absEIdx b := fun he => hab (by
      have := absEIdx_inj he; rw [this])
    simp [hab, this]

 theorem nidx_eq2_spec (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun c => c = decide (absNIdx a = absNIdx b)) := by
  intro c h
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  by_cases hab : a.word = b.word
  · have : absNIdx a = absNIdx b := by simp [absNIdx, hab]
    simp [hab, this]
  · have : absNIdx a ≠ absNIdx b := fun he => hab (by
      have := absNIdx_inj he; rw [this])
    simp [hab, this]

/-- `level::zeroness_of` against the twin's pure `Level.zeronessOf`; the
level is well formed (`read_level_m_ls` says so). -/
 theorem zeroness_of_spec {l : kernel.level.Level} (hl : ConRon.Refine.LevelWF l) :
    LSP (kernel.level.zeroness_of l)
      (fun pw => ConRon.Refine.absPropWhen pw = ConLeche.Level.zeronessOf (ConRon.Refine.absLevel l)) :=
  fun pw h => (ConRon.Refine.ExprOps.zeroness_of_refines hl pw h).1

/-! ## Reads -/

/-- `arena::monad::read_level_m` against `Arena.readLevelM`, over
`AStateRel₀`; the level it answers is well formed (a representation fact of
the Rust store, `read_level_m_wf`). -/
 theorem read_level_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LIdx) :
    LS pers (fun a b => ConRon.Refine.LevelWF a ∧ b = ConRon.Refine.absLevel a)
      (arena.monad.read_level_m pers st h) lst (Arena.readLevelM (absLIdx h)) := by
  intro o st' hrun
  have hwf := read_level_m_wf hinv hrun
  rw [arena.monad.read_level_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lidx_eq2 hinv.caches.readLC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.readLC h trivial
  rw [← hto] at hrelk
  rw [readLevelM_run]
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hrelk
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := Result.ok_injective hrun
    simp only [Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    simp only [Option.map_some] at hrelk
    rw [← hrelk]
    have hne : n = x := by
      rw [ConRon.Refine.level_dup_eq] at hn; exact (Result.ok_injective hn).symm
    subst hne
    exact ⟨_, lst, rfl, ⟨hwf.1 n rfl, rfl⟩, hrel, hinv⟩
  | none =>
    rw [hrc] at hrun hrelk
    simp only [Option.map_none] at hrelk
    rw [← hrelk]
    obtain ⟨ls0, hls0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ls] at hls0
    have hls2 : ls0 = st.store.lss.ls := (Result.ok_injective hls0).symm
    subst hls2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hd := denote_l_abs hrel.store.lss.lvl hv
    have hdw := denote_l_wf hinv.store.lss.lvl hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun hd
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho := Result.ok_injective hrun
      simp only [Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      show AErrSim _ _
      rw [EStore.ls, ← hd]
      exact AErrSim.internal rfl
    | some x =>
      rw [hvc] at hrun hd hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨l3, hl3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨old, hm⟩ := p
      rw [dupId_lidx _ _ hk1] at hp
      have hl3e : l3 = x := by
        rw [ConRon.Refine.level_dup_eq] at hl3; exact (Result.ok_injective hl3).symm
      subst hl3e
      have ho := Result.ok_injective hrun
      simp only [Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      obtain ⟨h1, h2⟩ := memo_insert_step lidx_eq2 absLIdx_inj hinv.caches.readLC
        hrel.caches.readLC hp
      have hins := ConRon.Refine.HashMap2.insert_refines_wf lidx_eq2
        hinv.caches.readLC ConRon.Refine.HashMap2.KeysOk_true trivial hp
      have hvals := memo_insert_vals h2 hins.2.2.1 hinv.caches.readLVals (hdw l3 rfl)
      rw [EStore.ls, ← hd]
      exact ⟨_, { lst with caches := { lst.caches with
          readLC := lst.caches.readLC.insert (absLIdx h) (ConRon.Refine.absLevel l3) } },
        rfl, ⟨hdw l3 rfl, rfl⟩,
        { hrel with caches := { hrel.caches with readLC := h1 } },
        { hinv with caches := { hinv.caches with readLC := h2, readLVals := hvals } }⟩

/-! ## Interns — pending the foundation's intern slice -/

/-- `arena::env::ifenv_find_proj` (a store-level step: it interns the
reserved projection-table name) against `IFEnv.findProj?`.  The Rust store
argument `s` is named apart from the state `st` the caller rebuilds from
(`hs`), so that a second lookup on the store the first one returned
(`annotate_proj_at`) matches without unifying `?st.store` with a store. -/
@[lockstep] theorem ifenv_find_proj_ls {pers vis st fe lfe lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (s : arena.store.EStore) (hs : st.store = s)
    (t : arena.handle.NIdx) (i : Std.U64) :
    LSS pers (fun a b => b = Option.map absIProjEntry a)
      (arena.env.ifenv_find_proj pers vis s fe t i) st lst
      (lfe.findProj? (absNIdx t) (absU i)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

end ConRon.Refine2.Lockstep.PG
