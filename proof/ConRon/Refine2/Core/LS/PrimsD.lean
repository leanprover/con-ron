/-
# `ConRon.Refine2.Core.LS.PrimsD` — region D's primitive pairs

Task #97-P5-Core round 5, region D (`whnfApp`/`betaPeel`, `whnfCoreStuckApp`,
`whnfCoreBody`, `whnfCoreBodyGated`).  The `@[lockstep]` pairs the region's
zips need that no shared file carries: the mode reads, the handle comparison,
the projection-table lookup (and the abstraction of its entry).
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PD

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## The mode reads -/

@[lockstep] theorem beta_skip_ls (mode : kernel.env.CheckMode) (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.env.beta_skip mode pw)
      (fun b => b = (ConRon.Refine.absMode mode).betaSkip (ConRon.Refine.absPropWhen pw)) :=
  by
    intro b h
    cases mode
    · simp only [kernel.env.beta_skip, kernel.env.certs, kernel.env.beta_gate, bind_tc_ok,
        reduceIte] at h
      rw [ConRon.Refine.PropWhen.is_never_refines h]; rfl
    · simp only [kernel.env.beta_skip, kernel.env.certs, bind_tc_ok, Bool.false_eq_true,
        if_false, Result.ok.injEq] at h
      rw [← h]; rfl

 theorem verified_checks_ls (mode : kernel.env.CheckMode) :
    LSP (kernel.env.verified_checks mode)
      (fun b => b = (ConRon.Refine.absMode mode).verifiedChecks) :=
  by
    intro b h
    cases mode <;> (simp only [kernel.env.verified_checks, Result.ok.injEq] at h; rw [← h]; rfl)

 theorem beta_gate_ls (mode : kernel.env.CheckMode) :
    LSP (kernel.env.beta_gate mode)
      (fun b => b = (ConRon.Refine.absMode mode).betaGate) :=
  by
    intro b h
    cases mode <;> (simp only [kernel.env.beta_gate, Result.ok.injEq] at h; rw [← h]; rfl)

 theorem is_never_ls (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.prop_when.is_never pw)
      (fun b => b = (ConRon.Refine.absPropWhen pw).isNever) :=
  fun _ h => ConRon.Refine.PropWhen.is_never_refines h

/-! ## Handle comparisons -/

 theorem eidx_eq2_ls (a b : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = (absEIdx a == absEIdx b)) := by
  intro r h
  obtain ⟨w⟩ := a; obtain ⟨w'⟩ := b
  simp only [arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  by_cases hw : w = w'
  · subst hw; simp
  · have : absEIdx ⟨w⟩ ≠ absEIdx ⟨w'⟩ := fun hc => hw (by
      have := absEIdx_inj hc; cases this; rfl)
    simp [hw, this]

 theorem nidx_eq2_ls (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absNIdx a = absNIdx b)) := by
  intro r h
  obtain ⟨w⟩ := a; obtain ⟨w'⟩ := b
  simp only [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  by_cases hw : w = w'
  · subst hw; simp
  · have : absNIdx ⟨w⟩ ≠ absNIdx ⟨w'⟩ := fun hc => hw (by
      have := absNIdx_inj hc; cases this; rfl)
    simp [hw, this]

 theorem dup2_nidx (h : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_nidx _ _ he

 theorem fail_dangling_ls_spec (T : Type) :
    LSP (arena.monad.fail_dangling_ls T) (fun r => ∃ v, r = .Err (.Internal v)) := by
  intro r h
  rw [arena.monad.fail_dangling_ls] at h
  obtain ⟨s, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨v, fail_run h⟩

/-! ## Casts and lengths -/

@[lockstep] theorem lift_cast_usize_u64 (x : Std.Usize) :
    LSP (lift (UScalar.cast .U64 x)) (fun r => r.val = x.val) := by
  intro r h
  cases Result.ok_injective h
  refine Std.UScalar.cast_val_mod_pow_greater_numBits_eq _ _ ?_
  rw [UScalarTy.Usize_numBits_eq, UScalarTy.U64_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> omega

@[lockstep_simp] theorem absEIdxList_length (v : alloc.vec.Vec arena.handle.EIdx) :
    (ExprOps.absEIdxList v).length = v.val.length := by
  simp [ExprOps.absEIdxList]

@[lockstep_simp] theorem absEIdxArr_size (v : alloc.vec.Vec arena.handle.EIdx) :
    (absEIdxArr v).size = v.val.length := by
  simp [absEIdxArr, ExprOps.absEIdxL]

@[lockstep_simp] theorem absSz_vec_len {α : Type} (v : alloc.vec.Vec α) :
    absSz (alloc.vec.Vec.len v) = v.val.length := by
  simp [absSz]

@[lockstep_simp] theorem length_map_absNIdx (v : List arena.handle.NIdx) :
    (v.map absNIdx).length = v.length := List.length_map _

attribute [lockstep_simp] absConstT

/-- `absU` is the value (for a LOCAL `lockstep_simp` where a Rust-only index
step's fact is stated through `absU` and the cursor arithmetic through `.val`). -/
theorem absU_eq_val (x : Std.U64) : absU x = x.val := rfl

/-! ## Store reads -/

 theorem view_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absConstT a) (arena.monad.view_const pers st h) st lst
      (Arena.viewConst (absEIdx h)) := by
  intro o hrun
  exact ⟨_, lst, view_const_run₀ hrel hrun, rfl, hrel, hinv⟩

 theorem view_ls_len_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LsIdx) :
    LSV pers (fun a b => b = Option.map absSz a) (arena.monad.view_ls_len pers st h) st lst
      (Arena.viewLsLen (absLsIdx h)) := by
  intro o hrun
  exact ⟨_, lst, view_ls_len_run₀ hrel hrun, rfl, hrel, hinv⟩

/-! ## The projection table -/

/-- `arena::env::ifenv_find_proj` against `IFEnv.findProj?`: a store-level
step (it interns the table's reserved name). -/
 theorem ifenv_find_proj_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (sn : arena.handle.NIdx) (i : Std.U64) :
    LSS pers (fun a b => b = Option.map absIProjEntry a)
      (arena.env.ifenv_find_proj pers vis st.store fe sn i) st lst
      (lfe.findProj? (absNIdx sn) (absU i)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

end ConRon.Refine2.Lockstep.PD
