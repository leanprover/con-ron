/-
# `ConRon.Refine2.Core.LS.PrimsA2` — region A2's primitive pairs

Task #97-P5-Core round 5, region A2 (the shape helpers and small loops).  The
`@[lockstep]` pairs `Core/LS/Shapes.lean` needs that no earlier file has:
the Rust-only value steps on binder data (`binder_meta_dup`, `prop_when::dup`,
`prop_when::beq`, `prop_when::is_never`, `verified_checks`, the `usize → u64`
cast, `NIdx` equality), the pin `pin_and`, the store-level name builders
(`proj_fn_name`, `ifenv_find_proj`) and the interns `intern_e_const` /
`intern_l_node`.  The interns and the name builders intern, so they are
stated here and wait on the foundation's intern slice.
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PA2

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep


/-! ## Rust-only value steps -/

@[lockstep] theorem verified_checks_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.verified_checks m)
      (fun b => b = (ConRon.Refine.absMode m).verifiedChecks) :=
  by
  intro b h
  cases m <;> (simp only [kernel.env.verified_checks, Result.ok.injEq] at h; rw [← h]; rfl)

@[lockstep] theorem binder_meta_dup_ls (m : kernel.expr.BinderMeta) :
    LSP (kernel.expr.binder_meta_dup m) (fun r => r = m) :=
  fun _ h => ConRon.Refine.Expr.binder_meta_dup_eq h

@[lockstep] theorem binder_meta_ls (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.expr.binder_meta pw) (fun r => r = { pw }) := by
  intro r h
  rw [kernel.expr.binder_meta] at h
  exact (Result.ok_injective h).symm

@[lockstep] theorem prop_when_dup_ls (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.prop_when.dup pw) (fun r => r = pw) :=
  fun _ h => ConRon.Refine.PropWhen.dup_eq h

@[lockstep] theorem prop_when_is_never_ls (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.prop_when.is_never pw)
      (fun b => b = (ConRon.Refine.absPropWhen pw).isNever) :=
  fun _ h => ConRon.Refine.PropWhen.is_never_refines h

/-- `prop_when::beq` is the twin's `==` on the abstraction, at two
canonical-form (`PropWhenWF`) data. -/
@[lockstep] theorem prop_when_beq_ls {a b : kernel.prop_when.PropWhen}
    (ha : ConRon.Refine.PropWhenWF a) (hb : ConRon.Refine.PropWhenWF b) :
    LSP (kernel.prop_when.beq a b)
      (fun c => c = (ConRon.Refine.absPropWhen a == ConRon.Refine.absPropWhen b)) := by
  intro c h
  have := ConRon.Refine.PropWhen.beq_iff (ConRon.Refine.PropWhen.wf_shape ha)
    (ConRon.Refine.PropWhen.wf_shape hb) h
  cases c <;> simp_all

/-- `usize as u64`: a widening, so the value is kept. -/
@[lockstep] theorem cast_u64_usize_ls (i : Std.Usize) :
    LSP (lift (UScalar.cast .U64 i)) (fun r : Std.U64 => r.val = i.val) := by
  intro r h
  simp only [lift, Result.ok.injEq] at h
  subst h
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have := i.hBounds
  simp only [UScalarTy.numBits] at this ⊢
  cases System.Platform.numBits_eq with
  | inl h => rw [h] at this; omega
  | inr h => rw [h] at this; omega

@[lockstep] theorem nidx_eq2_ls (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun o => o = (absNIdx a == absNIdx b)) := by
  intro o h
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absNIdx a ≠ absNIdx b := fun hc => hab (absNIdx_inj hc)
    simp [h1, h2]

@[lockstep] theorem dup2_nidx_ls (h : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun _ he => dupId_nidx _ _ he

@[lockstep] theorem dup2_lidx_ls (h : arena.handle.LIdx) :
    LSP (arena.handle.LIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun _ he => dupId_lidx _ _ he

@[lockstep] theorem dup2_lsidx_ls (h : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun _ he => dupId_lsidx _ _ he

@[lockstep] theorem cons_eidx_ls (a : arena.handle.EIdx) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.expr_ops.cons_eidx a xs)
      (fun r => absEIdxList r = absEIdx a :: absEIdxList xs) :=
  fun _ h => ExprOps.cons_eidx_refines h

@[lockstep] theorem snoc_eidx_of_ls (xs : alloc.vec.Vec arena.handle.EIdx) (y : arena.handle.EIdx) :
    LSP (arena.expr_ops.snoc_eidx_of xs y)
      (fun r => absEIdxList r = absEIdxList xs ++ [absEIdx y]) :=
  fun _ h => ExprOps.snoc_eidx_of_refines h

/-! ## The pin -/

@[lockstep] theorem pin_and_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_and st) st lst pinAnd := by
  intro o hrun
  rw [arena.pins.pin_and, arena.pins.pin_at] at hrun
  have hc : absSz arena.pins.PIN_AND = Arena.PIN_AND := by
    show (arena.pins.PIN_AND).val = _
    rw [arena.pins.PIN_AND]
    rfl
  show LOut pers _ o st ((Arena.pinAt Arena.PIN_AND).run lst)
  rw [← hc]
  generalize arena.pins.PIN_AND = i at hrun
  have hnames := hrel.pins.names
  have hlen : lst.pins.names.size = st.pins.names.val.length := by
    have h := congrArg List.length hnames
    simpa using h
  have hrun2 : (Arena.pinAt (absSz i)).run lst
      = (if h : absSz i < lst.pins.names.size
         then Except.ok (lst.pins.names[absSz i], lst)
         else Except.error
           (Arena.CheckError.internal "arena: reserved-name pins not interned")) := by
    by_cases h : absSz i < lst.pins.names.size
    · rw [dif_pos h]
      show (Arena.pinAt (absSz i)) lst = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, dif_pos h]
    · rw [dif_neg h]
      show (Arena.pinAt (absSz i)) lst = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, dif_neg h,
        Arena.fail, throwThe, MonadExceptOf.throw,
        Function.comp_apply, StateT.lift]
  split at hrun
  case isTrue hge =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 : core.result.Result.Err (T := arena.handle.NIdx)
        (kernel.core_types.CheckError.Internal cps) = o := Result.ok_injective hrun
    subst h2
    have hnl : ¬ (absSz i < lst.pins.names.size) := by
      rw [hlen]
      have hle : st.pins.names.val.length ≤ i.val := by scalar_tac
      show ¬ (i.val < st.pins.names.val.length)
      omega
    exact AErrSim.internal (s := "arena: reserved-name pins not interned")
      (by rw [hrun2, dif_neg hnl])
  case isFalse hlt =>
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨n1, hn1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : core.result.Result.Ok n1 = o := Result.ok_injective hrun
    subst h2
    rw [dupId_nidx _ _ hn1]
    obtain ⟨hlt2, rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hn
    have hlt3 : absSz i < lst.pins.names.size := by rw [hlen]; exact hlt2
    refine ⟨_, lst, ?_, rfl, hrel, hinv⟩
    rw [hrun2, dif_pos hlt3]
    have hi : lst.pins.names.toList[absSz i]? =
        (st.pins.names.val.map absNIdx)[absSz i]? := by rw [hnames]
    simp only [List.getElem?_map, Array.getElem?_toList] at hi
    have hsome : lst.pins.names[absSz i]? = some (absNIdx st.pins.names.val[absSz i]) := by
      simpa [hlt2] using hi
    rw [Array.getElem?_eq_getElem hlt3] at hsome
    rw [Option.some_inj.mp hsome]

/-! ## The name builders and the interns — pending the intern slice -/

end ConRon.Refine2.Lockstep.PA2
