/-
# `ConRon.Refine2.Inductives.SumInstall` — Theorem 2 for `arena::inductives::sum_install`

**Task #97-P5-Ind** (DESIGN.md §8.2); repaired by **task #105**.
`crates/con-ron-core/src/arena/inductives/sum_install.rs` against
`proof/ConRon/Arena/Inductives/SumInstall.lean`: the type former's
telescope and the constructors' stage, every
stage a check returning nothing.  `checkSumCtor` is ONE twin `def` and four Rust functions; the three tails are
`Refine2/Inductives/Spec.lean`'s `checkSumCtor{Frames,Resid,Sorts}Spec`, tied
back by `checkSumCtor_unfold`.  The per-field universe bound
(`check_struct_field_sorts_i`) is `Refine2/Inductives/StructInstall.lean`'s.

The Core tier arrives here: `check_sum_ctor` calls
`check_constant_val` (`Refine2/Checker/{KnotHyp,Base}.lean`).  `cons_sum_ctors` is PURE on both
sides (the index push touches no term).
-/
import ConRon.Refine2.Inductives.StructInstall
import ConRon.Refine2.Inductives.Prims
import ConRon.Refine2.Checker.LitFlags

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open scoped ConRon.Refine2.IndSide

open ConRon.Arena

/-! ## The type former's stage -/

open Lockstep in
/-- `check_sum_tele` ⊑ `checkSumTele` — the type former's telescope: `n` Π
binders ending in a sort.  The Rust reads the store by `&`, so it is a
reader (`LSR`). -/
@[lockstep] theorem check_sum_tele_ls
    {pers st lst}
    {n : Std.U64}
    {cv_ta0 : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (fun r => (absIConstantVal r.1, absLIdx r.2)) a)
      (arena.inductives.sum_install.check_sum_tele pers st n cv_ta0) st lst
      (checkSumTele (absU n) (absIConstantVal cv_ta0)) := by
  apply LSR.of_LS
  rw [arena.inductives.sum_install.check_sum_tele, checkSumTele]
  lockstep

/-! ## The constructors' stage -/

/-! ## `checkSumCtor`, split four ways (`Spec.lean`'s three `checkSumCtor…Spec`s) -/

open Lockstep in
/-- `field_doms_resolve` ⊑ `checkSumCtor`'s field-domain resolution, from the
cursor on. -/
@[lockstep] theorem field_doms_resolve_ls
    {pers st lst}
    {rf0 lf0}
    {x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf0 lf0) :
    LS pers (fun a b => b = id a) (arena.inductives.sum_install.field_doms_resolve pers st rf0 x_fvs i) lst
      (fieldDomsResolve lf0 (absEIdxLFrom x_fvs i)) := by
  revert st lst hrel hinv
  simp only [absEIdxLFrom]
  intro st lst hrel hinv
  refine ls_cursor x_fvs absEIdx (fieldDomsResolve lf0)
    (fun st i => arena.inductives.sum_install.field_doms_resolve pers st rf0 x_fvs i)
    ?_ ?_ i st lst hrel hinv
  · intro st lst i hn hrel hinv
    rw [arena.inductives.sum_install.field_doms_resolve.eq_def, fieldDomsResolve]
    rw [ite_eq_left (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    rw [arena.inductives.sum_install.field_doms_resolve.eq_def, fieldDomsResolve]
    rw [ite_eq_right (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
/-- `idx_args_resolve` ⊑ `checkSumCtor`'s index-expression resolution, from the
cursor on. -/
@[lockstep] theorem idx_args_resolve_ls
    {pers st lst}
    {rf0 lf0}
    {idx_args : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf0 lf0) :
    LS pers (fun a b => b = id a) (arena.inductives.sum_install.idx_args_resolve pers st rf0 idx_args i) lst
      (idxArgsResolve lf0 (absEIdxLFrom idx_args i)) := by
  revert st lst hrel hinv
  simp only [absEIdxLFrom]
  intro st lst hrel hinv
  refine ls_cursor idx_args absEIdx (idxArgsResolve lf0)
    (fun st i => arena.inductives.sum_install.idx_args_resolve pers st rf0 idx_args i)
    ?_ ?_ i st lst hrel hinv
  · intro st lst i hn hrel hinv
    rw [arena.inductives.sum_install.idx_args_resolve.eq_def, idxArgsResolve]
    rw [ite_eq_left (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    rw [arena.inductives.sum_install.idx_args_resolve.eq_def, idxArgsResolve]
    rw [ite_eq_right (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
/-- `check_sum_ctor_sorts` ⊑ `checkSumCtor`'s tail. -/
@[lockstep] theorem check_sum_ctor_sorts_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {n_p : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {n_f : Std.U64}
    {x_fvs idx_args : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI pers rf0 lf0)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True) (arena.inductives.sum_install.check_sum_ctor_sorts pers st mode rf0 rf n_p res_sort is_prop large n_f x_fvs idx_args) lst
      (checkSumCtorSortsSpec (ConRon.Refine.absMode mode) lf0 lf (absU n_p)
        (absLIdx res_sort) is_prop large (absU n_f)
        (absEIdxL x_fvs) (absEIdxL idx_args)) := by
  rw [arena.inductives.sum_install.check_sum_ctor_sorts, checkSumCtorSortsSpec]
  lockstep

open Lockstep in
/-- `check_sum_ctor_resid` ⊑ `checkSumCtor`'s residual stage. -/
@[lockstep] theorem check_sum_ctor_resid_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {n_f : Std.U64}
    {p_fvs x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI pers rf0 lf0)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True) (arena.inductives.sum_install.check_sum_ctor_resid pers st mode rf0 rf t lps n_p n_idx res_sort is_prop large n_f p_fvs x_fvs xrest) lst
      (checkSumCtorResidSpec (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absU n_f) (absEIdxL p_fvs) (absEIdxL x_fvs)
        (absEIdx xrest)) := by
  rw [arena.inductives.sum_install.check_sum_ctor_resid, checkSumCtorResidSpec]
  lockstep
  · -- the residual is the family at the parameters: the twin's test holds
    rename_i a3 a2 hT _ x hl1 hl2 k hk
    have e := absEIdxL_of_takeEidx hT
    have hb : List.map absEIdx a2.val = List.map absEIdx p_fvs.val := beq_iff_eq.mp hc
    simp only [absEIdxL] at e
    have hlen : a3.val.length = n_p.val + n_idx.val := by
      scalar_tac
    have hkk : k.val = n_p.val := by
      rcases hk with h | h
      · exact h
      · exfalso; have := a3.property; scalar_tac
    have hd : List.drop n_p.val (List.map absEIdx a3.val) = List.map absEIdx a.val := by
      have := hP; simp only [Lockstep.TwinEq, absEIdxL, hkk] at this; exact this
    rw [ite_eq_left (by simp [← e, hb, hlen]), hd]
    exact check_sum_ctor_sorts_ls hrel hinv hfe0 hfe
  · -- the parameter spine differs: both sides decline
    rename_i a3 a2 hT _ _ _
    have e := absEIdxL_of_takeEidx hT
    simp only [absEIdxL] at e
    have hne : ¬ (List.take n_p.val (List.map absEIdx a3.val) = List.map absEIdx p_fvs.val) := by
      rw [← e]; simpa using hc
    rw [ite_eq_right (by simp [hne])]
    lockstep

open Lockstep in
open scoped ConRon.Refine2.IndInstPrims in
/-- `check_sum_ctor_frames` ⊑ `checkSumCtor`'s frame stage. -/
@[lockstep] theorem check_sum_ctor_frames_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {n_f : Std.U64}
    {cv_ta cv_c : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI pers rf0 lf0)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True) (arena.inductives.sum_install.check_sum_ctor_frames pers st mode rf0 rf t lps n_p n_idx res_sort is_prop large n_f cv_ta cv_c) lst
      (checkSumCtorFramesSpec (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absU n_f) (absIConstantVal cv_ta) (absIConstantVal cv_c)) := by
  rw [arena.inductives.sum_install.check_sum_ctor_frames, checkSumCtorFramesSpec]
  lockstep

open Lockstep in
open scoped ConRon.Refine2.IndInstPrims in
/-- `check_sum_ctor` ⊑ `checkSumCtor` — stage 2, one constructor's type. -/
@[lockstep] theorem check_sum_ctor_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {cv_c : arena.env.IConstantVal}
    {n_f : Std.U64}
    {cv_ta : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI pers rf0 lf0)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True) (arena.inductives.sum_install.check_sum_ctor pers st mode rf0 rf t lps n_p n_idx res_sort is_prop large cv_c n_f cv_ta) lst
      (checkSumCtor (ConRon.Refine.absMode mode) lf0 lf (absNIdx t) (absNIdxL lps)
        (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absIConstantVal cv_c) (absU n_f) (absIConstantVal cv_ta)) := by
  rw [arena.inductives.sum_install.check_sum_ctor, checkSumCtor_unfold]
  lockstep

theorem check_sum_ctors_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf0 lf0 rf lf}
      {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
      {n_p n_idx : Std.U64} {res_sort : arena.handle.LIdx} {is_prop large : Bool}
      {cv_ta : arena.env.IConstantVal}
      {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize},
      ctors.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI pers rf0 lf0 → IFEnvRelI pers rf lf →
      Lockstep.LS pers (fun _ _ => True)
        (arena.inductives.sum_install.check_sum_ctors pers st mode rf0 rf t lps
          n_p n_idx res_sort is_prop large cv_ta ctors i) lst
        (checkSumCtors (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
          (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
          (absIConstantVal cv_ta) (absCtorsLFrom ctors i)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf0 lf0 rf lf t lps n_p n_idx res_sort is_prop large cv_ta ctors i
      hn hrel hinv hfe0 hfe
    rw [arena.inductives.sum_install.check_sum_ctors, ite_eq_left (by scalar_tac), absCtorsLFrom,
      vecFrom_nil _ _ _ (by omega), checkSumCtors]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf0 lf0 rf lf t lps n_p n_idx res_sort is_prop large cv_ta ctors i
      hn hrel hinv hfe0 hfe
    rw [arena.inductives.sum_install.check_sum_ctors, ite_eq_right (by scalar_tac), absCtorsLFrom,
      vecFrom_cons _ _ _ (by omega), checkSumCtors]
    lockstep

open Lockstep in
/-- `check_sum_ctors` ⊑ `checkSumCtors` from the cursor on. -/
@[lockstep] theorem check_sum_ctors_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {cv_ta : arena.env.IConstantVal}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI pers rf0 lf0)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True) (arena.inductives.sum_install.check_sum_ctors pers st mode rf0 rf t lps n_p n_idx res_sort is_prop large cv_ta ctors i) lst
      (checkSumCtors (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absIConstantVal cv_ta) (absCtorsLFrom ctors i)) :=
  check_sum_ctors_aux _ rfl hrel hinv hfe0 hfe

/-- `cons_sum_ctors` ⊑ `consSumCtors` from the cursor on — the constructors'
conses, in order (the first constructor deepest).  **Pure on both sides**: the
index push touches no term, so there is no monad and no state, and the
statement is an `IFEnvRel` of two folds. -/
theorem cons_sum_ctors_refines {pers : arena.store.PersTier} {n_p : Std.U64}
    {t : arena.handle.NIdx}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {rf lf} {o}
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.inductives.sum_install.cons_sum_ctors pers n_p t ctors i rf = ok o) :
    IFEnvRel pers o (consSumCtors (absU n_p) (absNIdx t) (absCtorsLFrom ctors i) lf) ∧
      IFEnvInv o := by
  refine cursor_induction (fun i : Std.Usize => i.val) ctors.val.length
    (fun i rf => ∀ lf o, IFEnvRel pers rf lf → IFEnvInv rf →
      arena.inductives.sum_install.cons_sum_ctors pers n_p t ctors i rf = ok o →
      IFEnvRel pers o (consSumCtors (absU n_p) (absNIdx t) (absCtorsLFrom ctors i) lf) ∧
        IFEnvInv o)
    ?_ ?_ i rf lf o hfe hfinv hrun
  · intro i rf hn lf o hfe hfinv h
    rw [arena.inductives.sum_install.cons_sum_ctors.eq_def] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ctors by scalar_tac)] at h
    obtain rfl := Result.ok_injective h
    rw [absCtorsLFrom, List.drop_eq_nil_of_le hn]
    exact ⟨hfe, hfinv⟩
  · intro i rf hi ih lf o hfe hfinv h
    rw [arena.inductives.sum_install.cons_sum_ctors.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ctors by scalar_tac)] at h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv, nf⟩ := p
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨tn, htn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨fe1, hfe1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx : ctors.val[i.val]? = some (iv, nf) := vec_index_some hp
    obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hrel1, hinv1⟩ := ifenv_push_refines (ci := .CtorInfo _ _ _ _) hfe hfinv hfe1
    have h3 : i3.val = i.val + 1 := by
      have := ConRon.Refine.Nat.uadd_val hi3; simpa using this
    have hdrop : absCtorsLFrom ctors i
        = (absIConstantVal iv, absU nf) :: absCtorsLFrom ctors i3 := by
      rw [absCtorsLFrom, absCtorsLFrom, h3,
        List.drop_eq_getElem_cons hb, hxv]
      simp
    rw [hdrop, consSumCtors]
    refine ih i3 fe1 h3 _ o ?_ hinv1 h
    have : absIConstantInfo (arena.env.IConstantInfo.CtorInfo iv1 n_p nf tn)
        = IConstantInfo.ctorInfo (absIConstantVal iv) (absU n_p) (absU nf) (absNIdx t) := by
      simp [absIConstantInfo, i_constant_val_dup_abs hiv1, dupId_nidx _ _ htn]
    rwa [this] at hrel1

open Lockstep in
/-- `cons_sum_ctors` against `consSumCtors`: a pure Rust-only step, the related
and well-formed environment after the folds. -/
@[lockstep] theorem cons_sum_ctors_ls {pers : arena.store.PersTier} {n_p : Std.U64}
    {t : arena.handle.NIdx}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {rf lf} (hfe : IFEnvRelI pers rf lf) :
    LSP (arena.inductives.sum_install.cons_sum_ctors pers n_p t ctors i rf)
      (fun o => IFEnvRelI pers o
        (consSumCtors (absU n_p) (absNIdx t) (absCtorsLFrom ctors i) lf)) :=
  fun _ h => cons_sum_ctors_refines hfe.rel hfe.inv h

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.check_sum_ctor_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_sum_ctor_ls

/-- info: 'ConRon.Refine2.cons_sum_ctors_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cons_sum_ctors_refines

end ConRon.Refine2
