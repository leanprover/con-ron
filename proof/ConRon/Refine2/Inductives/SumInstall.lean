/-
# `ConRon.Refine2.Inductives.SumInstall` — Theorem 2 for `arena::inductives::sum_install`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/sum_install.rs` against
`proof/ConRon/Arena/Inductives/SumInstall.lean`: official's telescope loop,
the type former's stage, the per-field universe bound, official's positivity
walk as a normalisation, the constructors' stage and the stored rules.

**Twenty-four `pub fn`s against fourteen twin `def`s.**  Ten of the
twenty-four are DESIGN §3.4's rules — the `check_sum_ctor` split three ways,
the two `allM`s under it, `check_sum_ind`'s tail, `field_sort_bound`,
`norm_pos_dom_at`, `eidx_contains` — and `Refine2/Inductives/Spec.lean`
carries every transcription.

**This is the module where `KnotRel` arrives in force.**  `whnf_telescope`
calls `whnf`, `check_struct_field_sorts_i` calls `infer_type_core` and
`ensure_sort_core`, `norm_pos_dom` calls `whnf`, and `check_sum_tele_slow` and
`norm_ctor_val` call `check_constant_val`, which is `arena::checker_base`'s
over the knot.  **Eleven statements carry `KnotRel checkFuel`** and **eleven
carry finding 10's `hvis`**.

**Two shapes are worth naming.**  `zip_fvar_doms` is the tier's only `SimRE`
— it takes `&AState` and can decline, with no state in the return at all,
which is exactly what task #97-P5-Checker's §1 added that shape for; and
`cons_sum_ctors` is PURE on both sides (the index push touches no term), so
its statement is the `IFEnvRel` of two pushes and carries no monad.
-/
import ConRon.Refine2.Inductives.StructInstallF

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The type former's stage -/

/-- `whnf_telescope` ⊑ `whnfTelescope`, with the accumulated binders in front
— **official's telescope loop** (`check_inductive_types`): peel `n` Π binders
off `e`, reducing the residual to weak head normal form before each binder and
at the end, where it must be a sort. -/
theorem whnf_telescope_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {i n : Std.U64} {e : arena.handle.EIdx}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.whnf_telescope pers vis st mode rf i n e out
      = ok o) :
    Sim₀ (fun r => (absBinderL r.1, absLIdx r.2)) pers lst o
      (do
        let q ← whnfTelescope (ConRon.Refine.absMode mode) lf (absU i) (absU n)
          (absEIdx e)
        pure (absBinderL out ++ q.1, q.2)) := by
  sorry

/-- `close_telescope` ⊑ `closeTelescope` from the cursor on: close a telescope
opened at the free variables `i ..< i + bs.length` back into a syntactic
Π-telescope over `body`. -/
theorem close_telescope_refines {pers st lst}
    {bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize} {i : Std.U64} {body : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.sum_install.close_telescope pers st bs k i body = ok o) :
    Sim₀ absEIdx pers lst o
      (closeTelescope (absBinderLFrom bs k) (absU i) (absEIdx body)) := by
  sorry

/-- `check_sum_tele_slow` ⊑ `checkSumTele`'s `where` clause — the `_` arm of
its match, named on both sides because over handles the syntactic test is two
`view`s and duplicating the arm would duplicate the whnf loop. -/
theorem check_sum_tele_slow_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {n : Std.U64}
    {cv_ta0 : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.check_sum_tele_slow pers vis st mode rf cv n
      cv_ta0 = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absLIdx r.2)) pers lst o
      (checkSumTele.checkSumTeleSlow (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absU n) (absIConstantVal cv_ta0)) := by
  sorry

/-- `check_sum_tele` ⊑ `checkSumTele` — the type former's TELESCOPE
(con-leche's task #195): the checked declared type when it is already a
syntactic telescope of `n` Π binders ending in a sort, else the declared
type's whnf'd telescope, closed and checked in its place. -/
theorem check_sum_tele_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {n : Std.U64}
    {cv_ta0 : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.check_sum_tele pers vis st mode rf cv n
      cv_ta0 = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absLIdx r.2)) pers lst o
      (checkSumTele (ConRon.Refine.absMode mode) lf (absIConstantVal cv) (absU n)
        (absIConstantVal cv_ta0)) := by
  sorry

/-- `native_caps_at` ⊑ `nativeCapsAt` — the capabilities a block on the
fixpoint route earns (con-leche's task #210 Part A).  Twinned in
`SumInstall.lean` rather than in `NativeInstall.lean` because `checkSumInd`
calls it where con-leche passes it in as a closure. -/
theorem native_caps_at_refines {pers st lst}
    {p : arena.inductives.sum_parts.InductiveShape} {is_rec : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.sum_install.native_caps_at pers st p is_rec = ok o) :
    Sim₀ absIIndCaps pers lst o
      (nativeCapsAt (absInductiveShape p) is_rec) := by
  sorry

/-- `check_sum_ind_at` ⊑ `checkSumInd`'s tail past `checkSumTele`. -/
theorem check_sum_ind_at_refines {pers st lst} {rf lf}
    {p : arena.inductives.sum_parts.InductiveShape} {is_rec : Bool}
    {cv_ta : arena.env.IConstantVal} {s : arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.inductives.sum_install.check_sum_ind_at pers st rf p is_rec cv_ta s
      = ok o) :
    SimRel₀ (fun r v => IFEnvRel r.1 v.1 ∧ v.2.1 = absIConstantVal r.2.1 ∧
        v.2.2 = absInductiveShape r.2.2)
      pers lst o
      (checkSumIndAtSpec lf (absInductiveShape p) is_rec (absIConstantVal cv_ta)
        (absLIdx s)) := by
  sorry

/-- `check_sum_ind` ⊑ `checkSumInd` — stage 1: the type former, stored with
the block's capability record at its telescope. -/
theorem check_sum_ind_refines {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p : arena.inductives.sum_parts.InductiveShape} {is_rec : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.check_sum_ind pers st mode rf p is_rec
      = ok o) :
    SimRel₀ (fun r v => IFEnvRel r.1 v.1 ∧ v.2.1 = absIConstantVal r.2.1 ∧
        v.2.2 = absInductiveShape r.2.2)
      pers lst o
      (checkSumInd (ConRon.Refine.absMode mode) lf (absInductiveShape p) is_rec) := by
  sorry

/-! ## The constructors' stage -/

/-- `eidx_contains` ⊑ `idxArgs.contains fv` from the cursor on — handles, so
`==` is word equality and the test transfers by `absEIdx`'s injectivity. -/
theorem eidx_contains_refines {xs : alloc.vec.Vec arena.handle.EIdx}
    {x : arena.handle.EIdx} {i : Std.Usize} {o}
    (hrun : arena.inductives.sum_install.eidx_contains xs x i = ok o) :
    o = (absEIdxLFrom xs i).contains (absEIdx x) := by
  simp only [absEIdxLFrom, List.contains_eq_any_beq, List.any_map, Function.comp_def]
  refine vec_cursor_any xs _
    (arena.inductives.sum_install.eidx_contains xs x) ?_ ?_ i o hrun
  · intro i o hn h
    rw [arena.inductives.sum_install.eidx_contains.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [← h]
  · intro i y o hy h
    have hlt : i.val < xs.val.length := (List.getElem?_eq_some_iff.mp hy).1
    rw [arena.inductives.sum_install.eidx_contains.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hey : e = y := by
      have h1 := vec_index_some he; rw [hy] at h1; exact (Option.some_inj.mp h1).symm
    subst hey
    have hbv : b = (absEIdx x == absEIdx e) := by
      rw [eidx_eq2_abs hb]
      by_cases hcc : absEIdx e = absEIdx x
      · simp [hcc]
      · have hcc' : ¬ absEIdx x = absEIdx e := fun z => hcc z.symm
        simp [hcc, hcc']
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨hbv.symm, h.symm⟩

/-- `field_sort_bound` ⊑ `checkStructFieldSortsI`'s per-field universe
bound. -/
theorem field_sort_bound_refines {pers st lst} {is_prop large : Bool}
    {s u : arena.handle.LIdx} {fv : arena.handle.EIdx}
    {idx_args : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.sum_install.field_sort_bound pers st is_prop large s u
      fv idx_args = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (fieldSortBoundSpec is_prop large (absLIdx s) (absLIdx u) (absEIdx fv)
        (absEIdxL idx_args)) := by
  sorry

/-- `check_struct_field_sorts_i` ⊑ `checkStructFieldSortsI` — the fields'
sorts over the opened constructor telescope, with the official per-field
universe bound unless the family is propositional.  Walks the fields from the
last to the first and returns the sorts in field order, which is why the
counter is the twin's `j + 1` recursion. -/
theorem check_struct_field_sorts_i_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {is_prop large : Bool} {s : arena.handle.LIdx}
    {n_p : Std.U64} {fvs idx_args : alloc.vec.Vec arena.handle.EIdx}
    {k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.check_struct_field_sorts_i pers vis st mode
      rf is_prop large s n_p fvs idx_args k = ok o) :
    Sim₀ absLIdxL pers lst o
      (checkStructFieldSortsI (ConRon.Refine.absMode mode) lf is_prop large
        (absLIdx s) (absU n_p) (absEIdxL fvs) (absEIdxL idx_args) (absU k)) := by
  sorry

/-! ## Official's positivity walk, as a normalisation -/

/-- `norm_pos_dom_at` ⊑ `normPosDom`'s arm past the two occurrence tests and
the whnf. -/
theorem norm_pos_dom_at_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {t : arena.handle.NIdx} {d fuel : Std.U64}
    {w : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.norm_pos_dom_at pers vis st mode rf t d fuel
      w = ok o) :
    Sim₀ absEIdx pers lst o
      (normPosDomAtSpec (ConRon.Refine.absMode mode) lf (absNIdx t) (absU d)
        (absU fuel) (absEIdx w)) := by
  sorry

/-- `norm_pos_dom` ⊑ `normPosDom`. -/
theorem norm_pos_dom_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {t : arena.handle.NIdx} {d fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.norm_pos_dom pers vis st mode rf t d fuel e
      = ok o) :
    Sim₀ absEIdx pers lst o
      (normPosDom (ConRon.Refine.absMode mode) lf (absNIdx t) (absU d) (absU fuel)
        (absEIdx e)) := by
  sorry

/-- `norm_field_doms` ⊑ `normFieldDoms`, with the accumulated binders in
front. -/
theorem norm_field_doms_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {t : arena.handle.NIdx} {i n : Std.U64}
    {h : arena.handle.EIdx}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.norm_field_doms pers vis st mode rf t i n h
      out = ok o) :
    Sim₀ (fun r => (absBinderL r.1, absEIdx r.2)) pers lst o
      (do
        let q ← normFieldDoms (ConRon.Refine.absMode mode) lf (absNIdx t) (absU i)
          (absU n) (absEIdx h)
        pure (absBinderL out ++ q.1, q.2)) := by
  sorry

/-- `zip_fvar_doms` ⊑ `zipFvarDoms` from the cursor on, with the accumulated
pairs in front.  **The tier's one `SimRE`**: the Rust takes `&AState` and can
decline, with no state in the return at all. -/
theorem zip_fvar_doms_refines {pers st lst} {xs : alloc.vec.Vec arena.handle.EIdx}
    {bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.sum_install.zip_fvar_doms pers st xs bs i out = ok o) :
    SimRE absBinderL lst o
      (do pure (absBinderL out ++
        (← zipFvarDoms (absEIdxLFrom xs i) (absBinderLFrom bs i)))) := by
  sorry

/-- `norm_ctor_val` ⊑ `normCtorVal` — the checked constructor with its field
domains normalised, closed back into a telescope and, when anything changed,
checked as the constructor's type in its place, from scratch. -/
theorem norm_ctor_val_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {t : arena.handle.NIdx} {n_p n_f : Std.U64}
    {cv_c cv_ca : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.norm_ctor_val pers vis st mode rf t n_p n_f
      cv_c cv_ca = ok o) :
    Sim₀ absIConstantVal pers lst o
      (normCtorVal (ConRon.Refine.absMode mode) lf (absNIdx t) (absU n_p) (absU n_f)
        (absIConstantVal cv_c) (absIConstantVal cv_ca)) := by
  sorry

/-! ## `checkSumCtor`, split four ways -/

/-- `field_doms_resolve` ⊑ `checkSumCtor`'s field-domain resolution, from the
cursor on. -/
theorem field_doms_resolve_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {x_fvs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.sum_install.field_doms_resolve pers vis st rf0 x_fvs i
      = ok o) :
    Sim₀ id pers lst o
      (fieldDomsResolveSpec lf0 (absEIdxLFrom x_fvs i)) := by
  sorry

/-- `idx_args_resolve` ⊑ `checkSumCtor`'s index-expression resolution, from the
cursor on. -/
theorem idx_args_resolve_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {idx_args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.sum_install.idx_args_resolve pers vis st rf0 idx_args i
      = ok o) :
    Sim₀ id pers lst o
      (idxArgsResolveSpec lf0 (absEIdxLFrom idx_args i)) := by
  sorry

/-- `check_sum_ctor_sorts` ⊑ `checkSumCtor`'s tail. -/
theorem check_sum_ctor_sorts_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf0 lf0} {rf lf} {n_p : Std.U64} {res_sort : arena.handle.LIdx}
    {is_prop large : Bool} {n_f : Std.U64} {cv_ca : arena.env.IConstantVal}
    {x_fvs idx_args : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe0 : IFEnvRel rf0 lf0) (hfinv0 : IFEnvInv rf0)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.check_sum_ctor_sorts pers st mode rf0 rf n_p
      res_sort is_prop large n_f cv_ca x_fvs idx_args = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absLIdxL r.2)) pers lst o
      (checkSumCtorSortsSpec (ConRon.Refine.absMode mode) lf0 lf (absU n_p)
        (absLIdx res_sort) is_prop large (absU n_f) (absIConstantVal cv_ca)
        (absEIdxL x_fvs) (absEIdxL idx_args)) := by
  sorry

/-- `check_sum_ctor_resid` ⊑ `checkSumCtor`'s residual stage. -/
theorem check_sum_ctor_resid_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf0 lf0} {rf lf} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx} {is_prop large : Bool} {n_f : Std.U64}
    {cv_ca : arena.env.IConstantVal}
    {p_fvs x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe0 : IFEnvRel rf0 lf0) (hfinv0 : IFEnvInv rf0)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.check_sum_ctor_resid pers st mode rf0 rf t
      lps n_p n_idx res_sort is_prop large n_f cv_ca p_fvs x_fvs xrest = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absLIdxL r.2)) pers lst o
      (checkSumCtorResidSpec (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absU n_f) (absIConstantVal cv_ca) (absEIdxL p_fvs) (absEIdxL x_fvs)
        (absEIdx xrest)) := by
  sorry

/-- `check_sum_ctor_frames` ⊑ `checkSumCtor`'s frame stage. -/
theorem check_sum_ctor_frames_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf0 lf0} {rf lf} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx} {is_prop large : Bool} {n_f : Std.U64}
    {cv_ta cv_ca : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe0 : IFEnvRel rf0 lf0) (hfinv0 : IFEnvInv rf0)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.check_sum_ctor_frames pers st mode rf0 rf t
      lps n_p n_idx res_sort is_prop large n_f cv_ta cv_ca = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absLIdxL r.2)) pers lst o
      (checkSumCtorFramesSpec (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absU n_f) (absIConstantVal cv_ta) (absIConstantVal cv_ca)) := by
  sorry

/-- `check_sum_ctor` ⊑ `checkSumCtor` — stage 2, one constructor's type. -/
theorem check_sum_ctor_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf0 lf0} {rf lf} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx} {is_prop large : Bool}
    {cv_c : arena.env.IConstantVal} {n_f : Std.U64}
    {cv_ta : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe0 : IFEnvRel rf0 lf0) (hfinv0 : IFEnvInv rf0)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.check_sum_ctor pers st mode rf0 rf t lps n_p
      n_idx res_sort is_prop large cv_c n_f cv_ta = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absLIdxL r.2)) pers lst o
      (checkSumCtor (ConRon.Refine.absMode mode) lf0 lf (absNIdx t) (absNIdxL lps)
        (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absIConstantVal cv_c) (absU n_f) (absIConstantVal cv_ta)) := by
  sorry

/-- `check_sum_ctors` ⊑ `checkSumCtors` from the cursor on, with the
accumulated constructors and sort lists in front. -/
theorem check_sum_ctors_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf0 lf0} {rf lf} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx} {is_prop large : Bool}
    {cv_ta : arena.env.IConstantVal}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {sout : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe0 : IFEnvRel rf0 lf0) (hfinv0 : IFEnvInv rf0)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install.check_sum_ctors pers st mode rf0 rf t lps
      n_p n_idx res_sort is_prop large cv_ta ctors i out sout = ok o) :
    Sim₀ (fun r => (absCtorsL r.1, absLIdxLL r.2)) pers lst o
      (do
        let q ← checkSumCtors (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
          (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
          (absIConstantVal cv_ta) (absCtorsLFrom ctors i)
        pure (absCtorsL out ++ q.1, absLIdxLL sout ++ q.2)) := by
  sorry

/-- `cons_sum_ctors` ⊑ `consSumCtors` from the cursor on — the constructors'
conses, in order (the first constructor deepest).  **Pure on both sides**: the
index push touches no term, so there is no monad and no state, and the
statement is an `IFEnvRel` of two folds. -/
theorem cons_sum_ctors_refines {n_p : Std.U64}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {rf lf} {o}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.inductives.sum_install.cons_sum_ctors n_p ctors i rf = ok o) :
    IFEnvRel o (consSumCtors (absU n_p) (absCtorsLFrom ctors i) lf) ∧
      IFEnvInv o := by
  refine cursor_induction (fun i : Std.Usize => i.val) ctors.val.length
    (fun i rf => ∀ lf o, IFEnvRel rf lf → IFEnvInv rf →
      arena.inductives.sum_install.cons_sum_ctors n_p ctors i rf = ok o →
      IFEnvRel o (consSumCtors (absU n_p) (absCtorsLFrom ctors i) lf) ∧ IFEnvInv o)
    ?_ ?_ i rf lf o hfe hfinv hrun
  · intro i rf hn lf o hfe hfinv h
    rw [arena.inductives.sum_install.cons_sum_ctors.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ctors by scalar_tac)] at h
    obtain rfl := Result.ok_injective h
    rw [absCtorsLFrom, List.drop_eq_nil_of_le hn]
    exact ⟨hfe, hfinv⟩
  · intro i rf hi ih lf o hfe hfinv h
    rw [arena.inductives.sum_install.cons_sum_ctors.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ctors by scalar_tac)] at h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv, nf⟩ := p
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨fe1, hfe1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx : ctors.val[i.val]? = some (iv, nf) := vec_index_some hp
    obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hrel1, hinv1⟩ := ifenv_push_refines hfe hfinv hfe1
    have h3 : i3.val = i.val + 1 := by
      have := ConRon.Refine.Nat.uadd_val hi3; simpa using this
    have hdrop : absCtorsLFrom ctors i
        = (absIConstantVal iv, absU nf) :: absCtorsLFrom ctors i3 := by
      rw [absCtorsLFrom, absCtorsLFrom, h3,
        List.drop_eq_getElem_cons hb, hxv]
      simp
    rw [hdrop, consSumCtors]
    refine ih i3 fe1 h3 _ o ?_ hinv1 h
    have : absIConstantInfo (arena.env.IConstantInfo.CtorInfo iv1 n_p nf)
        = IConstantInfo.ctorInfo (absIConstantVal iv) (absU n_p) (absU nf) := by
      simp [absIConstantInfo, i_constant_val_dup_abs hiv1]
    rwa [this] at hrel1

/-- `sum_rules` ⊑ `sumRules` from the cursor on, with the accumulated rules in
front. -/
theorem sum_rules_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rec_name : arena.handle.NIdx} {n_p m_i r_p : Std.U64}
    {rec_ty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {rhss : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.inductives.sum_install.sum_rules pers vis st rf rec_name n_p m_i
      r_p rec_ty ctors rhss i out = ok o) :
    Sim₀ absIRecRuleL pers lst o
      (do pure (absIRecRuleL out ++
        (← sumRules lf (absNIdx rec_name) (absU n_p) (absU m_i) (absU r_p)
          (absEIdx rec_ty) (absCtorsLFrom ctors i) (absEIdxLFrom rhss i)))) := by
  sorry

/-! ## The axiom census

`cons_sum_ctors_refines` is round 3 §R3.5's `ifenv_push` obligation cashed:
`Refine2/Checker/Shape.lean`'s `ifenv_push_refines` landed in round 4's second
`arena` merge, and this is the fold that was waiting on it. -/

/-- info: 'ConRon.Refine2.cons_sum_ctors_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cons_sum_ctors_refines

end ConRon.Refine2
