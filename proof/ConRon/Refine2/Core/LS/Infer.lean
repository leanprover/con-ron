/-
# `ConRon.Refine2.Core.LS.Infer` — region E: the inference bodies in lockstep

Task #97-P5-Core round 5, region E.  The Theorem-2 lockstep lemmas of
`arena::core`'s inference: the two bodies (`infer_body`, `infer_body_io`,
`BodyRel`'s `infer` / `inferIO` fields), the λ- and ∀-telescope loops
(`infer_lams`, `infer_pis` and their leaves), and the application spine
(`infer_spine`, `infer_spine_io`, `infer_app`, `infer_app_io_at`).
-/
import ConRon.Refine2.Core.LS.PrimsE

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PE

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

/-- Region A2: `head_and_args` against `headAndArgs`. -/
@[lockstep] theorem stub_head_and_args_ls {pers st v lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (absEIdx a.1, absEIdxArr a.2))
      (arena.core.head_and_args pers st v) st lst (headAndArgs (absEIdx v)) := by
  sorry

/-- Region A2: `infer_lam_result` against `inferLamResult`. -/
@[lockstep] theorem stub_infer_lam_result_ls {pers st ty bt depth mb lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_lam_result pers st ty bt depth mb) lst
      (inferLamResult (absEIdx ty) (absEIdx bt) (absU depth)
        (ConRon.Refine.absBinderMeta mb)) := by
  sorry

/-- Region A2: `infer_lams_out` against `inferLamsOut`.  The two `PropWhenWF`
premises are what `prop_when::beq` needs (see `PrimsE.lean`); a statement
without them is at least as strong for the consumer. -/
@[lockstep] theorem stub_infer_lams_out_ls {pers st mode d stk n cur prev_pw lst}
    (hx : ExprOpsHyp pers)
    (hstk : ∀ p ∈ (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)).val,
      ConRon.Refine.PropWhenWF p.2.pw)
    (hpw : ConRon.Refine.PropWhenWF prev_pw)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_lams_out pers st mode d stk n cur prev_pw) lst
      (inferLamsOut (ConRon.Refine.absMode mode) (absU d) (absLamStk stk) (absSz n)
        (absEIdx cur) (ConRon.Refine.absPropWhen prev_pw)) := by
  sorry

/-- Region A2: `infer_pis_out` against `inferPisOut`. -/
@[lockstep] theorem stub_infer_pis_out_ls {pers st mode stk n v pv lst}
    (hstk : ∀ p ∈ (stk : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)).val,
      ConRon.Refine.PropWhenWF p.2)
    (hpv : ConRon.Refine.PropWhenWF pv)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdx a)
      (arena.core.infer_pis_out pers st mode stk n v pv) lst
      (inferPisOut (ConRon.Refine.absMode mode) (absPiStk stk) (absSz n) (absLIdx v)
        (ConRon.Refine.absPropWhen pv)) := by
  sorry


/-! ## The application spine -/

@[lockstep_simp] theorem absEIdxArr_getElem (v : alloc.vec.Vec arena.handle.EIdx) (i : Nat)
    (h : i < (absEIdxArr v).size) :
    (absEIdxArr v)[i] = absEIdx (v.val[i]'(by simpa [absEIdxArr] using h)) := by
  simp [absEIdxArr]

@[lockstep_simp] theorem absEIdxArr_size (v : alloc.vec.Vec arena.handle.EIdx) :
    (absEIdxArr v).size = v.val.length := by
  simp [absEIdxArr]

theorem infer_spine_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth ty acc args i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_spine pers vis st mode lane fu fe depth ty acc args i) lst
        (inferSpine (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
          (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine, inferSpine, dif_neg (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine, inferSpine, dif_pos (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e


@[lockstep] theorem infer_spine_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty acc args i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_spine pers vis st mode lane fu fe depth ty acc args i) lst
      (inferSpine (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) :=
  infer_spine_aux hk _ hx rfl hrel hinv hctx hf

@[lockstep] theorem infer_app_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_app pers vis st mode lane fu fe depth e) lst
      (inferApp (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absEIdx e)) := by
  rw [arena.core.infer_app, inferApp]
  lockstep_e
  all_goals trace_state
  all_goals sorry

section spineIO
attribute [local lockstep_simp] twin_ite_bind

theorem infer_spine_io_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane io fu fe lfe depth ty acc args i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_spine_io pers vis st mode lane io fu fe depth ty acc args i) lst
        (inferSpineIO (ConRon.Refine.absMode mode)
          (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe (absU depth)
          (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane io fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine_io, inferSpineIO, dif_neg (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane io fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine_io, inferSpineIO, dif_pos (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e


@[lockstep] theorem infer_spine_io_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane io fu fe lfe depth ty acc args i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_spine_io pers vis st mode lane io fu fe depth ty acc args i) lst
      (inferSpineIO (ConRon.Refine.absMode mode)
        (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe (absU depth)
        (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) :=
  infer_spine_io_aux hk _ hx rfl hrel hinv hctx hf

end spineIO

/-- `infer_app_io_at` against `inferAppIOAt` at the io-view record. -/
@[lockstep] theorem infer_app_io_at_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane io fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_app_io_at pers vis st mode lane io fu fe depth e) lst
      (inferAppIOAt (ConRon.Refine.absMode mode)
        (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe (absU depth)
        (absEIdx e)) := by
  rw [arena.core.infer_app_io_at, inferAppIOAt]
  lockstep_e

/-! ## The λ telescope -/

@[lockstep] theorem infer_lams_leaf_check_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d k stk bt lst}
    (hstk : ∀ p ∈ (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)).val,
      ConRon.Refine.PropWhenWF p.2.pw)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.infer_lams_leaf_check pers vis st mode lane fu fe d k stk bt) lst
      (inferLamsLeafCheck (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absU k)
        (absLamStk stk) (absEIdx bt)) := by
  rw [arena.core.infer_lams_leaf_check, inferLamsLeafCheck]
  lockstep_e
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem infer_lams_leaf_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hstk : ∀ p ∈ (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)).val,
      ConRon.Refine.PropWhenWF p.2.pw)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_lams_leaf pers vis st mode lane fu fe d t k fvs stk) lst
      (inferLamsLeaf (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absEIdx t) (absU k)
        (absEIdxArr fvs) (absLamStk stk)) := by
  have hlp := @lam_pw_wf_ls pers hx
  rw [arena.core.infer_lams_leaf, inferLamsLeaf]
  lockstep_e
  -- glue: the port's `let (_, bm) = stk[j]; bm.pw.dup()` is a `match` on a
  -- non-constructor, which the zip cannot see through
  all_goals
    simp only [ConRon.Refine.PropWhen.dup_eq'] at hf
    generalize heq : (GetElem.getElem stk.val (_ : Nat) _ : arena.handle.EIdx × kernel.expr.BinderMeta) = p at hf
    obtain ⟨x, bm⟩ := p
    obtain rfl := (Result.ok_injective hf)
    refine LS.tail (stub_infer_lams_out_ls hx hstk ?_ hrel hinv) ?_ (fun _ _ h => h)
    · have hbm : bm = (x, bm).2 := rfl
      rw [hbm, ← heq]; exact hstk _ (List.getElem_mem _)
    · have hne : stk.val.length ≠ 0 := by scalar_tac
      simp only [vec_len_abs]
      rw [if_neg hne, absLamStk_last_pw stk _ (by assumption) (by scalar_tac), heq]


theorem infer_lams_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe d peel t k fvs stk lst},
      ExprOpsHyp pers → (peel : Std.U64).val = n →
      (∀ p ∈ (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)).val,
        ConRon.Refine.PropWhenWF p.2.pw) →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_lams pers vis st mode lane fu fe d peel t k fvs stk) lst
        (inferLams (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absU peel)
          (absEIdx t) (absU k) (absEIdxArr fvs) (absLamStk stk)) := by
  have hvb := @view_bind_wf_ls
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe d peel t k fvs stk lst hx hn hstk hrel hinv hctx hf
    rw [show absU peel = 0 from hn, inferLams, arena.core.infer_lams]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe d peel t k fvs stk lst hx hn hstk hrel hinv hctx hf
    rw [show absU peel = m + 1 from hn, inferLams, arena.core.infer_lams]
    lockstep_e
    all_goals
      -- glue: the pushed stack's well-formedness (the datum is `view_bind`'s)
      simp only [optBindWF] at *
      refine LS.tail (ih hx ?_ (lam_stk_push_wf (by assumption) hstk (by assumption))
        hrel hinv hctx hf) ?_ (fun _ _ h => h)
      · lockstep_side
      · lockstep_congr

end ConRon.Refine2.Lockstep
