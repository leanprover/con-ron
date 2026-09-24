/-
# `ConRon.Refine2.Core.LS.Infer` — region E: the inference bodies in lockstep

Task #97-P5-Core round 5, region E.  The Theorem-2 lockstep lemmas of
`arena::core`'s inference: the two bodies (`infer_body`, `infer_body_io`,
`BodyRel`'s `infer` / `inferIO` fields), the λ- and ∀-telescope loops
(`infer_lams`, `infer_pis` and their leaves), and the application spine
(`infer_spine`, `infer_spine_io`, `infer_app`, `infer_app_io_at`).
-/
import ConRon.Refine2.Core.LS.PrimsE
import ConRon.Refine2.Core.LS.Leaves
import ConRon.Refine2.Core.LS.Shapes
import ConRon.Refine2.Core.LS.Lits

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PB.CoreLSReg ConRon.Refine2.Lockstep.PE.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

-- `PrimsB`/`PrimsE` unfold the record abstraction only locally now (the
-- Checker lane reads it folded); the Core region files read it unfolded
attribute [local lockstep_simp] ConRon.Refine2.absIConstantVal

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PE

/-! ## Stubs (other regions' lemmas; deleted at merge) -/


/-! ## The application spine -/

-- `absEIdxArr_getElem`: the shared one (`Tactic/Prims`)

@[local lockstep_simp] theorem absEIdxArr_size (v : alloc.vec.Vec arena.handle.EIdx) :
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
  -- the port's `let (_, bm) = stk[j]; bm.pw.dup()` is stepped through (task
  -- #97-T2-TACTIC round 3); the tail call's premise and twin argument
  all_goals
    refine LS.tail (infer_lams_out_ls hx hstk ?_ hrel hinv) ?_ (fun _ _ h => h)
    · exact hstk _ (List.getElem_mem _)
    · have hne : stk.val.length ≠ 0 := by scalar_tac
      show inferLamsOut _ _ (absLamStk stk) _ _ _ = _
      simp only [vec_len_abs]
      rw [if_neg hne, absLamStk_last_pw stk _ (by assumption) (by scalar_tac)]


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

@[lockstep] theorem infer_lams_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d peel t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hstk : ∀ p ∈ (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)).val,
      ConRon.Refine.PropWhenWF p.2.pw)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_lams pers vis st mode lane fu fe d peel t k fvs stk) lst
      (inferLams (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absU peel)
        (absEIdx t) (absU k) (absEIdxArr fvs) (absLamStk stk)) :=
  infer_lams_aux hk _ hx rfl hstk hrel hinv hctx hf

/-! ## The ∀ telescope -/

@[lockstep] theorem infer_pis_leaf_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hstk : ∀ p ∈ (stk : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)).val,
      ConRon.Refine.PropWhenWF p.2)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_pis_leaf pers vis st mode lane fu fe d t k fvs stk) lst
      (inferPisLeaf (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absEIdx t) (absU k)
        (absEIdxArr fvs) (absPiStk stk)) := by
  rw [arena.core.infer_pis_leaf, inferPisLeaf]
  lockstep_e

theorem infer_pis_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe d peel t k fvs stk lst},
      ExprOpsHyp pers → (peel : Std.U64).val = n →
      (∀ p ∈ (stk : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)).val,
        ConRon.Refine.PropWhenWF p.2) →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_pis pers vis st mode lane fu fe d peel t k fvs stk) lst
        (inferPis (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absU peel)
          (absEIdx t) (absU k) (absEIdxArr fvs) (absPiStk stk)) := by
  have hvb := @view_bind_wf_ls
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe d peel t k fvs stk lst hx hn hstk hrel hinv hctx hf
    rw [show absU peel = 0 from hn, inferPis, arena.core.infer_pis]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe d peel t k fvs stk lst hx hn hstk hrel hinv hctx hf
    rw [show absU peel = m + 1 from hn, inferPis, arena.core.infer_pis]
    lockstep_e
    all_goals
      -- glue: the pushed stack's well-formedness (the datum is `view_bind`'s)
      simp only [optBindWF] at *
      refine LS.tail (ih hx ?_ (pi_stk_push_wf (by assumption) hstk (by simp_all))
        hrel hinv hctx hf) ?_ (fun _ _ h => h)
      · lockstep_side
      · lockstep_congr

@[lockstep] theorem infer_pis_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d peel t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hstk : ∀ p ∈ (stk : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)).val,
      ConRon.Refine.PropWhenWF p.2)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_pis pers vis st mode lane fu fe d peel t k fvs stk) lst
      (inferPis (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absU peel)
        (absEIdx t) (absU k) (absEIdxArr fvs) (absPiStk stk)) :=
  infer_pis_aux hk _ hx rfl hstk hrel hinv hctx hf

/-! ## The binder clauses -/

/-- The `.lam` clause.  `hmb`: the binder's datum is well formed (it comes out
of the store, `bms`' `TblInv`). -/
@[lockstep] theorem infer_lam_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty body mb lst}
    (hx : ExprOpsHyp pers) (hmb : ConRon.Refine.PropWhenWF (mb : kernel.expr.BinderMeta).pw)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_lam pers vis st mode lane fu fe depth ty body mb) lst
      (inferLam (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absEIdx ty)
        (absEIdx body) (ConRon.Refine.absBinderMeta mb)) := by
  rw [arena.core.infer_lam, inferLam]
  lockstep_e

/-- The `.forallE` clause. -/
@[lockstep] theorem infer_forall_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty body mb lst}
    (hx : ExprOpsHyp pers) (hmb : ConRon.Refine.PropWhenWF (mb : kernel.expr.BinderMeta).pw)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_forall pers vis st mode lane fu fe depth ty body mb) lst
      (inferForall (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absEIdx ty)
        (absEIdx body) (ConRon.Refine.absBinderMeta mb)) := by
  rw [arena.core.infer_forall, inferForall]
  lockstep_e

/-! ## The bodies -/

-- region A2's `ifenv_find_proj_ls` answers in `absIProjEntry`, region
-- A1's `proj_entry_type_at_ls` reads `absIProjEntry`: the same record, by
-- unfolding (three copies of the definition exist; the coordinator merges them)

attribute [lockstep_inline] arena.core.infer_sort arena.core.infer_fvar arena.core.infer_const
  arena.core.infer_lit_nat arena.core.infer_lit_str arena.core.infer_proj
  arena.core.infer_proj_at arena.core.infer_proj_prop

set_option maxHeartbeats 4000000 in
/-- **`BodyRel.infer`**, in lockstep. -/
@[lockstep] theorem infer_body_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_body pers vis st mode lane fu fe depth e) lst
      (inferBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absEIdx e)) := by
  have hv := @view_wf_ls
  rw [arena.core.infer_body, inferBody]
  refine LSR.bind (hv hrel hinv e) rfl ?_ ?_
  · intro e1; exact errArm_ok
  intro a b lst1 hR hrel hinv
  obtain ⟨hwf, rfl⟩ := hR
  cases a <;> dsimp only <;> lockstep_e

attribute [lockstep_inline] arena.core.infer_forall_io arena.core.infer_forall_io_at
  arena.core.infer_proj_io arena.core.infer_lam_open arena.core.infer_lam_cod

/-- `coreKnotIO`'s two infer slots are one function, at every fuel. -/
theorem coreKnotIO_infer_eq_inferIO (mode : ConLeche.CheckMode) (fe : IFEnv) (f : Nat) :
    (coreKnotIO mode fe f).infer = (coreKnotIO mode fe f).inferIO := by
  cases f <;> rfl

set_option maxHeartbeats 4000000 in
/-- **`BodyRel.inferIO`**, in lockstep. -/
@[lockstep] theorem infer_body_io_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane io fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hio : io = true ∨ lane = arena.core.LANE_IO) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_body_io pers vis st mode lane io fu fe depth e) lst
      (inferBodyIO (ConRon.Refine.absMode mode)
        (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe (absU depth)
        (absEIdx e)) := by
  have hv := @view_wf_ls
  have hlp := @lam_pw_wf_ls pers hx
  rw [arena.core.infer_body_io, inferBodyIO]
  refine LSR.bind (hv hrel hinv e) rfl ?_ ?_
  · intro e1; exact errArm_ok
  intro a b lst1 hR hrel hinv
  obtain ⟨hwf, rfl⟩ := hR
  cases a <;> dsimp only <;> lockstep_e
  -- one goal is left: the `.lam` clause's codomain-sort computation, where the
  -- port calls `knot_infer_io` and the twin `r.infer` at `r = laneKnotAt … io f`
  all_goals
    cases io with
    | true =>
      simp only [laneKnotAt_true_infer]
      lockstep_e
    | false =>
      -- region E's finding, repaired as `BodyRel.inferIO`'s call-site premise
      -- (the coordinator's ruling): at `io = false` the lane is `LANE_IO`, where
      -- `coreKnotIO`'s two infer slots are one function, so the twin's
      -- `r.infer` is the io slot the port's `infer_lam_cod` calls
      have hl : lane = arena.core.LANE_IO := hio.resolve_left (by simp)
      subst hl
      simp only [laneKnotAt_false, laneKnot_io, coreKnotIO_infer_eq_inferIO]
      lockstep_e

end ConRon.Refine2.Lockstep

/-! The region's `lockstep_simp` rules, registered `scoped` (task #97-P5-Core
round 5): active under `open scoped ConRon.Refine2.Lockstep.CoreLSReg` only, so that they
stay out of the other tiers' `lockstep` runs (the Checker lane imports the
knot since task #97-T2-LOCKSTEP lane Checker DeclCheck). -/
namespace ConRon.Refine2.Lockstep.CoreLSReg
open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PE
attribute [scoped lockstep_simp] absEIdxArr_size
end ConRon.Refine2.Lockstep.CoreLSReg
