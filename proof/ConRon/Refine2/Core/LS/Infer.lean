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
import ConRon.Refine2.Core.LS.PrimsF

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

/-! ## The application spine -/

-- `absEIdxArr_getElem`: the shared one (`Tactic/Prims`)

/-- The argument check of a full-grade application (task #125): an
`eagerReduce _ _` argument's type is compared in the eager tower (the knot's
`defeqE` slot), every other argument's in the knot's own. -/
@[lockstep] theorem defeq_arg_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a ta ty lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun x y => y = x)
      (arena.core.defeq_arg pers vis st mode lane fu fe depth a ta ty) lst
      (defeqArg (laneKnot (ConRon.Refine.absMode mode) lfe lane f) (absU depth)
        (absEIdx a) (absEIdx ta) (absEIdx ty)) := by
  rw [arena.core.defeq_arg, defeqArg]
  lockstep_e

theorem infer_spine_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth ty acc args i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_spine pers vis st mode lane fu fe depth ty acc args i) lst
        (inferSpine (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
          (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine, inferSpine, dite_eq_right (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine, inferSpine, dite_eq_left (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e

@[lockstep] theorem infer_spine_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty acc args i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_spine pers vis st mode lane fu fe depth ty acc args i) lst
      (inferSpine (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) :=
  infer_spine_aux hk _ hx rfl hrel hinv hctx hf

@[lockstep] theorem infer_app_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_app pers vis st mode lane fu fe depth e) lst
      (inferApp (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx e)) := by
  rw [arena.core.infer_app, inferApp]
  lockstep_e

section spineIO
attribute [local lockstep_simp] twin_ite_bind

/-- The io spine walk reads only the record's `whnf` slot, so it is stated at
any io view of the lane knot (`io` is fixed by the caller's twin). -/
theorem infer_spine_io_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane io fu fe lfe depth ty acc args i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_spine_io pers vis st mode lane fu fe depth ty acc args i) lst
        (inferSpineIO (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe (absU depth)
          (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane io fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine_io, inferSpineIO, dite_eq_right (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane io fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine_io, inferSpineIO, dite_eq_left (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e

@[lockstep] theorem infer_spine_io_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane io fu fe lfe depth ty acc args i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_spine_io pers vis st mode lane fu fe depth ty acc args i) lst
      (inferSpineIO (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe (absU depth)
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
      (inferAppIOAt (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe (absU depth)
        (absEIdx e)) := by
  rw [arena.core.infer_app_io_at, inferAppIOAt]
  lockstep_e

/-! ## The λ telescope -/

@[lockstep] theorem infer_lams_leaf_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_lams_leaf pers vis st mode lane fu fe d t k fvs stk) lst
      (inferLamsLeaf (laneKnot (ConRon.Refine.absMode mode) lfe lane f) (absU d) (absEIdx t)
        (absU k) (absEIdxArr fvs) (absLamStk stk)) := by
  rw [arena.core.infer_lams_leaf, inferLamsLeaf]
  lockstep_e

theorem infer_lams_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe d peel t k fvs stk lst},
      ExprOpsHyp pers → (peel : Std.U64).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_lams pers vis st mode lane fu fe d peel t k fvs stk) lst
        (inferLams (laneKnot (ConRon.Refine.absMode mode) lfe lane f) (absU d) (absU peel)
          (absEIdx t) (absU k) (absEIdxArr fvs) (absLamStk stk)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe d peel t k fvs stk lst hx hn hrel hinv hctx hf
    rw [show absU peel = 0 from hn, inferLams, arena.core.infer_lams]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe d peel t k fvs stk lst hx hn hrel hinv hctx hf
    rw [show absU peel = m + 1 from hn, inferLams, arena.core.infer_lams]
    lockstep_e

@[lockstep] theorem infer_lams_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d peel t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_lams pers vis st mode lane fu fe d peel t k fvs stk) lst
      (inferLams (laneKnot (ConRon.Refine.absMode mode) lfe lane f) (absU d) (absU peel)
        (absEIdx t) (absU k) (absEIdxArr fvs) (absLamStk stk)) :=
  infer_lams_aux hk _ hx rfl hrel hinv hctx hf

/-! ## The ∀ telescope -/

@[lockstep] theorem infer_pis_leaf_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d t k fvs stk lst}
    (_hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_pis_leaf pers vis st mode lane fu fe d t k fvs stk) lst
      (inferPisLeaf (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absEIdx t)
        (absU k) (absEIdxArr fvs) (absPiStk stk)) := by
  rw [arena.core.infer_pis_leaf, inferPisLeaf]
  lockstep_e

theorem infer_pis_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe d peel t k fvs stk lst},
      ExprOpsHyp pers → (peel : Std.U64).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_pis pers vis st mode lane fu fe d peel t k fvs stk) lst
        (inferPis (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absU peel)
          (absEIdx t) (absU k) (absEIdxArr fvs) (absPiStk stk)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe d peel t k fvs stk lst hx hn hrel hinv hctx hf
    rw [show absU peel = 0 from hn, inferPis, arena.core.infer_pis]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe d peel t k fvs stk lst hx hn hrel hinv hctx hf
    rw [show absU peel = m + 1 from hn, inferPis, arena.core.infer_pis]
    lockstep_e

@[lockstep] theorem infer_pis_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d peel t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_pis pers vis st mode lane fu fe d peel t k fvs stk) lst
      (inferPis (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absU peel)
        (absEIdx t) (absU k) (absEIdxArr fvs) (absPiStk stk)) :=
  infer_pis_aux hk _ hx rfl hrel hinv hctx hf

/-! ## The binder clauses -/

/-- The `.lam` clause. -/
@[lockstep] theorem infer_lam_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty body lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_lam pers vis st mode lane fu fe depth ty body) lst
      (inferLam (laneKnot (ConRon.Refine.absMode mode) lfe lane f) (absU depth) (absEIdx ty)
        (absEIdx body)) := by
  rw [arena.core.infer_lam, inferLam]
  lockstep_e

/-- The `.forallE` clause. -/
@[lockstep] theorem infer_forall_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty body lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_forall pers vis st mode lane fu fe depth ty body) lst
      (inferForall (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx ty) (absEIdx body)) := by
  rw [arena.core.infer_forall, inferForall]
  lockstep_e

/-! ## The bodies -/

-- region A2's `ifenv_find_proj_ls` answers in `absIProjEntry`, region
-- A1's `proj_entry_type_at_ls` reads `absIProjEntry`: the same record, by
-- unfolding (three copies of the definition exist; the coordinator merges them)

attribute [lockstep_inline] arena.core.infer_sort arena.core.infer_fvar arena.core.infer_const
  arena.core.infer_lit_nat arena.core.infer_lit_str arena.core.infer_proj
  arena.core.infer_proj_at arena.core.infer_proj_prop arena.core.infer_proj_miss
  arena.core.infer_let

attribute [local lockstep_simp] inferProj Option.isSome_map core.option.Option.is_some

/-- `lockstep_e` with one more error leaf: the projection miss, whose
`has_table` the port computes with `Option::is_some` and whose argument count
it casts (`projMissError`'s two arguments in the port's spelling). -/
macro "lockstep_ei" : tactic =>
  `(tactic| repeat' (first
      | lockstep_step
      | ls_state_bind
      | (apply LS.err; exact errSim_fail (by assumption))
      | (apply LS.err; exact errSim_throw (by assumption))
      | (apply LS.err; exact errSim_fail (by
          simp only [core.option.Option.is_some] at *
          rw [‹absAErrKind _ = _›]
          congr 2 <;> scalar_tac))))

set_option maxHeartbeats 4000000 in
/-- **`BodyRel.infer`**, in lockstep. -/
@[lockstep] theorem infer_body_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_body pers vis st mode lane fu fe depth e) lst
      (inferBody (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx e)) := by
  have hv := @PF.view_wf_ls
  have hptn := @proj_table_name_at_ls
  rw [arena.core.infer_body, inferBody]
  refine LSR.bind (hv hrel hinv e) rfl ?_ ?_
  · intro e1; exact errArm_ok
  intro a b lst1 hR hrel hinv
  obtain ⟨hwf, rfl⟩ := hR
  cases a <;> dsimp only <;> lockstep_ei

attribute [lockstep_inline] arena.core.infer_forall_io arena.core.infer_forall_io_at
  arena.core.infer_lam_open arena.core.infer_let_io

set_option maxHeartbeats 4000000 in
/-- **`BodyRel.inferIO`**, in lockstep.  (`hio`, `BodyRel.inferIO`'s
call-site premise, is not read since con-leche's task #346: every recursive
call of the io body is `knot_infer_at io`, `laneKnotAt`'s `infer`.) -/
@[lockstep] theorem infer_body_io_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane io fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (_hio : io = true ∨ lane = arena.core.LANE_IO) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_body_io pers vis st mode lane io fu fe depth e) lst
      (inferBodyIO (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe (absU depth)
        (absEIdx e)) := by
  have hv := @PF.view_wf_ls
  have hptn := @proj_table_name_at_ls
  rw [arena.core.infer_body_io, inferBodyIO]
  refine LSR.bind (hv hrel hinv e) rfl ?_ ?_
  · intro e1; exact errArm_ok
  intro a b lst1 hR hrel hinv
  obtain ⟨hwf, rfl⟩ := hR
  cases a <;> dsimp only <;> lockstep_ei

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
