/-
# `ConRon.Refine2.Frontend.ExprOpsSeam` — the ExprOps lane's lockstep statements, pending

**Task #97-T2-LOCKSTEP lane Frontend round 3.**  `proj_rec.rs` calls ten
`expr_ops` walks.  On `arena` their Theorem-2 lemmas are still in the
pre-lockstep shape (`AStateRel` + `StoreWF` + `EResolves`), and a lockstep
proof cannot consume them; the ExprOps lane's branch (`t2-lock-exprops-b`,
not yet landed) proves them as `@[lockstep]` `_ls` lemmas.

This file states those nine lemmas VERBATIM (the ExprOps branch's
`Refine2/ExprOps/{Read,Mut}.lean` statements, same judgement, same twin
action), `sorry`-ed, suffixed `_seam` so that they cannot collide with the
lane's names.  **When the ExprOps lane lands, this file is deleted** and its
uses become the lane's `_ls` lemmas (the `@[lockstep]` index finds them by the
Rust head, so the proofs that use the tactic do not change).

## `sorry` count in this file: 8 (`get_app_fn`/`get_app_args` are the Core lane's `_refines₀`)
-/
import ConRon.Refine2.Frontend.Spec

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Refine2.Lockstep

@[lockstep] theorem strip_lams_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = ExprOps.absStrip a) (arena.expr_ops.strip_lams pers st k h) st lst
      (stripLams (absU k) (absEIdx h)) := by sorry

@[lockstep] theorem strip_pis_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = ExprOps.absStrip a) (arena.expr_ops.strip_pis pers st k h) st lst
      (stripPis (absU k) (absEIdx h)) := by sorry

@[lockstep] theorem inst_lp_fast_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (ks : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_lp_fast pers st fuel ks us e) lst
      (instLPFast (absU fuel) (ks.val.map absNIdx) (absLsIdx us) (absEIdx e)) := by sorry

@[lockstep] theorem bvar_range_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (m_i n k : Std.U64) :
    LS pers (fun a b => b = absEIdxList a) (arena.expr_ops.bvar_range pers st m_i n k) lst
      (bvarRange (absU m_i) (absU n) (absU k)) := by sorry

@[lockstep] theorem instantiate1_lift_fast_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e v : arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => b = absEIdx a)
      (arena.expr_ops.instantiate1_lift_fast pers st fuel e v d) lst
      (instantiate1LiftFast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) := by sorry

@[lockstep] theorem get_app_fn_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.get_app_fn pers st fuel h) st lst
      (getAppFn (absU fuel) (absEIdx h)) := by
  intro o ho
  have := get_app_fn_refines₀ (fuel := fuel) (h := h) hrel hinv ho
  cases o with
  | Ok a => obtain ⟨lst', hx, h1, h2⟩ := this; exact ⟨_, lst', hx, rfl, h1, h2⟩
  | Err e => exact this

@[lockstep] theorem get_app_args_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = ExprOps.absEIdxList a) (arena.expr_ops.get_app_args pers st fuel h)
      st lst (getAppArgs (absU fuel) (absEIdx h)) := by
  intro o ho
  have := get_app_args_refines₀ (fuel := fuel) (h := h) hrel hinv ho
  cases o with
  | Ok a => obtain ⟨lst', hx, h1, h2⟩ := this; exact ⟨_, lst', hx, rfl, h1, h2⟩
  | Err e => exact this

@[lockstep] theorem lift_loose_bvars_fast_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel amount c : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.expr_ops.lift_loose_bvars_fast pers st fuel amount c e) lst
      (liftLooseBVarsFast (absU fuel) (absU amount) (absU c) (absEIdx e)) := by sorry

@[lockstep] theorem mk_app_n_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.mk_app_n pers st f args) lst
      (Arena.mkAppN (absEIdx f) (absEIdxList args)) := by sorry

@[lockstep] theorem pi_result_seam {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.pi_result pers st fuel h) st lst
      (piResult (absU fuel) (absEIdx h)) := by sorry

end ConRon.Refine2.Frontend
