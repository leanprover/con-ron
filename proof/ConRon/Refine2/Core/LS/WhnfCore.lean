/-
# `ConRon.Refine2.Core.LS.WhnfCore` — region D: the `whnfCore` body, the batched β spine

Task #97-P5-Core round 5, region D; task #119 (con-leche's task #342 R2, the
`WhnfStep` loops).  The lockstep lemmas of `arena::core::beta_peel` and
`whnf_app` (the batched β spine: each RETURNS its continuation, a
`WhnfStep`), `reduce_proj_core` (`Arena.reduceProjCore`, the projection rule,
shared with the defeq tier's `lazy_delta_proj_fields`; its fragments
`reduce_proj_core_at`, `reduce_proj_core_fire` are inlined), the step
`whnf_core_step` (with `whnf_core_step_proj`), and the loop
`whnf_core_loop_loop` / `whnf_core_loop` / `whnf_core_body` (`BodyRel`'s
`whnfCore` field) — Aeneas's `-loops-to-rec` spelling of the Rust loop, one
induction on the step budget against the twin's `whnfCoreLoop`.  The
official kernel's `cheap_proj` flag (task #109) is an argument on both sides
and is threaded unchanged.
-/
import ConRon.Refine2.Core.LS.PrimsD
import ConRon.Refine2.Core.LS.Shapes
import ConRon.Refine2.Core.LS.Iota

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PB.CoreLSReg ConRon.Refine2.Lockstep.PC1.CoreLSReg ConRon.Refine2.Lockstep.PC2.CoreLSReg ConRon.Refine2.Lockstep.PD.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

-- `PrimsB`/`PrimsE` unfold the record abstraction only locally now (the
-- Checker lane reads it folded); the Core region files read it unfolded
attribute [local lockstep_simp] ConRon.Refine2.absIConstantVal

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PD

/-! ## The step's answer -/

/-- `arena::core::WhnfStep` as the twin's `WhnfStep`, constructor for
constructor. -/
def absWhnfStep : arena.core.WhnfStep → WhnfStep
  | .Done e => .done (absEIdx e)
  | .Cont e => .cont (absEIdx e)

attribute [local lockstep_simp] absWhnfStep

attribute [lockstep_inline] arena.core.reduce_proj_core_at arena.core.reduce_proj_core_fire
  arena.core.intern_app

/-! ## The batched β spine: `beta_peel` / `whnf_app`

Each on the spine's remaining length `args.size - i` (the twin's
`termination_by args.size - i`); `beta_peel` no longer calls back into
`whnf_app` (a finished peel returns `.cont`), so the two inductions are
separate. -/

section spine

theorem map_getElem!_absEIdx (l : List arena.handle.EIdx) (i : Nat) (h : i < l.length) :
    (l.map absEIdx).toArray[i]! = absEIdx l[i] := by
  rw [getElem!_pos (l.map absEIdx).toArray i (by simpa using h)]
  simp

attribute [local lockstep_simp] absEIdxArr ExprOps.absEIdxL List.push_toArray
  List.map_append List.map_cons List.map_nil List.nil_append List.size_toArray
  List.length_map List.getElem_toArray List.getElem_map map_getElem!_absEIdx

theorem beta_peel_aux (n : Nat) :
    ∀ {pers st t acc args i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absWhnfStep a)
        (arena.core.beta_peel pers st t acc args i) lst
        (betaPeel (absEIdx t) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers st t acc args i lst hx hn hrel hinv
    rw [arena.core.beta_peel, betaPeel]
    by_cases hi : i.val < args.val.length
    · rw [dite_eq_left (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
    · rw [dite_eq_right (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
  | succ k ih =>
    intro pers st t acc args i lst hx hn hrel hinv
    rw [arena.core.beta_peel, betaPeel]
    by_cases hi : i.val < args.val.length
    · rw [dite_eq_left (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
    · rw [dite_eq_right (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core

@[lockstep] theorem beta_peel_ls {pers st t acc args i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.beta_peel pers st t acc args i) lst
      (betaPeel (absEIdx t) (absEIdxArr acc) (absEIdxArr args) (absSz i)) :=
  beta_peel_aux _ hx rfl hrel hinv

theorem whnf_app_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absWhnfStep a)
        (arena.core.whnf_app pers vis st mode lane fu fe depth v hd vargs same args nodes i) lst
        (whnfApp (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
          lfe (absU depth) (absEIdx v) (absEIdx hd) (absEIdxArr vargs) same (absEIdxArr args)
          (absEIdxArr nodes) (absSz i)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst hx hn hrel
      hinv hctx hf
    rw [arena.core.whnf_app, whnfApp]
    by_cases hi : i.val < args.val.length
    · rw [dite_eq_left (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
    · rw [dite_eq_right (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
  | succ k ih =>
    intro pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst hx hn hrel
      hinv hctx hf
    rw [arena.core.whnf_app, whnfApp]
    by_cases hi : i.val < args.val.length
    · rw [dite_eq_left (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
    · rw [dite_eq_right (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core

/-- `arena::core::whnf_app` against `Arena.whnfApp`. -/
@[lockstep] theorem whnf_app_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.whnf_app pers vis st mode lane fu fe depth v hd vargs same args nodes i) lst
      (whnfApp (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx v) (absEIdx hd) (absEIdxArr vargs) same (absEIdxArr args)
        (absEIdxArr nodes) (absSz i)) :=
  whnf_app_aux hk _ hx rfl hrel hinv hctx hf

end spine

/-! ## The projection rule: `reduce_proj_core` -/

@[lockstep] theorem reduce_proj_core_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth sn i c lst}
    (_hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.reduce_proj_core pers vis st mode lane fu fe depth sn i c) lst
      (reduceProjCore (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absNIdx sn)
        (absU i) (absEIdx c)) := by
  rw [arena.core.reduce_proj_core, reduceProjCore]
  lockstep_core

/-! ## The step: `whnf_core_step` (fragment `whnf_core_step_proj`) -/

@[lockstep] theorem whnf_core_step_proj_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe cheap depth e sn i pe lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.whnf_core_step_proj pers vis st mode lane fu fe cheap depth e sn i pe) lst
      (whnfCoreStepProj (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe cheap (absU depth) (absEIdx e)
        (absNIdx sn) (absU i) (absEIdx pe)) := by
  rw [arena.core.whnf_core_step_proj, whnfCoreStepProj]
  lockstep_core

@[lockstep] theorem whnf_core_step_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe cheap depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.whnf_core_step pers vis st mode lane fu fe cheap depth e) lst
      (whnfCoreStep (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe cheap (absU depth) (absEIdx e)) := by
  rw [arena.core.whnf_core_step, whnfCoreStep]
  lockstep_core

/-! ## The loop: `whnf_core_loop_loop` / `whnf_core_loop` / `whnf_core_body` -/

theorem whnf_core_loop_loop_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe cheap depth k cur lst},
      ExprOpsHyp pers → (k : Std.U64).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.whnf_core_loop_loop pers vis st mode lane fu fe cheap depth k cur) lst
        (whnfCoreLoop (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe cheap (absU depth) n
          (absEIdx cur)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe cheap depth k cur lst hx hn hrel hinv hctx hf
    rw [arena.core.whnf_core_loop_loop, whnfCoreLoop, ite_eq_left (by scalar_tac)]
    lockstep_core
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe cheap depth k cur lst hx hn hrel hinv hctx hf
    rw [arena.core.whnf_core_loop_loop, whnfCoreLoop, ite_eq_right (by scalar_tac)]
    lockstep_core

@[lockstep] theorem whnf_core_loop_loop_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe cheap depth k cur lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf_core_loop_loop pers vis st mode lane fu fe cheap depth k cur) lst
      (whnfCoreLoop (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe cheap (absU depth) (absU k)
        (absEIdx cur)) :=
  whnf_core_loop_loop_aux hk _ hx rfl hrel hinv hctx hf

@[local lockstep_simp] theorem whnf_core_loop_fuel_abs :
    absU arena.core.WHNF_CORE_LOOP_FUEL = whnfCoreLoopFuel := by
  rw [arena.core.WHNF_CORE_LOOP_FUEL, whnfCoreLoopFuel]; rfl

attribute [lockstep_inline] arena.core.whnf_core_loop

/-- **`BodyRel.whnfCore`**, in lockstep: the loop at its own step budget. -/
theorem whnf_core_body_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe cheap depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf_core_body pers vis st mode lane fu fe cheap depth e) lst
      (whnfCoreBody (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe cheap (absU depth) (absEIdx e)) := by
  rw [arena.core.whnf_core_body, whnfCoreBody]
  lockstep_core

end ConRon.Refine2.Lockstep
