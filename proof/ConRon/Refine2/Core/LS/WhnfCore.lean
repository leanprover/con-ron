/-
# `ConRon.Refine2.Core.LS.WhnfCore` — region D: the `whnfCore` body, the batched β spine

Task #97-P5-Core round 5, region D.  The lockstep lemmas of
`arena::core::whnf_app`/`beta_peel` (the batched β spine, one joint
induction on the spine cursor), `whnf_core_stuck_app`, `whnf_core_body`
(`BodyRel`'s `whnfCore` field; its fragments `whnf_core_proj`,
`whnf_core_proj_at`, `whnf_core_proj_fire`, `intern_app` are inlined) and
`arena::core_gated::whnf_core_body_gated` (fragment `whnf_core_app_gated`).
-/
import ConRon.Refine2.Core.LS.PrimsD

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PD

attribute [lockstep_inline] arena.core.whnf_core_proj arena.core.whnf_core_proj_at
  arena.core.whnf_core_proj_fire arena.core.intern_app
  arena.core_gated.whnf_core_app_gated

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

@[lockstep] theorem stub_get_app_spine_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = (absEIdx a.1, absEIdxArr a.2.1, absEIdxArr a.2.2))
      (arena.core.get_app_spine pers st fuel h) st lst
      (getAppSpine (absU fuel) (absEIdx h)) := by
  sorry

@[lockstep] theorem stub_head_and_args_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : arena.handle.EIdx) :
    LSR pers (fun a b => b = (absEIdx a.1, absEIdxArr a.2))
      (arena.core.head_and_args pers st v) st lst
      (headAndArgs (absEIdx v)) := by
  sorry

@[lockstep] theorem stub_intern_app_rebuilt_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) (same : Bool)
    (f a : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.core.intern_app_rebuilt pers st h same f a) lst
      (internAppRebuilt (absEIdx h) same (absEIdx f) (absEIdx a)) := by
  sorry

@[lockstep] theorem stub_iota_rec_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.iota_rec pers vis st mode lane fu fe depth e) lst
      (iotaRec (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx e)) := by
  sorry

@[lockstep] theorem stub_iota_rec_at_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth hd sargs n lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.iota_rec_at pers vis st mode lane fu fe depth hd sargs n) lst
      (iotaRecAt (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx hd) (absEIdxArr sargs) (absSz n)) := by
  sorry

@[lockstep] theorem stub_proj_lit_to_ctor_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.proj_lit_to_ctor pers vis st mode lane fu fe depth h) lst
      (projLitToCtor (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h)) := by
  sorry

@[lockstep] theorem stub_proj_cert_at_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth verified lic c us args lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.proj_cert_at pers vis st mode lane fu fe depth verified lic c us args) lst
      (projCertAt (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        verified lic (absNIdx c) (absLsIdx us) (absEIdxList args)) := by
  sorry

@[lockstep] theorem stub_proj_entry_fire_ok_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (entry : arena.env.IProjEntry) (us : arena.handle.LsIdx) :
    LS pers (fun a b => b = a) (arena.core.proj_entry_fire_ok pers st entry us) lst
      ((absIProjEntry entry).fireOk (absLsIdx us)) := by
  sorry

@[lockstep] theorem stub_get_d_eidx_ls (xs : alloc.vec.Vec arena.handle.EIdx) (i : Std.U64)
    (d : arena.handle.EIdx) :
    LSP (arena.core.get_d_eidx xs i d)
      (fun r => absEIdx r = (absEIdxList xs).getD (absU i) (absEIdx d)) := by
  sorry

/-! ## `whnf_core_body` -/

attribute [local lockstep_simp] absU_eq_val

theorem whnf_core_body_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf_core_body pers vis st mode lane fu fe depth e) lst
      (whnfCoreBody (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx e)) := by
  rw [arena.core.whnf_core_body, whnfCoreBody]
  lockstep_core
  all_goals trace_state
  all_goals sorry

end ConRon.Refine2.Lockstep
