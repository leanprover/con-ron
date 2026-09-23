/-
# `ConRon.Refine2.Core.LS.Iota` — region C2: the stuck-major rescue and the ι step

Task #97-P5-Core round 5, region C2.  The Theorem-2 lockstep lemmas of

* `majorToCtor` (Rust `major_to_ctor` and its nine fragments
  `major_to_ctor_{certs,k,eta_certs,eta,eta_build,and,and_build,at}`,
  `iota_certs_fam`), `etaFabArgsE`;
* `litMajorToCtor`, `projLitToCtor`, `prepareMajor`;
* `iotaRec` and `iotaRecAt` (Rust `iota_rec`, `iota_rec_at` and the fragments
  `iota_rec_{major,fire,params,certs,fam,reduct}`, `get_d_eidx`);
* `projCert`, `projCertAt`.

Each is one `lockstep_core` run over the Rust body with its fragments inlined
(`@[lockstep_inline]`) against the twin's body.
-/
import ConRon.Refine2.Core.LS.PrimsC2

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

/-- Region A1. -/
@[lockstep] theorem stub_const_ty_at_ls {pers st cv us lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.const_ty_at pers st cv us) lst
      (constTyAt (absIConstantVal cv) (absLsIdx us)) := by
  sorry

/-- Region C1. -/
@[lockstep] theorem stub_iota_certs_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth lic h args lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.iota_certs pers vis st mode lane fu fe depth lic h args 0#usize) lst
      (iotaCerts (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) lic
        (absEIdx h) (absEIdxList args)) := by
  sorry

/-- Region B. -/
@[lockstep] theorem stub_lit_to_ctor_if_nat_ls {pers vis st fe lfe h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = absEIdx a) (arena.core.lit_to_ctor_if_nat pers vis st fe h) lst
      (litToCtorIfNat lfe (absEIdx h)) := by
  sorry

/-- Region B. -/
@[lockstep] theorem stub_str_lit_supported_ls {pers vis st fe lfe lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.str_lit_supported pers vis st fe) lst
      (strLitSupported lfe) := by
  sorry

/-- Region B. -/
@[lockstep] theorem stub_str_lit_to_constructor_ls {pers st s lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.str_lit_to_constructor pers st s) lst
      (strLitToConstructor (ConRon.Refine.absString s)) := by
  sorry

/-- Region A2. -/
@[lockstep] theorem stub_eta_projs_ls {pers vis st fe lfe t us targs b nF lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = absEIdxList a)
      (arena.core.eta_projs pers vis st fe t us targs b nF) lst
      (etaProjs lfe (absNIdx t) (absLsIdx us) (absEIdxList targs) (absEIdx b) (absU nF)) := by
  sorry

/-! ## `projCert` / `projCertAt` -/

@[lockstep] theorem proj_cert_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth lic c us args lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.proj_cert pers vis st mode lane fu fe depth lic c us args) lst
      (projCert (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) lic
        (absNIdx c) (absLsIdx us) (absEIdxList args)) := by
  rw [arena.core.proj_cert, projCert]
  lockstep_core

@[lockstep] theorem proj_cert_at_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth verified lic c us args lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.proj_cert_at pers vis st mode lane fu fe depth verified lic c us args) lst
      (projCertAt (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        verified lic (absNIdx c) (absLsIdx us) (absEIdxList args)) := by
  rw [arena.core.proj_cert_at, projCertAt]
  lockstep_core

/-! ## The literal conversions -/

attribute [local lockstep_simp] ConRon.Refine.absLiteral

@[lockstep] theorem lit_major_to_ctor_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.lit_major_to_ctor pers vis st mode lane fu fe depth h) lst
      (litMajorToCtor (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h)) := by
  rw [arena.core.lit_major_to_ctor, litMajorToCtor]
  lockstep_core

@[lockstep] theorem proj_lit_to_ctor_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.proj_lit_to_ctor pers vis st mode lane fu fe depth h) lst
      (projLitToCtor (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h)) := by
  rw [arena.core.proj_lit_to_ctor, projLitToCtor]
  lockstep_core

/-! ## `etaFabArgsE` -/

@[lockstep] theorem eta_fab_args_e_ls {pers vis st fe lfe t ust targs major nF lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = absEIdxList a)
      (arena.core.eta_fab_args_e pers vis st fe t ust targs major nF) lst
      (etaFabArgsE lfe (absNIdx t) (absLsIdx ust) (absEIdxList targs) (absEIdx major)
        (absU nF)) := by
  rw [arena.core.eta_fab_args_e, etaFabArgsE]
  lockstep_core
  all_goals trace_state
  all_goals sorry

end ConRon.Refine2.Lockstep
