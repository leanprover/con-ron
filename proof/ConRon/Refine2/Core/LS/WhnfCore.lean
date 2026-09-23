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

attribute [local lockstep_simp] whnfCoreAppGated ConRon.Refine.absBinderMeta

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
        verified lic (absNIdx c) (absLsIdx us) (ExprOps.absEIdxList args)) := by
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
      (fun r => absEIdx r = (ExprOps.absEIdxList xs).getD (absU i) (absEIdx d)) := by
  sorry

/-! ## The batched β spine: `whnf_app` / `beta_peel`

One joint induction on the spine's remaining length `args.size - i` (the twin's
`termination_by (args.size - i, 0/1)`): at each length `whnf_app` is proved
first (it calls `beta_peel` and itself one argument further on), then
`beta_peel` (it calls itself one further on and `whnf_app` at the SAME
cursor). -/

section spine

theorem vec_new_val_eidx : (alloc.vec.Vec.new arena.handle.EIdx).val = [] := by simp

theorem map_getElem!_absEIdx (l : List arena.handle.EIdx) (i : Nat) (h : i < l.length) :
    (l.map absEIdx).toArray[i]! = absEIdx l[i] := by
  rw [getElem!_pos (l.map absEIdx).toArray i (by simpa using h)]
  simp

attribute [local lockstep_simp] absEIdxArr ExprOps.absEIdxL List.push_toArray List.map_append
  List.map_cons List.map_nil List.nil_append List.size_toArray List.length_map
  List.getElem_toArray List.getElem_map vec_new_val_eidx map_getElem!_absEIdx absU_eq_val

/-- The spine at remaining length `n`. -/
def WhnfAppAt (f : Nat) (n : Nat) : Prop :=
  ∀ {pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst},
    ExprOpsHyp pers → args.val.length - i.val = n →
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf_app pers vis st mode lane fu fe depth v hd vargs same args nodes i) lst
      (whnfApp (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx v) (absEIdx hd) (absEIdxArr vargs) same (absEIdxArr args)
        (absEIdxArr nodes) (absSz i))

/-- The peel at remaining length `n`. -/
def BetaPeelAt (f : Nat) (n : Nat) : Prop :=
  ∀ {pers vis st mode lane fu fe lfe depth t acc args nodes i lst},
    ExprOpsHyp pers → args.val.length - i.val = n →
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
    LS pers (fun a b => b = absEIdx a)
      (arena.core.beta_peel pers vis st mode lane fu fe depth t acc args nodes i) lst
      (betaPeel (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx t) (absEIdxArr acc) (absEIdxArr args) (absEIdxArr nodes)
        (absSz i))

theorem spine_ls {f : Nat} (hk : KnotRel f) : ∀ n, WhnfAppAt f n ∧ BetaPeelAt f n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst hx hn hrel
        hinv hctx hf
      rw [arena.core.whnf_app, whnfApp]
      by_cases hi : i.val < args.val.length
      · rw [dif_pos (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
        lockstep_core
      · rw [dif_neg (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
        lockstep_core
    · intro pers vis st mode lane fu fe lfe depth t acc args nodes i lst hx hn hrel hinv hctx hf
      rw [arena.core.beta_peel, betaPeel]
      by_cases hi : i.val < args.val.length
      · rw [dif_pos (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
        lockstep_core
      · rw [dif_neg (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
        lockstep_core
  | succ k ih =>
    obtain ⟨ihA, ihB⟩ := ih
    unfold WhnfAppAt at ihA
    unfold BetaPeelAt at ihB
    have hA : WhnfAppAt f (k + 1) := by
      intro pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst hx hn hrel
        hinv hctx hf
      rw [arena.core.whnf_app, whnfApp]
      by_cases hi : i.val < args.val.length
      · rw [dif_pos (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
        lockstep_core
      · rw [dif_neg (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
        lockstep_core
    refine ⟨hA, ?_⟩
    unfold WhnfAppAt at hA
    intro pers vis st mode lane fu fe lfe depth t acc args nodes i lst hx hn hrel hinv hctx hf
    rw [arena.core.beta_peel, betaPeel]
    by_cases hi : i.val < args.val.length
    · rw [dif_pos (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
    · rw [dif_neg (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core

/-- `arena::core::whnf_app` against `Arena.whnfApp` (`Core/Arms/Batched.lean`'s
`whnf_app_refines`, in the lockstep form). -/
@[lockstep] theorem whnf_app_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf_app pers vis st mode lane fu fe depth v hd vargs same args nodes i) lst
      (whnfApp (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx v) (absEIdx hd) (absEIdxArr vargs) same (absEIdxArr args)
        (absEIdxArr nodes) (absSz i)) :=
  (spine_ls hk _).1 hx rfl hrel hinv hctx hf

/-- `arena::core::beta_peel` against `Arena.betaPeel` (`beta_peel_refines`, in
the lockstep form). -/
@[lockstep] theorem beta_peel_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth t acc args nodes i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.beta_peel pers vis st mode lane fu fe depth t acc args nodes i) lst
      (betaPeel (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx t) (absEIdxArr acc) (absEIdxArr args) (absEIdxArr nodes)
        (absSz i)) :=
  (spine_ls hk _).2 hx rfl hrel hinv hctx hf

end spine

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

/-! ## `whnf_core_stuck_app` -/

/-- `arena::core::whnf_core_stuck_app` against `Arena.whnfCoreStuckApp`
(`whnf_core_stuck_app_refines`, in the lockstep form). -/
@[lockstep] theorem whnf_core_stuck_app_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h same fp a lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf_core_stuck_app pers vis st mode lane fu fe depth h same fp a) lst
      (whnfCoreStuckApp (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h) same (absEIdx fp) (absEIdx a)) := by
  rw [arena.core.whnf_core_stuck_app, whnfCoreStuckApp]
  lockstep_core

/-! ## `whnf_core_body_gated` -/

/-- `arena::core_gated::whnf_core_body_gated` against `Arena.whnfCoreBodyGated` —
`BodyRel`'s `whnfCoreGated` field, in the lockstep form. -/
theorem whnf_core_body_gated_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core_gated.whnf_core_body_gated pers vis st mode lane fu fe depth e) lst
      (whnfCoreBodyGated (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absEIdx e)) := by
  rw [arena.core_gated.whnf_core_body_gated, whnfCoreBodyGated]
  lockstep_core

end ConRon.Refine2.Lockstep
