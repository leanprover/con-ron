/-
# `ConRon.Refine2.Core.LS.Prims` — the Core tier's primitive pairs that need `CoreCtx`

Task #97-P5-Core round 5.  The `@[lockstep]` pairs whose statement needs the
Core tier's own context (`CoreCtx`, `ExprOpsHyp`) and so cannot live in
`Tactic/Prims.lean`, which the Core tier imports.
-/
import ConRon.Refine2.Core.LS.Knot

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

/-! ## Converters from the `AOut₀` form -/

theorem LSR.ofAOut₀ {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : ∀ o, m = ok o → AOut₀ A pers o st (x.run lst)) :
    LSR pers (fun a b => b = A a) m st lst x := by
  intro o hm
  have := h o hm
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨lst', hx, h1, h2⟩ := this
    exact ⟨_, lst', hx, rfl, h1, h2⟩

/-! ## Scalars and constants -/

@[lockstep_simp] theorem core_walk_fuel_val :
    (arena.core.CORE_WALK_FUEL).val = coreWalkFuel := core_walk_fuel_abs

attribute [lockstep_simp] etag_const_abs etag_lit_abs etag_fvar_abs

@[lockstep_simp] theorem absU32_beq_const (t : Std.U32) :
    (absU32 t == ETag.const) = decide (t = arena.handle.ETAG_CONST) := by
  rw [← etag_const_abs]
  by_cases h : t = arena.handle.ETAG_CONST
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_CONST := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_lit (t : Std.U32) :
    (absU32 t == ETag.lit) = decide (t = arena.handle.ETAG_LIT) := by
  rw [← etag_lit_abs]
  by_cases h : t = arena.handle.ETAG_LIT
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_LIT := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_fvar (t : Std.U32) :
    (absU32 t == ETag.fvar) = decide (t = arena.handle.ETAG_FVAR) := by
  rw [← etag_fvar_abs]
  by_cases h : t = arena.handle.ETAG_FVAR
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_FVAR := fun hc => h (absU32_inj hc)
    simp [h, this]

/-! ## The environment -/

attribute [lockstep_simp] absIConstantInfo

/-- `arena::env::ifenv_find` against `IFEnv.find?`: the twin's lookup is a
pure expression, so the pair is a `TwinEq` the twin side is rewritten with. -/
@[lockstep] theorem ifenv_find_ls {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx vis fe lfe) (n : arena.handle.NIdx) :
    LSP (arena.env.ifenv_find vis fe n)
      (fun o => TwinEq (lfe.find? (absNIdx n)) (o.map absIConstantInfo)) :=
  fun _ h => (ifenv_find_abs hctx h).symm

@[lockstep] theorem reducibility_hint_dup_ls (h : kernel.env.ReducibilityHint) :
    LSP (kernel.env.reducibility_hint_dup h) (fun r => r = h) := by
  intro r hr
  cases h <;> simp [kernel.env.reducibility_hint_dup] at hr <;> exact hr.symm

/-! ## The spine readers (read-only `ExprOps` walks, proved in `Core/Arms/Delta.lean`) -/

@[lockstep] theorem get_app_fn_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.get_app_fn pers st fuel h) st lst
      (getAppFn (absU fuel) (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => get_app_fn_refines₀ hrel hinv hr

@[lockstep] theorem get_app_args_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = ExprOps.absEIdxList a)
      (arena.expr_ops.get_app_args pers st fuel h) st lst
      (getAppArgs (absU fuel) (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => get_app_args_refines₀ hrel hinv hr

/-! ## The `const` name projection -/

@[lockstep] theorem view_const_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absNIdx a) (arena.monad.view_const_name pers st h)
      st lst (Arena.viewConstName (absEIdx h)) := by
  intro o hrun
  refine ⟨_, lst, rfl, ?_, hrel, hinv⟩
  rw [arena.monad.view_const_name] at hrun
  exact (estore_view_const_name_abs hrel.store hrun).symm ▸ rfl

/-! ## The `ExprOps` walks, through the `ExprOpsHyp` seam

Each wrapper's `hx : ExprOpsHyp pers` premise is closed from the context by
`assumption`: a body lemma carries the bundle as a hypothesis, and
`Core/Arms.lean`'s `exprOpsHyp` is the one place it is discharged. -/

@[lockstep] theorem inst_lp_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel lps us value) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_lp_fast pers st fuel lps us value)
      lst (instLPFast (absU fuel) (lps.val.map absNIdx) (absLsIdx us) (absEIdx value)) :=
  LS.ofSim₀ fun _ h => hx.instLPFast hrel hinv h

@[lockstep] theorem mk_app_n_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (f args) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.mk_app_n pers st f args)
      lst (Arena.mkAppN (absEIdx f) (absEIdxList args)) :=
  LS.ofSim₀ fun _ h => hx.mkAppN hrel hinv h

@[lockstep] theorem mk_app_n_from_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (f args i) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.mk_app_n_from pers st f args i)
      lst (mkAppNFrom (absEIdx f) (absEIdxArr args) (absSz i)) :=
  LS.ofSim₀ fun _ h => hx.mkAppNFrom hrel hinv h

@[lockstep] theorem instantiate1_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e v d) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_fast pers st fuel e v d)
      lst (instantiate1Fast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) :=
  LS.ofSim₀ fun _ h => hx.instantiate1Fast hrel hinv h

@[lockstep] theorem instantiate_list_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e vs d) :
    LS pers (fun a b => b = absEIdx a)
      (arena.expr_ops.instantiate_list_fast pers st fuel e vs d)
      lst (instantiateListFast (absU fuel) (absEIdx e) (absEIdxArr vs) (absU d)) :=
  LS.ofSim₀ fun _ h => hx.instantiateListFast hrel hinv h

@[lockstep] theorem abstract1_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e d k) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract1_fast pers st fuel e d k)
      lst (abstract1Fast (absU fuel) (absEIdx e) (absU d) (absU k)) :=
  LS.ofSim₀ fun _ h => hx.abstract1Fast hrel hinv h

@[lockstep] theorem abstract_range_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e d k c) :
    LS pers (fun a b => b = absEIdx a)
      (arena.expr_ops.abstract_range_fast pers st fuel e d k c)
      lst (abstractRangeFast (absU fuel) (absEIdx e) (absU d) (absU k) (absU c)) :=
  LS.ofSim₀ fun _ h => hx.abstractRangeFast hrel hinv h

@[lockstep] theorem inst_spine_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel args t e) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_spine pers st fuel args t e)
      lst (instSpine (absU fuel) (absEIdxList args) (absU t) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hx.instSpine hrel hinv h

@[lockstep] theorem intern_rebuilt_app_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (h same f a) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_app pers st h same f a)
      lst (internRebuiltApp (absEIdx h) same (absEIdx f) (absEIdx a)) :=
  LS.ofSim₀ fun _ hr => hx.internRebuiltApp hrel hinv hr

@[lockstep] theorem bvar_b_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e) :
    LS pers (fun a b => b = absU a) (arena.expr_ops.bvar_b pers st fuel e)
      lst (bvarB (absU fuel) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hx.bvarB hrel hinv h

@[lockstep] theorem has_fvar_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e) :
    LS pers (fun a b => b = a) (arena.expr_ops.has_fvar_fast pers st fuel e)
      lst (hasFvarFast (absU fuel) (absEIdx e)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.hasFvarFast hrel hinv h

@[lockstep] theorem loose_bvars_bounded_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel k e) :
    LS pers (fun a b => b = a) (arena.expr_ops.loose_bvars_bounded_fast pers st fuel k e)
      lst (looseBVarsBoundedFast (absU fuel) (absU k) (absEIdx e)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.looseBVarsBoundedFast hrel hinv h

@[lockstep] theorem lam_pw_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (h) :
    LSR pers (fun a b => b = ExprOps.absPwOpt a) (arena.expr_ops.lam_pw pers st h) st lst
      (lamPw (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => hx.lamPw hrel hinv hr

@[lockstep] theorem pi_result_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel h) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.pi_result pers st fuel h) st lst
      (piResult (absU fuel) (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => hx.piResult hrel hinv hr

@[lockstep] theorem strip_pis_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (k h) :
    LSR pers (fun a b => b = ExprOps.absStrip a) (arena.expr_ops.strip_pis pers st k h) st lst
      (stripPis (absU k) (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => hx.stripPis hrel hinv hr

@[lockstep] theorem wscoped_b_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel d h) :
    LSR pers (fun a b => b = a) (arena.expr_ops.wscoped_b_fast pers st fuel d h) st lst
      (wscopedBFast (absU fuel) (absU d) (absEIdx h)) :=
  LSR.ofAOut₀ (A := id) fun _ hr => hx.wscopedBFast hrel hinv hr

@[lockstep] theorem leaf_guard_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel fab base) :
    LSR pers (fun a b => b = a) (arena.expr_ops.leaf_guard pers st fuel fab base) st lst
      (leafGuard (absU fuel) (absEIdx fab) (absEIdx base)) :=
  LSR.ofAOut₀ (A := id) fun _ hr => hx.leafGuard hrel hinv hr

@[lockstep] theorem proof_pw_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel a) :
    LS pers (fun a b => b = ExprOps.absPwOpt a) (arena.prop_read.proof_pw pers vis st fe fuel a)
      lst (proofPW lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ fun _ h => hx.proofPW hrel hinv hctx h

@[lockstep] theorem type_sort_pw_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel t) :
    LS pers (fun a b => b = ExprOps.absPwOpt a)
      (arena.prop_read.type_sort_pw pers vis st fe fuel t)
      lst (typeSortPW lfe (absU fuel) (absEIdx t)) :=
  LS.ofSim₀ fun _ h => hx.typeSortPW hrel hinv hctx h

@[lockstep] theorem is_proof_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel a) :
    LS pers (fun a b => b = a) (arena.prop_read.is_proof_fast pers vis st fe fuel a)
      lst (isProofFast lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.isProofFast hrel hinv hctx h

@[lockstep] theorem not_proof_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel a) :
    LS pers (fun a b => b = a) (arena.prop_read.not_proof_fast pers vis st fe fuel a)
      lst (notProofFast lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.notProofFast hrel hinv hctx h

/-! ## The Core lemmas closed before round 5, as `@[lockstep]` -/

@[lockstep] theorem ensure_sort_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absLIdx a)
      (arena.core.ensure_sort pers vis st mode lane fu fe depth e) lst
      (ensureSort (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => ensure_sort_refines hk hrel hinv hctx hf h

@[lockstep] theorem unfold_definition_ls {pers vis st fe lfe e lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.unfold_definition pers vis st fe e) lst
      (unfoldDefinition lfe (absEIdx e)) :=
  LS.ofSim₀ fun _ h => unfold_definition_refines hx hrel hinv hctx h

@[lockstep] theorem const_val_at_ls {pers st lst n lps value us}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.const_val_at pers st n lps value us) lst
      (constValAt (absNIdx n) (lps.val.map absNIdx) (absEIdx value) (absLsIdx us)) :=
  LS.ofSim₀ fun _ h => const_val_at_refines hx hrel hinv h

end ConRon.Refine2.Lockstep
