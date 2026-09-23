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

end ConRon.Refine2.Lockstep
