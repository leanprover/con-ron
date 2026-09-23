import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

theorem is_ctor_app_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.is_ctor_app pers vis st fe e) lst
      (isCtorApp lfe (absEIdx e)) := by
  rw [arena.core.is_ctor_app, isCtorApp]
  lockstep_core
  all_goals trace_state
  all_goals sorry

theorem head_hint_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = ConRon.Refine.absHint a) (arena.core.head_hint pers vis st fe e) lst
      (headHint lfe (absEIdx e)) := by
  rw [arena.core.head_hint, headHint]
  lockstep_core
  all_goals trace_state
  all_goals sorry

end ConRon.Refine2.Lockstep
