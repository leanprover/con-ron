import ConRon.Refine2.Core.LS.Prims
import ConRon.Refine2.Core.Arms.Batched

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

attribute [local lockstep_inline] arena.core.whnf_core_proj arena.core.whnf_core_proj_at
  arena.core.whnf_core_proj_fire

example {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.whnf_core_body pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfCoreBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) := by
  refine LS.toSim₀ ?_ hrun
  rw [arena.core.whnf_core_body, whnfCoreBody]
  lockstep_core
  all_goals trace_state
  all_goals sorry

end ConRon.Refine2.Lockstep
