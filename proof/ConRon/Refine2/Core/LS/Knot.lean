/-
# `ConRon.Refine2.Core.LS.Knot` — the knot's six slots as `@[lockstep]` lemmas

Task #97-P5-Core round 5.  `KnotRel f`'s fields are `Sim₀` statements; here
each is restated in the `LS` judgement and filed under its port entry
(`arena.core.knot_whnf` …), so that a body's recursive call is one bind of
`lockstep_core`.  The premises `hk`, `hctx`, `hf` are closed from the context
by `assumption`.
-/
import ConRon.Refine2.Tactic.Prims
import ConRon.Refine2.Core.Arms.Delta

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

@[lockstep] theorem knot_whnf_core_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.knot_whnf_core pers vis st mode lane fu fe depth e) lst
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).whnfCore (absU depth) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hk.whnfCore hrel hinv hctx hf h

@[lockstep] theorem knot_whnf_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.knot_whnf pers vis st mode lane fu fe depth e) lst
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).whnf (absU depth) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hk.whnf hrel hinv hctx hf h

@[lockstep] theorem knot_infer_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.knot_infer pers vis st mode lane fu fe depth e) lst
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).infer (absU depth) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hk.infer hrel hinv hctx hf h

@[lockstep] theorem knot_infer_io_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.knot_infer_io pers vis st mode lane fu fe depth e) lst
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).inferIO (absU depth) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hk.inferIO hrel hinv hctx hf h

@[lockstep] theorem knot_infer_at_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane io fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.knot_infer_at pers vis st mode lane io fu fe depth e) lst
      ((laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f).infer (absU depth)
        (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hk.inferAt hrel hinv hctx hf h

@[lockstep] theorem knot_defeq_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun x y => y = x)
      (arena.core.knot_defeq pers vis st mode lane fu fe depth a b) lst
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).defeq (absU depth) (absEIdx a)
        (absEIdx b)) :=
  LS.ofSim₀ (A := id) fun _ h => hk.defeq hrel hinv hctx hf h

@[lockstep] theorem knot_annotate_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.knot_annotate pers vis st mode lane fu fe depth e) lst
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).annotate (absU depth)
        (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hk.annotate hrel hinv hctx hf h

end ConRon.Refine2.Lockstep
