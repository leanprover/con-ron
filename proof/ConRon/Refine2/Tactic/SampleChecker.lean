/-
# `ConRon.Refine2.Tactic.SampleChecker` — the lockstep tactic on a checker arm

Task #97-T2-TACTIC, sample 4.  `check_value_group` (old:
`Checker/Base.lean`, `check_value_group_refines`, 83 lines).  Its three callees
are other lanes' lemmas; their lockstep statements are hypotheses here.
-/
import ConRon.Refine2.Tactic.Prims
import ConRon.Refine2.Checker.Base

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.Sample

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

attribute [local lockstep_simp] check_fuel_abs

set_option profiler true in
theorem check_value_group_refines' {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup} {o}
    (hITC : ∀ {pers vis st mode fe lfe fu depth e lst},
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_type_core pers vis st mode fe fu depth e) lst
        (Arena.inferTypeCore (ConRon.Refine.absMode mode) lfe (absU fu) (absU depth)
          (absEIdx e)))
    (hESC : ∀ {pers vis st mode fe lfe fu depth e lst},
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      LS pers (fun a b => b = absLIdx a)
        (arena.core.ensure_sort_core pers vis st mode fe fu depth e) lst
        (ensureSortCore (ConRon.Refine.absMode mode) lfe (absU fu) (absU depth)
          (absEIdx e)))
    (hCVGV : ∀ {pers st lst} {vis : Std.U64} {rf lf} {mode} {g} {u},
      AStateRel₀ pers st lst → AStateInv pers st → IFEnvRel rf lf → IFEnvInv rf →
      LS pers (fun _ b => b = ())
        (arena.checker_split.check_value_group_value pers vis st mode rf g u) lst
        (checkValueGroupValueSpec (ConRon.Refine.absMode mode)
          (lf.restrictTo (absU vis)) (absValueGroup g) (absLIdx u)))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_split.check_value_group pers vis st mode rf g = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkValueGroup (ConRon.Refine.absMode mode) (lf.restrictTo (absU vis))
        (absValueGroup g)) := by
  have hctx := IFEnvInv.coreCtxAt vis hfe hfinv
  refine LS.toSim₀ ?_ hrun
  rw [arena.checker_split.check_value_group, checkValueGroup_unfold]
  lockstep

#print axioms check_value_group_refines'

end ConRon.Refine2.Lockstep.Sample
