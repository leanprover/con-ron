/-
# `ConRon.Refine2.Core.Arms.Batched` — the batched clauses, stated

**Task #97-P5-Arms.**  The five clauses P6 batched, each against the twin's own
batched form — *same shape both sides*, which is the point: tasks #97-P6-9, -11,
-12 and -14 changed the twin in lockstep, so there is no chained-versus-batched
identification to prove HERE.  (That identification is Theorem 1's, and task
#97-P6-14's own section writes it out on `defeq_peel`.)

What IS this tier's is task #97-P5-0's **finding 5**: one Rust type, two twin
containers.  `acc` is an `Array EIdx` in PUSH order (the accumulator ruling
before §8.7) and `args` an `Array EIdx` read from a cursor `i`, so
`ExprOps/Mut.lean`'s `absEIdxArr` is the reading on both — getting `absEIdxList`
in instead does not typecheck, which is the check the statements get for free.

These five are stated and open.  Each is a walk over its own second fuel
dimension (the spine's remaining length, measured by `args.size - i`), so the
shape step is `Refine2/Inv.lean`'s `lidx_vec_eq_from_iff` measure induction and
not `Core/Arms/Loops.lean`'s `Nat` induction — task #97-P5-0's finding 7 names
that as the other of the tier's two shape steps.
-/
import ConRon.Refine2.Core.Arms.Loops
import ConRon.Refine2.ExprOps.Mut
import ConRon.Refine2.Core.LS.WhnfCore
import ConRon.Refine2.Core.LS.Defeq

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

set_option maxRecDepth 4000

namespace ConRon.Refine2

open ConRon.Arena

/-- `arena::core::whnf_app` against `Arena.whnfApp` — the batched β spine's
head (task #97-P6-9). -/
theorem whnf_app_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.whnf_app pers vis st mode lane fu fe depth v hd vargs
      same args nodes i = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfApp (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx v) (absEIdx hd) (absEIdxArr vargs) same (absEIdxArr args)
        (absEIdxArr nodes) (absSz i)) :=
  Lockstep.LS.toSim₀ (Lockstep.whnf_app_ls hk hx hrel hinv hctx hf) hrun

/-- `arena::core::beta_peel` against `Arena.betaPeel` — the consecutive λ run
peeled into ONE `instantiateList` walk. -/
theorem beta_peel_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth t acc args nodes i lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.beta_peel pers vis st mode lane fu fe depth t acc args
      nodes i = ok o) :
    Sim₀ absEIdx pers lst o
      (betaPeel (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx t) (absEIdxArr acc) (absEIdxArr args) (absEIdxArr nodes)
        (absSz i)) :=
  Lockstep.LS.toSim₀ (Lockstep.beta_peel_ls hk hx hrel hinv hctx hf) hrun

/-- `arena::core::iota_rec_at` against `Arena.iotaRecAt` — the ι step at a
spine the caller already has. -/
theorem iota_rec_at_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth hd sargs n lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.iota_rec_at pers vis st mode lane fu fe depth hd sargs n
      = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (iotaRecAt (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx hd) (absEIdxArr sargs) (absSz n)) :=
  Lockstep.LS.toSim₀ (Lockstep.iota_rec_at_ls hk hx hrel hinv hctx hf) hrun

/-- `arena::core::defeq_peel_leaf` against `Arena.defeqPeelLeaf` — the batched
binder descent's leaf (task #97-P6-14). -/
theorem defeq_peel_leaf_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d a b k fvs mism mismLam lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.defeq_peel_leaf pers vis st mode lane fu fe d a b k fvs
      mism mismLam = ok o) :
    Sim₀ id pers lst o
      (defeqPeelLeaf (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        (absU d) (absEIdx a) (absEIdx b) (absU k) (absEIdxArr fvs) mism
        mismLam) :=
  Lockstep.LS.toSim₀ (Lockstep.defeq_peel_leaf_ls hk hx hrel hinv hctx hf) hrun

/-- `arena::core::whnf_core_stuck_app` against `Arena.whnfCoreStuckApp` — the
gated lane's only caller since the batched β landed. -/
theorem whnf_core_stuck_app_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h same fp a lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.whnf_core_stuck_app pers vis st mode lane fu fe depth h
      same fp a = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfCoreStuckApp (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h) same (absEIdx fp) (absEIdx a)) :=
  Lockstep.LS.toSim₀ (Lockstep.whnf_core_stuck_app_ls hk hx hrel hinv hctx hf) hrun

end ConRon.Refine2
