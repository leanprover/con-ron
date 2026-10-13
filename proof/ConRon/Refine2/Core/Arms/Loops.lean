/-
# `ConRon.Refine2.Core.Arms.Loops` — the `whnf` loop, and the SECOND fuel dimension

**Task #97-P5-Arms.**  Task #97-P5-Core §7 names these as the shape that is not
the `ExprOps` tier's: *"a local loop's continuation is a closure in the twin and
a counter in the port"*.

    whnfStep  r fe depth e : AM WhnfStep               whnf_step  … e
    whnfLoop  r fe depth (m + 1) e                      whnf_loop_loop  … k e

so the induction is on `k`, a second fuel dimension INSIDE the knot's induction
on `f`.  This is task #97-P5-0's finding 6 (`RenameRel`) one level up, and it is
the same move `Core/KnotRel.lean` makes for the lane.  (The `defeq` side had the
same pair, `defeqStep`/`defeqLoop`, until con-leche 8afe1815 — task #109 —
restructured definitional equality after the official `is_def_eq_core`; its
two remaining loops recurse on their own budget without a continuation, see
the last section.)

## The `WhnfStep` loop (task #119, con-leche's task #342 R2)

The step no longer takes the loop as a continuation: `whnf_step` returns a
`WhnfStep` and the loop iterates it (`whnf_loop_loop`, Aeneas's
`-loops-to-rec` spelling), as the twin's `whnfStep` / `whnfLoop` do.  So the
induction is on the loop's own counter `k` against the twin's `whnfLoop k`,
and task #97-P5-Core's finding 13 (the off-by-one between the step's `n` and
the loop's) has nothing left to say: the decrement is the loop's alone.

## What the loops are carried on

**Since task #97-P5-Core round 4, nothing but `ExprOpsHyp pers`** —
`Core/Arms/Delta.lean`'s bundle of the two `arena::expr_ops` walks the delta
leaf borrows, at the lockstep shape.  The loops are stated over `AStateRel₀`
with `Sim₀` conclusions, so the old `CoreAmbient` bundle is gone with every
one of its clauses: `wf` (`StoreWF` at every state the loop re-enters) left
with `storeWF`, which is Theorem 1's; `resWhnfCore` (the `whnfCore` reduct
resolves) and `resExt` (resolution travels along `Ext`) left because the twin
now tests the reduct's TAG where the port does — `reduceNat` and
`unfoldDefinition` are tag-first (round 4's audit) — and `Ext` is not in the
conclusion any more.  `AOut.widen`, the loop's old re-basing move, is gone
too: `AOut₀` does not mention the state a call started in.

## What was still `sorry`, and why the cut is here

(Everything below is closed since task #97-P5-Core rounds 5–6.)
`unfold_definition_refines` **closed** at task #97-P5-Core-2 and moved to
`Core/Arms/Delta.lean`.  What is left of the `whnf` loop is `reduce_nat` —
the fifteen `natOp*` guards and `natOpResult`'s dispatch, a body of its own
and not a step of the loop — and the whole `defeq` body, with its ≈ 40
helpers.  Nothing about the LOOP depends on either: taken as hypotheses, the
two `whnf` loop inductions close, which is what this file is for.
-/
import ConRon.Refine2.Core.Arms.Delta
import ConRon.Refine2.Core.LS.Lits
import ConRon.Refine2.Core.LS.Defeq

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PB.CoreLSReg ConRon.Refine2.Lockstep.PC1.CoreLSReg ConRon.Refine2.Lockstep.PF.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

set_option maxRecDepth 8000

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The `whnf` loop's two leaves — one closed, one open

`unfold_definition_refines` lives in `Core/Arms/Delta.lean`; what is left
here is `reduce_nat`. -/

/-- `arena::core::reduce_nat` against `Arena.reduceNat` — the literal
acceleration.  **Open**: the fifteen `natOp*` guards and `natOpResult`'s own
dispatch, i.e. a body of its own and not a step of the loop.  Its old second
conjunct ("the reduct resolves") is gone: the twin's `reduceNat` is tag-first
now, as the port's is (round 4's audit). -/
theorem reduce_nat_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.reduce_nat pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (reduceNat (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) :=
  Lockstep.LS.toSim₀ (Lockstep.reduce_nat_ls hk hrel hinv hctx hf) hrun

/-! ## The step and the loop, in lockstep

Since con-leche's task #342 R2 the step RETURNS its continuation
(`WhnfStep`) and the loop is the iteration (`whnf_loop_loop`, Aeneas's
`-loops-to-rec` spelling of the Rust `loop`), so the second fuel dimension is
the loop's own counter against the twin's `whnfLoop` argument, one induction,
and the step is a plain zip. -/

namespace Lockstep

open scoped ConRon.Refine2.Lockstep.PD.CoreLSReg

attribute [local lockstep_simp] absWhnfStep

@[lockstep] theorem whnf_step_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.whnf_step pers vis st mode lane fu fe depth e) lst
      (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx e)) := by
  rw [arena.core.whnf_step, whnfStep]
  lockstep

theorem whnf_loop_loop_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth k cur lst},
      ExprOpsHyp pers → (k : Std.U64).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.whnf_loop_loop pers vis st mode lane fu fe depth k cur) lst
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) n
          (absEIdx cur)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe depth k cur lst hx hn hrel hinv hctx hf
    rw [arena.core.whnf_loop_loop, whnfLoop, ite_eq_left (by scalar_tac)]
    lockstep
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe depth k cur lst hx hn hrel hinv hctx hf
    rw [arena.core.whnf_loop_loop, whnfLoop, ite_eq_right (by scalar_tac)]
    lockstep

@[lockstep] theorem whnf_loop_loop_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth k cur lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf_loop_loop pers vis st mode lane fu fe depth k cur) lst
      (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absU k)
        (absEIdx cur)) :=
  whnf_loop_loop_aux hk _ hx rfl hrel hinv hctx hf

end Lockstep

/-- `arena::core::whnf_loop` against `Arena.whnfLoop` — the second fuel
dimension, closed. -/
theorem whnf_loop_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.whnf_loop pers vis st mode lane fu fe depth n e = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absU n) (absEIdx e)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.core.whnf_loop]
  lockstep

/-- `arena::core::whnf_body` against `Arena.whnfBody`: the loop at its own step
budget, `WHNF_LOOP_FUEL = whnfLoopFuel` on both sides. -/
theorem whnf_body_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.whnf_body pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfBody (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) := by
  rw [arena.core.whnf_body] at hrun
  have h := whnf_loop_refines hk hx hrel hinv hctx hf hrun
  rw [show absU arena.core.WHNF_LOOP_FUEL = Arena.whnfLoopFuel from by
    rw [arena.core.WHNF_LOOP_FUEL, Arena.whnfLoopFuel]; rfl] at h
  exact h

/-! ## The `defeq` body

con-leche 8afe1815 (task #109) replaced the `defeq` step/loop pair by the
official kernel's `is_def_eq_core` shape: `defeqBody` runs straight through,
and the two loops left — `lazyDeltaReduction` and `lazyDeltaProjReduction` —
recurse on their OWN budget, `n + 1 ↦ n` in the twin and `n - 1` at `n ≠ 0` in
the port, so their port counter IS the twin's argument and neither has a
continuation (`Core/LS/Defeq.lean` proves them by induction on that counter).
The second-fuel-dimension shape of this file is now the `whnf` loop's alone. -/

/-- `arena::core::defeq_body` against `Arena.defeqBody`. -/
theorem defeq_body_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.defeq_body pers vis st mode lane fu fe depth a b
      = ok o) :
    Sim₀ id pers lst o
      (defeqBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) :=
  Lockstep.LS.toSim₀ (Lockstep.defeq_body_ls hk hx hrel hinv hctx hf) hrun

section Axioms

/-- info: 'ConRon.Refine2.whnf_body_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_body_refines

end Axioms

end ConRon.Refine2
