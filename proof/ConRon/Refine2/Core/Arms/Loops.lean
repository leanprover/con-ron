/-
# `ConRon.Refine2.Core.Arms.Loops` — the two loops, and the SECOND fuel dimension

**Task #97-P5-Arms.**  Task #97-P5-Core §7 names these as the shape that is not
the `ExprOps` tier's: *"a local loop's continuation is a closure in the twin and
a counter in the port"*.

    whnfStep  r fe depth (k : EIdx → AM EIdx) e         whnf_step  … n e
    whnfLoop  r fe depth (m + 1) e                      whnf_loop  … n e
    defeqStep mode r fe depth (k : Bool → EIdx → EIdx → AM Bool) pi a b
                                                        defeq_step … n pi a b

so the induction is on `n`, a second fuel dimension INSIDE the knot's induction
on `f`, and the refinement has to name the function the port's scalar stands
for.  This is task #97-P5-0's finding 6 (`RenameRel`) one level up, and it is
the same move `Core/KnotRel.lean` makes for the lane.

## Finding 13 — the off-by-one in task #97-P5-Core's two statements

That round stated `whnf_step_refines` against
`whnfStep … (whnfLoop … (absU n - 1))` with a side condition `1 ≤ absU n`, and
`defeq_step_refines` likewise.  **The port's `whnf_step` passes its own `n` on
unchanged**:

    whnf_loop(…, n, e) = if n = 0 then Internal else whnf_step(…, n - 1, e)
    whnf_step(…, n, e) = … whnf_loop(…, n, e₂) …

so `whnf_step(…, n, …)` is `whnfStep … (whnfLoop … (absU n))`: there is no
`- 1` and no side condition, because the decrement is the LOOP's and it is
exactly `whnfLoop (m + 1) = whnfStep … (whnfLoop m)`.  Stated the other way the
lemma claims the twin runs one iteration fewer than the port, which is false as
soon as a literal step or a delta step fires.  Both statements are re-cut here
and `1 ≤ absU n` is gone from both.

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

## What is still `sorry`, and why the cut is here

`unfold_definition_refines` **closed** at task #97-P5-Core-2 and moved to
`Core/Arms/Delta.lean`.  What is left of the `whnf` loop is `reduce_nat` —
the fifteen `natOp*` guards and `natOpResult`'s dispatch, a body of its own
and not a step of the loop — and the whole `defeq` pair, whose leaf
`defeq_after_whnf` has ≈ 40 helpers under it.  Nothing about the LOOP depends
on either: taken as hypotheses, the two `whnf` loop inductions close, which is
what this file is for.
-/
import ConRon.Refine2.Core.Arms.Delta
import ConRon.Refine2.Core.LS.Lits
import ConRon.Refine2.Core.LS.Defeq

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

/-! ## The twin's two equations -/

/-- `whnfStep`'s run, split at its three binds: the knot's `whnfCore`, then
`reduceNat`, then `unfoldDefinition`, with the continuation applied to
whichever reduct fired. -/
theorem whnfStep_run (r : CoreFnsA) (fe : IFEnv) (d : Nat)
    (k : EIdx → AM EIdx) (e : EIdx) (lst : AState) :
    (whnfStep r fe d k e).run lst
      = ((r.whnfCore d e).run lst) >>= fun p =>
          ((reduceNat r fe d p.1).run p.2) >>= fun q =>
            match q.1 with
            | some e2 => (k e2).run q.2
            | none =>
              ((unfoldDefinition fe p.1).run q.2) >>= fun s =>
                match s.1 with
                | some e2 => (k e2).run s.2
                | none => .ok (p.1, s.2) := by
  show ((do
      let e₁ ← r.whnfCore d e
      let n ← reduceNat r fe d e₁
      match n with
      | some e₂ => k e₂
      | none =>
        let u ← unfoldDefinition fe e₁
        match u with
        | some e₂ => k e₂
        | none => pure e₁) : AM EIdx).run lst = _
  rw [am_run_bind]
  cases (r.whnfCore d e).run lst with
  | error er => rfl
  | ok p =>
    obtain ⟨e1, lst1⟩ := p
    show ((do
        let n ← reduceNat r fe d e1
        match n with
        | some e₂ => k e₂
        | none =>
          let u ← unfoldDefinition fe e1
          match u with
          | some e₂ => k e₂
          | none => pure e1) : AM EIdx).run lst1
      = ((reduceNat r fe d e1).run lst1) >>= fun q =>
          match q.1 with
          | some e2 => (k e2).run q.2
          | none =>
            ((unfoldDefinition fe e1).run q.2) >>= fun s =>
              match s.1 with
              | some e2 => (k e2).run s.2
              | none => .ok (e1, s.2)
    rw [am_run_bind]
    cases (reduceNat r fe d e1).run lst1 with
    | error er => rfl
    | ok q =>
      obtain ⟨n, lst2⟩ := q
      cases n with
      | some e2 => rfl
      | none =>
        show ((do
            let u ← unfoldDefinition fe e1
            match u with
            | some e₂ => k e₂
            | none => pure e1) : AM EIdx).run lst2
          = ((unfoldDefinition fe e1).run lst2) >>= fun s =>
              match s.1 with
              | some e2 => (k e2).run s.2
              | none => .ok (e1, s.2)
        rw [am_run_bind]
        cases (unfoldDefinition fe e1).run lst2 with
        | error er => rfl
        | ok s => obtain ⟨u, lst3⟩ := s; cases u <;> rfl

/-- `whnfLoop` at a successor: one `whnfStep` whose continuation is the loop at
the predecessor.  The twin's own equation, named so the port's `n - 1` meets
it. -/
theorem whnfLoop_succ (r : CoreFnsA) (fe : IFEnv) (d m : Nat) (e : EIdx) :
    whnfLoop r fe d (m + 1) e = whnfStep r fe d (whnfLoop r fe d m) e := rfl

/-- `whnfLoop` at zero: the twin's own `internal`, which the port mirrors. -/
theorem whnfLoop_zero_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx)
    (lst : AState) :
    (whnfLoop r fe d 0 e).run lst
      = .error (Arena.CheckError.internal "fuel exhausted: whnf loop") := rfl

/-! ## `whnf_step`'s body, once, parametric in the continuation

The port's `whnf_step(n)` calls `whnf_loop(n)` and `whnf_loop(n)` calls
`whnf_step(n - 1)`, so the two are ONE recursion.  Factoring the step's body
out with the continuation's refinement as a hypothesis is what lets the loop's
induction and the public step lemma share it — the alternative is to write the
forty-line body twice. -/

private theorem whnf_step_of_cont {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hcont : ∀ {st' : arena.monad.AState} {lst' : AState} {e' o'},
      AStateRel₀ pers st' lst' → AStateInv pers st' →
      arena.core.whnf_loop pers vis st' mode lane fu fe depth n e' = ok o' →
      Sim₀ absEIdx pers lst' o'
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) (absU n) (absEIdx e')))
    (hrun : arena.core.whnf_step pers vis st mode lane fu fe depth n e = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth)
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) (absU n)) (absEIdx e)) := by
  rw [arena.core.whnf_step] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st1⟩ := p
  have hwc := hk.whnfCore hrel hinv hctx hf hp
  have t0 := whnfStep_run (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
    (absU depth)
    (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
      (absU depth) (absU n)) (absEIdx e) lst
  cases r with
  | Err er =>
    rw [← Result.ok_injective hrun]
    exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hwc) _) t0)
  | Ok e1 =>
    obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hwc
    have t1 : (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth)
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) (absU n)) (absEIdx e)).run lst
        = ((reduceNat (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
              (absU depth) (absEIdx e1)).run lst1) >>= fun q =>
            match q.1 with
            | some e2 =>
              ((whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
                  (absU depth) (absU n)) e2).run q.2
            | none =>
              ((unfoldDefinition lfe (absEIdx e1)).run q.2) >>= fun s =>
                match s.1 with
                | some e2 =>
                  ((whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
                      lfe (absU depth) (absU n)) e2).run s.2
                | none => .ok (absEIdx e1, s.2) := by
      rw [t0, hb1]; rfl
    obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r2, st2⟩ := p2
    have hrn := reduce_nat_refines hk hrel1 hinv1 hctx hf hp2
    cases r2 with
    | Err er =>
      rw [← Result.ok_injective hrun]
      exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hrn) _) t1)
    | Ok on =>
      obtain ⟨lst2, hb2, hrel2, hinv2⟩ := Sim₀.apply hrn
      cases on with
      | some e2 =>
        have t2 : (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
            lfe (absU depth)
            (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
              (absU depth) (absU n)) (absEIdx e)).run lst
            = ((whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
                (absU depth) (absU n)) (absEIdx e2)).run lst2 := by
          rw [t1, hb2]; rfl
        exact AOut₀.of_eq (hcont hrel2 hinv2 hrun) t2
      | none =>
        have t2 : (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
            lfe (absU depth)
            (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
              (absU depth) (absU n)) (absEIdx e)).run lst
            = ((unfoldDefinition lfe (absEIdx e1)).run lst2) >>= fun s =>
                match s.1 with
                | some e2 =>
                  ((whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
                      lfe (absU depth) (absU n)) e2).run s.2
                | none => .ok (absEIdx e1, s.2) := by
          rw [t1, hb2]; rfl
        obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r3, st3⟩ := p3
        have hud := unfold_definition_refines hx hrel2 hinv2 hctx hp3
        cases r3 with
        | Err er =>
          rw [← Result.ok_injective hrun]
          exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hud) _) t2)
        | Ok ou =>
          obtain ⟨lst3, hb3, hrel3, hinv3⟩ := Sim₀.apply hud
          cases ou with
          | some e2 =>
            have t3 : (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
                lfe (absU depth)
                (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
                  (absU depth) (absU n)) (absEIdx e)).run lst
                = ((whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
                    lfe (absU depth) (absU n)) (absEIdx e2)).run lst3 := by
              rw [t2, hb3]; rfl
            exact AOut₀.of_eq (hcont hrel3 hinv3 hrun) t3
          | none =>
            have t3 : (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
                lfe (absU depth)
                (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
                  (absU depth) (absU n)) (absEIdx e)).run lst
                = .ok (absEIdx e1, lst3) := by
              rw [t2, hb3]; rfl
            rw [← Result.ok_injective hrun]
            exact AOut₀.ok t3 hrel3 hinv3

/-! ## The loop, by induction on the port's counter -/

private theorem whnf_loop_aux {f : Nat} (hk : KnotRel f) (m : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth n e lst o},
      ExprOpsHyp pers →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      absU fu = f →
      absU n = m →
      arena.core.whnf_loop pers vis st mode lane fu fe depth n e = ok o →
      Sim₀ absEIdx pers lst o
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) m (absEIdx e)) := by
  induction m with
  | zero =>
    intro pers vis st mode lane fu fe lfe depth n e lst o _hx _hrel _hinv
      _hctx _hf hn hrun
    rw [arena.core.whnf_loop, if_pos (absU_eq_zero hn)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hr1] at hrun
    rw [← Result.ok_injective hrun]
    exact AOut₀.err (AErrSim.internal (s := "fuel exhausted: whnf loop")
      (whnfLoop_zero_run _ _ _ _ _))
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe depth n e lst o hx hrel hinv hctx
      hf hn hrun
    rw [arena.core.whnf_loop, if_neg (absU_ne_zero hn)] at hrun
    obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hiv : absU i = m := absU_pred hn hi
    rw [whnfLoop_succ, ← hiv]
    refine whnf_step_of_cont hk hx hrel hinv hctx hf ?_ hrun
    intro st' lst' e' o' hrel' hinv' hrun'
    rw [hiv]
    exact ih hx hrel' hinv' hctx hf hiv hrun'

/-- `arena::core::whnf_loop` against `Arena.whnfLoop` — the second fuel
dimension, closed (modulo `reduce_nat_refines` and the `ExprOpsHyp` seam). -/
theorem whnf_loop_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.whnf_loop pers vis st mode lane fu fe depth n e = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absU n) (absEIdx e)) :=
  whnf_loop_aux hk (absU n) hx hrel hinv hctx hf rfl hrun

/-- `arena::core::whnf_step` against `Arena.whnfStep` with the rest of the loop
named: **the port's `n` IS the twin's continuation `whnfLoop … (absU n)`** — no
`- 1`, see the module note's finding 13. -/
theorem whnf_step_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.whnf_step pers vis st mode lane fu fe depth n e = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth)
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) (absU n)) (absEIdx e)) :=
  whnf_step_of_cont hk hx hrel hinv hctx hf
    (fun h1 h2 h3 => whnf_loop_refines hk hx h1 h2 hctx hf h3) hrun

/-- `arena::core::whnf_body` against `Arena.whnfBody`: the loop at its own step
budget, `WHNF_LOOP_FUEL = whnfLoopFuel = 100000` on both sides. -/
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

/-! ## The `defeq` loop — stated at the corrected shape, open

The same pair at the lazy-delta loop.  Its leaf, `arena::core::defeq_after_whnf`,
has **no named twin** — it is the tail of `Arena.defeqStep`, one of task
#97-P5-0's finding-6 splits — so its statement needs a local transcription plus
an `_unfold` equation back to `defeqStep`, in the shape `ExprOps/Read.lean`
already has for `wscopedBGo`.  That transcription, not the loop, is what the
next round owes here: with it, `defeq_loop_refines` and `defeq_step_refines`
are `whnf_loop_aux` and `whnf_step_of_cont` verbatim. -/

/-- `arena::core::defeq_loop` against `Arena.defeqLoop`. -/
theorem defeq_loop_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n pi a b lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.defeq_loop pers vis st mode lane fu fe depth n pi a b
      = ok o) :
    Sim₀ id pers lst o
      (defeqLoop (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absU n) pi (absEIdx a) (absEIdx b)) :=
  Lockstep.LS.toSim₀ (Lockstep.defeq_loop_ls hk hx hrel hinv hctx hf) hrun

/-- `arena::core::defeq_step` against `Arena.defeqStep` — **the port's `n` IS
the twin's continuation `defeqLoop … (absU n)`**, finding 13 again. -/
theorem defeq_step_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n pi a b lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.defeq_step pers vis st mode lane fu fe depth n pi a b
      = ok o) :
    Sim₀ id pers lst o
      (defeqStep (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (defeqLoop (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
          (absU n)) pi (absEIdx a) (absEIdx b)) :=
  Lockstep.LS.toSim₀ (Lockstep.defeq_step_ls hk hx hrel hinv hctx hf) hrun

/-- `arena::core::defeq_body` against `Arena.defeqBody`: the loop at its own
step budget, `DEFEQ_LOOP_FUEL = defeqLoopFuel = 100000` on both sides, at
`pi = true`. -/
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
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.defeq_body] at hrun
  have h := defeq_loop_refines hk hx hrel hinv hctx hf hrun
  rw [show absU arena.core.DEFEQ_LOOP_FUEL = Arena.defeqLoopFuel from by
    rw [arena.core.DEFEQ_LOOP_FUEL, Arena.defeqLoopFuel]; rfl] at h
  exact h

section Axioms

/-- info: 'ConRon.Refine2.whnfStep_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnfStep_run

end Axioms

end ConRon.Refine2
