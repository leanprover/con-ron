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

Two hypotheses that are **Theorem 1's and are carried rather than proved**,
bundled as `CoreAmbient` so that P3's `StateOK` deletes them in one edit:

* `wf` — *"every twin state related to a port state this run reaches is well
  formed"*.  A loop re-enters its own body at a state its callees left, and
  `AOut` carries `Ext`, which does NOT carry `StoreWF`: `Arena/WF.lean`'s rank
  witness is re-established by the intern lemmas, not by `Ext`.
* `resWhnfCore` — `Core/Arms/Sort.lean`'s `AnswerResolves` at
  `knot_whnf_core`, because `whnf_step` hands the reduct straight to
  `reduce_nat` and to `unfold_definition`, both of which read its view.

Neither is new: both are clauses of what task #97-P5-0's finding 3 and task
#97-P5-Core §3 already say P3 owes this tier.

## What is still `sorry`, and why the cut is here

`reduce_nat_refines` and `unfold_definition_refines` — the `whnf` loop's two
leaves — are stated and open, and so is the whole `defeq` pair.  They are the
BODIES' own work (`reduce_nat` alone pulls in the fifteen `natOp*` guards;
`defeq_after_whnf` has ≈ 40 helpers under it) and nothing about the LOOP
depends on their proofs: taken as hypotheses, the two `whnf` loop inductions
close, which is what this file is for.
-/
import ConRon.Refine2.Core.Arms.Sort

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

set_option maxRecDepth 8000

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (EResolves)

/-! ## Two `AOut` moves that belong in `Refine2/Shape.lean`

Both are what a LOOP needs and a straight-line body does not: an outcome
established against a later twin state, re-based on the state the loop
started in. -/

/-- `AOut` transported along an equality of runs. -/
theorem AOut.of_eq' {α β : Type} {A : α → β} {WF : α → Prop}
    {o : core.result.Result α kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {lst : AState} {st' : arena.monad.AState}
    {x y : Except Arena.CheckError (β × AState)}
    (h : AOut A WF pers lst o st' x) (hxy : y = x) :
    AOut A WF pers lst o st' y := by rw [hxy]; exact h

/-- **The loop's re-basing move**: an outcome measured from `lst2` is an
outcome measured from any `lst` that `lst2` extends. -/
theorem AOut.widen {α β : Type} {A : α → β} {WF : α → Prop}
    {o : core.result.Result α kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {lst lst2 : AState}
    {st' : arena.monad.AState} {x : Except Arena.CheckError (β × AState)}
    (h : AOut A WF pers lst2 o st' x) (hext : Ext lst.store lst2.store) :
    AOut A WF pers lst o st' x := by
  cases o with
  | Err e => exact h
  | Ok r =>
    obtain ⟨lst', hx, h1, h2, h3, h4⟩ := h
    exact ⟨lst', hx, h1, h2, Ext.trans hext h3, h4⟩

/-! ## The carried half of P3's `StateOK` -/

/-- **What the two loops are carried on** — see the module note.  One structure
so that P3's `StateOK` clause replaces it in one edit. -/
structure CoreAmbient (pers : arena.store.PersTier) (vis : Std.U64)
    (mode : kernel.env.CheckMode) (lane : Std.U32) (fu : Std.U64)
    (fe : arena.env.IFEnv) : Prop where
  /-- Every twin state related to a port state this run reaches is well formed.
  `Ext` does not carry `StoreWF`, and a loop re-enters at its callees' state. -/
  wf : ∀ (st' : arena.monad.AState) (lst' : AState),
    AStateRel pers st' lst' → AStateInv pers st' → StoreWF lst'.store
  /-- `knot_whnf_core`'s answer resolves — finding 3 at the callee's answer
  (`Core/Arms/Sort.lean`'s `AnswerResolves`). -/
  resWhnfCore : ∀ {st' : arena.monad.AState} {depth e p},
    arena.core.knot_whnf_core pers vis st' mode lane fu fe depth e = ok p →
    AnswerResolves pers p
  /-- **`EResolves` travels along `Ext` on a well-formed store.**  `Ext` is a
  DENOTATION-preservation statement (`Arena/Denote.lean`), so on its own it
  says nothing about `view`; it carries `EResolves` only because
  `Arena/WF.lean`'s denotation is total on a well-formed store, which is again
  Theorem 1's.  `whnf_step` needs it because `unfold_definition` reads the
  `whnfCore` reduct at the state `reduce_nat` left. -/
  resExt : ∀ {lst1 lst2 : AState} {h : EIdx}, StoreWF lst1.store →
    Ext lst1.store lst2.store → EResolves lst1 h → EResolves lst2 h

/-- The `Option EIdx` form of `AnswerResolves`: what `reduce_nat` and
`unfold_definition` owe about the reduct they hand back to the loop. -/
def AnswerResolvesOpt (pers : arena.store.PersTier)
    (p : core.result.Result (Option arena.handle.EIdx)
      kernel.core_types.CheckError × arena.monad.AState) : Prop :=
  ∀ w, p.1 = .Ok (some w) → ∀ lst', AStateRel pers p.2 lst' →
    EResolves lst' (absEIdx w)

/-! ## The `whnf` loop's two leaves — stated, open -/

/-- `arena::core::reduce_nat` against `Arena.reduceNat` — the literal
acceleration.  **Open**: the fifteen `natOp*` guards and `natOpResult`'s own
dispatch, i.e. a body of its own and not a step of the loop.  The second
conjunct is what the loop needs of it beyond the simulation: the reduct it
answers is a handle the loop re-enters at. -/
theorem reduce_nat_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hrun : arena.core.reduce_nat pers vis st mode lane fu fe depth e = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (reduceNat (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))
    ∧ AnswerResolvesOpt pers o := by
  sorry

/-- `arena::core::unfold_definition` against `Arena.unfoldDefinition` — one
delta step.  **Open**: `getAppFn`, the environment probe, `constValAt`'s
memoised level substitution and `mkAppN`.  It takes neither `mode` nor `lane`
nor `fuel` — it is not a knot caller — so it carries no `KnotRel`. -/
theorem unfold_definition_refines {pers vis st fe lfe e lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e))
    (hrun : arena.core.unfold_definition pers vis st fe e = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (unfoldDefinition lfe (absEIdx e))
    ∧ AnswerResolvesOpt pers o := by
  sorry

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
    (ha : CoreAmbient pers vis mode lane fu fe)
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hcont : ∀ {st' : arena.monad.AState} {lst' : AState} {e' o'},
      AStateRel pers st' lst' → AStateInv pers st' → StoreWF lst'.store →
      EResolves lst' (absEIdx e') →
      arena.core.whnf_loop pers vis st' mode lane fu fe depth n e' = ok o' →
      Sim absEIdx (fun _ => True) pers lst' o'
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) (absU n) (absEIdx e')))
    (hrun : arena.core.whnf_step pers vis st mode lane fu fe depth n e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth)
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) (absU n)) (absEIdx e)) := by
  rw [arena.core.whnf_step] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st1⟩ := p
  have hwc := hk.whnfCore hrel hinv hctx hwf hres hf hp
  have t0 := whnfStep_run (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
    (absU depth)
    (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
      (absU depth) (absU n)) (absEIdx e) lst
  cases r with
  | Err er =>
    rw [← Result.ok_injective hrun]
    exact AOut.err (AErrSim.of_eq (AErrSim.bind (Sim.apply_err hwc) _) t0)
  | Ok e1 =>
    obtain ⟨lst1, hb1, hrel1, hinv1, hext1, -⟩ := Sim.apply hwc
    have hres1 : EResolves lst1 (absEIdx e1) := ha.resWhnfCore hp e1 rfl lst1 hrel1
    have hwf1 : StoreWF lst1.store := ha.wf _ _ hrel1 hinv1
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
    obtain ⟨hrn, hrnres⟩ :=
      reduce_nat_refines hk hrel1 hinv1 hctx hwf1 hres1 hf hp2
    cases r2 with
    | Err er =>
      rw [← Result.ok_injective hrun]
      exact AOut.err (AErrSim.of_eq (AErrSim.bind (Sim.apply_err hrn) _) t1)
    | Ok on =>
      obtain ⟨lst2, hb2, hrel2, hinv2, hext2, -⟩ := Sim.apply hrn
      have hwf2 : StoreWF lst2.store := ha.wf _ _ hrel2 hinv2
      cases on with
      | some e2 =>
        have t2 : (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
            lfe (absU depth)
            (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
              (absU depth) (absU n)) (absEIdx e)).run lst
            = ((whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
                (absU depth) (absU n)) (absEIdx e2)).run lst2 := by
          rw [t1, hb2]; rfl
        have hres2 : EResolves lst2 (absEIdx e2) := hrnres e2 rfl lst2 hrel2
        exact AOut.of_eq'
          (AOut.widen (hcont hrel2 hinv2 hwf2 hres2 hrun)
            (Ext.trans hext1 hext2)) t2
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
        obtain ⟨hud, hudres⟩ :=
          unfold_definition_refines hrel2 hinv2 hctx hwf2 (ha.resExt hwf1 hext2 hres1) hp3
        cases r3 with
        | Err er =>
          rw [← Result.ok_injective hrun]
          exact AOut.err (AErrSim.of_eq (AErrSim.bind (Sim.apply_err hud) _) t2)
        | Ok ou =>
          obtain ⟨lst3, hb3, hrel3, hinv3, hext3, -⟩ := Sim.apply hud
          have hwf3 : StoreWF lst3.store := ha.wf _ _ hrel3 hinv3
          cases ou with
          | some e2 =>
            have t3 : (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
                lfe (absU depth)
                (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
                  (absU depth) (absU n)) (absEIdx e)).run lst
                = ((whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
                    lfe (absU depth) (absU n)) (absEIdx e2)).run lst3 := by
              rw [t2, hb3]; rfl
            have hres3 : EResolves lst3 (absEIdx e2) := hudres e2 rfl lst3 hrel3
            exact AOut.of_eq'
              (AOut.widen (hcont hrel3 hinv3 hwf3 hres3 hrun)
                (Ext.trans (Ext.trans hext1 hext2) hext3)) t3
          | none =>
            have t3 : (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
                lfe (absU depth)
                (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
                  (absU depth) (absU n)) (absEIdx e)).run lst
                = .ok (absEIdx e1, lst3) := by
              rw [t2, hb3]; rfl
            rw [← Result.ok_injective hrun]
            exact AOut.ok t3 hrel3 hinv3
              (Ext.trans (Ext.trans hext1 hext2) hext3) trivial

/-! ## The loop, by induction on the port's counter -/

private theorem whnf_loop_aux {f : Nat} (hk : KnotRel f) (m : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth n e lst o},
      CoreAmbient pers vis mode lane fu fe →
      AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
      absU n = m →
      arena.core.whnf_loop pers vis st mode lane fu fe depth n e = ok o →
      Sim absEIdx (fun _ => True) pers lst o
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) m (absEIdx e)) := by
  induction m with
  | zero =>
    intro pers vis st mode lane fu fe lfe depth n e lst o _ha _hrel _hinv _hctx
      _hwf _hres _hf hn hrun
    rw [arena.core.whnf_loop, if_pos (absU_eq_zero hn)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hr1] at hrun
    rw [← Result.ok_injective hrun]
    exact AOut.err (AErrSim.internal (s := "fuel exhausted: whnf loop")
      (whnfLoop_zero_run _ _ _ _ _))
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe depth n e lst o ha hrel hinv hctx hwf
      hres hf hn hrun
    rw [arena.core.whnf_loop, if_neg (absU_ne_zero hn)] at hrun
    obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hiv : absU i = m := absU_pred hn hi
    rw [whnfLoop_succ, ← hiv]
    refine whnf_step_of_cont hk ha hrel hinv hctx hwf hres hf ?_ hrun
    intro st' lst' e' o' hrel' hinv' hwf' hres' hrun'
    rw [hiv]
    exact ih ha hrel' hinv' hctx hwf' hres' hf hiv hrun'

/-- `arena::core::whnf_loop` against `Arena.whnfLoop` — the second fuel
dimension, closed. -/
theorem whnf_loop_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n e lst o}
    (ha : CoreAmbient pers vis mode lane fu fe)
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hrun : arena.core.whnf_loop pers vis st mode lane fu fe depth n e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absU n) (absEIdx e)) :=
  whnf_loop_aux hk (absU n) ha hrel hinv hctx hwf hres hf rfl hrun

/-- `arena::core::whnf_step` against `Arena.whnfStep` with the rest of the loop
named: **the port's `n` IS the twin's continuation `whnfLoop … (absU n)`** — no
`- 1`, see the module note's finding 13. -/
theorem whnf_step_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n e lst o}
    (ha : CoreAmbient pers vis mode lane fu fe)
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hrun : arena.core.whnf_step pers vis st mode lane fu fe depth n e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth)
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) (absU n)) (absEIdx e)) :=
  whnf_step_of_cont hk ha hrel hinv hctx hwf hres hf
    (fun h1 h2 h3 h4 h5 => whnf_loop_refines hk ha h1 h2 hctx h3 h4 hf h5) hrun

/-- `arena::core::whnf_body` against `Arena.whnfBody`: the loop at its own step
budget, `WHNF_LOOP_FUEL = whnfLoopFuel = 100000` on both sides. -/
theorem whnf_body_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (ha : CoreAmbient pers vis mode lane fu fe)
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hrun : arena.core.whnf_body pers vis st mode lane fu fe depth e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (whnfBody (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) := by
  rw [arena.core.whnf_body] at hrun
  have h := whnf_loop_refines hk ha hrel hinv hctx hwf hres hf hrun
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
    (ha : CoreAmbient pers vis mode lane fu fe)
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hra : EResolves lst (absEIdx a)) (hrb : EResolves lst (absEIdx b))
    (hf : absU fu = f)
    (hrun : arena.core.defeq_loop pers vis st mode lane fu fe depth n pi a b
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (defeqLoop (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absU n) pi (absEIdx a) (absEIdx b)) := by
  sorry

/-- `arena::core::defeq_step` against `Arena.defeqStep` — **the port's `n` IS
the twin's continuation `defeqLoop … (absU n)`**, finding 13 again. -/
theorem defeq_step_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n pi a b lst o}
    (ha : CoreAmbient pers vis mode lane fu fe)
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hra : EResolves lst (absEIdx a)) (hrb : EResolves lst (absEIdx b))
    (hf : absU fu = f)
    (hrun : arena.core.defeq_step pers vis st mode lane fu fe depth n pi a b
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (defeqStep (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (defeqLoop (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
          (absU n)) pi (absEIdx a) (absEIdx b)) := by
  sorry

/-- `arena::core::defeq_body` against `Arena.defeqBody`: the loop at its own
step budget, `DEFEQ_LOOP_FUEL = defeqLoopFuel = 100000` on both sides, at
`pi = true`. -/
theorem defeq_body_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst o}
    (ha : CoreAmbient pers vis mode lane fu fe)
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hra : EResolves lst (absEIdx a)) (hrb : EResolves lst (absEIdx b))
    (hf : absU fu = f)
    (hrun : arena.core.defeq_body pers vis st mode lane fu fe depth a b
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (defeqBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.defeq_body] at hrun
  have h := defeq_loop_refines hk ha hrel hinv hctx hwf hra hrb hf hrun
  rw [show absU arena.core.DEFEQ_LOOP_FUEL = Arena.defeqLoopFuel from by
    rw [arena.core.DEFEQ_LOOP_FUEL, Arena.defeqLoopFuel]; rfl] at h
  exact h

section Axioms

/-- info: 'ConRon.Refine2.AOut.widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AOut.widen

/-- info: 'ConRon.Refine2.whnfStep_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnfStep_run

end Axioms

end ConRon.Refine2
