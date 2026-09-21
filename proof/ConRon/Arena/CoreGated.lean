/-
# `ConRon.Arena.CoreGated` — the gated (proof-tier) knot, over handles

The twin of `ConLeche/Kernel/CoreGated.lean`: `whnfCoreBody` with one clause
changed — the `.app` clause's β certificate is skipped when the λ-binder's
validated annotation licenses it — and the knot that ties it.  Every other
clause (iota, the projection rule, the value clauses) is `whnfCoreBody`'s,
verbatim.

**Class (S) in the census, twinned anyway**, for the same reason as
`CoreIO.lean`: con-leche's Rust port skips the gated variants because it has
one knot, and so does the arena; what these nine declarations are is the
*subject* a gated-lane claims tower would be stated at, and P3 will want
them to exist in the arena's own spelling rather than have to invent one.

**Unlike `coreKnotIO`, this knot is not a leaf**: reduction sits under
definitional equality and inference, so a gated `whnfCore` propagates through
the whole knot.  It is therefore a duplicated KNOT rather than a duplicated
clause — and, as in con-leche, it carries no memo: the executed core is
`Core.lean`'s `coreKnot`, and a second memoized knot over the same state
would let one lane's table answer the other lane's query, which DESIGN §8.3's
lesson 9 forbids.

The two β arms differ from `Core.lean`'s in one further way that is
con-leche's, not the arena's: the gated body's certificate infers at the
FULL grade (`r.infer`), where `whnfCoreBody`'s infers at the io grade
(`r.inferIO`, con-leche's task #172 B4).  Kept verbatim.
-/
import ConRon.Arena.CoreIO

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/CoreGated.lean:61-115 whnfCoreBodyGated —
**the gated `.app` clause**, named so that task #97-P6-7's upward cutoff has a
subject here too: the node the reduction rebuilds is the one the spine already
has whenever the head did not move (`internAppRebuilt`), and the stuck step is
`Core.lean`'s `whnfCoreStuckApp`.

The gated lane is **not** batched: it is class (S), it is not executed, and
con-leche's cached tier has no gated twin of `whnfAppI` either (task
#97-P6-9's ledger).  So this clause stays the chained one, and
`whnfCoreStuckApp` survives for it. -/
def whnfCoreAppGated (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (h : EIdx) (same : Bool) (fp a : EIdx) : AM EIdx := do
  if fp.tag == ETag.lam then
    match ← viewBind fp with
    | none => failDanglingE
    | some (ty, body, mb) => do
      -- **THE β SITE.**  The gate wraps the test only; both arms are
      -- `whnfCoreBody`'s verbatim.
      let ok ←
        if mode.verifiedChecks && mb.pw.isNever then pure true
        else do
          let ta ← r.infer depth a
          r.defeq depth ta ty
      if ok then do
        let b ← instantiate1Fast coreWalkFuel body a 0
        r.whnfCore depth b
      else internAppRebuilt h same fp a
  else whnfCoreStuckApp mode r fe depth h same fp a

/-- con-leche: ConLeche/Kernel/CoreGated.lean:61-115 whnfCoreBodyGated —
**the gated head-normalization body**: `whnfCoreBody` with the `.app`
clause's β certificate skipped at a `.never` binder under
`mode.verifiedChecks`.  The projection certificate is NOT gated — the
asymmetry fence keeps every zero-kind certificate, and the projection slot
has no `pw` datum of its own. -/
def whnfCoreBodyGated (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) :
    Nat → EIdx → AM EIdx :=
  fun depth e => do
    match ← view e with
    | .sort _ | .fvar _ _ | .forallE _ _ _ | .lam _ _ _ | .const _ _
    | .lit _ => pure e
    | .app f a => do
      let f' ← r.whnfCore depth f
      whnfCoreAppGated mode r fe depth e (f' == f) f' a
    | .proj sn i pe => do
      let e0 ← r.whnf depth pe
      let e' ← projLitToCtor r fe depth e0
      match ← fe.findProj? sn i with
      | some entry => do
        match ← view (← getAppFn coreWalkFuel e') with
        | .const c us => do
          let args ← getAppArgs coreWalkFuel e'
          match ← viewLsLen us with
          | none => failDanglingLs
          | some usl =>
          let fok ← entry.fireOk us
          if c = entry.ctor ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              usl = entry.levelParams.length ∧ fok = true then do
            let b0 ← internE (.bvar 0)
            let arg := args.getD (entry.numParams + i) b0
            if ← projCertAt r fe depth mode.verifiedChecks mode.betaGate c us
                args then
              r.whnfCore depth arg
            else internE (.proj sn i e')
          else internE (.proj sn i e')
        | _ => internE (.proj sn i e')
      | none => internE (.proj sn i e')
    | .letE _ _ _ =>
      fail (.internal "whnfCore: `let` in an annotated expression")
    | .bvar _ =>
      fail (.notImplemented "whnf beyond the supported fragment")

/-- con-leche: ConLeche/Kernel/CoreGated.lean:117-150 coreKnotGated — **the P
knot**: `coreKnot`'s tie with `whnfCoreBodyGated` in the `whnfCore` slot;
`whnf`, `infer`, `defeq` and `annotate` are the *same bodies*, tied to this
knot one fuel level down. -/
def coreKnotGated (mode : CheckMode) (fe : IFEnv) : Nat → CoreFnsA
  | 0 =>
    { whnfCore := fun _ _ => fail (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => fail (.internal "fuel exhausted: whnf")
      infer := fun _ _ => fail (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => fail (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => fail (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => fail (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    { whnfCore := fun d e =>
        whnfCoreBodyGated mode (coreKnotGated mode fe fuel) fe d e
      whnf := fun d e => whnfBody (coreKnotGated mode fe fuel) fe d e
      infer := fun d e => inferBody mode (coreKnotGated mode fe fuel) fe d e
      defeq := fun d a b =>
        defeqBody mode (coreKnotGated mode fe fuel) fe d a b
      annotate := fun d e =>
        annotateBody (coreKnotGated mode fe fuel) fe d e
      -- parked stage-1 artifact: the io grade postdates this knot, and
      -- nothing states claims at its io slot
      inferIO := fun d e =>
        inferBody mode (coreKnotGated mode fe fuel) fe d e }

/-- con-leche: ConLeche/Kernel/CoreGated.lean:152-155 pureFnsGated — the P
core, tied at `AM`. -/
def pureFnsGated (mode : CheckMode) (fe : IFEnv) : Nat → CoreFnsA :=
  coreKnotGated mode fe

/-- con-leche: ConLeche/Kernel/CoreGated.lean:157-159 whnfCoreGated — head
normalization with the β-cert gate (fueled). -/
def whnfCoreGated (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM EIdx :=
  (pureFnsGated mode fe fuel).whnfCore depth e

/-- con-leche: ConLeche/Kernel/CoreGated.lean:161-163 whnfGated — the full
reduction loop over the gated knot (fueled). -/
def whnfGated (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat) (e : EIdx) :
    AM EIdx :=
  (pureFnsGated mode fe fuel).whnf depth e

/-- con-leche: ConLeche/Kernel/CoreGated.lean:165-168 inferTypeCoreGated —
type inference over the gated knot (fueled). -/
def inferTypeCoreGated (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM EIdx :=
  (pureFnsGated mode fe fuel).infer depth e

/-- con-leche: ConLeche/Kernel/CoreGated.lean:170-173 isDefEqCoreGated —
definitional equality over the gated knot (fueled). -/
def isDefEqCoreGated (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (a b : EIdx) : AM Bool :=
  (pureFnsGated mode fe fuel).defeq depth a b

/-- con-leche: ConLeche/Kernel/CoreGated.lean:175-178 annotateCoreGated — the
annotation pass over the gated knot (fueled). -/
def annotateCoreGated (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM EIdx :=
  (pureFnsGated mode fe fuel).annotate depth e

/-- con-leche: ConLeche/Kernel/CoreGated.lean:180-183 ensureSortCoreGated —
`ensureSort` over the gated knot (fueled). -/
def ensureSortCoreGated (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM LIdx :=
  ensureSort (pureFnsGated mode fe fuel) fe depth e

end ConRon.Arena
