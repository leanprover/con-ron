/-
# `ConRon.Arena.Checker` — the check phase's sequential pieces, over handles

con-leche's driver is the parse, then the check (`ConLeche/Cached/StreamIndex.lean`,
`ConLeche/Driver/CheckPool.lean`): the stream's index is built from the records
alone (`buildIndex`, `Arena/StreamIndex.lean`), and every record's check is a JOB at
the index's view of its position (`recordJob`), the first failure in fold order the
verdict.  There is no install phase.  The binary runs the jobs on a pool of workers
(`crates/con-ron/src/pool.rs`; its twin shape is `Arena/Pooled.lean`); the twin's
own walk is `checkStream`, every job in fold order on one worker.

**A worker's state.**  The Rust's index is frozen into its `PersTier` and every
worker reads it by reference (`arena::checker::freeze_tier`); the twin keeps the
index as a value and its worker reads the persistent tier where it is
(`AState.worker`).  Each job opens and drops its own scratch tier and memos
(`recordJob`), so a worker's state between two jobs holds nothing of the first.

## The pins are interned at startup

DESIGN §8.6 P2d: "intern con-leche's `natOpPinSets` `Expr`s into the
persistent tier at startup — a one-time tree walk".  `internAllPins` below is
that walk, and it is what makes every later `pin`/`internCI` of the same datum
return the PERSISTENT handle whatever tier is live (DESIGN §8.3: `intern`
probes the persistent table first).  Without it a reserved name first
interned inside a scratch tier would compare unequal to the stream's own
persistent copy of it, which is the one way hash-consing can go wrong across
the tier boundary.
-/
module

public import ConRon.Arena.StreamIndex

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## The check phase -/

/-- con-leche: ConLeche/Driver/CheckPool.lean:116-123 runAt
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove Checker.AState.abandoned_bridge, then delete this line
**The state a FAILING job hands back**, and the reason it is not the pre-job
state.

con-leche's job lives in `Except (CheckError × Nat)` (`runAt`, each record's check
from a fresh memo state) and its error arm is `.error (e, t)` — no state comes
back, because `Except` carries none.  (B) has ONE monad (DESIGN §8.4) whose error type is
`CheckError`, so the position has to travel as a VALUE, and the error arm
therefore has to produce *some* state.  Task #97d wrote the pre-step state `s`
there, which reads as "restore".  It is not a restore that anything observes —
the walk is abandoned on an error, `checkStream` returns `.error`,
`runPipelineTail` renders the message and `runPipeline` / `runPipelineIO`
discard the state — but it is a second reference to the whole
`AState`, held across the entire step, so **every store append, every cache
insert and every memo insert inside that step ran at refcount 2 and copied**
(task #97g: `lean_inc_ref(s)` before the call in `Checker.c`, 83 % of the run
in `lean_copy_expand_array` + `lean_del_core_other`).

So the arm hands back the EMPTY state — which is what con-leche's arm means
(no state at all) and what the Rust twin will do (an `Err` return whose
`&mut` state the caller stops using).  Nothing on the error path reads it. -/
def AState.abandoned : AState := AState.init EStore.empty

/-- con-leche: ConLeche/Driver/CheckPool.lean:199-227 checkPool — **a worker's
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove Checker.AState.worker_bridge, then delete this line
state**: the driver's state with the scratch tier closed and empty, and fresh memos
and caches.  The Rust's `worker_state` builds the same thing over the FROZEN tier
(an empty store whose reads go to the `PersTier`); the twin has one store and reads
its persistent tier where it is. -/
def AState.worker (s : AState) : AState :=
  { s with store := s.store.dropScratch, memos := Memos.empty,
           caches := Caches.empty }

/-- con-leche: ConLeche/Driver/CheckPool.lean:116-123 runAt — **job `t`, run**: the
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove Checker.runJob_bridge, then delete this line
record's job at its position, the error tagged with that position.  A position past
the records is an internal error, never a verdict. -/
def runJob (mode : CheckMode) (pins : List INatOpPinSet) (I : IStreamIndex)
    (ds : Array IDeclaration) (t : Nat) : AM (Except (CheckError × Nat) Unit) := fun s =>
  match ds[t]? with
  | some d =>
    match recordJob mode pins I t d s with
    | .ok ((), s') => .ok (.ok (), s')
    | .error e => .ok (.error (e, t), AState.abandoned)
  | none => .ok (.error (.internal "check phase: no job", t), AState.abandoned)

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:432-455 parWorker — **a worker's
fold over the jobs it claimed**, on one state, the first failure the answer
(`PooledAccepts`, `Arena/Pooled.lean`). -/
def checkJobList (mode : CheckMode) (pins : List INatOpPinSet) (I : IStreamIndex)
    (ds : Array IDeclaration) : List Nat → AM (Except (CheckError × Nat) Unit)
  | [] => pure (.ok ())
  | t :: rest => fun s =>
    match runJob mode pins I ds t s with
    | .ok (.ok (), s') => checkJobList mode pins I ds rest s'
    | .ok (.error e, s') => .ok (.error e, s')
    | .error e => .error e

/-- con-leche: ConLeche/Driver/Run.lean:74-97 checkDeclsIO — **the check of a
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove Checker.checkStream_bridge, then delete this line
stream, as one worker runs it**: the index of the records, then every record's job in
fold order, from the worker's state.  The `× Nat` of the error is the failure's
POSITION in the fold. -/
def checkStream (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : Array IDeclaration) : AM (Except (CheckError × Nat) Unit) := fun s =>
  match buildIndex ds s with
  | .ok (.ok I, s₁) => checkJobList mode pins I ds (List.range ds.size) s₁.worker
  | .ok (.error e, s₁) => .ok (.error e, s₁)
  | .error e => .error e

/-- con-leche: ConLeche/Cached/Decls.lean:83-92 checkDecls — the fold's
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove Checker.atDecl_bridge, then delete this line
failure, with its POSITION rendered into the message.  con-leche's driver
reports the declaration by indexing the record array it already holds
(`ConLeche/Driver/Run.lean`'s `checkMain`); the seam of (B) has no position channel
(`Arena/Main.lean`'s note), so the position goes into the text — beside
`Frontend.atLine`, which does the same for the PARSE's position and must not
be confused with it: a line number and a fold position are different
numbers. -/
def atDecl : CheckError → Nat → CheckError
  | .notImplemented w, n => .notImplemented s!"{w} (declaration {n})"
  | .invalid w, n => .invalid s!"{w} (declaration {n})"
  | .internal w, n => .internal s!"{w} (declaration {n})"
  | .native w, n => .native s!"{w} (declaration {n})"

/-! ## The startup walk -/

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
con-leche: ConLeche/Kernel/Basis.lean:39-45 BasisKind.decls
**The one-time tree walk of DESIGN §8.6 P2d**: every datum the checker
compares a stream record against, interned into the tier that is live at the
call — which, at the driver's call, is the persistent one.

The five basis blocks' pins (what a basis block's and a quotient record's
check compares the record with), the standard and compiler-trust axiom pins, the reserved names the guards
compare by handle, and the `Nat`-operation pin variants, whose interned form
is the checker's pin-list parameter (con-leche's task #304).

The standard-axiom and `ofReduce*` pins are con-leche's (`iffA` … `choiceA`,
`ofReduceNatA`/`ofReduceBoolA`), compared by `matchesPin`'s plain equality. -/
def internAllPins (pins : List NatOpPinSet) : AM (List INatOpPinSet) := do
  let _ ← BasisKind.decls .eqK
  let _ ← BasisKind.decls .natK
  let _ ← BasisKind.decls .emptyK
  let _ ← BasisKind.decls .falseK
  let _ ← BasisKind.decls .quotK
  let _ ← iffA; let _ ← iffIntroA; let _ ← iffRecA
  let _ ← nonemptyA; let _ ← nonemptyIntroA; let _ ← nonemptyRecA
  let _ ← propextA; let _ ← choiceA
  let _ ← trueCvA; let _ ← trueIntroCvA; let _ ← trustCompilerA; let _ ← boolCvA
  let _ ← reduceNatCvA; let _ ← reduceBoolCvA
  let _ ← ofReduceNatA; let _ ← ofReduceBoolA
  let _ ← reduceNatDeclPin; let _ ← reduceBoolDeclPin
  let _ ← reservedBasisNames
  let _ ← natOpNames; let _ ← natDivModNames; let _ ← reduceOpNames
  let _ ← pinSorryAx; let _ ← pinQuotSound
  internPinSets pins

end ConRon.Arena
