/-
# `ConRon.Arena.Frontend.Olean.Records` — the import closure as one record stream (task #142)

The twin of `olean/records.rs`.  Upstream's `declOfF em.nm em.lv em.ex r` is
`processLineCoreD` over a `StateD` whose name and expression tables ARE the
emitter's: the stream parser's own record builder, over tables of handles.

**The reader's result is the parse's**, `Frontend.ParseResultD`, so everything after
it is `runPipelineTail`.
-/
module

public import ConRon.Arena.Frontend.Olean.Emit

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend
open ConRon.Arena.Frontend

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:47-55 declsGo
`declsOf`'s walk: `k` the position of the first of `rs`. -/
def declsGo (k : Nat) : List DeclRec → StateD → AM (Except (CheckError × Nat) StateD)
  | [], st => pure (.ok st)
  | r :: rs, st => do
    match ← processLineCoreD st r with
    | .inl st => declsGo (k + 1) rs st
    | .inr v => pure (.error (v.toError, k))

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:57-61 declsOf
**The `Declaration` records**, through the stream reader's builder.  A record's
verdict is the stream path's, at the record's position. -/
def declsOf (em : Emit) : AM (Except (CheckError × Nat) ParseResultD) := do
  let st : StateD := { names := { dense := em.names }, levels := {}, exprs := { dense := em.exprs } }
  match ← declsGo 0 em.out.toList st with
  | .error e => pure (.error e)
  | .ok st => pure (.ok (ParseResultD.ofState st))

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:63-70 rootConstants
The constants the emission starts from: the named ones, each of which the closure
must hold, or all of them. -/
def rootConstants (mg : Merged) : Option (Array NIdx) → AM (Array NIdx)
  | none => pure mg.order
  | some cs =>
    match cs.find? (!mg.map.contains ·) with
    | some c => do fail (.internal s!"the constant {← readName c} is not in the import closure")
    | none => pure cs

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:72-89 readOleans
**The whole read**: load, merge, emit, build.  `constants` names the constants to start
from; `none` is every constant of the closure. -/
def readOleans (fs : OleanFs) (sp : List System.FilePath) (roots : Array NIdx)
    (constants : Option (Array NIdx)) : AM (Except (CheckError × Nat) ParseResultD) := do
  let pk ← oleanPins
  let ls ← loadClosure fs pk sp roots
  let mg ← mergeAll pk ls
  blocksOk pk mg
  let cs ← rootConstants mg constants
  declsOf (← emitAll pk mg cs)

end ConRon.Arena.Frontend.Olean
