/-
# `ConRon.Arena.Frontend.Olean.Records` — the import closure as one record stream (task #142)

The twin of `olean/records.rs`.  Upstream's `declOfF em.nm em.lv em.ex r` is
`processLineCoreD` over a `StateD` whose name and expression tables ARE the
emitter's: the stream parser's own record builder, over tables of handles.

A theorem's record holds a reference to its value (`valueRef`), which its check reads
(`readValue`, upstream task #481; the check phase is `Arena/OleanJobs.lean`).
-/
module

public import ConRon.Arena.Frontend.Olean.Emit
public import ConRon.Arena.Frontend.NatOpGround

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend
open ConRon.Arena.Frontend
open ConLeche.Frontend.Olean (Region refModule refLoc)

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:51-59 declsGo
`declsOf`'s walk: `k` the position of the first of `rs`. -/
def declsGo (k : Nat) : List DeclRec → StateD → AM (Except (CheckError × Nat) StateD)
  | [], st => pure (.ok st)
  | r :: rs, st => do
    match ← processLineCoreD st r with
    | .inl st => declsGo (k + 1) rs st
    | .inr v => pure (.error (v.toError, k))

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:61-65 declsOf
**The `Declaration` records**, through the stream reader's builder.  A record's
verdict is the stream path's, at the record's position. -/
def declsOf (em : Emit) : AM (Except (CheckError × Nat) ParseResultD) := do
  let st : StateD := { names := { dense := em.names }, levels := {}, exprs := { dense := em.exprs } }
  match ← declsGo 0 em.out.toList st with
  | .error e => pure (.error e)
  | .ok st => pure (.ok (ParseResultD.ofState st))

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:67-74 rootConstants
The constants the emission starts from: the named ones, each of which the closure
must hold, or all of them. -/
def rootConstants (mg : Merged) : Option (Array NIdx) → AM (Array NIdx)
  | none => pure mg.order
  | some cs =>
    match cs.find? (!mg.map.contains ·) with
    | some c => do fail (.internal s!"the constant {← readName c} is not in the import closure")
    | none => pure cs

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:76-79 ModRef
What a theorem's check needs of a module of the closure's order. -/
structure ModRef where
  name : NIdx
  frontier : Frontier

instance : Inhabited ModRef := ⟨⟨default, {}⟩⟩

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:83-89 OleanRead
**What a read gives**: the records, a theorem's value as its reference; what its
check needs to read it, by the reference's module; the merged constants, for what a
value mentions; and the reader's pins (the Rust's note). -/
structure OleanRead where
  decls : Array IDeclaration
  values : Array ModRef
  merged : Merged
  pins : OleanPins

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:91-95 OleanRead.thmUses
-- con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove Records.OleanRead.thmUses_bridge, then delete this line
**What a theorem's record mentions**, which its reference does not say: what the
load read off the file.  `none` for any other record. -/
def OleanRead.thmUses (rd : OleanRead) : IDeclaration → Option (Array NIdx)
  | .thmDecl cv _ => (rd.merged.get cv.name).map (·.uses)
  | _ => none

/-- con-leche: ConLeche/Driver/CheckMain.lean:100-104 usedOf
What a record mentions, for the preparation of an `.olean` read: the record's
expressions say it, except a theorem's, whose load read it off the file.  Pass
`rd.usedOf` as `prepareD`'s `used` (the Rust's `impl UsedConsts for OleanRead`). -/
def OleanRead.usedOf (rd : OleanRead) (d : IDeclaration) : AM (Array NIdx) :=
  match rd.thmUses d with
  | some u => pure u
  | none => ConRon.Arena.Frontend.IDeclaration.usedConsts d

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:97-122 readOleans
The frontiers, out of the loaded modules (the Rust moves them): `ls.map fun l =>
⟨l.name, l.frontier⟩`. -/
def modRefs (mg : Merged) : Merged × Array ModRef :=
  ({ mg with ls := mg.ls.map fun l => { l with frontier := {} } },
   mg.ls.map fun l => ⟨l.name, l.frontier⟩)

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:97-122 readOleans
**The whole read**: load, merge, emit, build, the heartbeat saying each step.
`constants` names the constants to start from; `none` is every constant of the
closure.  A theorem's value is a reference. -/
def readOleans (fs : OleanFs) (sp : List System.FilePath) (roots : Array NIdx)
    (constants : Option (Array NIdx)) : AM (Except (CheckError × Nat) OleanRead) := do
  let pk ← oleanPins
  let ls ← loadClosure fs pk sp roots
  let () := fs.readNotesSay s!"merging the constants of {ls.size} modules"
  let mg ← mergeAll pk ls
  let () := fs.readNotesSay s!"checking the blocks of {mg.order.size} constants"
  blocksOk pk mg
  let cs ← rootConstants mg constants
  let () := fs.readNotesSay s!"emitting records from {cs.size} constants"
  match ← declsOf (← emitAll pk mg cs) with
  | .error e => pure (.error e)
  | .ok ds =>
    let (mg, values) := modRefs mg
    pure (.ok ⟨ds.decls, values, mg, pk⟩)

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:126-131 ValueCache
**What a worker keeps between its checks**: the region of the module it read last. -/
structure ValueCache where
  idx : Nat := 0
  region : Option Region := none

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:133-148 regionFor
The region of module `idx` (named `m`), from the cache or the files, with the cache
to go on with: a failure empties it. -/
def regionFor (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (m : NIdx) (idx : Nat)
    (c : ValueCache) : AM (ValueCache × Except CheckError Region) := do
  match c.region with
  | some r => if c.idx == idx then return (c, .ok r) else readRegion
  | none => readRegion
where
  /-- con-leche: ConLeche/Frontend/Olean/Records.lean:133-148 regionFor -/
  readRegion : AM (ValueCache × Except CheckError Region) := do
    let mn ← readName m
    match readFiles fs sp mn .private with
    | .error e => pure ({}, .error e)
    | .ok f =>
      match f.viewRegion .private with
      | none => pure ({}, .error (← viewError pk mn f .private))
      | some (r, _) => pure ({ idx, region := some r }, .ok r)

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:150-162 readValue
**A theorem's value, from its reference's code**: the files of its module
(`regionFor`), then the value, over the module's frontier (`frontierExpr`). -/
def readValue (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (values : Array ModRef)
    (c : ValueCache) (code : Nat) : AM (ValueCache × Except CheckError EIdx) := do
  match values[refModule code]? with
  | none => pure (c, .error (.internal s!"a theorem's value in module {refModule code}, of {values.size}"))
  | some md =>
    match ← regionFor fs pk sp md.name (refModule code) c with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok r) =>
      match ← frontierExpr pk r md.frontier (refLoc code) with
      | some e => pure (c, .ok e)
      | none => pure (c, .error (undecodable (← readName md.name)))

end ConRon.Arena.Frontend.Olean
