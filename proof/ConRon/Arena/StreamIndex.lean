/-
# `ConRon.Arena.StreamIndex` — the index of a stream, and a record's job

The twin of con-leche's `ConLeche/Cached/StreamIndex.lean`.

The stream's index is built once, after the parse and before any check, from the
records alone (`declConstants`, `declTables`, `Arena/Install.lean`): every constant
with its counter, its position among all the constants of the stream, and every
table with its record's position.  It is never written again.  The name's FIRST
entry wins: a record whose name an earlier record took sees that entry at its own
view, so its check fails with "duplicate declaration", in fold order.

A record's **job** is its check at the view of its position (`IStreamIndex.view`):
the index with everything from that record on hidden.  The jobs read the frozen
index and their own record, so they run independently of one another.

**Interning.**  What a record installs is a function of the record, but in the
arena a function that builds terms interns them, so `buildIndex` is an `AM` action.
The driver runs it with no scratch tier open, so every handle the index holds is
persistent.  The Rust (`arena::stream_index`) then freezes the index into its
`PersTier`, the base every worker reads by reference; the twin keeps it as a value.
-/
module

public import ConRon.Arena.Install
public import ConRon.Arena.CheckDecl

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Cached/StreamIndex.lean:38-43 StreamIndex — the index under
construction, and finished: the frozen layer (its bounds unused here), each record's
first counter, and the next counter. -/
structure IStreamIndex where
  base : IFBase := {}
  firsts : Array Nat := #[]
  next : Nat := 0

/-- con-leche: ConLeche/Cached/StreamIndex.lean:45-49 insertConsts — insert a
record's constants from counter `c` on, a name's first entry winning. -/
def insertConsts (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (c : Nat) :
    List IConstantInfo → Std.HashMap NIdx (Nat × IConstantInfo) × Nat
  | [] => (idx, c)
  | ci :: L => insertConsts (idx.insertIfNew ci.name (c, ci)) (c + 1) L

/-- con-leche: ConLeche/Cached/StreamIndex.lean:51-55 insertTables — insert a
record's tables, a name's first entry winning. -/
def insertTables (tbls : Std.HashMap NIdx (Nat × IProjTable)) (r : Nat) :
    List IProjTable → Std.HashMap NIdx (Nat × IProjTable)
  | [] => tbls
  | t :: Q => insertTables (tbls.insertIfNew t.structName (r, t)) r Q

/-- con-leche: ConLeche/Cached/StreamIndex.lean:57-62 StreamIndex.add — one record
into the index.  An `AM` action, as the module note says: reading off what a record
installs interns the terms it builds. -/
def IStreamIndex.add (I : IStreamIndex) (pd : IDeclaration) : AM IStreamIndex := do
  let L ← declConstants pd
  let Q ← declTables pd
  let (idx, next) := insertConsts I.base.idx I.next L
  pure { base := { I.base with idx, tbls := insertTables I.base.tbls I.firsts.size Q }
         firsts := I.firsts.push I.next
         next }

/-- con-leche: ConLeche/Cached/StreamIndex.lean:64-66 buildIndex — **the index of
a stream**, as an explicit list recursion (DESIGN §3.4 has no closures).  A failure
is the store's (a term could not be interned), tagged with the position of the
record whose reading failed. -/
def buildIndexGo (I : IStreamIndex) (k : Nat) :
    List IDeclaration → AM (Except (CheckError × Nat) IStreamIndex)
  | [] => pure (.ok I)
  | pd :: ds => fun s =>
    match I.add pd s with
    | .ok (I', s') => buildIndexGo I' (k + 1) ds s'
    | .error e => .ok (.error (e, k), s)

/-- con-leche: ConLeche/Cached/StreamIndex.lean:64-66 buildIndex — the index of the
records, from the empty one. -/
def buildIndex (ds : Array IDeclaration) : AM (Except (CheckError × Nat) IStreamIndex) :=
  buildIndexGo {} 0 ds.toList

/-- con-leche: ConLeche/Cached/StreamIndex.lean:68-72 StreamIndex.view — **the view
of record `k`**: no constants or tables of its own, the index visible below the
record's first counter and its position. -/
def IStreamIndex.view (I : IStreamIndex) (k : Nat) : IFEnv :=
  let c := I.firsts.getD k I.next
  ⟨⟨[], []⟩, {}, { I.base with below := c, belowRec := k }, {}⟩

/-- con-leche: ConLeche/Cached/StreamIndex.lean:74-81 recordJob — what the fold's
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove StreamIndex.recordCheck_bridge, then delete this line
step asks of record `pd` at position `k`: the `And` pin, then the record's check at
its view.  `recordJob` is this in its bracket. -/
def recordCheck (mode : CheckMode) (pins : List INatOpPinSet) (I : IStreamIndex)
    (k : Nat) (pd : IDeclaration) : AM Unit := do
  if ← andPinOk pd then
    let _ ← checkDecl mode pins (I.view k) pd
    pure ()
  else fail (.invalid "`And` must be the standard `And`")

/-- con-leche: ConLeche/Cached/StreamIndex.lean:74-81 recordJob — **record `pd`'s
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove StreamIndex.recordJob_bridge, then delete this line
job, at position `k`**: `recordCheck` from fresh memos and an empty scratch tier
(the cited `checkDeclStepC`'s fresh `{}`), the tier dropped after it.  Nothing the
job builds outlives it. -/
def recordJob (mode : CheckMode) (pins : List INatOpPinSet) (I : IStreamIndex)
    (k : Nat) (pd : IDeclaration) : AM Unit := do
  enterScratch
  recordCheck mode pins I k pd
  dropScratch

end ConRon.Arena
