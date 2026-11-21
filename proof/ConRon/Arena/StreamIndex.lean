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
index and their own record, so they run independently of one another.  The job
itself (`recordCheck`, `recordJob`) is in `Arena/Justify.lean`, since it reads a
solution's index there.

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

/-- con-leche: ConLeche/Cached/StreamIndex.lean:38-43 StreamIndex
con-leche: ConLeche/Cached/StreamIndex.lean:68-76 FrozenIndex — the index under
construction, and finished: the frozen layer (its bounds unused here), each record's
first counter, and the next counter.  Frozen (`IStreamIndex.freeze`), it is
con-leche's `FrozenIndex` too: the base holds the literal names, and for each literal
flag the first counter from which a record's view has it (`natFrom`, `strFrom`). -/
structure IStreamIndex where
  base : IFBase := {}
  firsts : Array Nat := #[]
  next : Nat := 0
  natFrom : Option Nat := none
  strFrom : Option Nat := none

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

/-- con-leche: ConLeche/Cached/StreamIndex.lean:78-80 StreamIndex.freeze — **freeze a
stream's index**: the literal names off the pin table into the base, and the literal
flags' thresholds over them (`litFrom`). -/
def IStreamIndex.freeze (I : IStreamIndex) : AM IStreamIndex := do
  let lits ← strLitNames
  let nf := litFrom I.base.idx lits 0 NAT_LIT_COUNT
  let sf := litFrom I.base.idx lits 0 STR_LIT_COUNT
  pure { I with base := { I.base with lits }, natFrom := nf, strFrom := sf }

/-- con-leche: ConLeche/Cached/StreamIndex.lean:64-66 buildIndex
con-leche: ConLeche/Driver/CheckPool.lean:57-75 Jobs.build — **the frozen index of
a stream** (con-leche's `Jobs` also holds a solution's index: the same build over the
solution's records, `solutionOf`),
as an explicit list recursion (DESIGN §3.4 has no closures), frozen past
the last record (`IStreamIndex.freeze`, con-leche's `Jobs.build`).  A failure is the
store's (a term could not be interned) or the pin table's, tagged with the position
of the record whose reading failed (past the last for the freeze). -/
def buildIndexGo (I : IStreamIndex) (k : Nat) :
    List IDeclaration → AM (Except (CheckError × Nat) IStreamIndex)
  | [] => fun s =>
    match I.freeze s with
    | .ok (F, s') => .ok (.ok F, s')
    | .error e => .ok (.error (e, k), s)
  | pd :: ds => fun s =>
    match I.add pd s with
    | .ok (I', s') => buildIndexGo I' (k + 1) ds s'
    | .error e => .ok (.error (e, k), s)

/-- con-leche: ConLeche/Cached/StreamIndex.lean:64-66 buildIndex — the index of the
records, from the empty one. -/
def buildIndex (ds : Array IDeclaration) : AM (Except (CheckError × Nat) IStreamIndex) :=
  buildIndexGo {} 0 ds.toList

/-- con-leche: ConLeche/Cached/StreamIndex.lean:82-93 FrozenIndex.view — **the view
of record `k`**: no constants or tables of its own, the index visible below the
record's first counter and its position, and its literal flags by one comparison each
against the frozen thresholds (`fromLe`). -/
def IStreamIndex.view (I : IStreamIndex) (k : Nat) : IFEnv :=
  let c := I.firsts.getD k I.next
  ⟨⟨[], []⟩, {}, { I.base with below := c, belowRec := k }, {},
    fromLe I.natFrom c, fromLe I.strFrom c⟩

end ConRon.Arena
