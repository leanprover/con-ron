/-
# `ConRon.Arena.Frontend.Olean.Reads` — taking less of a region (task #142)

The twin of `olean/reads.rs`.  `CKindF.skipped` and `CKindF.tag` are upstream's own.
-/
module

public import ConLeche.Frontend.Olean.Reads
public import ConRon.Arena.Frontend.Olean.Fast
public import ConRon.Arena.Frontend.Olean.Sparse

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Region CEntryF constSkel moduleSkel ImportF CKindF kName kExpr)

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:49-53 ModHeader
A module's flag and imports. -/
structure ModHeader where
  isModule : Bool
  imports : Array ImportRec

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:55-63 NamePosition
What `namePositionsAt` takes of one stored constant. -/
structure NamePosition where
  loc : Nat
  name : NIdx
  tag : Nat
  skipped : Bool

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:65-69 NamePositions
**The name positions** of a module. -/
structure NamePositions where
  header : ModHeader
  consts : Array NamePosition

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:71-74 namePosition
One constant's position and name. -/
def namePosition (pk : OleanPins) (r : Region) (c : Nat) : AM (Option NamePosition) := do
  match constSkel r c with
  | none => pure none
  | some s =>
    match ← nameP pk r s.name with
    | none => pure none
    | some n => pure (some ⟨c, n, s.kind.tag, s.kind.skipped⟩)

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:76-84 namePositionsAt
**The name positions**: no expression of the module is read.  A name two constants
bear fails it. -/
def namePositionsAt (pk : OleanPins) (r : Region) (root : UInt64) : AM (Option NamePositions) :=
  match moduleSkel r root with
  | none => pure none
  | some sk =>
    (do
      let imports ← sk.imports.mapM (m := OptionT AM) fun i =>
        i.mapM (m := OptionT AM) fun v => OptionT.mk (nameP pk r v)
      let cs ← sk.consts.mapM (m := OptionT AM) fun c => OptionT.mk (namePosition pk r c)
      if ConLeche.Frontend.Olean.distinctGo (cs.map (·.name)) (Std.HashSet.emptyWithCapacity cs.length) then
        pure ⟨⟨sk.isModule, imports.toArray⟩, cs.toArray⟩
      else failure : OptionT AM NamePositions).run

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:86-88 entryAt
**The constant at location `c`**, read with a memo of its own. -/
def entryAt (pk : OleanPins) (r : Region) (c : Nat) : AM (Option (CEntryF NIdx EIdx)) := do
  match constSkel r c with
  | none => pure none
  | some s =>
    skelFits s
    sparseEntry pk r s

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:90-92 stmtsAt
**The statements of the constants at some locations**, read together. -/
def stmtsAt (pk : OleanPins) (r : Region) (cs : List Nat) : AM (Option (List StmtRec)) := do
  match ← constsSkel r cs with
  | none => pure none
  | some sks => stmtsFast pk r sks

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:96-104 memoAdd
One root read into a memo shared by several constants (`sGo`, no frontier).  As the Rust's: a
root that does not read leaves the memo empty (upstream keeps what was read of it; a memo is
speed alone). -/
def memoAdd (pk : OleanPins) (r : Region) (k : UInt8) (st : SM) (v : UInt64) : AM SM := do
  match r.loc v with
  | some c =>
    match ← sGo pk r {} k c st with
    | some st => pure st
    | none => pure {}
  | none => pure st

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:96-104 memoAdd
`vs.foldl (memoAdd r k) st`. -/
def memoAddAll (pk : OleanPins) (r : Region) (k : UInt8) : SM → List UInt64 → AM SM
  | st, [] => pure st
  | st, v :: vs => do memoAddAll pk r k (← memoAdd pk r k st v) vs

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:106-108 memoRoots
The roots of a constant's skeleton into the memo: its names, then its expressions. -/
def memoRoots (pk : OleanPins) (r : Region) (st : SM) (sk : CEntryF UInt64 UInt64) : AM SM := do
  memoAddAll pk r kExpr (← memoAddAll pk r kName st sk.names) sk.exprs

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:110-118 memoName
A name pointer by the memo, else read on its own (`sparseNameP`). -/
def memoName (pk : OleanPins) (r : Region) (st : SM) (v : UInt64) : AM (Option NIdx) :=
  if v == 1 then pure (some pk.anon)
  else match r.loc v with
    | some c =>
      match st.names[c]? with
      | some n => pure (some n)
      | none => sparseNameP pk r v
    | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:120-127 memoExpr
An expression pointer by the memo, else read on its own (`sparseExprP`). -/
def memoExpr (pk : OleanPins) (r : Region) (st : SM) (v : UInt64) : AM (Option EIdx) :=
  match r.loc v with
  | some c =>
    match st.exprs[c]? with
    | some e => pure (some e)
    | none => sparseExprP pk r v
  | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:129-135 entriesAt
The two reads of `CEntryF.mapM (memoName r st) (memoExpr r st)`. -/
def memoRead (pk : OleanPins) (r : Region) (st : SM) : PtrRead :=
  ⟨memoName pk r st, memoExpr pk r st⟩

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:137-142 kindNamesAt
A kind's names read, its expressions left out (`s.kind.mapM rd (fun _ => some ())`). -/
def kindNames (rd : PtrRead) (k : CKindF UInt64 UInt64) : AM (Option (CKindF NIdx Unit)) :=
  (k.mapM (m := OptionT AM) (fun v => OptionT.mk (rd.rdName v)) (fun _ => pure ())).run

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:137-142 kindNamesAt
**The kind of the constant at location `c`, its expressions left out**: what Lean's
`subsumesInfo` reads of a kind beside the statement. -/
def kindNamesAt (pk : OleanPins) (r : Region) (c : Nat) : AM (Option (CKindF NIdx Unit)) := do
  match constSkel r c with
  | none => pure none
  | some s =>
    skelFits s
    kindNames ⟨sparseNameP pk r, sparseExprP pk r⟩ s.kind

end ConRon.Arena.Frontend.Olean
