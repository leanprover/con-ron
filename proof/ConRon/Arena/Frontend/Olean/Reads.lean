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
open ConLeche.Frontend.Olean (Region CEntryF constSkel moduleSkel ImportF CKindF)

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

end ConRon.Arena.Frontend.Olean
