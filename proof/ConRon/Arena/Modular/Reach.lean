/-
# `ConRon.Arena.Modular.Reach` — a worker's context (task #166)

The twin of `frontend/modular/reach.rs`: the types the reach is built on.
-/
module

public import ConRon.Arena.Frontend.Olean.Index
public import ConRon.Arena.Frontend.NatOpGround
public import ConRon.Arena.Install

@[expose] public section

namespace ConRon.Arena.Modular

open ConLeche
open ConRon.Arena.Frontend.Olean
open ConLeche.Frontend.Olean (OLeanLevel)

deriving instance Hashable for ConLeche.Frontend.Olean.OLeanLevel

/-- con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
**A part of a view**: a module and a level. -/
structure PartKey where
  mod : NIdx
  level : OLeanLevel
  deriving BEq, Hashable

/-- con-leche: ConLeche/Driver/Reach.lean:170-173 Spot
**A copy of a name**: the part holding it and its name position there. -/
structure Spot where
  part : PartKey
  pos : NamePosition

/-- con-leche: ConLeche/Driver/Reach.lean:923-930 Reach
**What the reach gives**: the context's records with their homes, the completed names with
the homes that located them, and its counts. -/
structure Reach where
  ctx : Array IDeclaration
  homes : Array NIdx
  completed : Array (NIdx × NIdx)
  searches : Nat
  inferred : Nat

/-! ## L3's STUB of lane L2's signatures (task #166): dropped when L2 integrates. -/

/-- con-leche: ConLeche/Driver/Reach.lean:94-95 recordReads
STUB (lane L2 ports it): what a record reads. -/
def recordReads (d : IDeclaration) : AM (Array NIdx) :=
  ConRon.Arena.Frontend.IDeclaration.usedConsts d

/-- con-leche: ConLeche/Driver/Reach.lean:871-873 ownerMap
STUB (lane L2 ports it): the record of each name of a context. -/
def ownerMap (ds : Array IDeclaration) : AM (Std.HashMap NIdx Nat) :=
  (List.range ds.size).foldlM (fun m j => do
    let ns ← declNames (ds.getD j default)
    pure (ns.foldl (fun m y => m.insert y j) m)) {}

/-- con-leche: ConLeche/Driver/Reach.lean:934-961 reach
STUB (lane L2 ports it): the reach of a module. -/
def reach (_fs : OleanFs) (_pk : OleanPins) (_sp : ConLeche.Frontend.Olean.Roots) (_m : NIdx)
    (_wr : WorkerReads) (_own : Std.HashSet NIdx) (_roots : Array NIdx) : AM Reach :=
  fail (.internal "stub")

end ConRon.Arena.Modular
