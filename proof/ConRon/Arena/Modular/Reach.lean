/-
# `ConRon.Arena.Modular.Reach` — a worker's context (task #166)

The twin of `frontend/modular/reach.rs`: the types the reach is built on.
-/
module

public import ConRon.Arena.Frontend.Olean.Index

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

end ConRon.Arena.Modular
