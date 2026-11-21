/-
# `ConRon.Arena.Frontend.Olean.Group` — one inductive group's record (task #166)

The twin of `olean/group.rs`.  `groupParts` gives names, which `Emit.block` takes; a merge of a
list is one loaded module (the anonymous name, no frontier) holding the entries kept.
-/
module

public import ConLeche.Frontend.Olean.Group
public import ConRon.Arena.Frontend.Olean.Records

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (CEntryF CKindF)

/-- con-leche: ConLeche/Frontend/Olean/Group.lean:31-35 mergedOfList
**Some constants as a merge**, in their order (each name once: the first copy kept). -/
def mergedOfList (pk : OleanPins) (cs : Array CEntry) : Merged :=
  let (map, order, kept) := cs.foldl (fun (acc : Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array CEntry) c =>
    let (map, order, kept) := acc
    if map.contains c.c.name then acc
    else (map.insert c.c.name (0, kept.size), order.push c.c.name, kept.push c)) ({}, #[], #[])
  { ls := #[{ name := pk.anon, constants := kept, frontier := {} }], map, order }

/-- con-leche: ConLeche/Frontend/Olean/Group.lean:37-48 groupParts
The constants of `n`'s group the emission takes, if `n` is a stored inductive type. -/
def groupParts (mg : Merged) (n : NIdx) : Option (List NIdx × List NIdx × List NIdx) :=
  match mg.get n with
  | some c =>
    match c.c.kind with
    | .induct _ _ all .. =>
      let tys := blockTys mg all
      some (tys, blockCtors mg tys, blockRecs mg (recMapOf mg) n)
    | _ => none
  | none => none

/-- con-leche: ConLeche/Frontend/Olean/Group.lean:50-51 groupEmit
The emission of `n`'s group alone. -/
def groupEmit (mg : Merged) (tys ctors recs : List NIdx) : Emit := ({} : Emit).block mg tys ctors recs

/-- con-leche: ConLeche/Frontend/Olean/Group.lean:53-69 groupRecord
**One inductive group's record, validated**: `n`'s group as the emission builds it, after
`blockStep` of `n` and of each of the group's constants. -/
def groupRecord (pk : OleanPins) (mg : Merged) (n : NIdx) : AM IDeclaration := do
  match groupParts mg n with
  | none => fail (.internal s!"the inductive group of {← readName n}: {← readName n} is not a \
      stored inductive type")
  | some (tys, ctors, recs) =>
    (n :: (tys ++ ctors ++ recs)).forM (blockStep pk mg)
    match ← declsOf (groupEmit mg tys ctors recs) with
    | .error (e, _) => fail e
    | .ok ds =>
      match ds.decls[0]? with
      | some d =>
        if ds.decls.size == 1 then pure d
        else fail (.internal s!"the inductive group of {← readName n}: {ds.decls.size} records")
      | none => fail (.internal s!"the inductive group of {← readName n}: no record")

end ConRon.Arena.Frontend.Olean
