/-
# `ConRon.Arena.Frontend.Olean.Levels` — what Lean loads for a module, from the headers (task #166)

The twin of `olean/levels.rs`.  `LoadFlags`, `LoadFlags.level` and `ModSet` with its operations
are upstream's own: two flags, a byte array.  The worklist is a `List`, as upstream's, the head
on top; the Rust's is a `Vec` and an index (`olean/closure.rs`'s stack).  A module's header is
read on the search path (`moduleImports`).
-/
module

public import ConLeche.Frontend.Olean.Levels
public import ConRon.Arena.Frontend.Olean.Files

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (LoadFlags closureFuel Roots OLeanLevel)

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:47-52 LvWork
One step of the fixpoint's worklist. -/
inductive LvWork where
  /-- an import `i` of a module at flags `pf` -/
  | imp (pf : LoadFlags) (i : ImportRec)
  /-- a newly met module's imports are done: it takes its place in the order -/
  | done (m : NIdx) (fl : LoadFlags)

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:54-63 LvState
The fixpoint's state. -/
structure LvState where
  flags : Std.HashMap NIdx LoadFlags := {}
  open_ : Std.HashSet NIdx := {}
  order : Array NIdx := #[]
  imports : Std.HashMap NIdx (Array ImportRec) := {}

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:65-67 LvWork.ofImports
A module's imports at its flags, as work, in their order. -/
def LvWork.ofImports (fl : LoadFlags) (imps : Array ImportRec) : List LvWork :=
  imps.toList.map (.imp fl)

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:69-111 levelsGo
An import of a module with its place already: its flags joined with `fl`, its imports
expanded again where they grew. -/
def levelsJoin (st : LvState) (fl : LoadFlags) (m : NIdx) (rest : List LvWork) :
    List LvWork × LvState :=
  match st.flags[m]? with
  | none => (rest, st)
  | some old =>
    let fl' : LoadFlags := { importAll := fl.importAll || old.importAll,
                             isExported := fl.isExported || old.isExported }
    if fl' == old then (rest, st) else
    match st.imports[m]? with
    | some is => (LvWork.ofImports fl' is ++ rest, { st with flags := st.flags.insert m fl' })
    | none => (rest, { st with flags := st.flags.insert m fl' })

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:69-111 levelsGo
**The fixpoint's worklist** (`importModulesCore.go`, iterative). -/
def levelsGo (fs : OleanFs) (pk : OleanPins) (sp : Roots) (gPriv : Bool) :
    Nat → List LvWork → LvState → AM LvState
  | _, [], st => pure st
  | 0, _ :: _, _ => fail (.internal "the header fixpoint ran out of steps")
  | fuel + 1, .done m fl :: rest, st =>
    levelsGo fs pk sp gPriv fuel rest
      { st with flags := st.flags.insert m fl, open_ := st.open_.erase m, order := st.order.push m }
  | fuel + 1, .imp pf i :: rest, st =>
    if !(i.isExported || pf.importAll) then levelsGo fs pk sp gPriv fuel rest st else
    let fl : LoadFlags := { importAll := gPriv || (pf.importAll && i.importAll),
                            isExported := pf.isExported && i.isExported }
    let m := i.module
    if st.flags.contains m then
      let (w, st) := levelsJoin st fl m rest
      levelsGo fs pk sp gPriv fuel w st
    else if st.open_.contains m then do
      fail (.internal s!"import cycle: a module importing {← readName m} is imported by it")
    else do
      let is ← moduleImports fs pk sp m
      levelsGo fs pk sp gPriv fuel (LvWork.ofImports fl is ++ .done m fl :: rest)
        { st with open_ := st.open_.insert m, imports := st.imports.insert m is }

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:113-122 HeaderLoads
**What Lean loads for a module**: its header's fixpoint, in Lean's module order. -/
structure HeaderLoads where
  order : Array NIdx
  flags : Array LoadFlags
  imports : Array (Array ImportRec)
  index : Std.HashMap NIdx Nat

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint
The fixpoint's state as `HeaderLoads`. -/
def HeaderLoads.ofState (st : LvState) : HeaderLoads :=
  let flags := st.order.map fun m => (st.flags[m]?).getD default
  let imps := st.order.map fun m => (st.imports[m]?).getD #[]
  let index := st.order.foldl (fun (acc : Std.HashMap NIdx Nat × Nat) m =>
    (acc.1.insert m acc.2, acc.2 + 1)) ({}, 0) |>.1
  { order := st.order, flags, imports := imps, index }

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint
**The header fixpoint** of a module whose header says `isModule` and `imports`. -/
def headerFixpoint (fs : OleanFs) (pk : OleanPins) (sp : Roots) (isModule : Bool)
    (imports : Array ImportRec) : AM HeaderLoads := do
  let root : LoadFlags := { importAll := true, isExported := isModule }
  let st ← levelsGo fs pk sp (!isModule) closureFuel (LvWork.ofImports root imports) {}
  pure (HeaderLoads.ofState st)

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:179-193 pubClosures
**Each loaded module's public-import closure**, by position in the load order. -/
def pubClosures (ld : HeaderLoads) : Array ConLeche.Frontend.Olean.ModSet :=
  let n := ld.order.size
  (List.range n).foldl (fun (acc : Array ConLeche.Frontend.Olean.ModSet) i =>
    let s := ((ld.imports[i]?).getD #[]).foldl (fun s imp =>
      if !imp.isExported then s else
      match ld.index[imp.module]? with
      | some j => if j < acc.size then s.union acc[j]! else s.add j
      | none => s) ((ConLeche.Frontend.Olean.ModSet.empty n).add i)
    acc.push s) (Array.mkEmpty n)

end ConRon.Arena.Frontend.Olean
