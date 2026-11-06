/-
# `ConRon.Arena.Frontend.Olean.Closure` — the import closure (task #142)

The twin of `olean/closure.rs`.  **Sequential**: `parMapExcept`'s model is the
sequential map, and the store has one writer (DESIGN.md's `### Task #142`).  Every
module is loaded by `Arena/Frontend/Olean/Lazy.lean`'s `loadView`, its theorems'
values left in the file (upstream task #481); the heartbeat's lines are the file
seam's (`OleanFs.readNotesSay`, `readNotesModuleLoaded`).

**The stacks are `List`s here, as upstream's are**, the head the top; the Rust's are
a `Vec` and an index with the top last, a one-line invariant for Theorem 2 and none
for Theorem 1.  `closureGo` takes fuel, as upstream's does (`Arena/Frontend/ExportC.lean`'s
"Fuel", DESIGN §8.4).
-/
module

public import ConLeche.Frontend.Olean.Closure
public import ConRon.Arena.Frontend.Olean.Files
public import ConRon.Arena.Frontend.Olean.Lazy

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (CEntryF CKindF closureFuel OLeanLevel)

/-- con-leche: none — a walk's fuel spent -/
def outOfFuel {α : Type} : AM α := fail (.internal "the import closure's walk ran out of steps")

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:23-50 closureGo
**The import closure, in Lean's module order**: a module after everything it imports,
by an explicit stack.  A module whose imports are being expanded is on the walk's
current path, so an import of it is a cycle. -/
def closureGo (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) :
    Nat → List (NIdx × Bool) → Std.HashSet NIdx → Std.HashSet NIdx → Array NIdx → AM (Array NIdx)
  | _, [], _, _, out => pure out
  | 0, _ :: _, _, _, _ => outOfFuel
  | fuel + 1, (m, true) :: rest, seen, done, out =>
    closureGo fs pk sp fuel rest seen (done.insert m) (out.push m)
  | fuel + 1, (m, false) :: rest, seen, done, out =>
    if seen.contains m then closureGo fs pk sp fuel rest seen done out
    else do
      let imps ← moduleImports fs pk sp m
      let imps := imps.map (·.module)
      let seen := seen.insert m
      if let some c := imps.find? fun i => seen.contains i && !done.contains i then
        fail (.internal s!"import cycle: {← readName m} imports {← readName c}")
      else
        let kids := imps.toList.filter (!seen.contains ·) |>.map (·, false)
        closureGo fs pk sp fuel (kids ++ (m, true) :: rest) seen done out

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:56-58 closureOrder
The closure's module order from the roots. -/
def closureOrder (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (roots : Array NIdx) :
    AM (Array NIdx) :=
  closureGo fs pk sp closureFuel (roots.toList.map (·, false)) {} {} #[]

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:62-74 loadModule
**Load one module** for the merge, module `idx` of the `total` in the closure's order:
its private view, its theorems' values left in the file (`loadView`). -/
def loadModule (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (total : Nat)
    (m : NIdx) (idx : Nat) : AM Loaded := do
  let mn ← readName m
  let f ← liftE (readFiles fs sp mn .private)
  -- a failed load's note (`size` 0) is the unit, as every note is: not spelled out
  let r ← loadView pk idx m f
  let () := fs.readNotesModuleLoaded total r.constants.size
  pure r

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:76-88 loadClosure
`order.toList.zipIdx`, loaded in order, up to the first failure. -/
def loadAll (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (order : Array NIdx) :
    AM (Array Loaded) :=
  (order.toList.zipIdx.mapM fun (m, i) => loadModule fs pk sp order.size m i).map List.toArray

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:76-88 loadClosure
**The closure, loaded**: its modules in Lean's order, the heartbeat saying when the
walk and the load start. -/
def loadClosure (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (roots : Array NIdx) :
    AM (Array Loaded) := do
  let () := fs.readNotesSay "tracing the import closure"
  let order ← closureOrder fs pk sp roots
  let () := fs.readNotesSay s!"loading {order.size} modules"
  loadAll fs pk sp order

end ConRon.Arena.Frontend.Olean
