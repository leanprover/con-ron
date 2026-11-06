/-
# `ConRon.Arena.Frontend.Olean.Closure` — the import closure (task #142)

The twin of `olean/closure.rs`.  **Sequential**: `parMapExcept`'s model is the
sequential map, and the store has one writer (DESIGN.md's `### Task #142`).

**The stacks are `List`s here, as upstream's are**, the head the top; the Rust's are
a `Vec` and an index with the top last, a one-line invariant for Theorem 2 and none
for Theorem 1.  Upstream's `constsGo` is `partial` and its `emitLoop` well-founded;
both take fuel here, as `closureGo` does upstream (`Arena/Frontend/ExportC.lean`'s
"Fuel", DESIGN §8.4).
-/
module

public import ConLeche.Frontend.Olean.Closure
public import ConRon.Arena.Frontend.Olean.Files

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (CEntryF CKindF closureFuel OLeanLevel)

/-- con-leche: none — a walk's fuel spent -/
def outOfFuel {α : Type} : AM α := fail (.internal "the import closure's walk ran out of steps")

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:25-62 constsGo
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Closure.addN_bridge, then delete this line
A name, once: "written out at each leaf" upstream. -/
@[inline] def addN (seenN : Std.HashSet NIdx) (out : Array NIdx) (n : NIdx) :
    Std.HashSet NIdx × Array NIdx :=
  if seenN.contains n then (seenN, out) else (seenN.insert n, out.push n)

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:25-62 constsGo
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Closure.constsGo_bridge, then delete this line
The DAG walk of `constsOf`.  A leaf needs no visited entry; by the tag, as the Rust's
walk tests it, so that a `bvar` or a `sort` is not looked at and a visited node is not
looked at again. -/
def constsGo (pk : OleanPins) : Nat → List EIdx → Std.HashSet EIdx → Std.HashSet NIdx →
    Array NIdx → AM (Array NIdx)
  | _, [], _, _, out => pure out
  | 0, _ :: _, _, _, _ => outOfFuel
  | fuel + 1, e :: rest, seen, seenN, out => do
    if e.tag == ETag.const || e.tag == ETag.lit then
      match ← view e with
      | .const n _ =>
        let (seenN, out) := addN seenN out n
        constsGo pk fuel rest seen seenN out
      | .lit (.natVal _) =>
        let (seenN, out) := addN seenN out pk.nNat
        constsGo pk fuel rest seen seenN out
      | .lit (.strVal _) =>
        let (seenN, out) := addN seenN out pk.nCharOfNat
        let (seenN, out) := addN seenN out pk.nStringOfList
        constsGo pk fuel rest seen seenN out
      | _ => constsGo pk fuel rest seen seenN out
    else if e.tag == ETag.bvar || e.tag == ETag.sort || seen.contains e then
      constsGo pk fuel rest seen seenN out
    else
      let seen := seen.insert e
      if ETag.proj < e.tag then constsGo pk fuel rest seen seenN out else
      match ← view e with
      | .app f a => constsGo pk fuel (f :: a :: rest) seen seenN out
      | .lam t b | .forallE t b => constsGo pk fuel (t :: b :: rest) seen seenN out
      | .letE t w b => constsGo pk fuel (t :: w :: b :: rest) seen seenN out
      | .proj _ _ x => constsGo pk fuel (x :: rest) seen seenN out
      | .fvar _ t => constsGo pk fuel (t :: rest) seen seenN out
      | _ => constsGo pk fuel rest seen seenN out

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:64-69 constsOf
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Closure.constsOf_bridge, then delete this line
**The constants an expression mentions**, in first-visit order, and the literal
dependencies lean4export adds. -/
def constsOf (pk : OleanPins) (es : List EIdx) : AM (Array NIdx) :=
  constsGo pk closureFuel es (Std.HashSet.emptyWithCapacity 256) (Std.HashSet.emptyWithCapacity 64) #[]

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:154-158 CEntry
**One stored constant**, as the merge and the emitter need it. -/
structure CEntry where
  c : CEntryF NIdx EIdx
  uses : Array NIdx := #[]

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:162-163 CEntry.skipped
`CKindF.skipped` of a stored constant. -/
@[inline] def CEntry.skipped (c : CEntry) : Bool := c.c.kind.skipped

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:82-87 CEntry.deps
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Closure.entryDeps_bridge, then delete this line
The expressions a record depends on. -/
def entryDeps (c : CEntryF NIdx EIdx) : List EIdx :=
  match c.kind with
  | .defn v .. | .thm v _ | .opaq v _ => [c.type, v]
  | .recur _ _ _ _ _ rules _ _ => c.type :: rules.map (·.2.2)
  | _ => [c.type]

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:89-92 CEntry.ofRead
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Closure.CEntry.ofRead_bridge, then delete this line
A constant with what it mentions. -/
def CEntry.ofRead (pk : OleanPins) (c : CEntryF NIdx EIdx) : AM CEntry := do
  pure { c, uses := ← constsOf pk (entryDeps c) }

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

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:165-170 Loaded
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Closure.Loaded_bridge, then delete this line
A loaded module: its constants at the private level. -/
structure Loaded where
  name : NIdx
  constants : Array CEntry

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:62-74 loadModule
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Closure.loadModule_bridge, then delete this line
**Load one module** for the merge: its private view, what Lean's own import outside
the module system and lean4export load. -/
def loadModule (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (m : NIdx) : AM Loaded := do
  let d ← readView fs pk sp m .private
  pure ⟨m, ← d.constants.mapM (CEntry.ofRead pk)⟩

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:76-88 loadClosure
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Closure.loadClosure_bridge, then delete this line
**The closure, loaded**: its modules in Lean's order, decoded. -/
def loadClosure (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (roots : Array NIdx) :
    AM (Array Loaded) := do
  let order ← closureOrder fs pk sp roots
  order.mapM (loadModule fs pk sp)

end ConRon.Arena.Frontend.Olean
