/-
# `con-ron-lean-olean-compare` — a home's read over the Lean twin (task #142)

`con-ron-lean-olean-compare --views SEARCHPATH MODULE...`: every module of the closure
read at its home (`readAllViews`) and each view against `readView`'s, the half of
upstream's `OleanCompare.lean` that `tests/olean.sh` drives.  A development tool: it is
what `scripts/diff-olean.sh` passes as `CMP` for the twin.  `--views` also runs
`OleanTests.lean`'s `agree` at each view, so that the reads no checking path takes run.
The top-level `main` is `OleanCompareExe.lean`'s, for `Exe.lean`'s reason.
-/
module

public import ConRon.Arena.Main

@[expose] public section

namespace ConRon.Arena.OleanCompare

open ConLeche
open ConRon.Arena.Frontend.Olean

/-- con-leche: OleanCompare.lean:118-121 viewsEq
A view's constants by the checker's equality. -/
def viewsEq (a b : ModDecoded) : Bool :=
  a.isModule == b.isModule && a.imports == b.imports && a.constants.size == b.constants.size &&
    (a.constants.zip b.constants).all fun (x, y) => entrySame x y

/-- con-leche: none — `tests/ConLecheTests/OleanTests.lean`'s `agree`, at a module's
home: every read of a part of a view is its part, so that `--views` runs the reads no
checking path takes. -/
def agree (pk : OleanPins) (f : ConLeche.Frontend.Olean.ModFiles) (d : ModDecoded)
    (level : ConLeche.Frontend.Olean.OLeanLevel) : AM Bool := do
  let some l ← readNamePositions pk f level | return false
  unless l.header.imports == d.imports && l.consts.size == d.constants.size do return false
  for (x, y) in l.consts.zip d.constants do
    unless x.name == y.name do return false
    let some en ← readEntry pk f level x.loc | return false
    unless entrySame en y do return false
  let some ss ← readStmts pk f level (l.consts.toList.map (·.loc)) | return false
  return ss == d.constants.toList.map entryStmt

/-- con-leche: OleanCompare.lean:124-141 runViews
`--views`: every module of the closure, as one `AM`. -/
def viewsGo (sp : List System.FilePath) (roots : Array Name) : AM (Except String Nat) := do
  let pk ← oleanPins
  let rs ← roots.mapM internName
  let order ← closureOrder stdFs pk sp rs
  for m in order do
    let (v, _) ← readAllViews stdFs pk sp m
    for level in [ConLeche.Frontend.Olean.OLeanLevel.exported, .server, .private] do
      let d ← readView stdFs pk sp m level
      unless viewsEq d (v.at level) do
        return .error s!"module {← readName m}: the {repr level} view differs from the home's"
      let f ← liftE (readFiles stdFs sp (← readName m) .private)
      unless ← agree pk f d level do
        return .error s!"module {← readName m}: the {repr level} reads of a part differ from the view"
  pure (.ok order.size)

/-- con-leche: OleanCompare.lean:150-204 main
The command line. -/
def main (args : List String) : IO UInt8 := do
  match args with
  | "--views" :: sp :: mods@(_ :: _) =>
    let roots := mods.toArray.filterMap ConLeche.Frontend.Olean.parseModName
    let dirs := (sp.splitOn ":").map System.FilePath.mk
    match (viewsGo dirs roots).run (AState.init EStore.empty) with
    | .error e =>
      IO.eprintln e.message
      return e.exitCode
    | .ok (.error m, _) =>
      IO.eprintln m
      return 3
    | .ok (.ok n, _) =>
      IO.println s!"{n} modules: every view read, one memo, agrees"
      return 0
  | _ =>
    IO.eprintln "usage: con-ron-lean-olean-compare --views SEARCHPATH MODULE..."
    return 3

end ConRon.Arena.OleanCompare
