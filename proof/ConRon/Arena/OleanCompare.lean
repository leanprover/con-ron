/-
# `con-ron-lean-olean-compare` — a home's read over the Lean twin (task #142)

`con-ron-lean-olean-compare --views SEARCHPATH MODULE...`: every module of the closure
read at its home (`readAllViews`) and each view against `readView`'s, the half of
upstream's `OleanCompare.lean` that `tests/olean.sh` drives.  A development tool: it is
what `scripts/diff-olean.sh` passes as `CMP` for the twin.
-/
module

public import ConRon.Arena.Main

@[expose] public section

namespace ConRon.Arena.OleanCompare

open ConLeche
open ConRon.Arena.Frontend.Olean

/-- con-leche: OleanCompare.lean:121-124 viewsEq
A view's constants by the checker's equality. -/
def viewsEq (a b : ModDecoded) : Bool :=
  a.isModule == b.isModule && a.imports == b.imports && a.constants.size == b.constants.size &&
    (a.constants.zip b.constants).all fun (x, y) => entrySame x y

/-- con-leche: OleanCompare.lean:127-144 runViews
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
  pure (.ok order.size)

/-- con-leche: OleanCompare.lean:153-207 main
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

/-- con-leche: OleanCompare.lean:153-207 main
The executable's entry point. -/
def main (args : List String) : IO UInt32 := do
  let c ← ConRon.Arena.OleanCompare.main args
  return c.toUInt32
