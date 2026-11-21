/-
# `ConRon.Arena.Modular.CompareModule` — the compare worker's closure walk (task #166)

The twin of `frontend/modular/compare_module.rs`, con-leche's `ConLeche/Driver/CompareModule.lean`:
the challenge's closure through the trusted path alone (`chalWalk`).  The compare worker itself is
`workerRead` with `import all S` added (`solutionImport`).
-/
module

public import ConRon.Arena.Modular.Graph

@[expose] public section

namespace ConRon.Arena.Modular

open ConLeche
open ConRon.Arena.Frontend.Olean
open ConLeche.Frontend.Olean (Roots)

/-- con-leche: ConLeche/Driver/CompareModule.lean:36-47 chalWalk
**The challenge's closure through the trusted path alone** (`chalSp`): its graph, its verdict
only. -/
def chalWalk (fs : OleanFs) (pk : OleanPins) (chalSp : Roots) (c : NIdx) : AM Unit := do
  let _ ← graphOf fs pk chalSp [c] none
  pure ()

end ConRon.Arena.Modular
