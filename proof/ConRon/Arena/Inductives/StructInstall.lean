/-
# `ConRon.Arena.Inductives.StructInstall` — the projection table's checks
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/StructInstall.lean` whole, over handles: the
binder-domain walk and the checks of the projection TABLE a structure-like
member installs (the table itself is read off the block, `Arena/Install.lean`).

**The cached twins collapse into these**: con-leche carries each of this
module's two functions twice — the specification over `Env`
(`StructInstall.lean`) and the cached driver's twin over `FEnv`
(`checkStructDomsAtC`, `ConLeche/Cached/IndBlock.lean`;
`checkStructProjTableC`, `ConLeche/Cached/IndTail.lean`).  The arena has ONE
environment type, the index, and one tier, so the twin is one function citing
both.
-/
module

public import ConRon.Arena.CheckerBase

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:31-50 checkStructDomsAt
con-leche: ConLeche/Cached/IndBlock.lean:117-125 checkStructDomsAtC
The reference kernels' binder-domain comparisons, run binder by binder **at
its own frame**: the `j`-th opened variable's annotation against the `j`-th
expected domain, at frame `off + j`.  Walks from the last binder to the
first. -/
def checkStructDomsAt (mode : CheckMode) (fe : IFEnv) (off : Nat)
    (fvs doms : List EIdx) : Nat → AM Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← isDefEqCore mode fe checkFuel (off + j) (← fvarTypeD a) b do
      fail (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAt mode fe off fvs doms j

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:52-74 checkStructProjTable
con-leche: ConLeche/Cached/IndTail.lean:194-202 checkStructProjTableC
Stage 5: **the projection table's checks** (task #175 S1), at the table the
block installs (`Arena/Install.lean`'s `blockTables`): its bodies' scoping at
its own level parameters and parameter count, validated once; the table
follows its structure, declared by the same block (the structure must be
stored), and its name is not yet taken.  Nothing is pushed. -/
def checkStructProjTable (t : IProjTable) (fe : IFEnv) : AM Unit := do
  -- the bodies' scoping, validated once at insertion: fvar-free, level
  -- parameters within the structure's, resolving, scoped at the parameters
  -- and the subject; one per field
  let scopedOk ← t.bodies.toList.allM fun b => do
    pure (!(← hasFvarFast coreWalkFuel b) &&
      (← allLevelParamsDefined t.levelParams b) &&
      (← constsResolveFFast fe b) &&
      (← looseBVarsBoundedFast coreWalkFuel (t.numParams + 1) b))
  unless t.bodies.size = t.numFields ∧ scopedOk do
    fail (.internal "direct structure: projection body scoping")
  -- the table follows its structure (declared by the same block)
  unless (fe.find? t.structName).isSome do
    fail (.internal "direct structure: projection table before its structure")
  unless (fe.findTable? t.structName).isNone do
    fail (.invalid "projection table taken")

end ConRon.Arena
