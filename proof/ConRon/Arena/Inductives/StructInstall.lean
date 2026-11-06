/-
# `ConRon.Arena.Inductives.StructInstall` — the projection table's checks
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/StructInstall.lean` whole, over handles: the
binder-domain walk and the checks of the projection TABLE a structure-like
member installs (the table itself is read off the block, `Arena/Install.lean`).

**The `…F` twins collapse into these** (task #97c's deviation 1): con-leche
carries each of this module's two functions twice — once over `Env`
(`StructInstall.lean`) and once over `FEnv`
(`ConLeche/Kernel/Inductives/StructInstallF.lean`), and
`checkStructDomsAtFA` a third time over `Array`.  The arena has ONE
environment type, the index, so the twin is one function citing all of them.
-/
module

public import ConRon.Arena.CheckerBase

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:31-50 checkStructDomsAt
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:25-34 checkStructDomsAtF
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:36-46 checkStructDomsAtFA
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

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:52-80 checkStructProjTable
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:71-89 checkStructProjTableF
Stage 5: **the projection table's checks** (task #175 S1): the fields'
result-type bodies read off the stored constructor type by substitution alone,
validated once; the table follows its structure, declared by the same block
(the structure must be stored), and its name is not yet taken.  Nothing is
pushed: the table is the block's install (`Arena/Install.lean`'s
`blockTables`). -/
def checkStructProjTable (T : NIdx) (lps : List NIdx) (nP nF : Nat)
    (cvCa : IConstantVal) (fe : IFEnv) : AM Unit := do
  let bodies ← unwrapOr (← structProjBodies T nP nF cvCa.type)
    (.internal "direct structure: projection bodies")
  -- the bodies' scoping, validated once at insertion: fvar-free, level
  -- parameters within the structure's, resolving, scoped at the parameters
  -- and the subject; one per field
  let scopedOk ← bodies.toList.allM fun b => do
    pure (!(← hasFvarFast coreWalkFuel b) &&
      (← allLevelParamsDefined lps b) &&
      (← constsResolveFFast fe b) &&
      (← looseBVarsBoundedFast coreWalkFuel (nP + 1) b))
  unless bodies.size = nF ∧ scopedOk do
    fail (.internal "direct structure: projection body scoping")
  -- the table follows its structure (declared by the same block)
  unless (fe.find? T).isSome do
    fail (.internal "direct structure: projection table before its structure")
  unless (fe.findTable? T).isNone do
    fail (.invalid "projection table taken")

end ConRon.Arena
