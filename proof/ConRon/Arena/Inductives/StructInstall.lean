/-
# `ConRon.Arena.Inductives.StructInstall` — the projection table's checks
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/StructInstall.lean` whole, over handles: the
binder-domain walk and the projection TABLE the uniform route stores at a
structure-like block.

**The `…F` twins collapse into these** (task #97c's deviation 1): con-leche
carries each of this module's two functions twice — once over `Env`
(`StructInstall.lean`) and once over `FEnv`
(`ConLeche/Kernel/Inductives/StructInstallF.lean`), and
`checkStructDomsAtFA` a third time over `Array`.  The arena has ONE
environment type, the index, so the twin is one function citing all of them.
-/
import ConRon.Arena.CheckerBase

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

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:52-84 checkStructProjTable
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:71-92 checkStructProjTableF
Stage 5: **the projection table** (task #175 S1).  One table per structure, in
the environment's table component: the fields' result-type bodies read off the
stored constructor type by substitution alone, the per-field guard levels, the
constructor and the counts.  The table follows its structure, installed by the
same block: the structure must be stored, its table not yet taken. -/
def checkStructProjTable (T C : NIdx) (lps : List NIdx) (nP nF : Nat)
    (resSort : LIdx) (guards : List LIdx) (cvCa : IConstantVal)
    (fe : IFEnv) : AM IFEnv := do
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
  unless (fe.find? T).isSome do
    fail (.internal "direct structure: projection table before its structure")
  unless (fe.findTable? T).isNone do
    fail (.invalid "projection table taken")
  pure (fe.pushTable ⟨T, lps, nP, C, nF, resSort, bodies, guards⟩)

end ConRon.Arena
