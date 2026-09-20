/-
# `ConRon.Arena.CheckerSplit` — the install/check seam of a value declaration

The twin of `ConLeche/Kernel/CheckerSplit.lean`: `checkDecl`'s three value
kinds split into an INSTALL half (the syntactic guards and the annotation) and
a CHECK half (the inference and the conversion), with `ValueGroup` as the
datum that crosses the seam.

**This is where (B)'s per-declaration bracket lives** (DESIGN §8.3's "Drop",
and this task's deliverable (b)).  `Arena/Core.lean`'s `enterScratch` /
`dropScratch` bracket the CHECK half and nothing else, because the split is
exactly the line between what a declaration LEAVES BEHIND and what it merely
computes:

* the install half writes the annotated type and the annotated value, and
  those are the terms the environment stores — so they must be PERSISTENT, and
  the half runs outside the bracket;
* the check half infers the type's sort, infers the value's type and compares
  it with the declared one.  Everything it allocates is intermediate, and the
  scratch tier is dropped at its end.

con-leche's `ConLeche/Cached/Installed.lean` makes the same split GLOBAL (all
the installs, then all the checks); `Arena/Checker.lean` mirrors that fold as
`installThenCheck`, and there the bracket is per record, which is what DESIGN
§8.3's "scratch = one declaration's check" asks for.
-/
import ConRon.Arena.CheckerBase

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:36-42 ValueKind — the three
declaration kinds whose value check is separable from their install.  Census
class (P): no term in it, copied verbatim. -/
inductive ValueKind where
  | defn
  | thm
  | opaque
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:44-48 ValueKind.word — the
kind's word in `checkDecl`'s type-mismatch message. -/
def ValueKind.word : ValueKind → String
  | .defn => "definition"
  | .thm => "theorem"
  | .opaque => "opaque"

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:50-59 ValueGroup — what the
install half hands the check half: the kind, the header with its type
annotated, and the value — ANNOTATED for a definition or an opaque, RAW for a
theorem (the install half never looked at it: a theorem is stored by its
statement, and the check half annotates the value itself). -/
structure ValueGroup where
  kind : ValueKind
  cvA : IConstantVal
  jv : EIdx
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:64-85 installConstantVal —
`checkConstantVal` minus its inference: the syntactic guards and the
annotation of the type.  con-leche writes the shared clauses out twice and so
does this, clause for clause. -/
def installConstantVal (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    AM IConstantVal := do
  if (fe.find? cv.name).isSome then
    fail (.invalid s!"duplicate declaration {← readName cv.name}")
  if (← reservedBasisNames).contains cv.name then
    fail (.invalid s!"reserved basis name {← readName cv.name}")
  if ← NIdx.isProjFnShape cv.name then
    fail (.invalid s!"reserved projection name {← readName cv.name}")
  unless nameNodup cv.levelParams do
    fail (.invalid s!"duplicate universe parameters in {← readName cv.name}")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.invalid s!"loose bound variable in type of {← readName cv.name}")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.invalid s!"unexpected free variable in type of {← readName cv.name}")
  let type ← annotateCore mode fe checkFuel 0 cv.type
  unless ← allLevelParamsDefined cv.levelParams type do
    fail (.invalid
      s!"undeclared universe parameter in type of {← readName cv.name}")
  unless ← constsResolveFFast fe type do
    fail (← unresolvedConstsError s!"type of {← readName cv.name}" type)
  pure { cv with type := type }

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:87-100 installValue — the
value half of `check{Defn,Thm,Opaque}Val` minus its inference: the guards and
the annotation of the value. -/
def installValue (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) : AM EIdx := do
  unless ← looseBVarsBoundedFast coreWalkFuel 0 value do
    fail (.invalid s!"loose bound variable in value of {← readName cv.name}")
  if ← hasFvarFast coreWalkFuel value then
    fail (.invalid s!"unexpected free variable in value of {← readName cv.name}")
  let value ← annotateCore mode fe checkFuel 0 value
  unless ← allLevelParamsDefined cv.levelParams value do
    fail (.invalid
      s!"undeclared universe parameter in value of {← readName cv.name}")
  unless ← constsResolveFFast fe value do
    fail (← unresolvedConstsError s!"value of {← readName cv.name}" value)
  pure value

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:102-119 checkValueGroup —
**the check half of a value declaration**, at the environment the constant was
installed at: the type's sort, the theorem's is-a-proposition test, for a
theorem the value's guards and annotation, and the value's type against the
declared one — the inference and conversion calls of `checkConstantVal` and
`check{Defn,Thm,Opaque}Val`, in their order, with their messages. -/
def checkValueGroup (mode : CheckMode) (fe : IFEnv) (g : ValueGroup) :
    AM Unit := do
  let stype ← inferTypeCore mode fe checkFuel 0 g.cvA.type
  let u ← ensureSortCore mode fe checkFuel 0 stype
  let jv ← if g.kind == .thm then do
      let z ← zeroLevel
      unless ← liftFueled "level comparison" (← lvlEq? u z) do
        fail (.invalid
          s!"type of theorem {← readName g.cvA.name} is not a proposition")
      installValue mode fe g.cvA g.jv
    else pure g.jv
  let vtype ← inferTypeCore mode fe checkFuel 0 jv
  unless ← isDefEqCore mode fe checkFuel 0 vtype g.cvA.type do
    fail (.invalid
      s!"type mismatch in {g.kind.word} {← readName g.cvA.name}")

end ConRon.Arena
