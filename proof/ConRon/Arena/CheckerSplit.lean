/-
# `ConRon.Arena.CheckerSplit` — the install/check seam of a value declaration

The twin of `ConLeche/Kernel/CheckerSplit.lean`: `checkDecl`'s three value
kinds split into an INSTALL half (the syntactic guards) and a CHECK half (the inference and the conversion), with `ValueGroup` as the
datum that crosses the seam.

**This is where (B)'s per-declaration bracket lives** (DESIGN §8.3's "Drop",
and this task's deliverable (b)).  `Arena/Core.lean`'s `enterScratch` /
`dropScratch` bracket the CHECK half and nothing else, because the split is
exactly the line between what a declaration LEAVES BEHIND and what it merely
computes:

* the install half guards the type and the value, which are the terms the
  environment stores as declared — so they must be PERSISTENT, and the half
  runs outside the bracket;
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

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:50-58 ValueGroup — what the
install half hands the check half: the kind, the header, and the value —
guarded for a definition or an opaque (the install half stored it), unguarded
for a theorem (the install half never looked at it: a theorem is stored by its
statement, and the check half runs the value's guards itself). -/
structure ValueGroup where
  kind : ValueKind
  cv : IConstantVal
  jv : EIdx
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:63-79 installHeader —
-- con-leche: CHANGED since ae1f3198 — re-port, re-test, re-prove CheckerSplit.installHeader_bridge, then delete this line
`checkConstantVal` minus its inference: the syntactic guards.  con-leche writes
the shared clauses out twice and so does this, clause for clause. -/
def installHeader (fe : IFEnv) (cv : IConstantVal) : AM Unit := do
  if (fe.find? cv.name).isSome then
    fail (.invalid "duplicate declaration")
  if (← reservedBasisNames).contains cv.name then
    fail (.invalid "reserved basis name")
  if ← NIdx.isProjFnShape cv.name then
    fail (.invalid "reserved projection name")
  unless nameNodup cv.levelParams do
    fail (.invalid "duplicate universe parameters")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.invalid "loose bound variable in type")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.invalid "unexpected free variable in type")
  unless ← allLevelParamsDefined cv.levelParams cv.type do
    fail (.invalid
      "undeclared universe parameter in type")
  unless ← constsResolveFFast fe cv.type do
    fail (← unresolvedConstsErrorL (← strLitSupported fe) "type" cv.type)

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:81-92 installValueGuards — the
value half of `check{Defn,Thm,Opaque}Val` minus its inference: the guards. -/
def installValueGuards (fe : IFEnv) (cv : IConstantVal) (value : EIdx) :
    AM Unit := do
  unless ← looseBVarsBoundedFast coreWalkFuel 0 value do
    fail (.invalid "loose bound variable in value")
  if ← hasFvarFast coreWalkFuel value then
    fail (.invalid "unexpected free variable in value")
  unless ← allLevelParamsDefined cv.levelParams value do
    fail (.invalid
      "undeclared universe parameter in value")
  unless ← constsResolveFFast fe value do
    fail (← unresolvedConstsErrorL (← strLitSupported fe) "value" value)

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:94-110 checkValueGroup —
**the check half of a value declaration**, at the environment the constant was
installed at: the type's sort, the theorem's is-a-proposition test, for a
theorem the value's guards, and the value's type against the
declared one — the inference and conversion calls of `checkConstantVal` and
`check{Defn,Thm,Opaque}Val`, in their order, with their messages. -/
def checkValueGroup (mode : CheckMode) (fe : IFEnv) (g : ValueGroup) :
    AM Unit := do
  let stype ← inferTypeCore mode fe checkFuel 0 g.cv.type
  let u ← ensureSortCore mode fe checkFuel 0 stype
  if g.kind == .thm then do
    let z ← zeroLevel
    unless ← liftFueled "level comparison" (← lvlEq? u z) do
      fail (.invalid "type of theorem is not a proposition")
    installValueGuards fe g.cv g.jv
  let vtype ← inferTypeCore mode fe checkFuel 0 g.jv
  unless ← isDefEqCore mode fe checkFuel 0 vtype g.cv.type do
    fail (.invalid s!"type mismatch in {g.kind.word}")

end ConRon.Arena
