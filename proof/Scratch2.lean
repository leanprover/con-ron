import ConRon.Arena

namespace ConRon.Arena
open ConLeche

theorem fail_bind' {α β : Type} (e : CheckError) (k : α → AM β) :
    (fail e >>= k) = fail e := rfl

theorem ite_bind' {α β : Type} (c : Prop) [Decidable c] (a b : AM α) (k : α → AM β) :
    ((if c then a else b) >>= k) = if c then a >>= k else b >>= k := by
  split <;> rfl

theorem dite_bind' {α β : Type} (c : Prop) [Decidable c] (a : c → AM α)
    (b : ¬ c → AM α) (k : α → AM β) :
    ((if h : c then a h else b h) >>= k) = if h : c then a h >>= k else b h >>= k := by
  split <;> rfl

def checkConstantValGuardsRestSpec' (cv : IConstantVal) : AM Unit := do
  if ← NIdx.isProjFnShape cv.name then
    fail (.invalid s!"reserved projection name {← readName cv.name}")
  unless nameNodup cv.levelParams do
    fail (.invalid s!"duplicate universe parameters in {← readName cv.name}")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.invalid s!"loose bound variable in type of {← readName cv.name}")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.invalid s!"unexpected free variable in type of {← readName cv.name}")

def checkConstantValGuardsSpec' (fe : IFEnv) (cv : IConstantVal) : AM Unit := do
  if (fe.find? cv.name).isSome then
    fail (.invalid s!"duplicate declaration {← readName cv.name}")
  if (← reservedBasisNames).contains cv.name then
    fail (.invalid s!"reserved basis name {← readName cv.name}")
  checkConstantValGuardsRestSpec' cv

def installConstantValTailSpec' (fe : IFEnv) (cv : IConstantVal) (ty : EIdx) :
    AM IConstantVal := do
  unless ← allLevelParamsDefined cv.levelParams ty do
    fail (.invalid
      s!"undeclared universe parameter in type of {← readName cv.name}")
  unless ← constsResolveFFast fe ty do
    fail (← unresolvedConstsError s!"type of {← readName cv.name}" ty)
  pure { cv with type := ty }

def checkConstantValAfterAnnotSpec' (mode : CheckMode) (fe : IFEnv)
    (cv : IConstantVal) (ty : EIdx) : AM IConstantVal := do
  let cvA ← installConstantValTailSpec' fe cv ty
  let stype ← inferTypeCore mode fe checkFuel 0 cvA.type
  let _u ← ensureSortCore mode fe checkFuel 0 stype
  pure cvA

theorem checkConstantVal_unfold' (mode : CheckMode) (fe : IFEnv)
    (cv : IConstantVal) :
    checkConstantVal mode fe cv = (do
      checkConstantValGuardsSpec' fe cv
      let type ← annotateCore mode fe checkFuel 0 cv.type
      checkConstantValAfterAnnotSpec' mode fe cv type) := by
  simp only [checkConstantVal, checkConstantValGuardsSpec',
    checkConstantValGuardsRestSpec', checkConstantValAfterAnnotSpec',
    installConstantValTailSpec', bind_assoc, pure_bind, fail_bind', ite_bind', dite_bind']

end ConRon.Arena
