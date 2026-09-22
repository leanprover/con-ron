/-
# `ConRon.Refine2.Checker.Spec` — the twin-side transcriptions the Rust's splits need

**Task #97-P5-Checker** (DESIGN.md §8.2, Theorem 2).  DESIGN §3.4's extraction
rule 5 — *a `HashMap::get` match that produces a value is its own function; a
`view`'s loans must be dead at the memo's join* — makes the Rust of the
declaration checker **finer-grained than the twin**: `check_constant_val` is
four Rust functions, `check_proj_rule` is six, `check_value_group` is three.
None of those splits has a twin of its own, and DESIGN §3.1's one-to-one rule
is about the TWIN's granularity, not the port's.

Task #97-P5-0's finding 6 (the smaller half) fixed the idiom for this case:
*"the `_node` functions are task #97-P6-2's Rust-only splits with no named
twin, so `_two` is stated against the twin's arm inline and `_node` needs a
LOCAL TRANSCRIPTION plus an `_unfold` equation back to the twin"*.  This file
is that transcription, collected rather than scattered, so that

* each Rust split has exactly one twin-side subject, spelled once;
* the `_unfold` equations that tie the transcriptions back to the named twins
  are in one place, where a reader can check them against
  `Arena/CheckerBase.lean` and `Arena/CheckerSplit.lean` clause for clause;
* nothing under `Arena/` is edited to make the refinement convenient, which is
  the standing rule for a twin (DESIGN §8.4).

**Every definition here is a transcription of a CONTIGUOUS run of clauses of
one named twin, and every `_unfold` says exactly that.**  The `_unfold`s are
the file's proof obligation and they are `rfl`-shaped: the twin is a `do`
block and the transcription is its tail.
-/
import ConRon.Refine2.Checker.KnotHyp

open Aeneas Aeneas.Std Result

namespace ConRon.Arena

open ConLeche

/-! ## `checkConstantVal` / `installConstantVal`, in four

The Rust splits the common constant check at the two points where a guard
would otherwise join on a borrowed state (`check_constant_val_guards` /
`_rest`) and at the annotation (`install_constant_val_tail` /
`check_constant_val_after_annot`).  `Arena/CheckerBase.lean`'s
`checkConstantVal` and `Arena/CheckerSplit.lean`'s `installConstantVal` write
the same clauses out twice, as con-leche does; these four are the shared
pieces. -/

/-- The four guards past the reserved-name test:
`Arena/CheckerBase.lean:checkConstantVal` clauses 3-6. -/
def checkConstantValGuardsRestSpec (cv : IConstantVal) : AM Unit := do
  if ← NIdx.isProjFnShape cv.name then
    fail (.invalid s!"reserved projection name {← readName cv.name}")
  unless nameNodup cv.levelParams do
    fail (.invalid s!"duplicate universe parameters in {← readName cv.name}")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.invalid s!"loose bound variable in type of {← readName cv.name}")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.invalid s!"unexpected free variable in type of {← readName cv.name}")

/-- The six SYNTACTIC guards, in the twin's order:
`checkConstantVal` clauses 1-6. -/
def checkConstantValGuardsSpec (fe : IFEnv) (cv : IConstantVal) : AM Unit := do
  if (fe.find? cv.name).isSome then
    fail (.invalid s!"duplicate declaration {← readName cv.name}")
  if (← reservedBasisNames).contains cv.name then
    fail (.invalid s!"reserved basis name {← readName cv.name}")
  checkConstantValGuardsRestSpec cv

/-- The two guards on the ANNOTATED type and the header they produce —
`installConstantVal`'s tail, which `checkConstantVal` shares. -/
def installConstantValTailSpec (fe : IFEnv) (cv : IConstantVal) (ty : EIdx) :
    AM IConstantVal := do
  unless ← allLevelParamsDefined cv.levelParams ty do
    fail (.invalid
      s!"undeclared universe parameter in type of {← readName cv.name}")
  unless ← constsResolveFFast fe ty do
    fail (← unresolvedConstsError s!"type of {← readName cv.name}" ty)
  pure { cv with type := ty }

/-- `checkConstantVal`'s tail past the annotation: the install-side tail, then
the type's own inference and sort check. -/
def checkConstantValAfterAnnotSpec (mode : CheckMode) (fe : IFEnv)
    (cv : IConstantVal) (ty : EIdx) : AM IConstantVal := do
  let cvA ← installConstantValTailSpec fe cv ty
  let stype ← inferTypeCore mode fe checkFuel 0 cvA.type
  let _u ← ensureSortCore mode fe checkFuel 0 stype
  pure cvA

/-- `installValue`'s tail past the annotation. -/
def installValueTailSpec (fe : IFEnv) (cv : IConstantVal) (valueA : EIdx) :
    AM EIdx := do
  unless ← allLevelParamsDefined cv.levelParams valueA do
    fail (.invalid
      s!"undeclared universe parameter in value of {← readName cv.name}")
  unless ← constsResolveFFast fe valueA do
    fail (← unresolvedConstsError s!"value of {← readName cv.name}" valueA)
  pure valueA

/-! ## `checkValueGroup`, in three -/

/-- `checkValueGroup`'s tail: the value's type against the declared one. -/
def checkValueGroupTailSpec (mode : CheckMode) (fe : IFEnv) (g : ValueGroup)
    (jv : EIdx) : AM Unit := do
  let vtype ← inferTypeCore mode fe checkFuel 0 jv
  unless ← isDefEqCore mode fe checkFuel 0 vtype g.cvA.type do
    fail (.invalid
      s!"type mismatch in {g.kind.word} {← readName g.cvA.name}")

/-- `checkValueGroup`'s middle: the theorem's is-a-proposition test and, for a
theorem, the value's guards and annotation. -/
def checkValueGroupValueSpec (mode : CheckMode) (fe : IFEnv) (g : ValueGroup)
    (u : LIdx) : AM Unit := do
  let jv ← if g.kind == .thm then do
      let z ← zeroLevel
      unless ← liftFueled "level comparison" (← lvlEq? u z) do
        fail (.invalid
          s!"type of theorem {← readName g.cvA.name} is not a proposition")
      installValue mode fe g.cvA g.jv
    else pure g.jv
  checkValueGroupTailSpec mode fe g jv

/-! ## `constsResolveFGo`'s miss arm -/

/-- `constsResolveFGo`'s inner `match ← view h with`, at the view.  The four
LEAF arms are unreachable from `consts_resolve_f_node` — its caller has
already answered them — but they are transcribed rather than defaulted, and
that is why the spec carries the HANDLE beside the view: the twin's leaf arm
calls `constsResolve` at the handle, and the port's split does not have one.
The lemma about `consts_resolve_f_node` therefore also carries
"`h` views as `v`", which is task #97-P5-0's finding 3 met once more. -/
def constsResolveFNodeSpec (fe : IFEnv) (memo : Std.HashMap EIdx Bool)
    (fuel : Nat) (h : EIdx) : ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .fvar _ ty => constsResolveFGo fe memo fuel ty
  | .app f a => do
    let (b₁, memo) ← constsResolveFGo fe memo fuel f
    let (b₂, memo) ← constsResolveFGo fe memo fuel a
    pure (b₁ && b₂, memo)
  | .lam ty body _ | .forallE ty body _ => do
    let (b₁, memo) ← constsResolveFGo fe memo fuel ty
    let (b₂, memo) ← constsResolveFGo fe memo fuel body
    pure (b₁ && b₂, memo)
  | .letE ty val body => do
    let (b₁, memo) ← constsResolveFGo fe memo fuel ty
    let (b₂, memo) ← constsResolveFGo fe memo fuel val
    let (b₃, memo) ← constsResolveFGo fe memo fuel body
    pure (b₁ && b₂ && b₃, memo)
  | .proj s _ sub => do
    let (b, memo) ← constsResolveFGo fe memo fuel sub
    pure ((fe.find? s).isSome && b, memo)
  | _ => do pure (← constsResolve fe coreWalkFuel h, memo)

/-! ## `indParamsOk`'s per-member test -/

/-- `indParamsOk`'s body at one member — **the stream's declared parameter
count, checked as official checks it** (con-leche's task #228). -/
def indParamsOkAtSpec (nP : Nat) : IConstantInfo → AM Bool
  | .indInfo cvT _ => do
    match ← piSortTeleLen? coreWalkFuel cvT.type with
    | some n => pure (decide (nP ≤ n))
    | none => pure true
  | .ctorInfo _ nPc _ => pure (nPc == nP)
  | _ => pure true

/-! ## `checkProjRule`, in six

The five tails, outermost first.  Each is a contiguous run of
`Arena/CheckerBase.lean:checkProjRule`'s clauses; composing them back is the
`_unfold` at the bottom of this section. -/

/-- The innermost tail: the constructor's residual telescope opened, the
λ-domains compared and the rule's own type inferred. -/
def checkProjRuleFrameSpec (mode : CheckMode) (fe : IFEnv) (nP nF : Nat)
    (fvsP : List EIdx) (crestP rhsA : EIdx) : AM EIdx := do
  let some (xFvs, _) ← openPisAtFvarsF nF crestP nP
    | fail (.notImplemented "projection constructor telescope")
  let some (ldoms, _) ← instLamsAtF coreWalkFuel (fvsP ++ xFvs) rhsA
    | fail (.notImplemented "projection rule telescope")
  checkDefEqList mode fe (nP + nF) (← fvarTypeDs (fvsP ++ xFvs)) ldoms
  let _rhsTy ← inferTypeCore mode fe checkFuel 0 rhsA
  pure rhsA

/-- The parameter frame: the projection type's telescope opened at fresh free
variables and the constructor's domains instantiated at them. -/
def checkProjRuleCertsSpec (mode : CheckMode) (fe : IFEnv) (pty : EIdx)
    (cvj : IConstantVal) (nP nF : Nat) (rhsA : EIdx) : AM EIdx := do
  let some (fvsP, _) ← openPisAtFvarsF nP pty 0
    | fail (.notImplemented "projection type telescope")
  let some (cdomsP, crestP) ← instPisAtF coreWalkFuel fvsP cvj.type
    | fail (.notImplemented "projection constructor telescope")
  checkDefEqList mode fe (nP + nF) (← fvarTypeDs fvsP) cdomsP
  checkProjRuleFrameSpec mode fe nP nF fvsP crestP rhsA

/-- The λ-telescope shape: the annotated rule is a λ over the constructor
telescope returning the field variable, and its domains are the
constructor's. -/
def checkProjRuleShapeSpec (mode : CheckMode) (fe : IFEnv) (pty : EIdx)
    (cvj : IConstantVal) (nP nF : Nat) (bv rhsA : EIdx) : AM EIdx := do
  let some (rbinders, rrbody) ← stripLams (nP + nF) rhsA
    | fail (.notImplemented "projection rule telescope")
  unless rrbody == bv do
    fail (.notImplemented "projection rule body")
  let some (cbindersR, _) ← stripPis (nP + nF) cvj.type
    | fail (.notImplemented "projection constructor telescope")
  unless domsMatchAux rbinders.toArray cbindersR.toArray 0 0 (nP + nF) do
    fail (.notImplemented "projection rule domain mismatch")
  checkProjRuleCertsSpec mode fe pty cvj nP nF rhsA

/-- The well-formedness conjunct on the ANNOTATED rule. -/
def checkProjRuleWfSpec (mode : CheckMode) (fe : IFEnv) (pty : EIdx)
    (cvj : IConstantVal) (lps : List NIdx) (nP nF : Nat) (bv rhsA : EIdx) :
    AM EIdx := do
  unless (← allLevelParamsDefined lps rhsA) && (← constsResolveFFast fe rhsA) &&
      (← looseBVarsBoundedFast coreWalkFuel 0 rhsA) &&
      !(← hasFvarFast coreWalkFuel rhsA) do
    fail (.notImplemented "projection rule wellformedness")
  checkProjRuleShapeSpec mode fe pty cvj nP nF bv rhsA

/-- The scoping test on the RAW rule, then the annotation. -/
def checkProjRuleScopedSpec (mode : CheckMode) (fe : IFEnv) (pty : EIdx)
    (cvj : IConstantVal) (lps : List NIdx) (nP nF : Nat) (bv rhs : EIdx) :
    AM EIdx := do
  unless !(← hasFvarFast coreWalkFuel rhs) &&
      (← looseBVarsBoundedFast coreWalkFuel 0 rhs) do
    fail (.notImplemented "projection rule scoping")
  let rhsA ← annotateCore mode fe checkFuel 0 rhs
  checkProjRuleWfSpec mode fe pty cvj lps nP nF bv rhsA

/-! ## The `_unfold` equations

Each says that the named twin IS its transcription composed — the file's whole
proof obligation, and the only thing a reader has to check against
`Arena/CheckerBase.lean` and `Arena/CheckerSplit.lean`. -/

/-- `checkConstantVal` is its four pieces. -/
theorem checkConstantVal_unfold (mode : CheckMode) (fe : IFEnv)
    (cv : IConstantVal) :
    checkConstantVal mode fe cv = (do
      checkConstantValGuardsSpec fe cv
      let type ← annotateCore mode fe checkFuel 0 cv.type
      checkConstantValAfterAnnotSpec mode fe cv type) := by
  sorry

/-- `installConstantVal` is the same guards and the install-side tail. -/
theorem installConstantVal_unfold (mode : CheckMode) (fe : IFEnv)
    (cv : IConstantVal) :
    installConstantVal mode fe cv = (do
      checkConstantValGuardsSpec fe cv
      let type ← annotateCore mode fe checkFuel 0 cv.type
      installConstantValTailSpec fe cv type) := by
  sorry

/-- `installValue` is its guards, its annotation and its tail. -/
theorem installValue_unfold (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) :
    installValue mode fe cv value = (do
      unless ← looseBVarsBoundedFast coreWalkFuel 0 value do
        fail (.invalid s!"loose bound variable in value of {← readName cv.name}")
      if ← hasFvarFast coreWalkFuel value then
        fail (.invalid
          s!"unexpected free variable in value of {← readName cv.name}")
      let valueA ← annotateCore mode fe checkFuel 0 value
      installValueTailSpec fe cv valueA) := by
  sorry

/-- `checkValueGroup` is its three pieces. -/
theorem checkValueGroup_unfold (mode : CheckMode) (fe : IFEnv) (g : ValueGroup) :
    checkValueGroup mode fe g = (do
      let stype ← inferTypeCore mode fe checkFuel 0 g.cvA.type
      let u ← ensureSortCore mode fe checkFuel 0 stype
      checkValueGroupValueSpec mode fe g u) := by
  sorry

/-- `constsResolveFGo` is its probe and its node transcription. -/
theorem constsResolveFGo_unfold (fe : IFEnv) (memo : Std.HashMap EIdx Bool)
    (fuel : Nat) (h : EIdx) :
    constsResolveFGo fe memo (fuel + 1) h = (do
      match ← view h with
      | .bvar _ | .sort _ | .lit _ | .const _ _ =>
        pure (← constsResolve fe coreWalkFuel h, memo)
      | _ => do
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let p ← constsResolveFNodeSpec fe memo fuel h (← view h)
          pure (p.1, p.2.insert h p.1)) := by
  sorry

/-- `indParamsOk` is its per-member test and the `&&` fold. -/
theorem indParamsOk_unfold (nP : Nat) (ci : IConstantInfo)
    (rest : List IConstantInfo) :
    indParamsOk nP (ci :: rest) = (do
      if ← indParamsOkAtSpec nP ci then indParamsOk nP rest else pure false) := by
  sorry

/-- `checkProjRule` is its six pieces. -/
theorem checkProjRule_unfold (mode : CheckMode) (fe : IFEnv) (pty : EIdx)
    (cvj : IConstantVal) (lps : List NIdx) (nP nF i : Nat) :
    checkProjRule mode fe pty cvj lps nP nF i = (do
      let bv ← internE (.bvar (nF - 1 - i))
      let some rhs ← pisToLams (nP + nF) cvj.type bv
        | fail (.notImplemented "projection rule telescope")
      checkProjRuleScopedSpec mode fe pty cvj lps nP nF bv rhs) := by
  sorry

end ConRon.Arena
