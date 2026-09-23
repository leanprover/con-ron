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
the file's proof obligation.

**They are NOT `rfl`-shaped** (task #97-P5-Checker-2, correcting that round's
§6).  The `do` elaborator pushes a statement's continuation INTO the branches
of the `if` above it — a join point — so a twin written `if c then fail e` and
then `rest` is `if c then fail e else rest`, where a transcription that names
the guard separately is `(if c then fail e else pure ()) >>= fun _ => rest`;
and `StateT`'s `bind` matches on the inner `Except`, so the two are not
definitionally equal at an opaque prefix.  **Rule 11**
(`Refine2/Checker/Shape.lean`) is the four-lemma reduction that closes them:
`bind_assoc`, `pure_bind`, `am_{ite,dite}_bind` and `am_fail_bind`, spelled
`twin_reduce [...]`.  Where the twin groups at a `match` rather than an `if`,
`am_bind_congr` peels the common prefix first — `congr 1` will NOT, because
`AM α` is a function type and `congr 1` eta-expands it instead.

Seven of the eight are closed; `divModCertStmts_unfold` is the exception and
its note says why.
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
    fail (.invalid "reserved projection name")
  unless nameNodup cv.levelParams do
    fail (.invalid "duplicate universe parameters")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.invalid "loose bound variable in type")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.invalid "unexpected free variable in type")

/-- The six SYNTACTIC guards, in the twin's order:
`checkConstantVal` clauses 1-6. -/
def checkConstantValGuardsSpec (fe : IFEnv) (cv : IConstantVal) : AM Unit := do
  if (fe.find? cv.name).isSome then
    fail (.invalid "duplicate declaration")
  if (← reservedBasisNames).contains cv.name then
    fail (.invalid "reserved basis name")
  checkConstantValGuardsRestSpec cv

/-- The two guards on the ANNOTATED type and the header they produce —
`installConstantVal`'s tail, which `checkConstantVal` shares. -/
def installConstantValTailSpec (fe : IFEnv) (cv : IConstantVal) (ty : EIdx) :
    AM IConstantVal :=
  allLevelParamsDefined cv.levelParams ty >>= fun d =>
    if d then
      constsResolveFFast fe ty >>= fun r =>
        if r then pure { cv with type := ty }
        else unresolvedConstsError "type" ty >>= fun e => fail e
    else fail (.invalid "undeclared universe parameter in type")

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
    AM EIdx :=
  allLevelParamsDefined cv.levelParams valueA >>= fun d =>
    if d then
      constsResolveFFast fe valueA >>= fun r =>
        if r then pure valueA
        else unresolvedConstsError "value" valueA >>= fun e => fail e
    else fail (.invalid "undeclared universe parameter in value")

/-! ## `checkValueGroup`, in three -/

/-- `checkValueGroup`'s tail: the value's type against the declared one. -/
def checkValueGroupTailSpec (mode : CheckMode) (fe : IFEnv) (g : ValueGroup)
    (jv : EIdx) : AM Unit := do
  let vtype ← inferTypeCore mode fe checkFuel 0 jv
  unless ← isDefEqCore mode fe checkFuel 0 vtype g.cvA.type do
    fail (.invalid s!"type mismatch in {g.kind.word}")

/-- `checkValueGroup`'s middle: the theorem's is-a-proposition test and, for a
theorem, the value's guards and annotation. -/
def checkValueGroupValueSpec (mode : CheckMode) (fe : IFEnv) (g : ValueGroup)
    (u : LIdx) : AM Unit := do
  let jv ← if g.kind == .thm then do
      let z ← zeroLevel
      unless ← liftFueled "level comparison" (← lvlEq? u z) do
        fail (.invalid "type of theorem is not a proposition")
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
  twin_reduce [checkConstantVal, checkConstantValGuardsSpec,
    checkConstantValGuardsRestSpec, checkConstantValAfterAnnotSpec,
    installConstantValTailSpec]

/-- `installConstantVal` is the same guards and the install-side tail. -/
theorem installConstantVal_unfold (mode : CheckMode) (fe : IFEnv)
    (cv : IConstantVal) :
    installConstantVal mode fe cv = (do
      checkConstantValGuardsSpec fe cv
      let type ← annotateCore mode fe checkFuel 0 cv.type
      installConstantValTailSpec fe cv type) := by
  twin_reduce [installConstantVal, checkConstantValGuardsSpec,
    checkConstantValGuardsRestSpec, installConstantValTailSpec]

/-- `installValue` is its guards, its annotation and its tail. -/
theorem installValue_unfold (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) :
    installValue mode fe cv value = (do
      unless ← looseBVarsBoundedFast coreWalkFuel 0 value do
        fail (.invalid "loose bound variable in value")
      if ← hasFvarFast coreWalkFuel value then
        fail (.invalid
          "unexpected free variable in value")
      let valueA ← annotateCore mode fe checkFuel 0 value
      installValueTailSpec fe cv valueA) := by
  twin_reduce [installValue, installValueTailSpec]

/-- `checkValueGroup` is its three pieces. -/
theorem checkValueGroup_unfold (mode : CheckMode) (fe : IFEnv) (g : ValueGroup) :
    checkValueGroup mode fe g = (do
      let stype ← inferTypeCore mode fe checkFuel 0 g.cvA.type
      let u ← ensureSortCore mode fe checkFuel 0 stype
      checkValueGroupValueSpec mode fe g u) := by
  twin_reduce [checkValueGroup, checkValueGroupValueSpec,
    checkValueGroupTailSpec]

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
  rw [constsResolveFGo]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro v
  cases v <;> try rfl
  all_goals
    (cases hm : memo[h]? with
     | some r => rfl
     | none =>
       refine ConRon.Refine2.am_bind_congr _ ?_
       intro v2
       cases v2 <;> twin_reduce [constsResolveFNodeSpec])

/-- `indParamsOk` is its per-member test and the `&&` fold. -/
theorem indParamsOk_unfold (nP : Nat) (ci : IConstantInfo)
    (rest : List IConstantInfo) :
    indParamsOk nP (ci :: rest) = (do
      if ← indParamsOkAtSpec nP ci then indParamsOk nP rest else pure false) := by
  cases ci <;> twin_reduce [indParamsOk, indParamsOkAtSpec]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro x
  cases x <;> twin_reduce

/-- `checkProjRule` is its six pieces. -/
theorem checkProjRule_unfold (mode : CheckMode) (fe : IFEnv) (pty : EIdx)
    (cvj : IConstantVal) (lps : List NIdx) (nP nF i : Nat) :
    checkProjRule mode fe pty cvj lps nP nF i = (do
      let bv ← internE (.bvar (nF - 1 - i))
      let some rhs ← pisToLams (nP + nF) cvj.type bv
        | fail (.notImplemented "projection rule telescope")
      checkProjRuleScopedSpec mode fe pty cvj lps nP nF bv rhs) := by
  rw [checkProjRule]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro bv
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro r
  cases r <;>
    twin_reduce [checkProjRuleScopedSpec, checkProjRuleWfSpec,
      checkProjRuleShapeSpec, checkProjRuleCertsSpec, checkProjRuleFrameSpec] <;>
    try rfl


/-! ## `arena::decl_check`'s splits (finding 11)

`decl_check.rs` is ninety-five `pub fn`s against thirty-three twin `def`s, and
`CertCtx` is the reason: `divModCertStmts` is a hundred-line `do` block over
twenty-one pinned handles, which DESIGN §3.4's rules split into twenty-three
Rust functions plus a record to carry the handles between them.  What follows
is the twin side of each split. -/

/-! ### The two axiom gates, in their arms -/

/-- `stdAxiomOk`'s pinned-`Eq`-basis test. -/
def eqBasisPinnedSpec (fe : IFEnv) : AM Bool := do
  let en ← pinEq
  let ea ← eqA
  pure (fe.find? en == some ea)

/-- `stdAxiomOk`'s `Iff` clause. -/
def iffPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← iffName) with
  | some (.indInfo cvI _) => cvI.matchesPin (← (← iffRaw).toConstantVal)
  | _ => pure false

/-- `stdAxiomOk`'s `Iff.intro` clause. -/
def iffIntroPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← iffIntroName) with
  | some (.ctorInfo cvIi 2 2) => cvIi.matchesPin (← (← iffIntroRaw).toConstantVal)
  | _ => pure false

/-- `stdAxiomOk`'s `Iff.rec` clause. -/
def iffRecPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← iffRecName) with
  | some (.recInfo cvIr 4 4 _) => cvIr.matchesPin (← (← iffRecRaw).toConstantVal)
  | _ => pure false

/-- `stdAxiomOk`'s `Nonempty` clause. -/
def nonemptyPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← nonemptyName) with
  | some (.indInfo cvN _) => cvN.matchesPin (← (← nonemptyRaw).toConstantVal)
  | _ => pure false

/-- `stdAxiomOk`'s `Nonempty.intro` clause. -/
def nonemptyIntroPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← nonemptyIntroName) with
  | some (.ctorInfo cvNi 1 1) =>
    cvNi.matchesPin (← (← nonemptyIntroRaw).toConstantVal)
  | _ => pure false

/-- `stdAxiomOk`'s `Nonempty.rec` clause. -/
def nonemptyRecPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← nonemptyRecName) with
  | some (.recInfo cvNr 3 3 _) => cvNr.matchesPin (← (← nonemptyRecRaw).toConstantVal)
  | _ => pure false

/-- `trustCompilerOk`'s `True` clause. -/
def truePinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← trueName) with
  | some (.indInfo cvT _) => cvT.matchesPin (← trueCvA)
  | _ => pure false

/-- `trustCompilerOk`'s `True.intro` clause. -/
def trueIntroPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← trueIntroName) with
  | some (.ctorInfo cvTi 0 0) => cvTi.matchesPin (← trueIntroCvA)
  | _ => pure false

/-- `stdAxiomOk`'s `propext` arm past the `Eq` basis test. -/
def stdAxiomOkPropextRestSpec (fe : IFEnv) (cvA : IConstantVal) : AM Bool := do
  if !(← iffPinnedSpec fe) then pure false
  else if !(← iffIntroPinnedSpec fe) then pure false
  else if !(← iffRecPinnedSpec fe) then pure false
  else cvA.matchesPin (← propextRaw)

/-- `stdAxiomOk`'s `propext` arm. -/
def stdAxiomOkPropextSpec (fe : IFEnv) (cvA : IConstantVal) : AM Bool := do
  if !(← eqBasisPinnedSpec fe) then pure false
  else stdAxiomOkPropextRestSpec fe cvA

/-- `stdAxiomOk`'s `Classical.choice` arm past the `Nonempty` clause. -/
def stdAxiomOkChoiceRestSpec (fe : IFEnv) (cvA : IConstantVal) : AM Bool := do
  if !(← nonemptyIntroPinnedSpec fe) then pure false
  else if !(← nonemptyRecPinnedSpec fe) then pure false
  else cvA.matchesPin (← choiceRaw)

/-- `stdAxiomOk`'s `Classical.choice` arm. -/
def stdAxiomOkChoiceSpec (fe : IFEnv) (cvA : IConstantVal) : AM Bool := do
  if !(← nonemptyPinnedSpec fe) then pure false
  else stdAxiomOkChoiceRestSpec fe cvA

/-- `reduceElemOk`'s `Bool` arm. -/
def reduceElemOkBoolSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← boolName) with
  | some (.indInfo cvB _) => cvB.matchesPin (← boolCvA)
  | _ => pure false

/-- `ofReduceAxOk`'s tail past the operation it names. -/
def ofReduceAxOkRestSpec (fe : IFEnv) (cvA : IConstantVal) (c : NIdx) :
    AM Bool := do
  if !(← eqBasisPinnedSpec fe) then pure false
  else if !(← reduceElemOk fe c) then pure false
  else if !(← reduceStoredOk fe c) then pure false
  else cvA.matchesPin (← ofReducePinA cvA.name)

/-! ### The ground-term guards

`reducePinGuard` and `divModPinGuard` are the same four tests at two different
pins, and the Rust factors them. -/

/-- The three tests past the loose-bound-variable one. -/
def groundGuardsRestSpec (fe : IFEnv) (p : EIdx) : AM Bool := do
  if ← hasFvarFast coreWalkFuel p then pure false
  else if !(← allLevelParamsDefined [] p) then pure false
  else constsResolveFFast fe p

/-- The four tests: closed, free-variable-free, no undeclared universe
parameter, and every constant resolves. -/
def groundGuardsSpec (fe : IFEnv) (p : EIdx) : AM Bool := do
  if !(← looseBVarsBoundedFast coreWalkFuel 0 p) then pure false
  else groundGuardsRestSpec fe p

/-! ### The reduce-operation install pin, in three -/

/-- `checkReducePin`'s identity certificate `value x ≡ x`. -/
def checkReduceIdentitySpec (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (valA : EIdx) : AM Unit := do
  let x ← reduceCertVar c
  let ax ← internE (.app valA x)
  let ok ← isDefEqCore mode fe checkFuel 1 ax x
  if ok then pure ()
  else fail (.internal
    "pinned compiler-trust opaque is not the identity")

/-- `checkReducePin`'s value half: the witness against the build-time pin, and
then the identity certificate. -/
def checkReducePinValueSpec (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (value : EIdx) : AM Unit := do
  let valA ← annotateCore mode fe checkFuel 0 value
  let pinA ← annotateCore mode fe checkFuel 0 (← reduceDeclPin c)
  let okPin ← isDefEqCore mode fe checkFuel 0 valA pinA
  if okPin then checkReduceIdentitySpec mode fe c valA
  else fail (.notImplemented
    "unsupported compiler-trust opaque spelling")

/-- `checkReducePin`'s guard prefix at the pre-insertion view: the element
guard, then the pin's own ground guards (the Rust's `check_reduce_pin_pre`). -/
def checkReducePinPreSpec (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (value : EIdx) : AM Unit := do
  if ← reduceElemOk fe c then
    if ← reducePinGuard fe c then checkReducePinValueSpec mode fe c value
    else fail (.notImplemented
      "unsupported compiler-trust opaque spelling (pin ground constants absent)")
  else fail (.notImplemented
    "unsupported compiler-trust opaque declaration")

/-! ### The three value kinds' tails -/

/-- `checkThmVal`'s tail past the is-a-proposition test. -/
def checkThmValWitnessSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) : AM IFEnv := do
  let jv ← installValue mode fe cv value
  let vtype ← inferTypeCore mode fe checkFuel 0 jv
  unless ← isDefEqCore mode fe checkFuel 0 vtype cv.type do
    fail (.invalid "type mismatch in theorem")
  pure (fe.push (.thmInfo cv value))

/-- `checkThmVal` past its proposition test is `checkThmValWitnessSpec` — the
Rust's `check_thm_val` / `check_thm_val_witness` split. -/
theorem checkThmVal_split (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) :
    checkThmVal mode fe cv value = (do
      let stype ← inferTypeCore mode fe checkFuel 0 cv.type
      let u ← ensureSortCore mode fe checkFuel 0 stype
      let z ← zeroLevel
      if ← liftFueled "level comparison" (← lvlEq? u z) then
        checkThmValWitnessSpec mode fe cv value
      else fail (.invalid "type of theorem is not a proposition")) := by
  unfold checkThmVal checkThmValWitnessSpec
  refine ConRon.Refine2.am_bind_congr _ fun _ => ConRon.Refine2.am_bind_congr _ fun _ =>
    ConRon.Refine2.am_bind_congr _ fun _ => ConRon.Refine2.am_bind_congr _ fun _ =>
    ConRon.Refine2.am_bind_congr _ fun b => ?_
  cases b <;> simp [ConRon.Refine2.am_fail_bind]

/-! ### The `Nat`-operation pin gate's splits -/

/-- `divModCertGuard`'s tail past the substituted proof's own ground guards. -/
def divModCertGuardRestSpec (fe : IFEnv) (c : NIdx) (annVal : EIdx)
    (hyps : List EIdx) (eqE : EIdx) : AM Bool := do
  if !(← constsResolveAll fe (← substConst0List c annVal hyps)) then pure false
  else constsResolveFFast fe (← substConst0 c annVal coreWalkFuel eqE)

/-- One `Bool` constructor stored at the type `Bool` itself. -/
abbrev boolCtorTypedSpec (fe2 : IFEnv) (n : NIdx) : AM Bool := boolCtorTyped fe2 n

/-- `divModEnvGuard`'s tail past the operation's own dependencies: the pinned
`Eq` basis and the two `Bool` constructors stored at the type `Bool`. -/
def divModEnvGuardRestSpec (fe2 : IFEnv) : AM Bool := do
  let en ← pinEq
  if fe2.find? en != some (← eqA) then pure false
  else if !(← boolCtorTypedSpec fe2 (← boolTrueName)) then pure false
  else boolCtorTypedSpec fe2 (← boolFalseName)

/-- `divModEnvGuardRestSpec` with its `Eq` test named, as the Rust's
`div_mod_env_guard_rest` calls `eq_basis_pinned`. -/
theorem divModEnvGuardRestSpec_split (fe2 : IFEnv) :
    divModEnvGuardRestSpec fe2 = (do
      if ← eqBasisPinnedSpec fe2 then
        if ← boolCtorTypedSpec fe2 (← boolTrueName) then
          boolCtorTypedSpec fe2 (← boolFalseName)
        else pure false
      else pure false) := by
  unfold divModEnvGuardRestSpec eqBasisPinnedSpec
  simp only [bind_assoc, pure_bind]
  refine ConRon.Refine2.am_bind_congr _ fun en => ConRon.Refine2.am_bind_congr _ fun ea => ?_
  by_cases h : (fe2.find? en == some ea) = true
  · simp only [h, bne, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    refine ConRon.Refine2.am_bind_congr _ fun t => ConRon.Refine2.am_bind_congr _ fun b => ?_
    cases b <;> rfl
  · simp [h, bne]

/-- `checkDivModCerts`' tail at one certificate, past the applied proof. -/
def checkDivModCertTailSpec (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (annVal : EIdx) (stmts : List (List EIdx × EIdx)) (proofs : List EIdx)
    (appliedA : EIdx) : AM Bool := do
  match stmts, proofs with
  | (_, eqE) :: srest, _ :: prest => do
    let tp ← inferTypeCore mode fe checkFuel 4 appliedA
    let rhs ← substConst0 c annVal coreWalkFuel eqE
    if ← isDefEqCore mode fe checkFuel 4 tp rhs then
      checkDivModCerts mode fe c annVal srest prest
    else pure false
  | _, _ => pure false

/-- `checkDivModPinLoop`'s step at a variant whose two guards passed — the
Rust's `check_div_mod_pin_try`: the `orElseAttempt` seam, then the twin's
`match` on the step (task #97-T2-LOCKSTEP lane Checker: the old statement
named the whole loop, guards included, where the Rust function starts past
them). -/
def checkDivModPinTrySpec (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (value' : EIdx) (ps : INatOpPinSet) (rest : List INatOpPinSet)
    (tried : List String) : AM Unit := do
  match ← orElseAttempt (checkDivModPinAt mode fe c value' ps) with
  | .matched => pure ()
  | .continued =>
    checkDivModPinLoop mode fe c value' rest (tried ++ [divModAttemptReason ps none])
  | .recovered e =>
    checkDivModPinLoop mode fe c value' rest (tried ++ [divModAttemptReason ps (some e)])
  | .failed e => fail e

/-- `checkDivModPinAt`'s certificate half, past the pin comparison. -/
def checkDivModPinCertsSpec (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (value' : EIdx) (ps : INatOpPinSet) : AM Bool := do
  checkDivModCerts mode fe c value' (← divModCertStmts c)
    (← divModCertProofs ps c)

/-- `divModCertApplied`'s hypothesis application, at a base already built. -/
def divModCertAppliedHypsSpec (base : EIdx) : List EIdx → AM EIdx
  | [h1] => do
    let f2 ← internE (.fvar 2 h1)
    internE (.app base f2)
  | [h1, h2] => do
    let f2 ← internE (.fvar 2 h1)
    let a1 ← internE (.app base f2)
    let f3 ← internE (.fvar 3 h2)
    internE (.app a1 f3)
  | _ => pure base

/-- The operation's slot in the pin record's eight-slot family.  The twin
spells the dispatch as a chain of handle comparisons inside `divModDeclPin`
and `divModCertProofs`; the port computes the index once. -/
def divModSlot2Spec (c : NIdx) : AM Nat := do
  if c == (← natXorName) then pure 4
  else if c == (← natShiftLeftName) then pure 5
  else if c == (← natShiftRightName) then pure 6
  else pure 7

/-- … past `Nat.div` (the Rust's `div_mod_slot_1`: `gcd`, `land`, `lor`). -/
def divModSlot1Spec (c : NIdx) : AM Nat := do
  if c == (← natGcdName) then pure 1
  else if c == (← natLandName) then pure 2
  else if c == (← natLorName) then pure 3
  else divModSlot2Spec c

/-- … from the top. -/
def divModSlotSpec (c : NIdx) : AM Nat := do
  if c == (← natDivName) then pure 0
  else divModSlot1Spec c

/-! ### `divModCertStmts`' context and its seven arms

`CertCtxA` is the twin-side reading of `arena::decl_check::CertCtx` — the
twenty-one handles the twin holds in `let`s and the port bundles in a record,
because a `let`-bound handle that outlives a `match` arm is a loan the Aeneas
subset will not take. -/

/-- The twenty-one pinned handles `divModCertStmts` opens with. -/
structure CertCtxA where
  natTy : EIdx
  x : EIdx
  y : EIdx
  one : EIdx
  bleN : NIdx
  boolTy : EIdx
  bT : EIdx
  bF : EIdx
  z : EIdx
  two : EIdx
  modN : NIdx
  divN : NIdx
  addN : NIdx
  mulN : NIdx
  subN : NIdx
  gcdN : NIdx
  slN : NIdx
  srN : NIdx
  landN : NIdx
  lorN : NIdx
  xorN : NIdx

/-- `divModCertStmts`' opening `let`s, through the `Bool` type and its two
constructors. -/
def certCtxBoolSpec : AM (EIdx × EIdx × EIdx) := do
  let bn ← boolName
  let boolTy ← constE bn
  let bT ← constE (← boolTrueName)
  let bF ← constE (← boolFalseName)
  pure (boolTy, bT, bF)

/-- … through the numerals `0` and `2`. -/
def certCtxNumsSpec (one : EIdx) : AM (EIdx × EIdx) := do
  let z ← constE (← pinNatZero)
  let two ← natAp1 (← pinNatSucc) one
  pure (z, two)

/-- … and the eleven arithmetic and bitwise names. -/
def certCtxNamesSpec : AM (NIdx × NIdx × NIdx × NIdx × NIdx × NIdx × NIdx ×
    NIdx × NIdx × NIdx × NIdx) := do
  pure (← natModName, ← natDivName, ← natAddName, ← natMulName, ← natSubName,
    ← natGcdName, ← natShiftLeftName, ← natShiftRightName, ← natLandName,
    ← natLorName, ← natXorName)

/-- **The whole context.** -/
def certCtxSpec : AM CertCtxA := do
  let nt ← pinNat
  let natTy ← constE nt
  let x ← natVar 0
  let y ← natVar 1
  let one ← natOne
  let bleN ← natBleName
  let (boolTy, bT, bF) ← certCtxBoolSpec
  let (z, two) ← certCtxNumsSpec one
  let (modN, divN, addN, mulN, subN, gcdN, slN, srN, landN, lorN, xorN) ←
    certCtxNamesSpec
  pure ⟨natTy, x, y, one, bleN, boolTy, bT, bF, z, two, modN, divN, addN, mulN,
    subN, gcdN, slN, srN, landN, lorN, xorN⟩

/-- The guard shape all seven branches are written with. -/
def certGuardSpec (cx : CertCtxA) (a b r : EIdx) : AM EIdx := do
  eqAt1 cx.boolTy (← natAp2 cx.bleN a b) r

/-- The characteristic equation all seven branches are written with. -/
def certEqSpec (cx : CertCtxA) (c : NIdx) (rhs : EIdx) : AM EIdx := do
  eqAt1 cx.natTy (← natAp2 c cx.x cx.y) rhs

/-- The bitwise branches' `op2 (x/2) (y/2)`. -/
def certHalvesSpec (cx : CertCtxA) (c : NIdx) : AM EIdx := do
  let hx ← natAp2 cx.divN cx.x cx.two
  let hy ← natAp2 cx.divN cx.y cx.two
  natAp2 c hx hy

/-- The six one-hypothesis branches' shared shape. -/
def certTwoEqsSpec (cx : CertCtxA) (c : NIdx) (h1 h2 r1 r2 : EIdx) :
    AM (List (List EIdx × EIdx)) := do
  let e1 ← certEqSpec cx c r1
  let e2 ← certEqSpec cx c r2
  pure [([h1], e1), ([h2], e2)]

/-- `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`. -/
def certGcdSpec (cx : CertCtxA) (c : NIdx) : AM (List (List EIdx × EIdx)) := do
  let h1 ← certGuardSpec cx cx.one cx.x cx.bT
  let h2 ← certGuardSpec cx cx.one cx.x cx.bF
  let r1 ← natAp2 c (← natAp2 cx.modN cx.y cx.x) cx.x
  certTwoEqsSpec cx c h1 h2 r1 cx.y

/-- `<<<`: `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`. -/
def certShiftLeftSpec (cx : CertCtxA) (c : NIdx) :
    AM (List (List EIdx × EIdx)) := do
  let h1 ← certGuardSpec cx cx.one cx.y cx.bT
  let h2 ← certGuardSpec cx cx.one cx.y cx.bF
  let r1 ← natAp2 c (← natAp2 cx.mulN cx.two cx.x)
    (← natAp2 cx.subN cx.y cx.one)
  certTwoEqsSpec cx c h1 h2 r1 cx.x

/-- `>>>`: `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`. -/
def certShiftRightSpec (cx : CertCtxA) (c : NIdx) :
    AM (List (List EIdx × EIdx)) := do
  let h1 ← certGuardSpec cx cx.one cx.y cx.bT
  let h2 ← certGuardSpec cx cx.one cx.y cx.bF
  let r1 ← natAp2 cx.divN (← natAp2 c cx.x (← natAp2 cx.subN cx.y cx.one)) cx.two
  certTwoEqsSpec cx c h1 h2 r1 cx.x

/-- `&&&`: `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`. -/
def certLandSpec (cx : CertCtxA) (c : NIdx) : AM (List (List EIdx × EIdx)) := do
  let h1 ← certGuardSpec cx cx.one cx.x cx.bT
  let h2 ← certGuardSpec cx cx.one cx.x cx.bF
  let rec1 ← certHalvesSpec cx c
  let r1 ← natAp2 cx.addN (← natAp2 cx.mulN cx.two rec1)
    (← natAp2 cx.mulN (← natAp2 cx.modN cx.x cx.two)
      (← natAp2 cx.modN cx.y cx.two))
  certTwoEqsSpec cx c h1 h2 r1 cx.z

/-- `|||`'s right-hand side. -/
def certLorRhsSpec (cx : CertCtxA) (c : NIdx) : AM EIdx := do
  let rec1 ← certHalvesSpec cx c
  let t2 ← natAp2 cx.mulN cx.two rec1
  let mx ← natAp2 cx.modN cx.x cx.two
  let my ← natAp2 cx.modN cx.y cx.two
  natAp2 cx.addN t2 (← natAp2 cx.subN (← natAp2 cx.addN mx my)
    (← natAp2 cx.mulN mx my))

/-- `|||`: `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`. -/
def certLorSpec (cx : CertCtxA) (c : NIdx) : AM (List (List EIdx × EIdx)) := do
  let h1 ← certGuardSpec cx cx.one cx.x cx.bT
  let h2 ← certGuardSpec cx cx.one cx.x cx.bF
  let r1 ← certLorRhsSpec cx c
  certTwoEqsSpec cx c h1 h2 r1 cx.y

/-- `^^^`'s right-hand side. -/
def certXorRhsSpec (cx : CertCtxA) (c : NIdx) : AM EIdx := do
  let rec1 ← certHalvesSpec cx c
  let t2 ← natAp2 cx.mulN cx.two rec1
  let mx ← natAp2 cx.modN cx.x cx.two
  let my ← natAp2 cx.modN cx.y cx.two
  natAp2 cx.addN t2 (← natAp2 cx.modN (← natAp2 cx.addN mx my) cx.two)

/-- `^^^`: `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`. -/
def certXorSpec (cx : CertCtxA) (c : NIdx) : AM (List (List EIdx × EIdx)) := do
  let h1 ← certGuardSpec cx cx.one cx.x cx.bT
  let h2 ← certGuardSpec cx cx.one cx.x cx.bF
  let r1 ← certXorRhsSpec cx c
  certTwoEqsSpec cx c h1 h2 r1 cx.y

/-- The `div`/`mod` branch's `c (x - y) y`. -/
def certRecRhsSpec (cx : CertCtxA) (c : NIdx) : AM EIdx := do
  let d ← natAp2 cx.subN cx.x cx.y
  natAp2 c d cx.y

/-- The `div`/`mod` branch's three certificates, at the four guards. -/
def certDivModEqsSpec (cx : CertCtxA) (c : NIdx)
    (h1 h2 h3 h4 recRhs baseRhs : EIdx) : AM (List (List EIdx × EIdx)) := do
  let e1 ← certEqSpec cx c recRhs
  let e2 ← certEqSpec cx c baseRhs
  pure [([h1, h2], e1), ([h3], e2), ([h4], e2)]

/-- The `div`/`mod` branch's four guards. -/
def certDivModGuardsSpec (cx : CertCtxA) (c : NIdx) (recRhs baseRhs : EIdx) :
    AM (List (List EIdx × EIdx)) := do
  let h1 ← certGuardSpec cx cx.y cx.x cx.bT
  let h2 ← certGuardSpec cx cx.one cx.y cx.bT
  let h3 ← certGuardSpec cx cx.y cx.x cx.bF
  let h4 ← certGuardSpec cx cx.one cx.y cx.bF
  certDivModEqsSpec cx c h1 h2 h3 h4 recRhs baseRhs

/-- The `div`/`mod` branch, whole. -/
def certDivModSpec (cx : CertCtxA) (c : NIdx) : AM (List (List EIdx × EIdx)) := do
  let recRhs ←
    if c == cx.divN then natAp1 (← pinNatSucc) (← certRecRhsSpec cx c)
    else certRecRhsSpec cx c
  let baseRhs := if c == cx.divN then cx.z else cx.x
  certDivModGuardsSpec cx c recRhs baseRhs

/-- The seven-way dispatch over the operation name. -/
def divModCertStmtsAtSpec (cx : CertCtxA) (c : NIdx) :
    AM (List (List EIdx × EIdx)) := do
  if c == cx.gcdN then certGcdSpec cx c
  else if c == cx.slN then certShiftLeftSpec cx c
  else if c == cx.srN then certShiftRightSpec cx c
  else if c == cx.landN then certLandSpec cx c
  else if c == cx.lorN then certLorSpec cx c
  else if c == cx.xorN then certXorSpec cx c
  else certDivModSpec cx c

/-- `divModCertStmts` is its context and its dispatch.

**The tier's one open `_unfold`, and it is a COST problem.**  The two sides
are the same `do` block regrouped — twenty-one `let`s and a seven-way
dispatch — but the single `twin_reduce` that spells out all fifteen
`cert*Spec` definitions does not finish inside ten minutes on the resulting
term.  The fix is to peel the twenty-one binders with `am_bind_congr` and
`split` the dispatch, rather than to hand `simp` the whole thing at once;
task #97-P5-Checker-2 left it rather than spend the round's last hour on
it. -/
theorem divModCertStmts_unfold (c : NIdx) :
    divModCertStmts c = (do divModCertStmtsAtSpec (← certCtxSpec) c) := by
  sorry


/-! ### The context's four partial builders

Each Rust split returns the WHOLE record, so each twin subject is
`certCtxSpec`'s tail with the fields already computed supplied. -/

/-- `cert_ctx_names_rest`'s subject. -/
def certCtxNamesRestFullSpec (natTy x y one : EIdx) (bleN : NIdx)
    (boolTy bT bF z two : EIdx) (modN divN addN mulN subN gcdN : NIdx) :
    AM CertCtxA := do
  let slN ← natShiftLeftName
  let srN ← natShiftRightName
  let landN ← natLandName
  let lorN ← natLorName
  let xorN ← natXorName
  pure ⟨natTy, x, y, one, bleN, boolTy, bT, bF, z, two, modN, divN, addN, mulN,
    subN, gcdN, slN, srN, landN, lorN, xorN⟩

/-- `cert_ctx_names`' subject. -/
def certCtxNamesFullSpec (natTy x y one : EIdx) (bleN : NIdx)
    (boolTy bT bF z two : EIdx) : AM CertCtxA := do
  let modN ← natModName
  let divN ← natDivName
  let addN ← natAddName
  let mulN ← natMulName
  let subN ← natSubName
  let gcdN ← natGcdName
  certCtxNamesRestFullSpec natTy x y one bleN boolTy bT bF z two modN divN addN
    mulN subN gcdN

/-- `cert_ctx_nums`' subject. -/
def certCtxNumsFullSpec (natTy x y one : EIdx) (bleN : NIdx)
    (boolTy bT bF : EIdx) : AM CertCtxA := do
  let (z, two) ← certCtxNumsSpec one
  certCtxNamesFullSpec natTy x y one bleN boolTy bT bF z two

/-- `cert_ctx_bool`'s subject. -/
def certCtxBoolFullSpec (natTy x y one : EIdx) : AM CertCtxA := do
  let bleN ← natBleName
  let (boolTy, bT, bF) ← certCtxBoolSpec
  certCtxNumsFullSpec natTy x y one bleN boolTy bT bF

/-- `cert_ctx`'s subject, and `certCtxSpec` spelled through the four. -/
def certCtxFullSpec : AM CertCtxA := do
  let nt ← pinNat
  let natTy ← constE nt
  let x ← natVar 0
  let y ← natVar 1
  let one ← natOne
  certCtxBoolFullSpec natTy x y one


/-! ## `arena::checker`'s splits

`checkDecl`'s seven arms are twenty Rust functions, for extraction rule 5's
reason at every one: an arm that computes `fe2` and then runs a pin gate holds
two environments and a handle across a `match`. -/

/-- `checkDecl`'s `.quotDecl` arm. -/
def checkQuotDeclSpec (fe : IFEnv) (k : QuotKind) (cv : IConstantVal) :
    AM IFEnv := do
  if ← quotPinHit k cv then
    match k with
    | .type => checkBasisDecl fe .quotK
    | _ => pure fe
  else fail (.notImplemented (match k with
    | .sound => "quotient soundness axiom mismatch"
    | _ => "quotient declaration mismatch"))

/-- `checkDecl`'s `.indDecl` arm: **the pinned basis blocks** recognised
first — a stream's `Nat` block arrives as an ordinary `indDecl` — then the
inductive routes. -/
def checkIndDeclArmSpec (mode : CheckMode) (fe : IFEnv)
    (block : List IConstantInfo) (nP : Nat) : AM IFEnv := do
  match ← basisPinHit block with
  | some kind => checkBasisDecl fe kind
  | none => Inductives.checkIndDecl mode fe block nP

/-- `checkDecl`'s axiom arm past the `ofReduce*` test: the two standard
axioms' shape mismatch, `sorryAx` tolerated as a DECLARATION, everything else
declined. -/
def checkAxiomDeclRestSpec (fe : IFEnv) (cvA : IConstantVal) : AM IFEnv := do
  if cvA.name == (← propextName) || cvA.name == (← choiceName) then
    fail (.notImplemented
      "standard axiom shape mismatch")
  else if cvA.name == (← pinSorryAx) then pure fe
  else fail (.notImplemented "non-standard axiom")

/-- `checkDecl`'s axiom arm at the `ofReduce*` names. -/
def checkAxiomDeclOfReduceSpec (fe : IFEnv) (cvA : IConstantVal) : AM IFEnv := do
  if cvA.name == (← ofReduceNatName) || cvA.name == (← ofReduceBoolName) then
    if ← ofReduceAxOk fe cvA then pure (fe.push (.axiomInfo cvA))
    else fail (.notImplemented
      "unsupported compiler-trust axiom environment")
  else checkAxiomDeclRestSpec fe cvA

/-- `checkDecl`'s axiom arm at `Lean.trustCompiler`. -/
def checkAxiomDeclTrustSpec (fe : IFEnv) (cvA : IConstantVal) : AM IFEnv := do
  if cvA.name == (← trustCompilerName) then
    if ← trustCompilerOk fe cvA then pure (fe.push (.axiomInfo cvA))
    else fail (.notImplemented
      "unsupported Lean.trustCompiler shape")
  else checkAxiomDeclOfReduceSpec fe cvA

/-- `checkDecl`'s axiom arm past `Quot.sound`: the common constant check, then
the standard-axiom gate. -/
def checkAxiomDeclStdSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    AM IFEnv := do
  let cvA ← checkConstantVal mode fe cv
  if ← stdAxiomOk fe cvA then pure (fe.push (.axiomInfo cvA))
  else checkAxiomDeclTrustSpec fe cvA

/-- `checkDecl`'s `Quot.sound` record: compared with the pin, installing
NOTHING of its own. -/
def checkQuotSoundRecordSpec (fe : IFEnv) (cv : IConstantVal) : AM IFEnv := do
  let blk ← BasisKind.decls .quotK
  match blk[4]? with
  | some pinned =>
    if ← IConstantInfo.canonEq (.axiomInfo cv) pinned then pure fe
    else fail (.notImplemented "quotient soundness axiom mismatch")
  | none => fail (.notImplemented "quotient soundness axiom mismatch")

/-- `checkDecl`'s `.axiomDecl` arm, whole. -/
def checkAxiomDeclSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    AM IFEnv := do
  if cv.name == (← pinQuotSound) then checkQuotSoundRecordSpec fe cv
  else checkAxiomDeclStdSpec mode fe cv

/-- `checkDecl`'s `.opaqueDecl` arm. -/
def checkOpaqueDeclSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) : AM IFEnv := do
  let cv ← checkConstantVal mode fe cv
  let fe2 ← checkOpaqueVal mode fe cv value
  if (← reduceOpNames).contains cv.name then
    checkReducePin mode (fe2.restrictTo fe.visibleBelow) fe2 cv.name value
  pure fe2

/-- The structural-`Nat` pins' certification, at the equations already built. -/
def checkStructuralNatPinCertifySpec (mode : CheckMode) (fe fe2 : IFEnv)
    (seqs : List (EIdx × EIdx)) : AM IFEnv := do
  let ok ← certifyNatEqs mode fe seqs
  unless ok do
    fail (.notImplemented "nonstandard structural Nat operation")
  pure fe2

/-- … with the equations built from the stored value. -/
def checkStructuralNatPinEqsSpec (mode : CheckMode) (fe fe2 : IFEnv) (n : NIdx) :
    AM IFEnv := do
  match fe2.find? n with
  | some (.defnInfo _ value' _) => do
    let eqs ← natOpEquations 0 n
    checkStructuralNatPinCertifySpec mode fe fe2 (← substConst0Pairs n value' eqs)
  | _ => fail (.internal "structural Nat operation not stored")

/-- … behind the environment guard: the fast-path ops must be the standard
structural recursions. -/
def checkStructuralNatPinSpec (mode : CheckMode) (fe fe2 : IFEnv) (n : NIdx) :
    AM IFEnv := do
  let g ← natOpGuard fe2 n
  let deps ← natOpDeps n
  unless g && (← natOpStoredOkAll fe2 deps) do
    fail (.notImplemented
      "nonstandard structural Nat operation environment")
  checkStructuralNatPinEqsSpec mode fe fe2 n

/-- The `Nat.div`/`Nat.mod` gate at a definition. -/
def checkDefnDivModPinSpec (mode : CheckMode) (pins : List INatOpPinSet)
    (fe fe2 : IFEnv) (n : NIdx) : AM IFEnv := do
  if (← natDivModNames).contains n then
    checkDivModPin mode pins fe fe2 n
  pure fe2

/-- Both pin gates, in the twin's order. -/
def checkDefnPinsSpec (mode : CheckMode) (pins : List INatOpPinSet)
    (fe fe2 : IFEnv) (n : NIdx) : AM IFEnv := do
  if (← natOpNames).contains n then
    let _ ← checkStructuralNatPinSpec mode fe fe2 n
    checkDefnDivModPinSpec mode pins fe fe2 n
  else checkDefnDivModPinSpec mode pins fe fe2 n

/-- `checkDecl`'s `.defnDecl` arm, whole. -/
def checkDefnDeclSpec (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (cv : IConstantVal) (value : EIdx) (hint : ReducibilityHint) : AM IFEnv := do
  let cv ← checkConstantVal mode fe cv
  let fe2 ← checkDefnVal mode fe cv value hint
  checkDefnPinsSpec mode pins (fe2.restrictTo fe.visibleBelow) fe2 cv.name

/-! ### Phase A's step body, in six -/

/-- `annotStepGo`'s `.opaqueDecl` install half. -/
def annotStepOpaqueInstallSpec (mode : CheckMode) (fe : IFEnv)
    (cv : IConstantVal) (value : EIdx) : AM (IFEnv × Option ValueGroup) := do
  let cvA ← installConstantVal mode fe cv
  let jv ← installValue mode fe cvA value
  pure (fe.push (.axiomInfo cvA), some ⟨.opaque, cvA, jv⟩)

/-- `annotStepGo`'s `.opaqueDecl` arm. -/
def annotStepOpaqueSpec (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (pd : IDeclaration) (cv : IConstantVal) (value : EIdx) :
    AM (IFEnv × Option ValueGroup) := do
  if (← reduceOpNames).contains cv.name then
    pure (← checkDecl mode pins fe pd, none)
  else annotStepOpaqueInstallSpec mode fe cv value

/-- `annotStepGo`'s `.thmDecl` arm: a theorem installs BY STATEMENT. -/
def annotStepThmSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) : AM (IFEnv × Option ValueGroup) := do
  let cvA ← installConstantVal mode fe cv
  pure (fe.push (.thmInfo cvA value), some ⟨.thm, cvA, value⟩)

/-- `annotStepGo`'s `.defnDecl` install half. -/
def annotStepDefnInstallSpec (mode : CheckMode) (fe : IFEnv)
    (cv : IConstantVal) (value : EIdx) (hint : ReducibilityHint) :
    AM (IFEnv × Option ValueGroup) := do
  let cvA ← installConstantVal mode fe cv
  let jv ← installValue mode fe cvA value
  pure (fe.push (.defnInfo cvA jv hint), some ⟨.defn, cvA, jv⟩)

/-- `annotStepGo`'s `.defnDecl` arm. -/
def annotStepDefnSpec (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (pd : IDeclaration) (cv : IConstantVal) (value : EIdx)
    (hint : ReducibilityHint) : AM (IFEnv × Option ValueGroup) := do
  if (← natOpNames).contains cv.name || (← natDivModNames).contains cv.name then
    pure (← checkDecl mode pins fe pd, none)
  else annotStepDefnInstallSpec mode fe cv value hint

/-! ### The startup walk, in six

**Restated by task #97-P5-Top: the old six were chained to the wrong
continuations.**  They were written as one continuation-passing chain —
`internAllReducePinsSpec` ran `internAllNamesSpec`, `internAllBasisSpec []`
ran `internAllAxiomPinsSpec`, and `internAllAxiomPinsRestSpec` started at
`nonemptyA` — so that `internAllBasisSpec` of the six kinds WAS the whole walk
minus the pin sets.  The Rust functions do not nest that way:
`intern_all_basis` stops at the end of its cursor, `intern_all_axiom_pins`
runs `iff`, `iff.intro`, `iff.rec`, `Nonempty` and then `_rest`,
`intern_all_reduce_pins` stops after the two declaration pins, and
`intern_all_pins` calls the basis walk, the axiom pins, the names and the pin
sets in sequence.  Five of the six statements were therefore false (every one
but `internAllNamesSpec`'s: its twin interned MORE than the port).

**And they intern the RAW pins, as the Rust does.**
`arena::std_axioms` interns `iff_raw` … `choice_raw` and `arena::trust_axioms`
`of_reduce_pin_a` = the RAW `ofReduceRaw` (both modules' notes: `matchesPin`
erases the `pw` datum, which is all annotation writes).  Task #97-P5-Top found
the twin's `internAllPins` interning the ANNOTATED `iffA` … `choiceA`,
`ofReduceNatA`, `ofReduceBoolA` — six of them different values, so `StoreRel`,
which is exact, failed.  Round 2 took ruling (a): the twin interns the raw
pins too (`Arena/Checker.lean`'s `internAllPins`, `Arena/DeclCheck.lean`'s
`stdAxiomOk`, and `Arena/TrustAxioms.lean`'s `ofReduceNatA`/`ofReduceBoolA`,
whose slots now hold the raw pins), Theorem 1 carrying the `matchesPin`
equalities (`Bridge/Checker/Basis.lean`).  So `internAllPinsPortSpec` below
IS `internAllPins`, up to the monad laws (`internAllPinsPortSpec_eq`,
`Checker/Top.lean`), and the check-time transcriptions above compare against
the raw pins as well. -/

/-- `internAllPins`' reserved-name half — `intern_all_names`. -/
def internAllNamesSpec : AM Unit := do
  let _ ← reservedBasisNames
  let _ ← natOpNames; let _ ← natDivModNames; let _ ← reduceOpNames
  let _ ← pinSorryAx; let _ ← pinQuotSound

/-- `intern_all_reduce_pins`: the four `reduce*`/`ofReduce*` shapes (raw) and
the two pinned defining expressions. -/
def internAllReducePinsSpec : AM Unit := do
  let _ ← reduceNatCvA; let _ ← reduceBoolCvA
  let _ ← ofReduceNatA; let _ ← ofReduceBoolA
  let _ ← reduceNatDeclPin; let _ ← reduceBoolDeclPin

/-- `intern_all_trust_pins`: the compiler-trust shapes, then the reduce pins. -/
def internAllTrustPinsSpec : AM Unit := do
  let _ ← trueCvA; let _ ← trueIntroCvA; let _ ← trustCompilerA; let _ ← boolCvA
  internAllReducePinsSpec

/-- `intern_all_axiom_pins_rest`: the standard axiom pins past `Nonempty`
(raw), then the trust pins. -/
def internAllAxiomPinsRestSpec : AM Unit := do
  let _ ← nonemptyIntroRaw; let _ ← nonemptyRecRaw
  let _ ← propextRaw; let _ ← choiceRaw
  internAllTrustPinsSpec

/-- `intern_all_axiom_pins`: the `Iff` family and `Nonempty` (raw), then the
rest. -/
def internAllAxiomPinsSpec : AM Unit := do
  let _ ← iffRaw; let _ ← iffIntroRaw; let _ ← iffRecRaw; let _ ← nonemptyRaw
  internAllAxiomPinsRestSpec

/-- `intern_all_basis` from the cursor on: the basis blocks in BOTH forms. -/
def internAllBasisSpec : List BasisKind → AM Unit
  | [] => pure ()
  | k :: ks => do
    let _ ← BasisKind.decls k
    let _ ← BasisKind.declsA k
    internAllBasisSpec ks

/-- **The port's startup walk**, as a twin action: `intern_all_pins`' four
calls in order — `internAllPins` itself, re-bracketed
(`internAllPinsPortSpec_eq`, `Checker/Top.lean`). -/
def internAllPinsPortSpec (pins : List NatOpPinSet) : AM (List INatOpPinSet) := do
  internAllBasisSpec [.eqK, .natK, .punitK, .emptyK, .falseK, .quotK]
  internAllAxiomPinsSpec
  internAllNamesSpec
  internPinSets pins

/-! ## `checkDecl`, arm by arm (task #97-P5-Checker round 4)

Task #97-P5-Checker round 3 §10 item 2 named `checkDecl_unfold` as the one
thing between `check_decl_refines` and a seven-way `cases`: the twin writes
the seven arms inline and the tier's statements are against the
transcriptions above.  **Six of the seven are equations and are closed here.
The seventh was not an equation** while the twin's `.defnDecl` arm read the
constant's name back (`readName`, which throws `internal` at a dangling
handle) for its decline messages.  Task #97-T2-LOCKSTEP lane Checker gave the
twin the Rust's constant messages, and `checkDecl_defnDecl` below closes the
seventh too.-/

theorem checkDecl_axiomDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) :
    checkDecl mode pins fe (.axiomDecl cv) = checkAxiomDeclSpec mode fe cv := by
  -- the transcription reads `cvA.name` where the twin reads `cv.name` in its
  -- decline messages; `checkConstantVal` answers `{ cv with type := _ }`, so
  -- exposing that `pure` makes the two the same projection.  The `Quot.sound`
  -- arm matches on `blk[4]?` at two different matchers, so it is peeled first.
  simp only [checkDecl, checkAxiomDeclSpec]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro q
  by_cases hq : (cv.name == q) = true
  · simp only [hq, ↓reduceIte, checkQuotSoundRecordSpec]
    refine ConRon.Refine2.am_bind_congr _ ?_
    intro blk
    cases blk[4]? <;> rfl
  · simp only [hq, ↓reduceIte, Bool.false_eq_true]
    twin_reduce [checkAxiomDeclStdSpec, checkAxiomDeclTrustSpec,
      checkAxiomDeclOfReduceSpec, checkAxiomDeclRestSpec, checkConstantVal_unfold,
      checkConstantValAfterAnnotSpec, installConstantValTailSpec]

/-- The stored definition's value — the twin's `match fe2.find? c with |
some (.defnInfo _ v _)`, under the name the Rust gives it (`defn_value`). -/
def defnValueOf (fe : IFEnv) (c : NIdx) : Option EIdx :=
  match fe.find? c with
  | some (.defnInfo _ v _) => some v
  | _ => none

/-- `checkDivModPin` with its stored-value lookup named `defnValueOf`, as the
Rust's `check_div_mod_pin` calls `defn_value`. -/
theorem checkDivModPin_split (mode : CheckMode) (pins : List INatOpPinSet)
    (fe fe2 : IFEnv) (c : NIdx) :
    checkDivModPin mode pins fe fe2 c = (do
      if ← divModEnvGuard fe2 c then
        match defnValueOf fe2 c with
        | some v => checkDivModPinLoop mode fe c v pins []
        | none => fail (.internal "Nat.div/mod operation not stored")
      else fail (.notImplemented "unsupported Nat.div/mod environment")) := by
  unfold checkDivModPin defnValueOf
  refine ConRon.Refine2.am_bind_congr _ fun g => ?_
  split
  · cases fe2.find? c with
    | none => rfl
    | some ci => cases ci <;> rfl
  · rfl

/-- `checkStructuralNatPinEqsSpec` with its stored-value lookup named
`defnValueOf`, as the Rust's `check_structural_nat_pin_eqs` calls
`defn_value`. -/
theorem checkStructuralNatPinEqsSpec_split (mode : CheckMode) (fe fe2 : IFEnv)
    (n : NIdx) :
    checkStructuralNatPinEqsSpec mode fe fe2 n =
      match defnValueOf fe2 n with
      | some v => (do
          let eqs ← natOpEquations 0 n
          checkStructuralNatPinCertifySpec mode fe fe2 (← substConst0Pairs n v eqs))
      | none => fail (.internal "structural Nat operation not stored") := by
  unfold checkStructuralNatPinEqsSpec defnValueOf
  cases fe2.find? n with
  | none => rfl
  | some ci => cases ci <;> rfl

/-- `checkReducePin` is the stored guard at the post-insertion index, then
`checkReducePinPreSpec` at the pre-insertion one — the Rust's
`check_reduce_pin` / `check_reduce_pin_pre` split (task #97-T2-LOCKSTEP lane
Checker round 2). -/
theorem checkReducePin_split (mode : CheckMode) (fe fe2 : IFEnv) (c : NIdx)
    (value : EIdx) :
    checkReducePin mode fe fe2 c value = (do
      if ← reduceStoredOk fe2 c then checkReducePinPreSpec mode fe c value
      else fail (.notImplemented "unsupported compiler-trust opaque declaration")) := by
  rfl

/-- **The seventh arm is an equation too** (task #97-T2-LOCKSTEP lane
Checker): the twin's `.defnDecl` declines carry the Rust's constant messages
now, with no `readName`, so the arm IS its transcription. -/
theorem checkDecl_defnDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) (value : EIdx) (hint : ReducibilityHint) :
    checkDecl mode pins fe (.defnDecl cv value hint) =
      checkDefnDeclSpec mode pins fe cv value hint := by
  twin_reduce [checkDecl, checkDefnDeclSpec, checkDefnPinsSpec,
    checkDefnDivModPinSpec, checkStructuralNatPinSpec, checkStructuralNatPinEqsSpec,
    checkStructuralNatPinCertifySpec]
  refine congrArg _ (funext fun cvA => congrArg _ (funext fun fe2 =>
    congrArg _ (funext fun ns => ?_)))
  split
  · refine congrArg _ (funext fun deps => congrArg _ (funext fun a =>
      congrArg _ (funext fun b => ?_)))
    split
    · cases fe2.find? cvA.name with
      | none => simp only [ConRon.Refine2.am_fail_bind]
      | some ci =>
        cases ci <;> simp only [ConRon.Refine2.am_fail_bind, bind_assoc]
        refine congrArg _ (funext fun eqs => congrArg _ (funext fun q =>
          congrArg _ (funext fun ok => ?_)))
        split <;> simp only [pure_bind, ConRon.Refine2.am_fail_bind]
    · rfl
  · rfl

theorem checkDecl_thmDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) (value : EIdx) :
    checkDecl mode pins fe (.thmDecl cv value) = (do
      let cvA ← checkConstantVal mode fe cv
      checkThmVal mode fe cvA value) := by
  twin_reduce [checkDecl]

theorem checkDecl_opaqueDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) (value : EIdx) :
    checkDecl mode pins fe (.opaqueDecl cv value)
      = checkOpaqueDeclSpec mode fe cv value := by
  twin_reduce [checkDecl, checkOpaqueDeclSpec]

theorem checkDecl_basisDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (kind : BasisKind) :
    checkDecl mode pins fe (.basisDecl kind) = checkBasisDecl fe kind := by
  twin_reduce [checkDecl]

theorem checkDecl_indDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (block : List IConstantInfo) (nP : Nat) :
    checkDecl mode pins fe (.indDecl block nP)
      = checkIndDeclArmSpec mode fe block nP := by
  rw [checkDecl, checkIndDeclArmSpec]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro v
  cases v <;> rfl

theorem checkDecl_quotDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (k : QuotKind) (cv : IConstantVal) :
    checkDecl mode pins fe (.quotDecl k cv) = checkQuotDeclSpec fe k cv := by
  unfold checkDecl checkQuotDeclSpec
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro b
  cases b <;> cases k <;> rfl

/-! ## `annotStepGo`, arm by arm (task #97-P5-Top)

The twin writes phase A's step body as one `match` with its three value arms
inline; the port splits each into a function, and the tier states them
against the `annotStep*Spec` transcriptions above.  These four equations are
what makes `annot_step_go_refines` a dispatch. -/

theorem annotStepGo_defnDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) (value : EIdx) (hint : ReducibilityHint) :
    annotStepGo mode pins fe (.defnDecl cv value hint)
      = annotStepDefnSpec mode pins fe (.defnDecl cv value hint) cv value hint := by
  simp only [annotStepGo, annotStepDefnSpec, annotStepDefnInstallSpec]

theorem annotStepGo_thmDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) (value : EIdx) :
    annotStepGo mode pins fe (.thmDecl cv value) = annotStepThmSpec mode fe cv value := by
  simp only [annotStepGo, annotStepThmSpec]

theorem annotStepGo_opaqueDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) (value : EIdx) :
    annotStepGo mode pins fe (.opaqueDecl cv value)
      = annotStepOpaqueSpec mode pins fe (.opaqueDecl cv value) cv value := by
  simp only [annotStepGo, annotStepOpaqueSpec, annotStepOpaqueInstallSpec]

/-- The catch-all: every kind but the three value kinds takes the ordinary
step and records nothing. -/
theorem annotStepGo_other (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (pd : IDeclaration)
    (h : ∀ cv v hint, pd ≠ .defnDecl cv v hint) (h2 : ∀ cv v, pd ≠ .thmDecl cv v)
    (h3 : ∀ cv v, pd ≠ .opaqueDecl cv v) :
    annotStepGo mode pins fe pd = (do pure (← checkDecl mode pins fe pd, none)) := by
  cases pd with
  | defnDecl cv v hint => exact absurd rfl (h cv v hint)
  | thmDecl cv v => exact absurd rfl (h2 cv v)
  | opaqueDecl cv v => exact absurd rfl (h3 cv v)
  | _ => rfl

/-! ## The axiom census

**Task #97-P5-Checker-2**: the seven `_unfold`s that closed.  They are the
only obligations of this file about the TWIN rather than the port, and rule
11 (`Refine2/Checker/Shape.lean`'s `twin_reduce`) is what closes them. -/

/-- info: 'ConRon.Arena.checkConstantVal_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkConstantVal_unfold

/-- info: 'ConRon.Arena.checkValueGroup_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkValueGroup_unfold

/-- info: 'ConRon.Arena.constsResolveFGo_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms constsResolveFGo_unfold

/-- info: 'ConRon.Arena.checkProjRule_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkProjRule_unfold

/-- info: 'ConRon.Arena.checkDecl_axiomDecl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkDecl_axiomDecl

/-- info: 'ConRon.Arena.checkDecl_quotDecl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkDecl_quotDecl

end ConRon.Arena
