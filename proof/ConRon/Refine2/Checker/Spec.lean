/-
# `ConRon.Refine2.Checker.Spec` — the twin-side transcriptions the Rust's splits need

**Task #97-P5-Checker** (DESIGN.md §8.2, Theorem 2).  DESIGN §3.4's extraction
rule 5 — *a `HashMap::get` match that produces a value is its own function; a
`view`'s loans must be dead at the memo's join* — makes the Rust of the
declaration checker **finer-grained than the twin**: `check_constant_val` is
four Rust functions, `value_guards` two.
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
  `Arena/CheckerBase.lean`, `Arena/DeclCheck.lean` and `Arena/CheckDecl.lean` clause
  for clause;
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

All are closed.  (`divModCertStmts_unfold`, the eighth, was false: the twin
interned in another order than the port.  The twin now has the port's
factoring and the equation is its definition — task #97-T2-LOCKSTEP lane
Checker DeclCheck slice 2.)
-/
import ConRon.Refine2.Checker.KnotHyp

open Aeneas Aeneas.Std Result

namespace ConRon.Arena

open ConLeche

/-! ## `checkConstantVal`, in three

The Rust splits the common constant check at the two points where a guard would
otherwise join on a borrowed state (`check_constant_val_guards` / `_rest`) and at
the declared type's two resolution guards (`check_constant_val_tail`). -/

/-- The guards past the operation-name test: `Arena/CheckerBase.lean:checkConstantVal`
clauses 4-7, the literal shape first. -/
def checkConstantValGuardsRestSpec (cv : IConstantVal) : AM Unit := do
  unless ← litShapeOk (.axiomInfo cv) do
    fail (.notImplemented "a declaration at a literal's name with another shape")
  unless nameNodup cv.levelParams do
    fail (.invalid "duplicate universe parameters")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.invalid "loose bound variable in type")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.invalid "unexpected free variable in type")

/-- The SYNTACTIC guards, in the twin's order: `checkConstantVal` clauses 1-6. -/
def checkConstantValGuardsSpec (fe : IFEnv) (cv : IConstantVal) (allowOp : Bool) :
    AM Unit := do
  if (fe.find? cv.name).isSome then
    fail (.invalid "duplicate declaration")
  if (← natOpName cv.name) && !allowOp then
    fail (.invalid s!"a certified Nat operation's name, not a definition: {← readName cv.name}")
  checkConstantValGuardsRestSpec cv

/-- The failing arm of an unresolved constant, `throw (unresolvedConstsErrorL
(strLitStored fe) where_ e)` — the Rust's `unresolved_consts_fail`. -/
def unresolvedConstsFailSpec {α : Type} (fe : IFEnv) (where_ : String) (e : EIdx) :
    AM α := do
  fail (← unresolvedConstsErrorL (← strLitStored fe) where_ e)

/-- The two guards on the declared type (the Rust's `check_constant_val_tail`). -/
def checkConstantValTailSpec (fe : IFEnv) (cv : IConstantVal) : AM Unit :=
  allLevelParamsDefined cv.levelParams cv.type >>= fun d =>
    if d then
      constsResolveFFast fe cv.type >>= fun r =>
        if r then pure ()
        else unresolvedConstsFailSpec fe "type" cv.type
    else fail (.invalid "undeclared universe parameter in type")

/-- `valueGuards`' tail past the two scope tests (the Rust's `value_guards_tail`). -/
def valueGuardsTailSpec (fe : IFEnv) (cv : IConstantVal) (value : EIdx) : AM Unit :=
  allLevelParamsDefined cv.levelParams value >>= fun d =>
    if d then
      constsResolveFFast fe value >>= fun r =>
        if r then pure ()
        else unresolvedConstsFailSpec fe "value" value
    else fail (.invalid "undeclared universe parameter in value")

/-! ## `indParamsOk`'s per-member test -/

/-- `indParamsOk`'s body at one member — **the stream's declared parameter
count, checked as official checks it** (con-leche's task #228). -/
def indParamsOkAtSpec (nP : Nat) : IConstantInfo → AM Bool
  | .indInfo cvT _ => do
    match ← piSortTeleLen? coreWalkFuel cvT.type with
    | some n => pure (decide (nP ≤ n))
    | none => pure true
  | .ctorInfo _ nPc _ _ => pure (nPc == nP)
  | _ => pure true

/-! ## The `_unfold` equations

Each says that the named twin IS its transcription composed — the file's whole
proof obligation, and the only thing a reader has to check against
`Arena/CheckerBase.lean` and `Arena/DeclCheck.lean`. -/

/-- `checkConstantVal` is its three pieces and the inference. -/
theorem checkConstantVal_unfold (mode : CheckMode) (fe : IFEnv)
    (cv : IConstantVal) (allowOp : Bool) :
    checkConstantVal mode fe cv allowOp = (do
      checkConstantValGuardsSpec fe cv allowOp
      checkConstantValTailSpec fe cv
      let stype ← inferTypeCore mode fe checkFuel 0 cv.type
      let _u ← ensureSortCore mode fe checkFuel 0 stype) := by
  twin_reduce [checkConstantVal, checkConstantValGuardsSpec,
    checkConstantValGuardsRestSpec, checkConstantValTailSpec, unresolvedConstsFailSpec]

/-- `valueGuards` is its two scope tests and its tail. -/
theorem valueGuards_unfold (fe : IFEnv) (cv : IConstantVal) (value : EIdx) :
    valueGuards fe cv value = (do
      unless ← looseBVarsBoundedFast coreWalkFuel 0 value do
        fail (.invalid "loose bound variable in value")
      if ← hasFvarFast coreWalkFuel value then
        fail (.invalid "unexpected free variable in value")
      valueGuardsTailSpec fe cv value) := by
  twin_reduce [valueGuards, valueGuardsTailSpec, unresolvedConstsFailSpec]

/-- `indParamsOk` is its per-member test and the `&&` fold. -/
theorem indParamsOk_unfold (nP : Nat) (ci : IConstantInfo)
    (rest : List IConstantInfo) :
    indParamsOk nP (ci :: rest) = (do
      if ← indParamsOkAtSpec nP ci then indParamsOk nP rest else pure false) := by
  cases ci <;> twin_reduce [indParamsOk, indParamsOkAtSpec]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro x
  cases x <;> twin_reduce

/-! ## `arena::decl_check`'s splits (finding 11)

`decl_check.rs` is ninety-five `pub fn`s against thirty-three twin `def`s, and
`CertCtx` is the reason: `divModCertStmts` is a hundred-line `do` block over
twenty-one pinned handles, which DESIGN §3.4's rules split into twenty-three
Rust functions plus a record to carry the handles between them.  What follows
is the twin side of each split. -/

/-! ### The two axiom gates, in their arms -/

/-- `stdAxiomOk`'s `Iff` clause. -/
def iffPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← iffName) with
  | some (.indInfo cvI _) => cvI.matchesPin (← iffA).toConstantVal
  | _ => pure false

/-- `stdAxiomOk`'s `Iff.intro` clause, its arity test an explicit `if` as the
port writes it (the twin's literal pattern `.ctorInfo cv 2 2`, split by
`stdAxiomOk_split`). -/
def iffIntroPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← iffIntroName) with
  | some (.ctorInfo cvIi np nf _) =>
    if np == 2 && nf == 2 then do cvIi.matchesPin (← iffIntroA).toConstantVal
    else pure false
  | _ => pure false

/-- `stdAxiomOk`'s `Iff.rec` clause. -/
def iffRecPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← iffRecName) with
  | some (.recInfo cvIr mi rp _ _) =>
    if mi == 4 && rp == 4 then do cvIr.matchesPin (← iffRecA).toConstantVal
    else pure false
  | _ => pure false

/-- `stdAxiomOk`'s `Nonempty` clause. -/
def nonemptyPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← nonemptyName) with
  | some (.indInfo cvN _) => cvN.matchesPin (← nonemptyA).toConstantVal
  | _ => pure false

/-- `stdAxiomOk`'s `Nonempty.intro` clause. -/
def nonemptyIntroPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← nonemptyIntroName) with
  | some (.ctorInfo cvNi np nf _) =>
    if np == 1 && nf == 1 then do cvNi.matchesPin (← nonemptyIntroA).toConstantVal
    else pure false
  | _ => pure false

/-- `stdAxiomOk`'s `Nonempty.rec` clause. -/
def nonemptyRecPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← nonemptyRecName) with
  | some (.recInfo cvNr mi rp _ _) =>
    if mi == 3 && rp == 3 then do cvNr.matchesPin (← nonemptyRecA).toConstantVal
    else pure false
  | _ => pure false

/-- `trustCompilerOk`'s `True` clause. -/
def truePinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← trueName) with
  | some (.indInfo cvT _) => cvT.matchesPin (← trueCvA)
  | _ => pure false

/-- `trustCompilerOk`'s `True.intro` clause. -/
def trueIntroPinnedSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← trueIntroName) with
  | some (.ctorInfo cvTi np nf _) =>
    if np == 0 && nf == 0 then do cvTi.matchesPin (← trueIntroCvA)
    else pure false
  | _ => pure false

/-- `stdAxiomOk`'s `propext` arm past the `Eq` basis and `Iff` clauses (the
port's `std_axiom_ok_propext_rest` starts at `iff_intro_pinned`). -/
def stdAxiomOkPropextRestSpec (fe : IFEnv) (cv : IConstantVal) : AM Bool := do
  if !(← iffIntroPinnedSpec fe) then pure false
  else if !(← iffRecPinnedSpec fe) then pure false
  else cv.matchesPin (← propextA)

/-- `stdAxiomOk`'s `propext` arm. -/
def stdAxiomOkPropextSpec (fe : IFEnv) (cv : IConstantVal) : AM Bool := do
  if !(← eqStored fe) then pure false
  else if !(← iffPinnedSpec fe) then pure false
  else stdAxiomOkPropextRestSpec fe cv

/-- `stdAxiomOk`'s `Classical.choice` arm past the `Nonempty` and
`Nonempty.intro` clauses (the port's `std_axiom_ok_choice_rest` starts at
`nonempty_rec_pinned`). -/
def stdAxiomOkChoiceRestSpec (fe : IFEnv) (cv : IConstantVal) : AM Bool := do
  if !(← nonemptyRecPinnedSpec fe) then pure false
  else cv.matchesPin (← choiceA)

/-- `stdAxiomOk`'s `Classical.choice` arm. -/
def stdAxiomOkChoiceSpec (fe : IFEnv) (cv : IConstantVal) : AM Bool := do
  if !(← nonemptyPinnedSpec fe) then pure false
  else if !(← nonemptyIntroPinnedSpec fe) then pure false
  else stdAxiomOkChoiceRestSpec fe cv

/-- `reduceElemOk`'s `Bool` arm. -/
def reduceElemOkBoolSpec (fe : IFEnv) : AM Bool := do
  match fe.find? (← boolName) with
  | some (.indInfo cvB _) => cvB.matchesPin (← boolCvA)
  | _ => pure false

/-- `ofReduceAxOk`'s tail past the operation it names and the `Eq` basis test
(the port's `of_reduce_ax_ok_rest` starts at `reduce_elem_ok`). -/
def ofReduceAxOkRestSpec (fe : IFEnv) (cv : IConstantVal) (c : NIdx) :
    AM Bool := do
  if !(← reduceElemOk fe c) then pure false
  else if !(← reduceStoredOk fe c) then pure false
  else cv.matchesPin (← ofReducePinA cv.name)

/-- `ofReduceAxOk` split where the port splits it. -/
theorem ofReduceAxOk_split (fe : IFEnv) (cv : IConstantVal) :
    ofReduceAxOk fe cv = (do
      let c ← ofReduceOp cv.name
      if !(← eqStored fe) then pure false
      else ofReduceAxOkRestSpec fe cv c) := by
  simp only [ofReduceAxOk, ofReduceAxOkRestSpec]

/-- `trustCompilerOk` split where the port splits it, the twin's literal arity
pattern read as the port's explicit test. -/
theorem trustCompilerOk_split (fe : IFEnv) (cv : IConstantVal) :
    trustCompilerOk fe cv = (do
      if !(← truePinnedSpec fe) then pure false
      else if !(← trueIntroPinnedSpec fe) then pure false
      else cv.matchesPin (← trustCompilerA)) := by
  simp only [trustCompilerOk, truePinnedSpec, trueIntroPinnedSpec, bind_assoc]
  congr 1; funext n
  rcases fe.find? n with _ | ci
  · simp
  cases ci <;> simp
  congr 1; funext p; congr 1; funext b
  cases b
  · simp
  simp only [Bool.true_eq_false, ite_false]
  congr 1; funext n2
  rcases fe.find? n2 with _ | ci
  · simp
  cases ci <;> simp
  rename_i np nf
  rcases np with _ | np <;> rcases nf with _ | nf <;> simp

/-- `stdAxiomOk` split where the port splits it (`std_axiom_ok` →
`std_axiom_ok_{propext,choice}`), the literal arity patterns read as the port's
explicit tests. -/
theorem stdAxiomOk_split (fe : IFEnv) (cv : IConstantVal) :
    stdAxiomOk fe cv = (do
      let pn ← propextName
      if cv.name == pn then stdAxiomOkPropextSpec fe cv
      else do
        let cn ← choiceName
        if cv.name == cn then stdAxiomOkChoiceSpec fe cv else pure false) := by
  simp only [stdAxiomOk, stdAxiomOkPropextSpec, stdAxiomOkPropextRestSpec, eqStored,
    iffPinnedSpec, iffIntroPinnedSpec, iffRecPinnedSpec, stdAxiomOkChoiceSpec,
    stdAxiomOkChoiceRestSpec, nonemptyPinnedSpec, nonemptyIntroPinnedSpec,
    nonemptyRecPinnedSpec, bind_assoc, pure_bind]
  congr 1; funext pn
  split
  · congr 1; funext en
    split
    · rfl
    congr 1; funext n1
    rcases fe.find? n1 with _ | ci
    · simp
    cases ci <;> simp
    congr 1; funext p; congr 1; funext b
    cases b <;> simp
    congr 1; funext n2
    rcases fe.find? n2 with _ | ci
    · simp
    cases ci <;> simp
    rename_i np nf
    rcases np with _ | _ | _ | np <;> rcases nf with _ | _ | _ | nf <;> simp
    congr 1; funext p; congr 1; funext b
    cases b <;> simp
    congr 1; funext n3
    rcases fe.find? n3 with _ | ci
    · simp
    cases ci <;> simp
    rename_i mi rp _ _
    rcases mi with _ | _ | _ | _ | _ | mi <;> rcases rp with _ | _ | _ | _ | _ | rp <;> simp
  · congr 1; funext cn
    split
    · congr 1; funext n1
      rcases fe.find? n1 with _ | ci
      · simp
      cases ci <;> simp
      congr 1; funext p; congr 1; funext b
      cases b <;> simp
      congr 1; funext n2
      rcases fe.find? n2 with _ | ci
      · simp
      cases ci <;> simp
      rename_i np nf
      rcases np with _ | _ | np <;> rcases nf with _ | _ | nf <;> simp
      congr 1; funext p; congr 1; funext b
      cases b <;> simp
      congr 1; funext n3
      rcases fe.find? n3 with _ | ci
      · simp
      cases ci <;> simp
      rename_i mi rp _ _
      rcases mi with _ | _ | _ | _ | mi <;> rcases rp with _ | _ | _ | _ | rp <;> simp
    · rfl

/-! ### The ground-term guards

`reducePinGuard` and `divModPinGuard` are the same four tests at two different
pins, and the Rust factors them. -/

/-- The two tests past the free-variable one (the Rust's `ground_guards_rest`
starts at `all_level_params_defined`). -/
def groundGuardsRestSpec (fe : IFEnv) (p : EIdx) : AM Bool := do
  if !(← allLevelParamsDefined [] p) then pure false
  else constsResolveFFast fe p

/-- The four tests: closed, free-variable-free, no undeclared universe
parameter, and every constant resolves. -/
def groundGuardsSpec (fe : IFEnv) (p : EIdx) : AM Bool := do
  if !(← looseBVarsBoundedFast coreWalkFuel 0 p) then pure false
  else if ← hasFvarFast coreWalkFuel p then pure false
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
  let pinA ← reduceDeclPin c
  let okPin ← isDefEqCore mode fe checkFuel 0 value pinA
  if okPin then checkReduceIdentitySpec mode fe c value
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

/-- `checkReducePinPre` is its three transcriptions. -/
theorem checkReducePinPre_unfold (mode : CheckMode) (fe : IFEnv) (c : NIdx) (value : EIdx) :
    checkReducePinPre mode fe c value = checkReducePinPreSpec mode fe c value := by
  twin_reduce [checkReducePinPre, checkReducePinPreSpec, checkReducePinValueSpec,
    checkReduceIdentitySpec]

/-! ### The three value kinds' tails -/

/-- `checkThmVal`'s tail past the is-a-proposition test. -/
def checkThmValWitnessSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) : AM IConstantInfo := do
  valueGuards fe cv value
  let vtype ← inferTypeCore mode fe checkFuel 0 value
  unless ← isDefEqCore mode fe checkFuel 0 vtype cv.type do
    fail (.invalid "type mismatch in theorem")
  pure (.thmInfo cv)

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

/-- One `Bool` constructor stored at the type `Bool` itself. -/
abbrev boolCtorTypedSpec (fe2 : IFEnv) (n : NIdx) : AM Bool := boolCtorTyped fe2 n

/-- `divModEnvGuard`'s tail past the operation's own dependencies: the pinned
`Eq` basis and the two `Bool` constructors stored at the type `Bool`. -/
def divModEnvGuardRestSpec (fe2 : IFEnv) : AM Bool := do
  if !(← eqStored fe2) then pure false
  else if !(← boolCtorTypedSpec fe2 (← boolTrueName)) then pure false
  else boolCtorTypedSpec fe2 (← boolFalseName)

/-- `checkDivModPinLoop`'s step at a variant whose two guards passed — the
Rust's `check_div_mod_pin_try`: the attempt, then the loop's tail call on
`false`. -/
def checkDivModPinTrySpec (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (value' : EIdx) (ps : INatOpPinSet) (rest : List INatOpPinSet)
    (tried : List String) : AM Unit := do
  if ← checkDivModPinAt mode fe c value' ps then pure ()
  else checkDivModPinLoop mode fe c value' rest (tried ++ [divModAttemptReason ps])

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

/-! ### `divModCertStmts`' context, split where the port splits it

The twin (`Arena/DeclCheck.lean`) holds the context in `CertCtxA` and builds
it flat (`certCtx`); the port splits the build in four. -/

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

/-- `cert_ctx`'s subject: the twin's `certCtx` spelled through the four. -/
def certCtxFullSpec : AM CertCtxA := do
  let nt ← pinNat
  let natTy ← constE nt
  let x ← natVar 0
  let y ← natVar 1
  let one ← natOne
  certCtxBoolFullSpec natTy x y one

/-- The port's four-way split of the context is the twin's flat build. -/
theorem certCtxFullSpec_eq : certCtxFullSpec = certCtx := by
  simp only [certCtxFullSpec, certCtxBoolFullSpec, certCtxNumsFullSpec,
    certCtxNamesFullSpec, certCtxNamesRestFullSpec, certCtxBoolSpec, certCtxNumsSpec,
    certCtx, bind_assoc, pure_bind]


/-! ## `arena::check_decl`'s splits

`checkDeclKind`'s arms are the Rust's `check_*_decl` functions and their tails, for
extraction rule 5's reason at every one: an arm that runs a pin gate holds the
environment and a record across a `match`. -/

/-- `checkDeclKind`'s `.indDecl` arm (`check_ind_decl`): the declared parameter
count, then the one uniform route (`checkBlock`) at every block `readBlock`
reads, the pinned basis blocks included, or the reader's reject. -/
def checkIndDeclArmSpec (mode : CheckMode) (fe : IFEnv)
    (block : List IConstantInfo) (nP : Nat) : AM IFEnv := do
  if !(← indParamsOk nP block) then
    fail (.invalid "number of parameters mismatch")
  else
    match ← readBlock nP block with
    | .ok p => checkBlock mode fe block p
    | .error e => fail e

/-- `checkDecl`'s axiom arm past the `ofReduce*` test: the two standard
axioms' shape mismatch, `sorryAx` tolerated as a DECLARATION, everything else
declined. -/
def checkAxiomDeclRestSpec (fe : IFEnv) (cv : IConstantVal) : AM IFEnv := do
  if cv.name == (← propextName) || cv.name == (← choiceName) then
    fail (.notImplemented
      "standard axiom shape mismatch")
  else if cv.name == (← pinSorryAx) then pure fe
  else fail (.notImplemented (ConLeche.nonStdAxiomMsg (← readNameM cv.name)))

/-- `checkDecl`'s axiom arm at the `ofReduce*` names. -/
def checkAxiomDeclOfReduceSpec (fe : IFEnv) (cv : IConstantVal) : AM IFEnv := do
  if cv.name == (← ofReduceNatName) || cv.name == (← ofReduceBoolName) then
    if ← ofReduceAxOk fe cv then pure (fe.push (.axiomInfo cv))
    else fail (.notImplemented
      "unsupported compiler-trust axiom environment")
  else checkAxiomDeclRestSpec fe cv

/-- `checkDecl`'s axiom arm at `Lean.trustCompiler`. -/
def checkAxiomDeclTrustSpec (fe : IFEnv) (cv : IConstantVal) : AM IFEnv := do
  if cv.name == (← trustCompilerName) then
    if ← trustCompilerOk fe cv then pure (fe.push (.axiomInfo cv))
    else fail (.notImplemented
      "unsupported Lean.trustCompiler shape")
  else checkAxiomDeclOfReduceSpec fe cv

/-- `checkDecl`'s axiom arm past `Quot.sound`: the common constant check, then
the standard-axiom gate (`check_axiom_decl_std`). -/
def checkAxiomDeclStdSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    AM IFEnv := do
  checkConstantVal mode fe cv false
  if ← stdAxiomOk fe cv then pure (fe.push (.axiomInfo cv))
  else checkAxiomDeclTrustSpec fe cv

/-- `checkDecl`'s `.axiomDecl` arm, whole (`check_axiom_decl`). -/
def checkAxiomDeclSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    AM IFEnv := do
  if cv.name == (← pinQuotSound) then checkQuotRecord fe .sound cv
  else checkAxiomDeclStdSpec mode fe cv

/-- `checkDecl`'s `.opaqueDecl` tail past the value check
(`check_opaque_reduce_pin`): the reduce-operation gate, then the push. -/
def checkOpaqueReducePinSpec (mode : CheckMode) (fe : IFEnv) (ci : IConstantInfo)
    (n : NIdx) (value : EIdx) : AM IFEnv := do
  let fe ← if (← reduceOpNames).contains n then checkReducePin mode fe ci n value
    else pure fe
  pure (fe.push ci)

/-- `checkDecl`'s `.opaqueDecl` arm (`check_opaque_decl`). -/
def checkOpaqueDeclSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) : AM IFEnv := do
  checkConstantVal mode fe cv false
  let ci ← checkOpaqueVal mode fe cv value
  checkOpaqueReducePinSpec mode fe ci cv.name value

/-- `checkDecl`'s `.thmDecl` arm (`check_thm_decl`). -/
def checkThmDeclSpec (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) : AM IFEnv := do
  checkConstantVal mode fe cv false
  let ci ← checkThmVal mode fe cv value
  pure (fe.push ci)

/-- The structural-`Nat` gate's certification at the environment without the
definition (`check_structural_nat_pin_eqs`). -/
def checkStructuralNatPinEqsSpec (mode : CheckMode) (fe : IFEnv) (n : NIdx)
    (value' : EIdx) : AM Unit := do
  let eqs ← natOpEquations 0 n
  unless ← certifyNatEqs mode fe (← substConst0Pairs n value' eqs) do
    fail (.notImplemented "nonstandard structural Nat operation")

/-- The `Nat.div`/`Nat.mod` gate at a definition, then the push
(`check_defn_div_mod_pin`). -/
def checkDefnDivModPinSpec (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) : AM IFEnv := do
  let fe ← if (← natDivModNames).contains n then checkDivModPin mode pins fe ci n
    else pure fe
  pure (fe.push ci)

/-- Both pin gates, in the twin's order (`check_defn_pins`). -/
def checkDefnPinsSpec (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) : AM IFEnv := do
  let fe ← if (← natOpNames).contains n then checkStructuralNatPin mode fe ci n
    else pure fe
  checkDefnDivModPinSpec mode pins fe ci n

/-- `checkDecl`'s `.defnDecl` arm, whole (`check_defn_decl`). -/
def checkDefnDeclSpec (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (cv : IConstantVal) (value : EIdx) (hint : ReducibilityHint) : AM IFEnv := do
  checkConstantVal mode fe cv true
  let ci ← checkDefnVal mode fe cv value hint
  checkDefnPinsSpec mode pins fe ci cv.name

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

**The pins are con-leche's plain values** (task #119: the raw/annotated
pair is gone with the annotation), interned as the Rust interns them, so
`internAllPinsPortSpec` below IS `internAllPins`, up to the monad laws
(`internAllPinsPortSpec_eq`, `Checker/Top.lean`). -/

/-- `internAllPins`' reserved-name half — `intern_all_names`. -/
def internAllNamesSpec : AM Unit := do
  let _ ← reservedBasisNames
  let _ ← natOpNames; let _ ← natDivModNames; let _ ← reduceOpNames
  let _ ← pinSorryAx; let _ ← pinQuotSound

/-- `intern_all_reduce_pins`: the four `reduce*`/`ofReduce*` shapes and
the two pinned defining expressions. -/
def internAllReducePinsSpec : AM Unit := do
  let _ ← reduceNatCvA; let _ ← reduceBoolCvA
  let _ ← ofReduceNatA; let _ ← ofReduceBoolA
  let _ ← reduceNatDeclPin; let _ ← reduceBoolDeclPin

/-- `intern_all_trust_pins`: the compiler-trust shapes, then the reduce pins. -/
def internAllTrustPinsSpec : AM Unit := do
  let _ ← trueCvA; let _ ← trueIntroCvA; let _ ← trustCompilerA; let _ ← boolCvA
  internAllReducePinsSpec

/-- `intern_all_axiom_pins_rest`: the standard axiom pins past `Nonempty`,
then the trust pins. -/
def internAllAxiomPinsRestSpec : AM Unit := do
  let _ ← nonemptyIntroA; let _ ← nonemptyRecA
  let _ ← propextA; let _ ← choiceA
  internAllTrustPinsSpec

/-- `intern_all_axiom_pins`: the `Iff` family and `Nonempty`, then the
rest. -/
def internAllAxiomPinsSpec : AM Unit := do
  let _ ← iffA; let _ ← iffIntroA; let _ ← iffRecA; let _ ← nonemptyA
  internAllAxiomPinsRestSpec

/-- `intern_all_basis` from the cursor on: the basis blocks. -/
def internAllBasisSpec : List BasisKind → AM Unit
  | [] => pure ()
  | k :: ks => do
    let _ ← BasisKind.decls k
    internAllBasisSpec ks

/-- **The port's startup walk**, as a twin action: `intern_all_pins`' four
calls in order — `internAllPins` itself, re-bracketed
(`internAllPinsPortSpec_eq`, `Checker/Top.lean`). -/
def internAllPinsPortSpec (pins : List NatOpPinSet) (maxNatSize : Nat) :
    AM (List INatOpPinSet) := do
  let s ← get
  set { s with pins := { s.pins with maxNatSize := maxNatSize } }
  internAllBasisSpec [.eqK, .natK, .emptyK, .falseK, .quotK]
  internAllAxiomPinsSpec
  internAllNamesSpec
  internPinSets pins

/-! ## `checkDeclKind`, arm by arm (task #97-P5-Checker round 4)

Task #97-P5-Checker round 3 §10 item 2 named `checkDecl_unfold` as the one
thing between `check_decl_refines` and a seven-way `cases`: the twin writes
the seven arms inline and the tier's statements are against the
transcriptions above.  **Six of the seven are equations and are closed here.
The seventh was not an equation** while the twin's `.defnDecl` arm read the
constant's name back (`readName`, which throws `internal` at a dangling
handle) for its decline messages.  Task #97-T2-LOCKSTEP lane Checker gave the
twin the Rust's constant messages, and `checkDeclKind_defnDecl` below closes the
seventh too.-/

theorem checkDeclKind_axiomDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) :
    checkDeclKind mode pins fe (.axiomDecl cv) = checkAxiomDeclSpec mode fe cv := by
  twin_reduce [checkDeclKind, checkAxiomDeclSpec, checkAxiomDeclStdSpec, checkAxiomDeclTrustSpec,
    checkAxiomDeclOfReduceSpec, checkAxiomDeclRestSpec]

/-- The stored definition's value — the twin's `match fe2.find? c with |
some (.defnInfo _ v _)`, under the name the Rust gives it (`defn_value`). -/
def defnValueOf (fe : IFEnv) (c : NIdx) : Option EIdx :=
  match fe.find? c with
  | some (.defnInfo _ v _) => some v
  | _ => none

/-- `checkDivModPinAtFe2` at the stored value as the Rust reads it (`defn_value`). -/
theorem checkDivModPinAtFe2_split (fe2 : IFEnv) (c : NIdx) :
    checkDivModPinAtFe2 fe2 c = (do
      if ← divModEnvGuard fe2 c then
        match defnValueOf fe2 c with
        | some v => pure v
        | none => fail (.internal "Nat.div/mod operation not stored")
      else fail (.notImplemented "unsupported Nat.div/mod environment")) := by
  unfold checkDivModPinAtFe2 defnValueOf
  refine ConRon.Refine2.am_bind_congr _ fun g => ?_
  cases g
  · rfl
  · simp only [ite_true]
    rcases fe2.find? c with _ | ci
    · rfl
    · cases ci <;> rfl

/-- `checkStructuralNatPinAtFe2` in the Rust's arrangement: the two guards nested,
the stored value as `defn_value` reads it. -/
theorem checkStructuralNatPinAtFe2_split (fe2 : IFEnv) (n : NIdx) :
    checkStructuralNatPinAtFe2 fe2 n = (do
      let g ← natOpGuard fe2 n
      let deps ← natOpDeps n
      let d ← natOpStoredOkAll fe2 deps
      if g then
        if d then
          match defnValueOf fe2 n with
          | some v => pure v
          | none => fail (.internal "structural Nat operation not stored")
        else fail (.notImplemented "nonstandard structural Nat operation environment")
      else fail (.notImplemented "nonstandard structural Nat operation environment")) := by
  unfold checkStructuralNatPinAtFe2 defnValueOf
  refine ConRon.Refine2.am_bind_congr _ fun g => ConRon.Refine2.am_bind_congr _ fun _ =>
    ConRon.Refine2.am_bind_congr _ fun d => ?_
  cases g <;> cases d <;> simp only [Bool.and_true, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, ConRon.Refine2.am_fail_bind]
  all_goals
    rcases fe2.find? n with _ | ci
    · rfl
    · cases ci <;> rfl

/-- `checkStructuralNatPin` is the reads at the environment with the definition,
the pop, and the certification (`check_structural_nat_pin_eqs`). -/
theorem checkStructuralNatPin_split (mode : CheckMode) (fe : IFEnv) (ci : IConstantInfo)
    (n : NIdx) :
    checkStructuralNatPin mode fe ci n = (do
      let v ← checkStructuralNatPinAtFe2 (fe.push ci) n
      checkStructuralNatPinEqsSpec mode ((fe.push ci).popTemp n fe.idx[n]?) n v
      pure ((fe.push ci).popTemp n fe.idx[n]?)) := by
  twin_reduce [checkStructuralNatPin, checkStructuralNatPinEqsSpec]

theorem checkDeclKind_defnDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) (value : EIdx) (hint : ReducibilityHint) :
    checkDeclKind mode pins fe (.defnDecl cv value hint) =
      checkDefnDeclSpec mode pins fe cv value hint := by
  twin_reduce [checkDeclKind, checkDefnDeclSpec, checkDefnPinsSpec, checkDefnDivModPinSpec]

theorem checkDeclKind_thmDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) (value : EIdx) :
    checkDeclKind mode pins fe (.thmDecl cv value) = checkThmDeclSpec mode fe cv value := by
  twin_reduce [checkDeclKind, checkThmDeclSpec]

theorem checkDeclKind_opaqueDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (cv : IConstantVal) (value : EIdx) :
    checkDeclKind mode pins fe (.opaqueDecl cv value)
      = checkOpaqueDeclSpec mode fe cv value := by
  twin_reduce [checkDeclKind, checkOpaqueDeclSpec, checkOpaqueReducePinSpec]

theorem checkDeclKind_indDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (block : List IConstantInfo) (nP : Nat) :
    checkDeclKind mode pins fe (.indDecl block nP)
      = checkIndDeclArmSpec mode fe block nP := rfl

theorem checkDeclKind_quotDecl (mode : CheckMode) (pins : List INatOpPinSet)
    (fe : IFEnv) (k : QuotKind) (cv : IConstantVal) :
    checkDeclKind mode pins fe (.quotDecl k cv) = checkQuotRecord fe k cv := by
  rw [checkDeclKind]

/-! ## The axiom census

**Task #97-P5-Checker-2**: the seven `_unfold`s that closed.  They are the
only obligations of this file about the TWIN rather than the port, and rule
11 (`Refine2/Checker/Shape.lean`'s `twin_reduce`) is what closes them. -/

/-- info: 'ConRon.Arena.checkConstantVal_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkConstantVal_unfold


/-- info: 'ConRon.Arena.checkDeclKind_axiomDecl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkDeclKind_axiomDecl

/-- info: 'ConRon.Arena.checkDeclKind_quotDecl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkDeclKind_quotDecl

end ConRon.Arena
