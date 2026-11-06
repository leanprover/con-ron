/-
# `ConRon.Arena.CheckDecl` — the checker's fold step, over handles
(DESIGN.md §8, task #105)

The twin of con-leche's `Kernel/CheckDecl.lean` — `checkShapeless` and
`checkDecl` — and of `Cached/Decls.lean`'s spec fold (`declStep`,
`checkDecls`), and the Rust twin of `arena::check_decl`.  The stages it
dispatches to are `Arena/DeclCheck.lean`'s (values, the certified `Nat`
operations, the pinned axioms, the pinned blocks and the quotient records) and
`Arena/Inductives/BlockTail.lean`'s (the uniform inductive route).

**Deviations:**

* **`checkDecl` is one `match`**, where the Rust splits it into a dispatch and
  six arm functions so that every arm stays a tail call (task #97-P4c's split
  rule); each Rust arm cites this function.  The gates' reads at the
  environment WITH the declaration (`fe.overlay [ci]` upstream) are their own
  `def`s here, as in the Rust (`checkStructuralNatPinAtFe2`).
* **The spec fold's step** (`checkDeclStep`) is `declStep`'s: the `And` pin,
  then the record's check from fresh memos (`flushCaches` and an empty
  `Memos`), the scratch tier OFF, so what the record pushes is persistent and
  is read by the next step.
-/
module

public import ConRon.Arena.Inductives.BlockTail
public import ConRon.Arena.DeclCheck
public import ConRon.Arena.Basis

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## A block the recogniser does not read -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:26-38 checkShapeless
con-leche: ConLeche/Cached/ParsedC.lean:68-76 checkShapelessS
The cited `block.foldlM`: every type former checked as a constant and
discarded, every other member skipped (the Rust's
`check_shapeless_formers`). -/
def checkShapelessFormers (mode : CheckMode) (fe : IFEnv) :
    List IConstantInfo → AM Unit
  | [] => pure ()
  | ci :: rest => do
    match ci with
    | .indInfo cv _ => do
      checkConstantVal mode fe cv false
      checkShapelessFormers mode fe rest
    | _ => checkShapelessFormers mode fe rest

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:26-38 checkShapeless
con-leche: ConLeche/Cached/ParsedC.lean:68-76 checkShapelessS
**An inductive block the recogniser does not read**: its type formers are
checked as constants (a reserved name, a duplicate, a malformed type are
official's rejects and stay rejects), and what survives that is a POSITIVE
decline, since the uniform route takes every block it recognises.  It never
returns an environment.  The message drops con-leche's interpolated block
name (§3.1). -/
def checkShapeless (mode : CheckMode) (fe : IFEnv) (block : List IConstantInfo) :
    AM IFEnv := do
  checkShapelessFormers mode fe block
  fail (.notImplemented "inductive block : shape not recognised")

/-! ## One declaration -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
The `.defnDecl` arm's structural-`Nat` gate, its reads at `fe2` (the
environment with the definition): `natOpGuard` and the dependencies' storage,
then the stored value. -/
def checkStructuralNatPinAtFe2 (fe2 : IFEnv) (n : NIdx) : AM EIdx := do
  let g ← natOpGuard fe2 n
  let deps ← natOpDeps n
  let d ← natOpStoredOkAll fe2 deps
  unless g && d do
    fail (.notImplemented "nonstandard structural Nat operation environment")
  match fe2.find? n with
  | some (.defnInfo _ value' _) => pure value'
  | _ => fail (.internal "structural Nat operation not stored")

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
**The structural-`Nat` gate**: the reads at `fe2`, then `certifyNatEqs` at `fe`,
the environment without the definition, over the equations with the
operation's self-references substituted.  Certifying with the definition
stored would let the operation's own fast path discharge its all-literal
equations vacuously.  `fe2` is `fe.overlay [ci]`, pushed and popped
(`IFEnv.popTemp`, the port's overlay); the index comes back. -/
def checkStructuralNatPin (mode : CheckMode) (fe : IFEnv) (ci : IConstantInfo)
    (n : NIdx) : AM IFEnv := do
  let prev := fe.idx[n]?
  let fe2 := fe.push ci
  let value' ← checkStructuralNatPinAtFe2 fe2 n
  let fe := fe2.popTemp n prev
  let eqs ← natOpEquations 0 n
  unless ← certifyNatEqs mode fe (← substConst0Pairs n value' eqs) do
    fail (.notImplemented "nonstandard structural Nat operation")
  pure fe

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
**Check a single declaration, extending the environment on success**: every
kind is checked in its arm.  A value arm checks the value returning the record
unpushed, runs its pinned gates, and pushes last. -/
def checkDecl (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (d : IDeclaration) : AM IFEnv := do
  match d with
  | .defnDecl cv value hint => do
    checkConstantVal mode fe cv true
    let ci ← checkDefnVal mode fe cv value hint
    let fe ← if (← natOpNames).contains cv.name then checkStructuralNatPin mode fe ci cv.name
      else pure fe
    let fe ← if (← natDivModNames).contains cv.name then checkDivModPin mode pins fe ci cv.name
      else pure fe
    pure (fe.push ci)
  | .thmDecl cv value => do
    checkConstantVal mode fe cv false
    let ci ← checkThmVal mode fe cv value
    pure (fe.push ci)
  | .opaqueDecl cv value => do
    checkConstantVal mode fe cv false
    let ci ← checkOpaqueVal mode fe cv value
    let fe ← if (← reduceOpNames).contains cv.name then checkReducePin mode fe ci cv.name value
      else pure fe
    pure (fe.push ci)
  | .axiomDecl cv => do
    -- **`Quot.sound` is the pinned quotient package's own record**: the export
    -- writes it as an ordinary axiom record beside the four `#QUOT` ones.  The
    -- name is a reserved basis name: this record IS the package's.
    if cv.name == (← pinQuotSound) then checkQuotRecord fe .sound cv
    else do
      checkConstantVal mode fe cv false
      if ← stdAxiomOk fe cv then
        pure (fe.push (.axiomInfo cv))
      else if cv.name == (← trustCompilerName) then
        -- `Lean.trustCompiler : True` is trivially realizable: installed
        -- exactly like a checked `opaque` with witness value `True.intro`
        -- over the pinned `True` family.
        if ← trustCompilerOk fe cv then
          pure (fe.push (.axiomInfo cv))
        else fail (.notImplemented
          "unsupported Lean.trustCompiler shape")
      else if cv.name == (← ofReduceNatName) || cv.name == (← ofReduceBoolName) then
        -- The pinned `ofReduce*` axioms: over the stored `Eq`, the element
        -- inductive and the identity-certified reduce opaque,
        -- `∀ a b, reduce a = b → a = b` interprets to an inhabited
        -- proposition.
        if ← ofReduceAxOk fe cv then
          pure (fe.push (.axiomInfo cv))
        else fail (.notImplemented
          "unsupported compiler-trust axiom environment")
      else if cv.name == (← propextName) || cv.name == (← choiceName) then
        fail (.notImplemented
          "standard axiom shape mismatch")
      else if cv.name == (← pinSorryAx) then
        -- `sorryAx` is the one axiom the checker tolerates as a DECLARATION:
        -- the record is skipped and the run continues, and any USE of the
        -- name declines at the record that uses it.
        pure fe
      else
        -- Every other axiom declines, the message naming it and the tactic
        -- that apparently added it (con-leche's own `nonStdAxiomMsg`, over
        -- the name read back from the store).
        fail (.notImplemented (ConLeche.nonStdAxiomMsg (← readNameM cv.name)))
  | .indDecl block nP => do
    -- **THE PINNED BASIS BLOCKS FIRST**: a stream's `Nat` block arrives as an
    -- ordinary `indDecl`; its members' names say it is the pinned block's
    -- record, and its check compares it with the pin.  Then the DECLARED
    -- parameter count (task #228: official's own check, one-sided), and ONE
    -- ROUTE: the uniform route takes every block the recogniser reads
    -- (`blockShape?`), at any number of members, nested ones included; any
    -- other block declines once its formers are checked (`checkShapeless`).
    match ← basisNameHit block with
    | some kind => checkBasisBlock fe kind block
    | none => do
      if !(← indParamsOk nP block) then
        fail (.invalid "number of parameters mismatch")
      else
        match ← blockShape? nP block with
        | some p => checkBlock mode fe block p
        | none => checkShapeless mode fe block
  | .quotDecl k cv => checkQuotRecord fe k cv

/-! ## The spec fold -/

/-- con-leche: ConLeche/Cached/Decls.lean:38-52 declStep
con-leche: ConLeche/Kernel/CheckDecl.lean:187-191 checkDeclsPure
**One record of the fold**: the `And` pin, then the record's check from a
fresh memo state (`flushCaches`, an empty `Memos`: the cited `checkDeclStepC`'s
`{}`).  The scratch tier stays OFF, so what the record pushes is persistent and
crosses to the next record, which is all that crosses.  The position the cited
step threads is the caller's (the fold's error is not tagged here). -/
def checkDeclStep (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (d : IDeclaration) : AM IFEnv := do
  unless ← andPinOk d do
    fail (.invalid "`And` must be the standard `And`")
  flushCaches
  let s ← get
  set { s with memos := Memos.empty }
  checkDecl mode pins fe d

/-- con-leche: ConLeche/Cached/Decls.lean:77-86 checkDecls
con-leche: ConLeche/Kernel/CheckDecl.lean:187-191 checkDeclsPure
The fold over a list of records, one `checkDeclStep` each.  con-leche's
`ds.foldlM (declStep mode pins)` takes a closure, which DESIGN §3.4 forbids, so
the fold is an explicit list recursion. -/
def checkDeclsPureGo (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) :
    List IDeclaration → AM IFEnv
  | [] => pure fe
  | d :: ds => do checkDeclsPureGo mode pins (← checkDeclStep mode pins fe d) ds

/-- con-leche: ConLeche/Cached/Decls.lean:77-86 checkDecls
con-leche: ConLeche/Kernel/CheckDecl.lean:187-191 checkDeclsPure
**The spec fold**: from the empty environment. -/
def checkDeclsPure (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : List IDeclaration) : AM IFEnv :=
  checkDeclsPureGo mode pins (mkIFEnv IEnv.empty) ds

end ConRon.Arena
