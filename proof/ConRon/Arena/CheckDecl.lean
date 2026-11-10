/-
# `ConRon.Arena.CheckDecl` — the checker's fold step, over handles
(DESIGN.md §8, task #105)

The twin of con-leche's `Kernel/CheckDecl.lean` — `checkDeclKind` (a
declaration's own checks) and `checkDecl` (those, then the reserved names'
check `basisNamesOk`) — and of `Cached/Decls.lean`'s spec fold (`declStep`,
`checkDecls`), and the Rust twin of `arena::check_decl`.  The stages it
dispatches to are `Arena/DeclCheck.lean`'s (values, the certified `Nat`
operations, the pinned axioms and the quotient records) and
`Arena/Inductives/BlockTail.lean`'s (the uniform inductive route, which takes
the pinned basis blocks too).

**Deviations:**

* **`checkDeclKind` is one `match`**, where the Rust splits it into a dispatch and
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

/-! ## One declaration -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind
con-leche: ConLeche/Cached/ParsedC.lean:243-315 checkDeclKindC
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

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind
con-leche: ConLeche/Cached/ParsedC.lean:243-315 checkDeclKindC
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

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind
con-leche: ConLeche/Cached/ParsedC.lean:243-315 checkDeclKindC
**A declaration's own checks**, by its kind, extending the environment on
success.  A value arm checks the value returning the record unpushed, runs its
pinned gates, and pushes last.  A block under a pinned basis block's names
takes the same route as every other block. -/
def checkDeclKind (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
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
    -- The DECLARED parameter count first (task #228: official's own check,
    -- one-sided), then ONE ROUTE: the uniform route takes every block
    -- `readBlock` reads, at any number of members, nested ones and the pinned
    -- basis blocks included; any other block is rejected with the reason
    -- `readBlock` gives.
    if !(← indParamsOk nP block) then
      fail (.invalid "number of parameters mismatch")
    else
      match ← readBlock nP block with
      | .ok p => checkBlock mode fe block p
      | .error e => fail e
  | .quotDecl k cv => checkQuotRecord fe k cv

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:166-174 checkDecl
con-leche: ConLeche/Cached/ParsedC.lean:317-323 checkDeclC
**Check a single declaration**: its own checks (`checkDeclKind`), then the
reserved names' (`basisNamesOk`), which justify the model's fixed meanings of
the basis names.  The per-declaration caches are flushed between the two (the
port's deviation, the Rust's too: the next record flushes first anyway), so the
reserved names' check starts from an empty readback memo; a cache only
memoises, so no verdict moves. -/
def checkDecl (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (d : IDeclaration) : AM IFEnv := do
  let fe₂ ← checkDeclKind mode pins fe d
  flushCaches
  if ← basisNamesOk d then pure fe₂
  else fail (← basisNamesError d)

/-! ## The spec fold -/

/-- con-leche: ConLeche/Cached/Decls.lean:44-58 declStep
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove CheckDecl.checkDeclStep_bridge, then delete this line
con-leche: ConLeche/Kernel/CheckDecl.lean:176-180 checkDeclsPure
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

/-- con-leche: ConLeche/Cached/Decls.lean:83-92 checkDecls
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove CheckDecl.checkDeclsPureGo_bridge, then delete this line
con-leche: ConLeche/Kernel/CheckDecl.lean:176-180 checkDeclsPure
The fold over a list of records, one `checkDeclStep` each.  con-leche's
`ds.foldlM (declStep mode pins)` takes a closure, which DESIGN §3.4 forbids, so
the fold is an explicit list recursion. -/
def checkDeclsPureGo (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) :
    List IDeclaration → AM IFEnv
  | [] => pure fe
  | d :: ds => do checkDeclsPureGo mode pins (← checkDeclStep mode pins fe d) ds

/-- con-leche: ConLeche/Cached/Decls.lean:83-92 checkDecls
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove CheckDecl.checkDeclsPure_bridge, then delete this line
con-leche: ConLeche/Kernel/CheckDecl.lean:176-180 checkDeclsPure
**The spec fold**: from the empty environment. -/
def checkDeclsPure (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : List IDeclaration) : AM IFEnv :=
  checkDeclsPureGo mode pins (mkIFEnv IEnv.empty) ds

end ConRon.Arena
