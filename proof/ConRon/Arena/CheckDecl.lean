/-
# `ConRon.Arena.CheckDecl` — the checker's fold step, over handles
(DESIGN.md §8, task #105)

The twin of con-leche's `Kernel/CheckDecl.lean` — `checkShapeless`,
`checkDecl` and `checkDeclsPure`, which upstream moved out of
`Kernel/Checker.lean` because the uniform inductive route's stages sit above
the checker's value stages — and the Rust twin of `arena::check_decl`.  The
stages it dispatches to are this module's `checkBasisDecl` (the pinned basis
install), `Arena/DeclCheck.lean`'s (values, the certified `Nat` operations,
the pinned axioms) and `Arena/Inductives/BlockTail.lean`'s (the uniform
inductive route).

**Deviations:**

* **`checkBasisDecl` lives HERE**, not in `Arena/Checker.lean` beside the
  Rust's `arena::checker::check_basis_decl`: the Rust's `check_decl` and
  `checker` modules call each other (a cycle Rust allows), and the arena's
  import order is fixed by what calls what.  `Arena/Checker.lean` imports
  this module.
* **`checkDecl` is one `match`**, where the Rust splits it into a dispatch
  and seven arm functions so that every arm stays a tail call (task
  #97-P4c's split rule); each Rust arm cites this function.
* **The fold steps are bracketed** (`checkDeclStep`), as
  `Arena/Checker.lean`'s module note explains.
-/
import ConRon.Arena.Inductives.BlockTail
import ConRon.Arena.DeclCheck
import ConRon.Arena.Promote

namespace ConRon.Arena

open ConLeche

/-! ## The pinned basis install -/

/-- con-leche: ConLeche/Kernel/Checker.lean:425-435 checkBasisDecl —
**install the pinned (pre-annotated) basis block.**  The three records that
install one — the fold's own `basisDecl` kind, a stream block `basisPinHit`
recognises and a quotient record `quotPinHit` recognises — share this body.
The quotient block's types mention the pinned equality former, which is why
it requires the `Eq` basis first. -/
def checkBasisDecl (fe : IFEnv) (kind : BasisKind) : AM IFEnv := do
  if kind == .quotK then do
    let en ← pinEq
    unless fe.find? en == some (← eqA) do
      fail (.notImplemented "quotient basis requires the pinned Eq basis")
  installBasisDecls fe (← BasisKind.declsA kind)

/-! ## A block the recogniser does not read -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:26-38 checkShapeless
con-leche: ConLeche/Cached/ParsedC.lean:78-86 checkShapelessS
The cited `block.foldlM`: every type former checked as a constant and
discarded, every other member skipped (the Rust's
`check_shapeless_formers`). -/
def checkShapelessFormers (mode : CheckMode) (fe : IFEnv) :
    List IConstantInfo → AM Unit
  | [] => pure ()
  | ci :: rest => do
    match ci with
    | .indInfo cv _ => do
      let _ ← checkConstantVal mode fe cv
      checkShapelessFormers mode fe rest
    | _ => checkShapelessFormers mode fe rest

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:26-38 checkShapeless
con-leche: ConLeche/Cached/ParsedC.lean:78-86 checkShapelessS
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

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl — **check a
single declaration, extending the environment on success.**  Clause for
clause; `env : Env` is the index (`Arena/Core.lean`'s deviation 1). -/
def checkDecl (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (d : IDeclaration) : AM IFEnv := do
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantVal mode fe cv
    let fe2 ← checkDefnVal mode fe cv value hint
    -- Structural-`Nat` pins: the fast-path ops must be the standard
    -- structural recursions — their recurrence equations are checked by
    -- definitional equality here, once, in the PRE-insertion environment with
    -- the operation's self-references replaced by its stored value.
    --
    -- **The pre-insertion environment is `fe2` restricted to `fe`'s counter**
    -- (task #97-T2-LOCKSTEP lane Checker round 2): the Rust keeps ONE index
    -- and runs the three pin gates at `restrict(fe2, k_pre)`, so the twin
    -- does too.  It answers every `find?` exactly as `fe` does (the pushed
    -- name was fresh), which is all Theorem 1 needs
    -- (`Bridge/Checker/Inv.lean`'s `IFEnv.find?_push_restrict`).
    -- The guard, then the dependency list, then the stored-dependency test:
    -- the Rust's order (`check_structural_nat_pin`).
    if (← natOpNames).contains cv.name then do
      let g ← natOpGuard fe2 cv.name
      let deps ← natOpDeps cv.name
      unless g && (← natOpStoredOkAll fe2 deps) do
        fail (.notImplemented
          "nonstandard structural Nat operation environment")
      match fe2.find? cv.name with
      | some (.defnInfo _ value' _) => do
        let eqs ← natOpEquations 0 cv.name
        let ok ← certifyNatEqs mode (fe2.restrictTo fe.visibleBelow)
          (← substConst0Pairs cv.name value' eqs)
        unless ok do
          fail (.notImplemented
            "nonstandard structural Nat operation")
      | _ => fail (.internal
          "structural Nat operation not stored")
    -- WF-recursive `Nat` pins (`Nat.div`/`Nat.mod`): the stored value must be
    -- definitionally equal to some committed pin variant, and that variant's
    -- certificates must check.  No variant matching is a decline.
    if (← natDivModNames).contains cv.name then
      checkDivModPin mode pins (fe2.restrictTo fe.visibleBelow) fe2 cv.name
    pure fe2
  | .thmDecl cv value => do
    let cv ← checkConstantVal mode fe cv
    checkThmVal mode fe cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantVal mode fe cv
    let fe2 ← checkOpaqueVal mode fe cv value
    -- Compiler-trust opaques (`Lean.reduceNat`/`Lean.reduceBool`): the stored
    -- value must be definitionally equal to the build-time pin.
    if (← reduceOpNames).contains cv.name then
      checkReducePin mode (fe2.restrictTo fe.visibleBelow) fe2 cv.name value
    pure fe2
  | .axiomDecl cv => do
    -- **`Quot.sound` is the pinned quotient BLOCK's own record**: the export
    -- writes it as an ordinary axiom record beside the four `#QUOT` ones, so
    -- it arrives here — compared with the pin and installing NOTHING of its
    -- own, and DECLINING when it does not match.  The comparison precedes the
    -- common checks because the name is a reserved basis name: this record IS
    -- the pinned block's, not a redeclaration of it.
    if cv.name == (← pinQuotSound) then do
      let blk ← BasisKind.decls .quotK
      match blk[4]? with
      | some pinned =>
        if ← IConstantInfo.canonEq (.axiomInfo cv) pinned then pure fe
        else fail (.notImplemented "quotient soundness axiom mismatch")
      | none => fail (.notImplemented "quotient soundness axiom mismatch")
    else do
      let cvA ← checkConstantVal mode fe cv
      if ← stdAxiomOk fe cvA then
        pure (fe.push (.axiomInfo cvA))
      else if cvA.name == (← trustCompilerName) then
        -- `Lean.trustCompiler : True` is trivially realizable: installed
        -- exactly like a checked `opaque` with witness value `True.intro`
        -- over the pinned `True` family.
        if ← trustCompilerOk fe cvA then
          pure (fe.push (.axiomInfo cvA))
        else fail (.notImplemented
          "unsupported Lean.trustCompiler shape")
      else if cvA.name == (← ofReduceNatName) || cvA.name == (← ofReduceBoolName) then
        -- The pinned `ofReduce*` axioms: over the pinned `Eq` basis, the
        -- element inductive and the identity-certified reduce opaque,
        -- `∀ a b, reduce a = b → a = b` interprets to an inhabited
        -- proposition.
        if ← ofReduceAxOk fe cvA then
          pure (fe.push (.axiomInfo cvA))
        else fail (.notImplemented
          "unsupported compiler-trust axiom environment")
      else if cvA.name == (← propextName) || cvA.name == (← choiceName) then
        fail (.notImplemented
          "standard axiom shape mismatch")
      else if cvA.name == (← pinSorryAx) then
        -- `sorryAx` is the one axiom the checker tolerates as a DECLARATION:
        -- the record is skipped and the run continues, and any USE of the
        -- name declines at the record that uses it.
        pure fe
      else
        fail (.notImplemented "non-standard axiom")
  | .basisDecl kind => checkBasisDecl fe kind
  | .indDecl block nP => do
    -- **THE PINNED BASIS BLOCKS FIRST**: a stream's `Nat` block arrives as an
    -- ordinary `indDecl` and is recognised HERE.  A block under a pinned name
    -- that does not match falls through to the ordinary route, where
    -- `checkConstantVal`'s reserved-name check REJECTS it.  Then the DECLARED
    -- parameter count (task #228: official's own check, one-sided), and ONE
    -- ROUTE: the uniform route takes every block the recogniser reads
    -- (`blockParts?`), at any number of members, nested ones included; any
    -- other block declines once its formers are checked (`checkShapeless`).
    match ← basisPinHit block with
    | some kind => checkBasisDecl fe kind
    | none => do
      if !(← indParamsOk nP block) then
        fail (.invalid "number of parameters mismatch")
      else
        match ← blockParts? nP block with
        | some p => checkBlock mode fe block p
        | none => checkShapeless mode fe block
  | .quotDecl k cv => do
    -- **THE QUOTIENT PACKAGE**: the export writes it as four records; each is
    -- compared with the pinned block's constant at its own kind, and the
    -- FIRST that matches installs the pinned block whole.
    if ← quotPinHit k cv then
      match k with
      | .type => checkBasisDecl fe .quotK
      | _ => pure fe
    else fail (.notImplemented (match k with
      | .sound => "quotient soundness axiom mismatch"
      | _ => "quotient declaration mismatch"))

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:216-220 checkDeclsPure — **one
step of the pure fold, bracketed**: `checkDecl` inside the per-declaration
scratch tier, with the constants it installed promoted before the tier goes.

The bracket is `annotStep`'s, letter for letter — one `checkDecl` where phase
A has an install half, and no `ValueGroup` because the pure fold checks what
it installs in the same step.  DESIGN §8.3's amendment puts it here too, so
that **the two folds stay one algorithm**: the tier regime is not an
optimisation of the driver's fold that the theorem's fold may do without, it
is where every term the checker builds lives, and a Theorem-1 statement about
a fold with no tiers would say nothing about the fold the binary runs. -/
def checkDeclStep (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (d : IDeclaration) : AM IFEnv := do
  let vis := fe.visibleBelow
  flushCaches
  enterScratch
  let fe ← checkDecl mode pins fe d
  let k := fe.visibleBelow - vis
  let (_, fe) ← promoteNew PMemo.empty coreWalkFuel k fe
  dropScratch
  pure fe

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:216-220 checkDeclsPure — check a
list of declarations in order, starting from the empty environment.  THE
THEOREM'S SHAPE (module note): one step per record, install and check
together.  con-leche's `ds.foldlM (checkDecl mode ops pins) Env.empty` takes a
closure, which DESIGN §3.4 forbids, so the fold is an explicit list
recursion. -/
def checkDeclsPureGo (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) :
    List IDeclaration → AM IFEnv
  | [] => pure fe
  | d :: ds => do checkDeclsPureGo mode pins (← checkDeclStep mode pins fe d) ds

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:216-220 checkDeclsPure — the fold
from the empty environment. -/
def checkDeclsPure (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : List IDeclaration) : AM IFEnv :=
  checkDeclsPureGo mode pins (mkIFEnv IEnv.empty) ds

end ConRon.Arena
