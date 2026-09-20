/-
# `ConRon.Arena.Checker` — the declaration fold, over handles

The twin of `ConLeche/Kernel/Checker.lean`'s `checkDecl` / `checkDeclsPure`
and of `ConLeche/Cached/Installed.lean`'s two-phase `checkDecls`.

## Two folds, and which is which

con-leche has both, and so does (B), because they are different things:

* **`checkDeclsPure`** is the THEOREM's shape — `ConLeche/Model/Fold.lean`'s
  `checkDeclsPure_sound_of` consumes it, and DESIGN §8.2's Theorem 1 folds
  `checkDecl` over the stream.  One step per record, install and check
  together.
* **`installThenCheck`** is what the BINARY runs
  (`ConLeche/Cached/Installed.lean:450-455`, whose `checkDecls` is the
  driver's own algorithm): phase A installs every record, annotating its
  header and its value but not inferring; phase B checks each recorded
  declaration against the PREFIX VIEW it was installed at.  con-leche proves
  the two are the same accept (`fullyChecked_checkDecls`); the arena's two
  call the same `checkDecl` pieces, which is what keeps them the same
  computation.

## Every declaration is bracketed, in both folds

DESIGN §8.3: "Persistent = parse + installed environment; scratch = one
declaration's check."  Phase B's business is exactly what a declaration merely
COMPUTES — a sort, an inferred type, a conversion — so `checkPending` is
`enterScratch` … `dropScratch` around `checkValueGroup`, and every node it
appends goes with the tier.

**Phase A is bracketed too, with promotion** (DESIGN §8.3's amendment, task
#97-P6-2).  Task #97d ran phase A persistently, because the terms an install
leaves behind must not be in a tier that is about to vanish.  They must not —
but they are a handful of handles, and the install was interning every
intermediate of the annotation and the inference under them beside those: on
`Init`, 5.06 M permanent nodes on top of the parse's 6.14 M, **+82 %**.  So
phase A opens the scratch tier as phase B does, and the handles that leave the
step are **promoted** into the persistent tier first — a memoised structural
copy, `Arena/Promote.lean`, run on the constants the step installed and on the
`PendingCheck` it recorded.  `annotStep` is that bracket; `annotStepGo` is the
four arms it wraps.

`checkDeclsPure` gets the same bracket, in `checkDeclStep`.  It is the
theorem's shape and Theorem 1 is stated about it, and that is precisely why:
the tier regime is where every term the checker builds lives, so the two folds
must be one algorithm under it and differ only in their phase structure.

What is NOT bracketed is `checkDecl` itself — a bracket belongs to a FOLD
STEP, and `checkDecl` is also called from inside one (`annotStepGo`'s
fall-through clause, for the kinds whose check is not separable from their
install: axioms, basis and quotient blocks, inductive blocks and the
`Nat`-operation and `reduce*` pin gates).  Those install what they check, and
the enclosing step promotes the whole installed block.

## The pins are interned at startup

DESIGN §8.6 P2d: "intern con-leche's `natOpPinSets` `Expr`s into the
persistent tier at startup — a one-time tree walk", and "intern con-leche's
`BasisKind.declsA` at startup the same way".  `internAllPins` below is that
walk, and it is what makes every later `pin`/`internCI` of the same datum
return the PERSISTENT handle whatever tier is live (DESIGN §8.3: `intern`
probes the persistent table first).  Without it a reserved name first
interned inside a scratch tier would compare unequal to the stream's own
persistent copy of it, which is the one way hash-consing can go wrong across
the tier boundary.
-/
import ConRon.Arena.DeclCheck
import ConRon.Arena.Inductives
import ConRon.Arena.Promote

namespace ConRon.Arena

open ConLeche

/-! ## The pinned basis install -/

/-- con-leche: ConLeche/Kernel/Checker.lean:427-437 checkBasisDecl —
**install the pinned (pre-annotated) basis block.**  The three records that
install one — the fold's own `basisDecl` kind, a stream block `basisPinHit`
recognises and a quotient record `quotPinHit` recognises — share this body.
The quotient block's types mention the pinned equality former, which is why
it requires the `Eq` basis first. -/
def checkBasisDecl (fe : IFEnv) (kind : BasisKind) : AM IFEnv := do
  if kind == .quotK then do
    let en ← pin eqName
    unless fe.find? en == some (← eqA) do
      fail (.notImplemented "quotient basis requires the pinned Eq basis")
  installBasisDecls fe (← BasisKind.declsA kind)

/-! ## One declaration -/

/-- con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl — **check a
single declaration, extending the environment on success.**  Clause for
clause; `env : Env` is the index (`Arena/Core.lean`'s deviation 1), and the
`.indDecl` arm's route choice is `Arena/Inductives.lean`'s seam. -/
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
    if (← natOpNames).contains cv.name then do
      let deps ← natOpDeps cv.name
      unless (← natOpGuard fe2 cv.name) && (← natOpStoredOkAll fe2 deps) do
        fail (.notImplemented
          s!"nonstandard structural Nat operation environment \
            ({← readName cv.name})")
      match fe2.find? cv.name with
      | some (.defnInfo _ value' _) => do
        let eqs ← natOpEquations 0 cv.name
        let ok ← certifyNatEqs mode fe (← substConst0Pairs cv.name value' eqs)
        unless ok do
          fail (.notImplemented
            s!"nonstandard structural Nat operation ({← readName cv.name})")
      | _ => fail (.internal
          s!"structural Nat operation not stored ({← readName cv.name})")
    -- WF-recursive `Nat` pins (`Nat.div`/`Nat.mod`): the stored value must be
    -- definitionally equal to some committed pin variant, and that variant's
    -- certificates must check.  No variant matching is a decline.
    if (← natDivModNames).contains cv.name then
      checkDivModPin mode pins fe fe2 cv.name
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
      checkReducePin mode fe fe2 cv.name value
    pure fe2
  | .axiomDecl cv => do
    -- **`Quot.sound` is the pinned quotient BLOCK's own record**: the export
    -- writes it as an ordinary axiom record beside the four `#QUOT` ones, so
    -- it arrives here — compared with the pin and installing NOTHING of its
    -- own, and DECLINING when it does not match.  The comparison precedes the
    -- common checks because the name is a reserved basis name: this record IS
    -- the pinned block's, not a redeclaration of it.
    if cv.name == (← pin quotSoundName) then do
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
          s!"unsupported Lean.trustCompiler shape ({← readName cv.name})")
      else if cvA.name == (← ofReduceNatName) || cvA.name == (← ofReduceBoolName) then
        -- The pinned `ofReduce*` axioms: over the pinned `Eq` basis, the
        -- element inductive and the identity-certified reduce opaque,
        -- `∀ a b, reduce a = b → a = b` interprets to an inhabited
        -- proposition.
        if ← ofReduceAxOk fe cvA then
          pure (fe.push (.axiomInfo cvA))
        else fail (.notImplemented
          s!"unsupported compiler-trust axiom environment ({← readName cv.name})")
      else if cvA.name == (← propextName) || cvA.name == (← choiceName) then
        fail (.notImplemented
          s!"standard axiom shape mismatch ({← readName cv.name})")
      else if cvA.name == (← pin sorryAxName) then
        -- `sorryAx` is the one axiom the checker tolerates as a DECLARATION:
        -- the record is skipped and the run continues, and any USE of the
        -- name declines at the record that uses it.
        pure fe
      else
        fail (.notImplemented s!"non-standard axiom ({← readName cv.name})")
  | .basisDecl kind => checkBasisDecl fe kind
  | .indDecl block nP => do
    -- **THE PINNED BASIS BLOCKS**: a stream's `Nat` block arrives as an
    -- ordinary `indDecl` and is recognised HERE.  A block under a pinned name
    -- that does not match falls through to the ordinary route, where
    -- `checkConstantVal`'s reserved-name check REJECTS it.
    match ← basisPinHit block with
    | some kind => checkBasisDecl fe kind
    | none => Inductives.checkIndDecl mode fe block nP
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

/-- con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure — **one
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

/-- con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure — check a
list of declarations in order, starting from the empty environment.  THE
THEOREM'S SHAPE (module note): one step per record, install and check
together.  con-leche's `ds.foldlM (checkDecl mode ops pins) Env.empty` takes a
closure, which DESIGN §3.4 forbids, so the fold is an explicit list
recursion. -/
def checkDeclsPureGo (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) :
    List IDeclaration → AM IFEnv
  | [] => pure fe
  | d :: ds => do checkDeclsPureGo mode pins (← checkDeclStep mode pins fe d) ds

/-- con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure — the fold
from the empty environment. -/
def checkDeclsPure (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : List IDeclaration) : AM IFEnv :=
  checkDeclsPureGo mode pins (mkIFEnv IEnv.empty) ds

/-! ## The two-phase fold the binary runs -/

/-- con-leche: ConLeche/Cached/Installed.lean:185-195 annotDeclStep
con-leche: ConLeche/Cached/Installed.lean:429-436 checkPendingList
**The state a FAILING fold step hands back**, and the reason it is not the
pre-step state.

con-leche's two fold steps live in `StateT CState (Except (CheckError × Nat))`
and their error arm is `.error (e, i)` — the state is *dropped*, because
`Except` carries none.  (B) has ONE monad (DESIGN §8.4) whose error type is
`CheckError`, so the position has to travel as a VALUE, and the error arm
therefore has to produce *some* state.  Task #97d wrote the pre-step state `s`
there, which reads as "restore".  It is not a restore that anything observes —
both folds abandon the walk on an error, `installThenCheck` returns
`.error`, `runPipelineTail` renders the message and `runPipeline` /
`runPipelineIO` discard the state — but it is a second reference to the whole
`AState`, held across the entire step, so **every store append, every cache
insert and every memo insert inside that step ran at refcount 2 and copied**
(task #97g: `lean_inc_ref(s)` before the call in `Checker.c`, 83 % of the run
in `lean_copy_expand_array` + `lean_del_core_other`).

So the arm hands back the EMPTY state — which is what con-leche's arm means
(no state at all) and what the Rust twin will do (an `Err` return whose
`&mut` state the caller stops using).  Nothing on the error path reads it. -/
def AState.abandoned : AState := AState.init EStore.empty

/-- con-leche: ConLeche/Cached/Installed.lean:83-91 PendingCheck — a phase-A
record awaiting its phase-B check: the datum that crosses the install/check
seam, the fold position of the declaration (its error tag) and the environment
counter at the install. -/
structure PendingCheck where
  vg : ValueGroup
  pos : Nat
  vis : Nat
  deriving Inhabited

/-- con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC — phase A's
step body: annotate-and-install for the three value kinds, the ordinary step
`checkDecl` for everything else.

**The body, not the step** — `annotStep` below is this under the
per-declaration bracket, and the split exists so the bracket is written ONCE
for the four arms instead of four times (DESIGN §8.3, "Phase A runs in the
scratch tier too, with promotion").  What the body returns is what a step
LEAVES BEHIND: the extended environment, and — for the three value kinds — the
`ValueGroup` phase B will check.  The fold position and the environment
counter the pending record carries are the bracket's to supply; it reads the
counter BEFORE the step, which is both con-leche's own RC-linearity note (read
it after the push and the push copies the whole index) and what makes the
promotion's `k` computable without holding `fe` across the step. -/
def annotStepGo (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) :
    IDeclaration → AM (IFEnv × Option ValueGroup)
  | .defnDecl cv value hint => do
    if (← natOpNames).contains cv.name || (← natDivModNames).contains cv.name then
      pure (← checkDecl mode pins fe (.defnDecl cv value hint), none)
    else do
      let cvA ← installConstantVal mode fe cv
      let jv ← installValue mode fe cvA value
      pure (fe.push (.defnInfo cvA jv hint), some ⟨.defn, cvA, jv⟩)
  | .thmDecl cv value => do
    -- a theorem installs BY STATEMENT: the header's install half only; the
    -- value is recorded raw and never touched here (phase B annotates it), so
    -- phase A never enters a theorem's body
    let cvA ← installConstantVal mode fe cv
    pure (fe.push (.thmInfo cvA value), some ⟨.thm, cvA, value⟩)
  | .opaqueDecl cv value => do
    if (← reduceOpNames).contains cv.name then
      pure (← checkDecl mode pins fe (.opaqueDecl cv value), none)
    else do
      let cvA ← installConstantVal mode fe cv
      let jv ← installValue mode fe cvA value
      pure (fe.push (.axiomInfo cvA), some ⟨.opaque, cvA, jv⟩)
  | pd => do
    pure (← checkDecl mode pins fe pd, none)

/-- con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC — **phase A's
step, bracketed**; `i` is the fold position the record is tagged with.

**The bracket, and why phase A has one** (DESIGN §8.3, "Phase A runs in the
scratch tier too, with promotion", the coordinator's amendment after task
#97-P4f's measurement).  Task #97d ran phase A in the PERSISTENT tier, on the
reading that the install writes exactly the terms the environment keeps.  It
does — but it does not write ONLY those: `installConstantVal` and
`installValue` annotate, and annotation infers, and inference reduces, and
every intermediate of all of that was interned permanently beside them.
Measured on `Init`: 5.06 M permanent nodes on top of the parse's 6.14 M,
**+82 %**, and con-ron's own peak RSS ×3.9.  con-leche and con-ron get the
same effect from GC; the arena's answer is con-leche #64's, and it is the
bracket phase B already has with one operation added at its end:

    flushCaches; enterScratch; <the step>; promote; dropScratch

`promote` (`Arena/Promote.lean`) is the memoised structural copy scratch →
persistent, run on **exactly what leaves the step**: the `k` constants the
step installed (`promoteNew`, `k` from the counter read before it) and the
pending record (`promoteVG` — an `opaque`'s value is not in the environment,
so the seam has to be promoted beside it, at the SAME memo, so that the
sharing between a header's type and its value survives the copy).  A
persistent handle promotes to itself, so a record that installs what the parse
already built pays one tier-bit test per handle.  After it the environment and
the `PendingCheck`s name persistent handles only, which is what lets
`dropScratch` take the tier — and it must run after the step and before the
drop: the scratch nodes are gone once the tier is dropped.

**The flush stays where con-leche puts it, at the head** — `annotStepC`
reaches its four arms through `annotValueC` (`Cached/Installed.lean:139`), the
`.thmDecl` arm's own `flushC` (`:168`) and `checkDeclStepC`
(`Cached/ParsedC.lean:279-282`, "one step of the converted-declaration fold:
flush, then check"), so con-leche enters every phase-A record with EMPTY
caches (task #97g's item 4).  `dropScratch` flushes too — no cache row may
name a handle of the tier it drops — so what the head flush covers is the
FIRST record of the fold, whose caches are whatever `internAllPins` left. -/
def annotStep (mode : CheckMode) (pins : List INatOpPinSet) (i : Nat)
    (fe : IFEnv) (pend : Array PendingCheck) (pd : IDeclaration) :
    AM (IFEnv × Array PendingCheck) := do
  let vis := fe.visibleBelow
  flushCaches
  enterScratch
  let (fe, vg?) ← annotStepGo mode pins fe pd
  let k := fe.visibleBelow - vis
  match vg? with
  | none => do
    let (_, fe) ← promoteNew PMemo.empty coreWalkFuel k fe
    dropScratch
    pure (fe, pend)
  | some vg => do
    let (m, vg) ← promoteVG PMemo.empty coreWalkFuel vg
    let (_, fe) ← promoteNew m coreWalkFuel k fe
    dropScratch
    pure (fe, pend.push ⟨vg, i, vis⟩)

/-- con-leche: ConLeche/Cached/Installed.lean:185-195 annotDeclStep — phase
A's step with the position carried and the error tagged: a failing step
reports the `CheckError` together with `i`, the fold position of the
declaration that failed.

con-leche changes monad here (`StateT CState (Except (CheckError × Nat))`);
(B) has ONE monad (DESIGN §8.4), so the tag is produced as a VALUE by reading
the step's own outcome — the treatment task #97e gives the parser's two
position-carrying failures. -/
def annotDeclStep (mode : CheckMode) (pins : List INatOpPinSet)
    (p : Nat × IFEnv × Array PendingCheck) (pd : IDeclaration) :
    AM (Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck)) := fun s =>
  match annotStep mode pins p.1 p.2.1 p.2.2 pd s with
  | .ok ((fe', pend'), s') => .ok (.ok (p.1 + 1, fe', pend'), s')
  | .error e => .ok (.error (e, p.1), AState.abandoned)

/-- con-leche: ConLeche/Cached/Installed.lean:450-455 checkDecls — phase A as
a fold over the records.  con-leche's `Array.foldlM` takes a closure; DESIGN
§3.4's rule for a `List` fold is an explicit recursion. -/
def annotFold (mode : CheckMode) (pins : List INatOpPinSet)
    (p : Nat × IFEnv × Array PendingCheck) :
    List IDeclaration →
    AM (Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck))
  | [] => pure (.ok p)
  | d :: ds => do
    match ← annotDeclStep mode pins p d with
    | .error e => pure (.error e)
    | .ok p' => annotFold mode pins p' ds

/-- con-leche: ConLeche/Cached/Installed.lean:260-274 checkPending — **phase
B's check of one record**, against the prefix view `fe.restrictTo pc.vis`,
from a fresh memo state.

**Phase B's half of the per-declaration bracket** (DESIGN §8.3, module note):
the scratch tier is turned on, `checkValueGroup` runs the inference and the
conversion, and the tier — with every node they appended and every cache row
naming one — is dropped.  Nothing crosses back, so there is nothing to
promote: phase B's business is exactly what a declaration does NOT keep, which
is what made phase B the easy half and phase A the one that needed
`Arena/Promote.lean`.  con-leche's `flushC` at the same place drops its memo
tables whole, and so does `dropScratch` (task #97f's amendment). -/
def checkPending (mode : CheckMode) (fe : IFEnv) (pc : PendingCheck) :
    AM Unit := do
  enterScratch
  checkValueGroup mode (fe.restrictTo pc.vis) pc.vg
  dropScratch

/-- con-leche: ConLeche/Cached/Installed.lean:429-436 checkPendingList — phase
B as a pure walk: every record checked from a fresh memo state, a failure
tagged with the record's fold position. -/
def checkPendingList (mode : CheckMode) (fe : IFEnv) :
    List PendingCheck → AM (Except (CheckError × Nat) Unit)
  | [] => pure (.ok ())
  | pc :: rest => fun s =>
    match checkPending mode fe pc s with
    | .ok ((), s') => checkPendingList mode fe rest s'
    | .error e => .ok (.error (e, pc.pos), AState.abandoned)

/-- con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls — **the
declaration fold the binary runs**: install every record (phase A), check
every recorded declaration (phase B), return the environment.  The `× Nat` of
the error is the failure's POSITION in the fold. -/
def installThenCheck (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : Array IDeclaration) : AM (Except (CheckError × Nat) IFEnv) := do
  match ← annotFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList with
  | .error e => pure (.error e)
  | .ok (_, fe, pend) =>
    match ← checkPendingList mode fe pend.toList with
    | .error e => pure (.error e)
    | .ok () => pure (.ok fe)

/-- con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls — the fold's
failure, with its POSITION rendered into the message.  con-leche's driver
reports the declaration by indexing the record array it already holds
(`Main.lean:461-711`); the seam of (B) has no position channel
(`Arena/Main.lean`'s note), so the position goes into the text — beside
`Frontend.atLine`, which does the same for the PARSE's position and must not
be confused with it: a line number and a fold position are different
numbers. -/
def atDecl : CheckError → Nat → CheckError
  | .notImplemented w, n => .notImplemented s!"{w} (declaration {n})"
  | .invalid w, n => .invalid s!"{w} (declaration {n})"
  | .internal w, n => .internal s!"{w} (declaration {n})"
  | .native w, n => .native s!"{w} (declaration {n})"

/-! ## The startup walk -/

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
**The one-time tree walk of DESIGN §8.6 P2d**: every datum the checker
compares a stream record against, interned into the tier that is live at the
call — which, at the driver's call, is the persistent one.

The six basis blocks in both forms (the RAW ones `basisPinHit` and
`quotPinHit` compare against, the ANNOTATED ones `checkBasisDecl` installs),
the standard and compiler-trust axiom pins, the reserved names the guards
compare by handle, and the `Nat`-operation pin variants, whose interned form
is the checker's pin-list parameter (con-leche's task #304). -/
def internAllPins (pins : List NatOpPinSet) : AM (List INatOpPinSet) := do
  let _ ← BasisKind.decls .eqK;    let _ ← BasisKind.declsA .eqK
  let _ ← BasisKind.decls .natK;   let _ ← BasisKind.declsA .natK
  let _ ← BasisKind.decls .punitK; let _ ← BasisKind.declsA .punitK
  let _ ← BasisKind.decls .emptyK; let _ ← BasisKind.declsA .emptyK
  let _ ← BasisKind.decls .falseK; let _ ← BasisKind.declsA .falseK
  let _ ← BasisKind.decls .quotK;  let _ ← BasisKind.declsA .quotK
  let _ ← iffA; let _ ← iffIntroA; let _ ← iffRecA
  let _ ← nonemptyA; let _ ← nonemptyIntroA; let _ ← nonemptyRecA
  let _ ← propextA; let _ ← choiceA
  let _ ← trueCvA; let _ ← trueIntroCvA; let _ ← trustCompilerA; let _ ← boolCvA
  let _ ← reduceNatCvA; let _ ← reduceBoolCvA
  let _ ← ofReduceNatA; let _ ← ofReduceBoolA
  let _ ← reduceNatDeclPin; let _ ← reduceBoolDeclPin
  let _ ← reservedBasisNames
  let _ ← natOpNames; let _ ← natDivModNames; let _ ← reduceOpNames
  let _ ← pin sorryAxName; let _ ← pin quotSoundName
  internPinSets pins

end ConRon.Arena
