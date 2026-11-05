/-
# `ConRon.Arena.Checker` — the declaration fold, over handles

The twin of `ConLeche/Cached/Installed.lean`'s two-phase `checkDecls`, over
`Arena/CheckDecl.lean`'s `checkDecl` / `checkDeclsPure` (con-leche's
`Kernel/CheckDecl.lean`, which upstream moved out of `Kernel/Checker.lean`;
the Rust keeps both folds in `arena::checker`).

## Two folds, and which is which

con-leche has both, and so does (B), because they are different things:

* **`checkDeclsPure`** is the THEOREM's shape — `ConLeche/Model/Fold.lean`'s
  `checkDeclsPure_sound_of` consumes it, and DESIGN §8.2's Theorem 1 folds
  `checkDecl` over the stream.  One step per record, install and check
  together.
* **`installThenCheck`** is what the BINARY runs (con-leche's driver,
  `ConLeche/Driver/Run.lean`'s `checkDeclsIO`): phase A installs every record,
  guarding its header and its value but not inferring, and pushes an inductive
  block as stored (`Arena/Inductives/StoredInstall.lean`); phase B runs the jobs
  in fold order: each recorded declaration's check against the PREFIX VIEW it was
  installed at, and each block's checked install at the environment it was
  installed at, compared with its stored pushes (`blockCheck`).  con-leche proves
  the two are the same accept (`fullyChecked_checkDecls`, `Verify/Cached/Defer.lean`);
  the arena's two call the same `checkDecl` pieces, which is what keeps them the
  same computation.

**The twin has one environment value per job, and no base.**  The Rust's phase-B
environment has two tiers: phase A's index frozen into the `PersTier`, and an own
layer per job (`arena::env`'s `IFEnv` note, `arena::checker::block_check`).  Here a
value check reads `fe.restrictTo pc.vis` as it always has, and a block job holds
its own `IFEnv` (`BlockCheck.view`): `fe` as the block found it, with an empty
`env`, so that what the job pushes is `W'.env`.  A lookup answers the same on the
two: the own layer, then the base below the block's counter, is `fe`'s index at
the block, because no install overwrites a row (a taken name stops phase A).

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
intermediate of the inference under them beside those: on
`Init`, 5.06 M permanent nodes on top of the parse's 6.14 M, **+82 %**.  So
phase A opens the scratch tier as phase B does, and the handles that leave the
step are **promoted** into the persistent tier first — a memoised structural
copy, `Arena/Promote.lean`, run on the constants the step installed and on the
`PendingCheck` it recorded.  `installStep` is that bracket; `installStepGo` is the
four arms it wraps.

`checkDeclsPure` gets the same bracket, in `checkDeclStep`.  It is the
theorem's shape and Theorem 1 is stated about it, and that is precisely why:
the tier regime is where every term the checker builds lives, so the two folds
must be one algorithm under it and differ only in their phase structure.

What is NOT bracketed is `checkDecl` itself — a bracket belongs to a FOLD
STEP, and `checkDecl` is also called from inside one (`installStepGo`'s
fall-through clause, for the kinds whose check is not separable from their
install: axioms, basis and quotient blocks and the `Nat`-operation and `reduce*`
pin gates).  Those install what they check, and the enclosing step promotes the
whole installed block.  An inductive block's stored install has brackets of its
own (`Arena/Inductives/StoredInstall.lean`'s note).

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
module

public import ConRon.Arena.CheckDecl
public import ConRon.Arena.Inductives.StoredInstall

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## The two-phase fold the binary runs -/

/-- con-leche: ConLeche/Cached/Installed.lean:179-200 installDeclStep
con-leche: ConLeche/Cached/Installed.lean:308-315 checkPendingList
**The state a FAILING fold step hands back**, and the reason it is not the
pre-step state.

con-leche's two fold steps live in `Except (CheckError × Nat)` (phase A's
`installDeclStep` installs every record from a fresh memo state since con-leche
task #329, P0) and their error arm is `.error (e, i)` — no state comes back,
because `Except` carries none.  (B) has ONE monad (DESIGN §8.4) whose error type is
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

/-- con-leche: ConLeche/Cached/Installed.lean:91-99 PendingCheck — a phase-A
record awaiting its phase-B check: the datum that crosses the install/check
seam, the fold position of the declaration (its error tag) and the environment
counter at the install. -/
structure PendingCheck where
  vg : ValueGroup
  pos : Nat
  vis : Nat
  deriving Inhabited

/-- con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC — phase A's
step body: guard-and-install for the three value kinds, the ordinary step
`checkDecl` for everything else.

**The body, not the step** — `installStep` below is this under the
per-declaration bracket, and the split exists so the bracket is written ONCE
for the four arms instead of four times (DESIGN §8.3, "Phase A runs in the
scratch tier too, with promotion").  What the body returns is what a step
LEAVES BEHIND: the extended environment, and — for the three value kinds — the
`ValueGroup` phase B will check.  The fold position and the environment
counter the pending record carries are the bracket's to supply; it reads the
counter BEFORE the step, which is both con-leche's own RC-linearity note (read
it after the push and the push copies the whole index) and what makes the
promotion's `k` computable without holding `fe` across the step. -/
def installStepGo (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) :
    IDeclaration → AM (IFEnv × Option ValueGroup)
  | .defnDecl cv value hint => do
    if (← natOpNames).contains cv.name || (← natDivModNames).contains cv.name then
      pure (← checkDecl mode pins fe (.defnDecl cv value hint), none)
    else do
      installHeader fe cv
      installValueGuards fe cv value
      pure (fe.push (.defnInfo cv value hint), some ⟨.defn, cv, value⟩)
  | .thmDecl cv value => do
    -- a theorem installs BY STATEMENT: the header's install half only, the
    -- constant pushed with its statement only (con-leche task #329 THMVAL);
    -- the value is recorded raw and never touched here (phase B guards it),
    -- so phase A never enters a theorem's body
    installHeader fe cv
    pure (fe.push (.thmInfo cv), some ⟨.thm, cv, value⟩)
  | .opaqueDecl cv value => do
    if (← reduceOpNames).contains cv.name then
      pure (← checkDecl mode pins fe (.opaqueDecl cv value), none)
    else do
      installHeader fe cv
      installValueGuards fe cv value
      pure (fe.push (.axiomInfo cv), some ⟨.opaque, cv, value⟩)
  | pd => do
    pure (← checkDecl mode pins fe pd, none)

/-- con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC — **phase A's
step, bracketed**; `i` is the fold position the record is tagged with.

**The bracket, and why phase A has one** (DESIGN §8.3, "Phase A runs in the
scratch tier too, with promotion", the coordinator's amendment after task
#97-P4f's measurement).  Task #97d ran phase A in the PERSISTENT tier, on the
reading that the install writes exactly the terms the environment keeps.  It
does — but it did not write ONLY those: the install annotated (until
con-leche's task #342), and annotation inferred, and inference reduced, and
every intermediate of all of that was interned permanently beside them.
Measured on `Init`: 5.06 M permanent nodes on top of the parse's 6.14 M,
**+82 %**, and con-ron's own peak RSS ×3.9.  con-leche and con-ron get the
same effect from GC; the arena's answer is con-leche #64's, and it is the
bracket phase B already has with one operation added at its end:

    flushCaches; enterScratch; <the step>; promote; dropScratch

`promote` (`Arena/Promote.lean`) is the memoised structural copy scratch →
persistent, run on **exactly what leaves the step**: the `k` constants and the
`kt` projection tables the step installed (`promoteNew`, `k` and `kt` from the
counter and the table count read before it) and the
pending record (`promoteVG` — an `opaque`'s value is not in the environment,
so the seam has to be promoted beside it, at the SAME memo, so that the
sharing between a header's type and its value survives the copy).  A
persistent handle promotes to itself, so a record that installs what the parse
already built pays one tier-bit test per handle.  After it the environment and
the `PendingCheck`s name persistent handles only, which is what lets
`dropScratch` take the tier — and it must run after the step and before the
drop: the scratch nodes are gone once the tier is dropped.

**The flush stays where con-leche puts it, at the head** — `installStepC`
reaches its four arms through `installGuardsC`, the `.thmDecl` arm's own
`flushC` and `checkDeclStepC`
(`Cached/ParsedC.lean:279-282`, "one step of the converted-declaration fold:
flush, then check"), so con-leche enters every phase-A record with EMPTY
caches (task #97g's item 4).  `dropScratch` flushes too — no cache row may
name a handle of the tier it drops — so what the head flush covers is the
FIRST record of the fold, whose caches are whatever `internAllPins` left. -/
def installStep (mode : CheckMode) (pins : List INatOpPinSet) (i : Nat)
    (fe : IFEnv) (pend : Array PendingCheck) (pd : IDeclaration) :
    AM (IFEnv × Array PendingCheck) := do
  let vis := fe.visibleBelow
  let nt := fe.env.tables.length
  flushCaches
  enterScratch
  let (fe, vg?) ← installStepGo mode pins fe pd
  let k := fe.visibleBelow - vis
  let kt := fe.env.tables.length - nt
  match vg? with
  | none => do
    let (_, fe) ← promoteNew PMemo.empty coreWalkFuel k kt fe
    dropScratch
    pure (fe, pend)
  | some vg => do
    let (m, vg) ← promoteVG PMemo.empty coreWalkFuel vg
    let (_, fe) ← promoteNew m coreWalkFuel k kt fe
    dropScratch
    pure (fe, pend.push ⟨vg, i, vis⟩)

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:51-57 BlockCheck
**A block's job of the check phase**: the view its checked install runs at (the
environment as the block found it, with an empty `env`, so that what the job pushes
is the view's own), the block, its parameter count, its fold position (the error
tag), and what the stored install pushed: the constants `L` and the tables `Q`, in
install order. -/
structure BlockCheck where
  view : IFEnv
  block : List IConstantInfo
  nP : Nat
  pos : Nat
  L : List IConstantInfo
  Q : List IProjTable

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:121-127 installStepG
**Phase A's step on an inductive block**: the stored install, whose pushes the job
records.  No value check is recorded: the block's verdict is its job's.  The caches
go on the way out too, because a block the recogniser does not read has no bracket:
every phase-A step leaves them empty. -/
def installBlockStep (mode : CheckMode) (i : Nat) (fe : IFEnv) (D : Array BlockCheck)
    (block : List IConstantInfo) (nP : Nat) : AM (IFEnv × Array BlockCheck) := do
  let nc := fe.env.consts.length
  let nt := fe.env.tables.length
  flushCaches
  let fe₂ ← storedInstall mode fe block nP
  flushCaches
  let L := (fe₂.env.consts.take (fe₂.env.consts.length - nc)).reverse
  let Q := (fe₂.env.tables.take (fe₂.env.tables.length - nt)).reverse
  pure (fe₂, D.push ⟨{ fe with env := IEnv.empty }, block, nP, i, L, Q⟩)

/-- con-leche: ConLeche/Cached/Installed.lean:179-200 installDeclStep
con-leche: ConLeche/Verify/Cached/Defer.lean:108-110 deferredBlock?
Phase A's step with the position carried and the error tagged: a failing step
reports the `CheckError` together with `i`, the fold position of the declaration
that failed.  An inductive block is installed as stored (`installBlockStep`), every
other record by its ordinary step.

**The `And` pin comes first** (con-leche's ANDPIN, `andPinOk`): a record that
declares `And`, `And.intro` or `And.rec` and is not the toolchain's `And`
block is rejected here, whatever its kind, ahead of the kind dispatch and
outside the scratch bracket.

con-leche changes monad here (`Except (CheckError × Nat)`, each record
installed from a fresh memo state since its task #329; the twin threads its
`AState`, whose per-declaration caches the bracket flushes, so the store and
the level memos alone cross a record — the port's own memory discipline, not a
verdict); (B) has ONE monad (DESIGN §8.4), so the tag is produced as a VALUE by reading
the step's own outcome — the treatment task #97e gives the parser's two
position-carrying failures. -/
def installDeclStep (mode : CheckMode) (pins : List INatOpPinSet)
    (p : Nat × IFEnv × Array PendingCheck × Array BlockCheck) (pd : IDeclaration) :
    AM (Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck × Array BlockCheck)) := fun s =>
  match andPinOk pd s with
  | .ok (true, s₁) =>
    match pd with
    | .indDecl block nP =>
      match installBlockStep mode p.1 p.2.1 p.2.2.2 block nP s₁ with
      | .ok ((fe', D'), s') => .ok (.ok (p.1 + 1, fe', p.2.2.1, D'), s')
      | .error e => .ok (.error (e, p.1), AState.abandoned)
    | _ =>
      match installStep mode pins p.1 p.2.1 p.2.2.1 pd s₁ with
      | .ok ((fe', pend'), s') => .ok (.ok (p.1 + 1, fe', pend', p.2.2.2), s')
      | .error e => .ok (.error (e, p.1), AState.abandoned)
  | .ok (false, _) =>
    .ok (.error (.invalid "`And` must be the standard `And`", p.1), AState.abandoned)
  | .error e => .ok (.error (e, p.1), AState.abandoned)

/-- con-leche: ConLeche/Cached/Installed.lean:317-334 checkDecls — phase A as
a fold over the records.  con-leche's `Array.foldlM` takes a closure; DESIGN
§3.4's rule for a `List` fold is an explicit recursion. -/
def installFold (mode : CheckMode) (pins : List INatOpPinSet)
    (p : Nat × IFEnv × Array PendingCheck × Array BlockCheck) :
    List IDeclaration →
    AM (Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck × Array BlockCheck))
  | [] => pure (.ok p)
  | d :: ds => do
    match ← installDeclStep mode pins p d with
    | .error e => pure (.error e)
    | .ok p' => installFold mode pins p' ds

/-- con-leche: ConLeche/Cached/Installed.lean:258-276 checkPending — **phase
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

/-- con-leche: ConLeche/Cached/Installed.lean:308-315 checkPendingList — phase
B as a pure walk: every record checked from a fresh memo state, a failure
tagged with the record's fold position. -/
def checkPendingList (mode : CheckMode) (fe : IFEnv) :
    List PendingCheck → AM (Except (CheckError × Nat) Unit)
  | [] => pure (.ok ())
  | pc :: rest => fun s =>
    match checkPending mode fe pc s with
    | .ok ((), s') => checkPendingList mode fe rest s'
    | .error e => .ok (.error (e, pc.pos), AState.abandoned)

/-! ## The block jobs, and the check phase's jobs in fold order -/

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:68-70 pushesAgree
**The checked install pushed `L` and `Q`** onto a view whose own environment is
empty: its constants and tables, in install order, compared pointer-first. -/
def pushesAgree (W' : IFEnv) (L : List IConstantInfo) (Q : List IProjTable) : Bool :=
  listBeqBy IConstantInfo.beqP W'.env.consts.reverse L &&
    listBeqBy IProjTable.beqP W'.env.tables.reverse Q

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:77-84 blockCheck
**The block's job**: its checked install at the view, from fresh caches and an empty
scratch tier, and the comparison of its pushes with the stored install's.  A
difference is an internal error: the stored reading is not the checked install's, a
defect of the reader, not of the stream.  Nothing the job builds outlives it.  The
message drops con-leche's interpolated block name (§3.1). -/
def blockCheck (mode : CheckMode) (pins : List INatOpPinSet) (b : BlockCheck) : AM Unit := do
  enterScratch
  let W' ← checkDecl mode pins b.view (.indDecl b.block b.nP)
  unless pushesAgree W' b.L b.Q do
    fail (.internal "inductive block : the stored install's constants or tables are not the checked install's")
  dropScratch

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:217-221 blockFailure
**The first failing block job**, in fold order, with its position. -/
def blockFailure (mode : CheckMode) (pins : List INatOpPinSet) :
    List BlockCheck → AM (Option (CheckError × Nat))
  | [] => pure none
  | b :: rest => fun s =>
    match blockCheck mode pins b s with
    | .ok ((), s') => blockFailure mode pins rest s'
    | .error e => .ok (some (e, b.pos), AState.abandoned)

/-- con-leche: ConLeche/Driver/CheckPool.lean:213-227 checkWorker — **a phase-B worker's state**:
the phase-A state with the scratch tier closed and empty, and fresh memos and
caches.  The Rust's `worker_state` builds the same thing over the FROZEN tier
(an empty store whose reads go to the `PersTier`); the twin has one store and
reads its persistent tier where it is. -/
def AState.worker (s : AState) : AState :=
  { s with store := s.store.dropScratch, memos := Memos.empty,
           caches := Caches.empty }

/-- con-leche: ConLeche/Driver/ParInstall.lean:690-808 commitLoop
**The verdict of a phase A that failed at record `i` with `e`**: the first failing
block job before it; else, at a block past its `And` pin, that block's own job (a
name was taken, or the store gave out); else `e`.  `s` is the state phase A started
from: a failing step takes the state with it, and the Rust installs the records
before `i` once more too. -/
def phaseAFailure (mode : CheckMode) (pins : List INatOpPinSet) (ds : List IDeclaration)
    (e : CheckError) (i : Nat) (s : AState) : CheckError × Nat :=
  match installFold mode pins (0, mkIFEnv IEnv.empty, #[], #[]) (ds.take i) s with
  | .ok (.ok (_, fe, _, D), s') =>
    let w := s'.worker
    match blockFailure mode pins D.toList w with
    | .ok (some f, _) => f
    | .ok (none, w') =>
      match ds[i]? with
      | some (.indDecl block nP) =>
        match andPinOk (.indDecl block nP) w' with
        | .ok (true, w'') =>
          match blockCheck mode pins
              ⟨{ fe with env := IEnv.empty }, block, nP, i, [], []⟩ w'' with
          | .error e₂ => (e₂, i)
          | .ok _ => (e, i)
        | _ => (e, i)
      | _ => (e, i)
    | .error e₂ => (e₂, i)
  | .ok (.error f, _) => f
  | .error e₂ => (e₂, i)

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:243 Job
A job: a recorded value check (`false`) or a block job (`true`), by its index in
its array. -/
abbrev Job := Bool × Nat

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:255-276 runJob
**Run a job**, the error tagged with its fold position. -/
def runJob (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (pend : Array PendingCheck) (D : Array BlockCheck) (j : Job) :
    AM (Except (CheckError × Nat) Unit) := fun s =>
  if j.1 then
    match D[j.2]? with
    | some b =>
      match blockCheck mode pins b s with
      | .ok ((), s') => .ok (.ok (), s')
      | .error e => .ok (.error (e, b.pos), AState.abandoned)
    | none => .ok (.error (.internal "check phase: no such block check", 0), AState.abandoned)
  else
    match pend[j.2]? with
    | some pc =>
      match checkPending mode fe pc s with
      | .ok ((), s') => .ok (.ok (), s')
      | .error e => .ok (.error (e, pc.pos), AState.abandoned)
    | none => .ok (.error (.internal "check phase: no such record", 0), AState.abandoned)

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:281-292 jobOrder
The merge behind `jobOrder`, from positions `a` and `b`. -/
def jobOrderGo (pend : Array PendingCheck) (D : Array BlockCheck) (a b : Nat)
    (acc : Array Job) : Array Job :=
  if ha : a < pend.size then
    if hb : b < D.size then
      if D[b].pos < pend[a].pos then jobOrderGo pend D a (b + 1) (acc.push (true, b))
      else jobOrderGo pend D (a + 1) b (acc.push (false, a))
    else jobOrderGo pend D (a + 1) b (acc.push (false, a))
  else if b < D.size then jobOrderGo pend D a (b + 1) (acc.push (true, b))
  else acc
termination_by (pend.size - a) + (D.size - b)

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:281-292 jobOrder
**The jobs in fold order**: the recorded checks and the block checks, each array
sorted by position, merged (a block before a record at a larger position). -/
def jobOrder (pend : Array PendingCheck) (D : Array BlockCheck) : Array Job :=
  jobOrderGo pend D 0 0 (Array.mkEmpty (pend.size + D.size))

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:299-338 collectJobs
Phase B as a walk: every job in turn, on one state, the first failure the answer.
A worker's fold over the jobs it claimed (`PooledAccepts`, `Arena/Pooled.lean`). -/
def checkJobList (mode : CheckMode) (pins : List INatOpPinSet) (fe : IFEnv)
    (pend : Array PendingCheck) (D : Array BlockCheck) :
    List Job → AM (Except (CheckError × Nat) Unit)
  | [] => pure (.ok ())
  | j :: rest => fun s =>
    match runJob mode pins fe pend D j s with
    | .ok (.ok (), s') => checkJobList mode pins fe pend D rest s'
    | .ok (.error e, s') => .ok (.error e, s')
    | .error e => .error e

/-- con-leche: ConLeche/Driver/Run.lean:87-210 checkDeclsIO
**The declaration fold the binary runs**: install every record (phase A), run every
job (phase B), return the environment.  A failure of phase A is reported at the
first failing block job before it (`phaseAFailure`).  The `× Nat` of the error is the
failure's POSITION in the fold. -/
def installThenCheck (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : Array IDeclaration) : AM (Except (CheckError × Nat) IFEnv) := fun s =>
  match installFold mode pins (0, mkIFEnv IEnv.empty, #[], #[]) ds.toList s with
  | .ok (.error (e, i), s₁) => .ok (.error (phaseAFailure mode pins ds.toList e i s), s₁)
  | .ok (.ok (_, fe, pend, D), s₁) =>
    match checkJobList mode pins fe pend D (jobOrder pend D).toList s₁ with
    | .ok (.ok (), s₂) => .ok (.ok fe, s₂)
    | .ok (.error e, s₂) => .ok (.error e, s₂)
    | .error e => .error e
  | .error e => .error e

/-- con-leche: ConLeche/Cached/Installed.lean:317-334 checkDecls — the fold's
failure, with its POSITION rendered into the message.  con-leche's driver
reports the declaration by indexing the record array it already holds
(`ConLeche/Driver/Run.lean`'s `checkMain`); the seam of (B) has no position channel
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

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
con-leche: ConLeche/Kernel/BasisA.lean:48-54 BasisKind.declsA
**The one-time tree walk of DESIGN §8.6 P2d**: every datum the checker
compares a stream record against, interned into the tier that is live at the
call — which, at the driver's call, is the persistent one.

The six basis blocks in both forms (the RAW ones `basisPinHit` and
`quotPinHit` compare against, the STORED ones `checkBasisDecl` installs),
the standard and compiler-trust axiom pins, the reserved names the guards
compare by handle, and the `Nat`-operation pin variants, whose interned form
is the checker's pin-list parameter (con-leche's task #304).

The standard-axiom and `ofReduce*` pins are con-leche's (`iffA` … `choiceA`,
`ofReduceNatA`/`ofReduceBoolA`), compared by `matchesPin`'s plain equality. -/
def internAllPins (pins : List NatOpPinSet) : AM (List INatOpPinSet) := do
  let _ ← BasisKind.decls .eqK;    let _ ← BasisKind.declsA .eqK
  let _ ← BasisKind.decls .natK;   let _ ← BasisKind.declsA .natK
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
  let _ ← pinSorryAx; let _ ← pinQuotSound
  internPinSets pins

end ConRon.Arena
