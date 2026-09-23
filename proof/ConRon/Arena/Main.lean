import ConRon.Arena.Frontend.Prelude
import ConRon.Arena.Frontend.InModel
import ConRon.Arena.CheckerGated

/-!
# `con-ron-lean` — the arena checker's driver (DESIGN.md §8.4, task #97 P2f)

The command-line driver of **(B)**, the Lean arena checker of DESIGN.md §8:
con-leche's `Main.lean`, with the pure checker behind one function.

Its reason to exist before the checker does is the GATE.  §8.6 P2f is
"348/348 and `Init` parity", and the thing that decides that is
`scripts/diff-e2e.sh --bin=…` running the fixtures against a binary.  A
binary that speaks the command line exactly — the same flags, the same
usage text, the same 0/1/2/3 — can be put under that sweep from the first
day, and every later phase is then measured rather than argued.  The
baseline was 36 of 348 with `runPipeline` a stub; with the frontend of task
#97e behind it, 60 — and every one of the 288 that still differ is a
decline where the fold would have decided, never a wrong verdict.

    lake -C proof build con-ron-lean
    scripts/diff-e2e.sh --bin=proof/.lake/build/bin/con-ron-lean

**THE ONE SEAM.**  Everything below the command line is `runPipeline`:

    runPipeline : List ByteArray → CheckMode → List NatOpPinSet
                → Except CheckError Nat

the chunks of the input, the mode, the pin list, and out comes the
FILE's accepted declaration-record count or the error whose kind is the
exit code.  Nothing else in this module knows anything about parsing or
checking, so P2b–P2e grow the checker without touching the driver, and the
capstone of §8.2 will be a statement about this one function.  It is the
same shape as con-leche's `checkMain` ∘ `parseChunks`, minus the IO: the
heartbeat, the receipts and the diagnostics are the driver's and touch no
verdict (`Main.lean:461-711`'s own argument for why ONE loop serves the
plain run and `--progress` alike).

**What is NOT here.**  No `import ConRon.Refine`: (B) is a checker, not a
proof about the Rust one, and the two tiers meet only at Theorem 2 (§8.2).
`CheckMode` is still copied here (§8's census class (P): pure data with no
term inside) and P2d moves it into the `Kernel` twins beside the rest;
`CheckError` moved to `Arena/Monad.lean` with P2b, which needed it and gave
it the fourth constructor the store's capacity limit raises (`native`).

**con-leche IS imported, below the seam** (task #97e).  §8.7's ruling: (B)
imports con-leche's representation-free types and pure functions rather than
copying them, and since the parser landed that extends to the byte recogniser
— `ConLeche/Frontend/Scan/{Types,Fast}.lean` produces records in stream
indices with no `Expr`, `Name` or `Level` in them, so `scanLineFwd` is reused
rather than twinned (`Arena/Frontend/ExportC.lean`'s note has the check).  A
twin that imported its original's *checker* would prove nothing; a twin that
re-typed its original's byte recogniser would prove nothing either.

**Chunked reading, 4 MiB** (`ConLeche/Frontend/ExportC.lean:903-931`): the
handle is read strictly forward and never seeked, so the source may be a
pipe.  **The reads are INTERLEAVED with the parse** (task #97e part 2): each
4 MiB buffer is fed to `Frontend.chunkStep` and then dropped, so the input is
never held whole.  Part 1 read the whole file into a chunk list first, which
on `Init` was 0.33 GB of a 0.82 GB peak and on Mathlib would be 6.1 GB before
a byte is parsed.

**`runPipeline` stays the pure SPECIFICATION**, and the driver's loop is the
SAME FOLD.  `Frontend.parseChunks` is `chunkStep` folded over a list with
`chunkFinish` at its end (`parseChunksGo`); `readFold` below is the same
`chunkStep` folded over the buffers the handle hands out, ended by the same
`chunkFinish`, from the same `StateD.init` — the list and the handle differ
only in where the next buffer comes from, so a later proof equates them by
induction on the reads, which is con-leche's own
`parseChunks_eq_parseExportD`.  Everything around the fold — the prelude parse
before it and `preparePrelude` after it — is `runPipelineHead` /
`runPipelineTail`, shared verbatim by the two.
-/

namespace ConRon.Arena

open ConLeche

/-! ## `CheckMode` is con-leche's own

Task #97e's "for part 2" note item 6 left `CheckMode` as the driver's copy;
P2d retires it.  `Arena/Core.lean` and every twin below it already branch on
`ConLeche.CheckMode` (DESIGN §8.7: (B) IMPORTS con-leche's
representation-free types rather than copying them), and two spellings of one
two-constructor enum in one import closure is one too many. -/

/-- con-leche: Main.lean:48-51 ConLeche.CheckError.exitCode
The exit code of each error kind.  1 rejected, 2 declined, 3 error; 0 is
the accept and has no error to map.  The 1/2 distinction is con-leche's
and is load-bearing: a reject is a verdict about the input, a decline a
statement about the checker, and a decline is never "something
unexpectedly went wrong" — that is 3.  `native` — the arena's own fourth
kind, raised when §8.3's handle word runs out at 2^27 nodes per constructor
per tier — is a 3 for the same reason: it claims nothing about the input. -/
def CheckError.exitCode : CheckError → UInt32
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3
  | .native _ => 3

/-- con-leche: Main.lean:48-51 ConLeche.CheckError.exitCode
The message a failing run prints, beside the code above.  con-leche builds
it from the error's own `ToString`; the arena's is the same three words in
front of the same payload, plus its own for `native`. -/
def CheckError.message : CheckError → String
  | .notImplemented what => s!"declined: {what}"
  | .invalid what => s!"invalid: {what}"
  | .internal msg => s!"internal: {msg}"
  | .native what => s!"native: {what}"

/-! ## The pin list is con-leche's data, interned at startup

Task #97e left `NatOpPinSet` a one-field placeholder here; P2d replaces it
with `Arena/NatOpPinSet.lean`'s `INatOpPinSet` — the same seventeen fields
over handles — and `Arena/Checker.lean`'s `internAllPins`, the one-time tree
walk of DESIGN §8.6 P2d.

**The seam's parameter stays con-leche's `List NatOpPinSet`**, i.e. the pin
VALUES: they are representation-free data (con-leche's task #304 made the
list a parameter so that a statement about the checker can be made for an
arbitrary one), and the store they are interned into is the seam's own.  The
shipped binary passes `ConLeche.natOpPinSets`, the variants this toolchain
committed, exactly as con-leche's driver does. -/

/-- con-leche: none — the read size, 4 MiB, so a Mathlib-scale export never
materialises as one buffer and the handle stays readable as a pipe.  It is
`Frontend.chunkSize` (con-leche's `ExportC.lean:813-814`), named here so the
driver reads as con-leche's does. -/
def chunkSize : USize := Frontend.chunkSize

/-- con-leche: Main.lean:461-711 checkMain
**THE SEAM** (DESIGN.md §8.4): the whole checker, from the input's chunks
to the verdict.

`chunks` are the 4 MiB reads in order, `mode` the checking mode, `pins`
the pin-variant list; the result is the FILE's accepted
declaration-record count — con-leche's verdict number, "a property of the
INPUT" (`Main.lean:661-676`): the records the parse produced less the ones
the in-process modeller generated, which no later step moves.

**The FRONTEND half is real since task #97e**: the built-in prelude is
parsed, the stream's chunks are parsed into the persistent tier of one
`EStore`, the projection-function rewrite runs, the modeller seam is
instantiated (`Frontend.inProcessModeller`, DESIGN §8.2's unverified hook,
which delegates to con-leche's own generator on the block's denotation) and
the prepared record list is built.  What is still a stub is the FOLD, so a run
that parses cleanly ends in a decline that names the count it would have
checked.  Every verdict the frontend itself reaches — a malformed line, a
rebound index, an `unsafe` declaration, a block whose redundant fields
contradict its own records, a block the modeller declines — is already this
function's answer, with con-leche's own exit code.

P2c (the `Core` knot) and P2d (the checker and the declaration check) replace
`runPipelineTail`'s last three lines; the driver below is already what it will
be.

This is the pipeline BEFORE the parse: the built-in prelude, parsed into the
same store the stream goes into, and the parse state the stream's first chunk
is fed to.  Shared verbatim by the pure seam and by the driver's interleaved
loop. -/
def runPipelineHead (md : Frontend.Modeller) (im : Bool := true) (ce : Bool := false) :
    AM (Except (CheckError × Nat) (Frontend.PreludeIx × Frontend.StateD)) := do
  -- **The reserved-name pins, interned ONCE** (task #97-P6-4a): immediately
  -- after the state is made and before the prelude, so the scratch tier is
  -- closed and every pinned handle is persistent.
  internReservedPins
  match ← Frontend.builtinPreludeE md with
  | .error e => pure (.error e)
  | .ok pre => pure (.ok (pre, ← Frontend.StateD.init im ce))

/-- con-leche: Main.lean:461-711 checkMain
The pipeline AFTER the parse: `preparePrelude`, then **the fold** (task
#97d), then the verdict number.  Shared verbatim by the pure seam and by the
driver's interleaved loop, which is what makes the two the same computation.

The verdict number is con-leche's own, "a property of the INPUT"
(`Main.lean:661-676`): the records the parse produced less the ones the
in-process modeller generated, which no later step moves.  The fold's own
environment is discarded — an accept is the statement, not the environment.

`internAllPins` runs BEFORE the fold and while the scratch tier is still off,
which is what DESIGN §8.6 P2d means by "at startup": every pinned datum is in
the persistent cons table before any declaration's check can intern one into
a tier that is about to vanish. -/
def runPipelineTail (mode : CheckMode) (pins : List NatOpPinSet)
    (pre : Frontend.PreludeIx) (r : Frontend.ParseResultD) :
    AM (Except CheckError Nat) := do
  -- The verdict number is read HERE, before the fold, so that `r` — whose
  -- `inModelGen`, `genOwner`, `inModelDeclined`, `projRewrites` and
  -- `inModelled` the fold never looks at — dies at `preparePrelude` instead
  -- of being pinned across the whole check (DESIGN §8.4: decide the rare
  -- branch, and read what a later line needs, BEFORE the expensive step).
  let records := r.decls.size - r.genRecords
  let ds ← Frontend.preparePrelude pre r.decls
  let ipins ← internAllPins pins
  match ← installThenCheck mode ipins ds with
  | .error (e, n) => pure (.error (atDecl e n))
  | .ok _ => pure (.ok records)

/-- con-leche: Main.lean:461-711 checkMain
**THE PURE SEAM'S BODY**: the prelude, `parseChunks` (which is `chunkStep`
folded over the chunk list with `chunkFinish` at its end), and the tail.  The
driver's `readFold` is the same fold over the same steps with the buffers read
one at a time; see the module note. -/
def runPipelineM (md : Frontend.Modeller) (mode : CheckMode)
    (pins : List NatOpPinSet) (chunks : List ByteArray) (im : Bool := true)
    (ce : Bool := false) :
    AM (Except CheckError Nat) := do
  match ← runPipelineHead md im ce with
  | .error (e, n) => pure (.error (Frontend.atLine e n))
  | .ok (pre, st) =>
    match ← Frontend.parseChunksGo md st .empty 0 0 chunks with
    | .error (e, n) => pure (.error (Frontend.atLine e n))
    | .ok r => runPipelineTail mode pins pre r

/-- con-leche: Main.lean:461-711 checkMain
**THE SEAM ITSELF**: `runPipelineM` run at the empty store, with the parse's
own `(CheckError × Nat)` position folded into the message (`Frontend.atLine`)
because this signature has no position channel.

`im`/`ce` are the binary's two environment flags (`CON_LECHE_INMODEL`,
`CON_LECHE_INMODEL_CENSUS`; `crates/con-ron/src/bin/con-ron.rs` reads them
and `driver.rs` hands them to `state_d_init`), defaulting to the binary's own
defaults.  Task #97-COMPOSE's mismatch 4: until round 7 of task
#97-P3-Frontend they were hard-coded here, so a run with a non-default flag
was outside the theorem. -/
def runPipeline (chunks : List ByteArray) (mode : CheckMode)
    (pins : List NatOpPinSet) (im : Bool := true) (ce : Bool := false) :
    Except CheckError Nat :=
  match (runPipelineM Frontend.inProcessModeller mode pins chunks im ce).run
      (AState.init EStore.empty) with
  | .error e => .error e
  | .ok (r, _) => r

/-- con-leche: Main.lean:423-434 progressStride
The progress heartbeat's stride, read off `--progress[=<stride>]`.  No
flag is off; bare `--progress` is stride 1.  A value that is not a decimal
numeral, and `0` — the flag asking for no heartbeat — are usage errors
(exit 3): a run's output must be readable off its invocation, never
silently degraded. -/
def progressStride (v : String) : Except String Nat :=
  match v.toNat? with
  | some 0 => .error "--progress takes a declaration stride of at least 1 \
      (a decimal numeral); omit the flag for no heartbeat"
  | some n => .ok n
  | none => .error s!"--progress takes a declaration stride \
      (a decimal numeral of at least 1), got {repr v}"

/-- con-leche: Main.lean:436-459 jobsCount
The worker count, read off `--jobs=<n>`: a decimal numeral of at least 1.
`0` and a non-numeral are usage errors (exit 3); without the flag the
count is the machine's hardware thread count.

**The arena is single-threaded today** and the flag is accepted and
validated all the same, because `scripts/diff-e2e.sh` passes it on every
fixture and because §8.3's parallel plan is already written down: the
persistent tier is immutable in phase B and each worker owns a scratch
tier, so the count will mean what con-leche's means when P2d gets there.
An accepted-and-ignored flag is what `con-ron`'s own driver does with
`--no-mark-persistent`, for the same reason. -/
def jobsCount (v : String) : Except String Nat :=
  match v.toNat? with
  | some 0 => .error "--jobs takes a worker count of at least 1 \
      (a decimal numeral); omit the flag for one worker per hardware thread"
  | some n => .ok n
  | none => .error s!"--jobs takes a worker count \
      (a decimal numeral of at least 1), got {repr v}"

/-- con-leche: none — the millisecond-to-seconds rendering of the
heartbeat's `t=` field.  con-leche has it as `ConLeche.Cached.msSecs`,
which `scripts/provenance-skip.txt` lists as driver-only rendering the
Rust port does not carry; the arena's driver prints the same line, so it
carries the same three lines of arithmetic. -/
def msSecs (ms : Nat) : String :=
  let s := ms / 1000
  let c := (ms % 1000) / 10
  s!"{s}.{if c < 10 then "0" else ""}{c}"

/-- con-leche: ConLeche/Frontend/ExportC.lean:903-931 parseExportHandleD
**THE READ LOOP**: the handle read strictly forward, 4 MiB at a time, each
buffer fed to `Frontend.chunkStep` and then dropped; the first empty read is
its end of file and `Frontend.chunkFinish` closes the stream.  Never seeked,
never re-opened, never asked for its size — so the source may be a pipe, and
no scratch file exists anywhere (con-leche's task #180).

**This is the same fold as `Frontend.parseChunksGo`**, which the pure seam
runs over a chunk LIST: the same `chunkStep` at the same four accumulators,
the same `chunkFinish` at the end, differing only in where the next buffer
comes from.  A later proof equates the two by induction on the reads
(con-leche's `parseChunks_eq_parseExportD` is that argument), which is why
`runPipeline` keeps the list signature as the specification.

`AState` is threaded by hand rather than in a transformer stack, because the
step is `AM` (`StateT AState (Except CheckError)`, DESIGN §8.4's one monad)
and the loop is `IO`: running the step and passing its state on is what a
`StateT … IO` would compile to, without giving (B)'s own monad an `IO` layer
it must not have. -/
partial def readFold (md : Frontend.Modeller) (h : IO.FS.Handle)
    (st : Frontend.StateD) (carry : ByteArray) (lineNo total chunks : Nat)
    (s : AState) :
    IO (Except CheckError (Except (CheckError × Nat) Frontend.ParseResultD ×
      AState × Nat)) := do
  let buf ← h.read chunkSize
  if buf.isEmpty then
    match (Frontend.chunkFinish md st carry lineNo).run s with
    | .error e => pure (.error e)
    | .ok (r, s) => pure (.ok (r, s, chunks))
  else
    match (Frontend.chunkStep md st carry lineNo total buf).run s with
    | .error e => pure (.error e)
    | .ok (.error e, s) => pure (.ok (.error e, s, chunks + 1))
    | .ok (.ok (st, carry, lineNo, total), s) =>
      readFold md h st carry lineNo total (chunks + 1) s

/-- con-leche: Main.lean:461-711 checkMain
**THE SEAM, DRIVEN FROM A HANDLE**: `runPipelineHead`, then `readFold` in
place of the pure seam's `parseChunksGo`, then `runPipelineTail` — the same
three steps `runPipeline` runs, with the input never held whole.  The chunk
count comes back for the heartbeat, and so does **the moment the parse
ended** — `checkMain`'s heartbeat used to print its own clock reading AFTER
this function returned and call it "parse done", which is the whole run and
not the parse (task #97g found it measuring the fold as parse time).  The
reading is taken between `readFold` and `runPipelineTail`, which is where the
parse actually ends. -/
def runPipelineIO (h : IO.FS.Handle) (mode : CheckMode)
    (pins : List NatOpPinSet) : IO (Except CheckError Nat × Nat × Nat × Nat) := do
  let md := Frontend.inProcessModeller
  let s0 := AState.init EStore.empty
  match (runPipelineHead md).run s0 with
  | .error e => pure (.error e, 0, 0, 0)
  | .ok (.error (e, n), _) => pure (.error (Frontend.atLine e n), 0, 0, 0)
  | .ok (.ok (pre, st), s) =>
    match ← readFold md h st .empty 0 0 0 s with
    | .error e => pure (.error e, 0, 0, 0)
    | .ok (.error (e, n), _, chunks) =>
      pure (.error (Frontend.atLine e n), chunks, ← IO.monoMsNow, 0)
    | .ok (.ok r, s, chunks) =>
      let tParse ← IO.monoMsNow
      match (runPipelineTail mode pins pre r).run s with
      | .error e => pure (.error e, chunks, tParse, 0)
      | .ok (v, s') => pure (v, chunks, tParse, s'.store.persCount)

/-- con-leche: Main.lean:714-944 usage
The usage text, on stdout under `--help` and on stderr before a usage
error.  It is con-leche's, shortened to what this binary actually has and
saying plainly what it does not: the shape and the vocabulary are the same
so that a script written against one reads against the other. -/
def usage : String := String.intercalate "\n" [
  "usage: con-ron-lean [--verified|--trusted] [--jobs=<n>] [--no-pins]",
  "                    [--progress[=<stride>]] FILE.ndjson",
  "       con-ron-lean --help",
  "",
  "  (B), the Lean arena checker of con-ron's DESIGN.md section 8: con-leche's",
  "  pure checker over an append-only DAG of per-constructor handle arrays,",
  "  with con-leche's command line and con-leche's exit codes, so that",
  "  scripts/diff-e2e.sh can run the same 348 fixtures against either binary.",
  "",
  "  --verified        the default, and the mode the capstones are about.",
  "  --trusted         the unverified mode: the SAME checker bodies with the",
  "                    certification-only work switched off.  An accept in",
  "                    this mode is outside the theorem.",
  "  --jobs=<n>        the check phase's worker count (default: the machine's",
  "                    hardware thread count).  ACCEPTED AND VALIDATED, and",
  "                    today ignored: the arena checker is single-threaded",
  "                    until section 8.3's scratch-tier-per-worker plan is",
  "                    built.  0 or a non-numeral is a usage error.",
  "  --no-mark-persistent",
  "                    accepted and ignored: the mark is a Lean-runtime",
  "                    measurement switch of the shipped con-leche, and the",
  "                    arena's two tiers are not it.  It changes no verdict.",
  "  --no-pins         check with the EMPTY Nat-operation pin list instead of",
  "                    the toolchain's own.  con-ron's flag, not con-leche's,",
  "                    and the third row of scripts/diff-e2e.sh's matrix: the",
  "                    seventeen fixtures that define Nat.div then decline,",
  "                    which is the empty-list arm of the pin loop tested.",
  "  --progress[=<stride>]",
  "                    opt-in progress heartbeat on STDERR.  Bare --progress",
  "                    is stride 1.  A stride that is not a decimal numeral,",
  "                    or 0, is a usage error.  The flag may come before or",
  "                    after the other flags.",
  "  --help            print this text on STDOUT and exit 0, in any argument",
  "                    position; no input is read.",
  "",
  "EXIT CODES, con-leche's (Main.lean:15-31):",
  "  0  accepted -- every declaration checked; the verdict line names the",
  "     FILE's declaration-record count, which is a property of the input",
  "  1  rejected -- a declaration is invalid",
  "  2  declined -- the checker positively detected something it does not",
  "     support, and says which.  Never 'something went wrong'.",
  "  3  error    -- bad usage, malformed input, or an internal failure of",
  "     unclear cause",
  "",
  "STATUS.  The checker is whole: the input is parsed into the arena's",
  "persistent tier and the two-phase fold installs and checks every",
  "declaration, each check inside its own scratch tier.  Every verdict is",
  "this binary's own answer with con-leche's exit code.  DESIGN.md section",
  "8.6's P2f gate is run through this command line and is MET: all 348",
  "fixtures of scripts/diff-e2e.sh agree with con-leche, in both modes.",
  "What is NOT here is the PROOF: Theorem 1 of section 8.2 (this checker",
  "accepting implies con-leche's pure checker accepting) is phase P3."]

/-- con-leche: Main.lean:946-960 Args
The parsed command line.  `progress = 0` is "no flag given"; `jobs = none`
is "no flag given", one worker per hardware thread. -/
structure Args where
  mode : CheckMode := .verified
  progress : Nat := 0
  jobs : Option Nat := none
  noMark : Bool := false
  noPins : Bool := false
  files : Array String := #[]
  bad : Option String := none

/-- con-leche: Main.lean:962-990 parseArgs
The argument parse, clause for clause: the mode flags in either order with
the heartbeat, `=`-carrying spellings after the bare ones, an unknown
`-`-leading word a usage error, everything else a file. -/
def parseArgs : List String → Args → Args
  | [], a => a
  | "--verified" :: rest, a => parseArgs rest { a with mode := .verified }
  | "--trusted" :: rest, a => parseArgs rest { a with mode := .trusted }
  | "--progress" :: rest, a => parseArgs rest { a with progress := 1 }
  | "--no-mark-persistent" :: rest, a => parseArgs rest { a with noMark := true }
  | "--no-pins" :: rest, a => parseArgs rest { a with noPins := true }
  | s :: rest, a =>
    if s.startsWith "--progress=" then
      match progressStride (s.drop "--progress=".length).toString with
      | .ok n => parseArgs rest { a with progress := n }
      | .error msg => { a with bad := some msg }
    else if s.startsWith "--jobs=" then
      match jobsCount (s.drop "--jobs=".length).toString with
      | .ok n => parseArgs rest { a with jobs := some n }
      | .error msg => { a with bad := some msg }
    else if s == "--jobs" then
      { a with bad := some "--jobs takes a worker count: --jobs=<n>; omit the \
          flag for one worker per hardware thread" }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {s}" }
    else parseArgs rest { a with files := a.files.push s }

/-- con-leche: Main.lean:461-711 checkMain
The driver, which `main` calls in process: read the chunks, run the seam,
print the verdict.  Every VERDICT line names the mode — a `--trusted` run,
the unverified lane, must never be mistaken for a `--verified` one in a
log, whatever it says — and what the heartbeat prints between the steps
touches no verdict, which is why there is one path and not two. -/
def checkMain (file : String) (mode : CheckMode) (pins : List NatOpPinSet)
    (stride : Nat) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let h? ← try
      pure (some (← IO.FS.Handle.mk file .read))
    catch e => do
      IO.eprintln s!"con-ron-lean: {file}: {e} ({modeTag})"
      pure none
  let some h := h? | return 3
  let (verdict, chunks, tParse, nodes) ← runPipelineIO h mode pins
  if stride > 0 then
    let tRead ← IO.monoMsNow
    IO.eprintln s!"con-ron-lean: parse done: {chunks} chunks read \
      t={msSecs (tParse - t0)}s; fold t={msSecs (tRead - tParse)}s"
    -- task #97-P6-2: the PERSISTENT expression-node count at the end of the
    -- run, which after the promotion is the parse's DAG plus what the
    -- installed environment kept.  The number the Rust twin is checked
    -- against; it costs one field read and is printed only under --progress.
    IO.eprintln s!"con-ron-lean: persistent expression nodes: {nodes}"
    (← IO.getStderr).flush
  match verdict with
  | .ok records =>
    IO.println s!"con-ron-lean: accepted {records} declarations ({modeTag})"
    return 0
  | .error e =>
    let now ← IO.monoMsNow
    IO.eprintln s!"con-ron-lean: {e.message} ({modeTag}) t={msSecs (now - t0)}s"
    return e.exitCode

/-- con-leche: Main.lean:992-1019 main
`--help` in any argument position prints the usage on stdout and exits 0,
reading nothing.  A bad flag prints its message and the usage on stderr
and exits 3, as does a command line that does not name exactly one file.
Everything else runs the checker IN THIS PROCESS. -/
def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println usage
    return 0
  let a := parseArgs args {}
  if let some msg := a.bad then
    IO.eprintln s!"con-ron-lean: {msg}"
    IO.eprintln usage
    return 3
  match a.files.toList with
  | [file] =>
    checkMain file a.mode (if a.noPins then [] else ConLeche.natOpPinSets) a.progress
  | _ =>
    IO.eprintln usage
    return 3

end ConRon.Arena

-- (The top-level `main` Lake's `con-ron-lean` executable needs lives in
-- `ConRon/Arena/Exe.lean`, not here: task #97-COMPOSE found that a top-level
-- `main` in this module collides with `ConRon/Dump/Pins.lean`'s the moment
-- one file imports both Theorem 1's capstone, which imports this module for
-- `runPipeline`, and Theorem 2's tier, which reaches `ConRon.Dump.Pins`
-- through `ConRon.Refine.Pins`.)
