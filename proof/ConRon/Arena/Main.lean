module

public import ConRon.Arena.Frontend.Prelude
public import ConRon.Arena.Frontend.Olean.Records
public import ConRon.Arena.OleanJobs
public import ConRon.Arena.Frontend.Compare
public import ConRon.Arena.Modular.Graph
public import ConRon.Arena.Modular.Worker
public import ConRon.Arena.Modular.CompareModule
public import ConLeche.Driver.Schedule.Run
public import ConLeche.Kernel.NatOpPins
public import ConLeche.Frontend.Pace

@[expose] public section

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
verdict (`ConLeche/Driver/CheckMain.lean`'s `checkMainG`, its own argument for why ONE loop serves the
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

/-- con-leche: ConLeche/Driver/CheckMain.lean:32-39 ConLeche.CheckError.exitCode
The exit code of each error kind.  1 rejected, 2 declined, 3 error; 0 is
the accept and has no error to map.  The 1/2 distinction is con-leche's
and is load-bearing: a reject is a verdict about the input, a decline a
statement about the checker, and a decline is never "something
unexpectedly went wrong" — that is 3.  `native` — the arena's own fourth
kind, raised when §8.3's handle word runs out at its index cap per constructor
per tier — is a 3 for the same reason: it claims nothing about the input. -/
def CheckError.exitCode : CheckError → UInt8
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3
  | .native _ => 3

/-- con-leche: ConLeche/Driver/CheckMain.lean:32-39 ConLeche.CheckError.exitCode
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
materialises as one buffer.  It is
`Frontend.chunkSize` (con-leche's `ExportC.lean:813-814`), named here so the
driver reads as con-leche's does. -/
def chunkSize : USize := Frontend.chunkSize

/-- con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
**THE SEAM** (DESIGN.md §8.4): the whole checker, from the input's chunks
to the verdict.

`chunks` are the 4 MiB reads in order, `mode` the checking mode, `pins`
the pin-variant list; the result is the FILE's accepted
declaration-record count — con-leche's verdict number, "a property of the
INPUT" (`ConLeche/Driver/CheckMain.lean`'s `checkMainG`).

**The FRONTEND half is real since task #97e**: the built-in prelude is
parsed, the stream's chunks are parsed into the persistent tier of one
`EStore`, and the prepared record list is built.  There is no
projection-function rewrite and no modeller seam left to run any more
(con-leche's `uniform-inds` merge, task #105): every inductive block is
pushed as one `IndDecl`, unconditionally, and the uniform installer
(`Arena/Inductives/**`) does the rest.  Every verdict the frontend itself
reaches — a malformed line, a rebound index, an `unsafe` declaration, a block
whose redundant fields contradict its own records — is already this
function's answer, with con-leche's own exit code.

This is the pipeline BEFORE the parse: the built-in prelude, parsed into the
same store the stream goes into, and the parse state the stream's first chunk
is fed to.  Shared verbatim by the pure seam and by the driver's interleaved
loop. -/
def runPipelineHead :
    AM (Except (CheckError × Nat) (Frontend.PreludeIx × Frontend.StateD)) := do
  -- **The reserved-name pins, interned ONCE** (task #97-P6-4a): immediately
  -- after the state is made and before the prelude, so the scratch tier is
  -- closed and every pinned handle is persistent.
  internReservedPins
  match ← Frontend.builtinPreludeE with
  | .error e => pure (.error e)
  | .ok pre => pure (.ok (pre, ← Frontend.StateD.init))

/-- con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
con-leche's `checkMainG` runs its check at `justify = none` (`checkDeclsIO … J rfl`) and
its verdict with `who = ""` on this path: neither is a parameter here.
The pipeline AFTER the parse: `preparePrelude`, then **the check**: the
stream's index and every record's job (`checkStream`), then the verdict number.  Shared verbatim by the pure seam and by the
driver's interleaved loop, which is what makes the two the same computation.

The verdict number is con-leche's own, "a property of the INPUT"
(`ConLeche/Driver/CheckMain.lean`'s `checkMainG`): the records the parse produced, which no later step
moves.

`internAllPins` runs BEFORE the check and while the scratch tier is still off,
which is what DESIGN §8.6 P2d means by "at startup": every pinned datum is in
the persistent cons table before any declaration's check can intern one into
a tier that is about to vanish; so does the index build (`checkStream`). -/
def runPipelineTail (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat)
    (pre : Frontend.PreludeIx) (r : Frontend.ParseResultD) :
    AM (Except CheckError Nat) := do
  -- The verdict number is read HERE, before the fold, so that `r` dies at
  -- `preparePrelude` instead of being pinned across the whole check (DESIGN
  -- §8.4: decide the rare branch, and read what a later line needs, BEFORE
  -- the expensive step).
  let records := r.decls.size
  let ds ← Frontend.preparePrelude pre r.decls
  let ipins ← internAllPins pins maxNatSize
  match ← checkStream mode ipins ds with
  | .error (e, n) => pure (.error (atDecl e n))
  | .ok _ => pure (.ok records)

/-- con-leche: ConLeche/Driver/Cli.lean:56-77 progressPace
The progress heartbeat's pace, read off the `--progress[=N|P%|Ss]` flag: every
`N` declarations, per `P` percent of a phase, or at the first one done after `S`
seconds (con-leche's own `Pace`, a representation-free type).  No flag is off;
bare `--progress` is every one.  A value of another form, and a zero, are usage
errors (exit 3): a run's output must be readable off its invocation, never
silently degraded. -/
def progressPace (v : String) : Except String Pace :=
  let bad : Except String Pace := .error s!"--progress takes a number of declarations of at \
    least 1, a percentage from 1% to 100%, or seconds of at least 1s, got {Display.str v}; \
    omit the flag for no heartbeat"
  if v.endsWith "%" then
    match (v.dropEnd 1).toString.toNat? with
    | some p => if 1 ≤ p && p ≤ 100 then .ok (.percent p) else bad
    | none => bad
  else if v.endsWith "s" then
    match (v.dropEnd 1).toString.toNat? with
    | some 0 | none => bad
    | some s => .ok (.seconds s)
  else
    match v.toNat? with
    | some 0 | none => bad
    | some n => .ok (.every n)

/-- con-leche: ConLeche/Driver/Cli.lean:79-101 jobsCount
The worker count, read off `--jobs=<n>`: a decimal numeral of at least 1.
`0` and a non-numeral are usage errors (exit 3); without the flag the
count is the machine's hardware thread count.

**The arena is single-threaded today** and the flag is accepted and
validated all the same, because `scripts/diff-e2e.sh` passes it on every
fixture and because §8.3's parallel plan is already written down: the
persistent tier is immutable in phase B and each worker owns a scratch
tier, so the count will mean what con-leche's means when P2d gets there.
-/
def jobsCount (v : String) : Except String Nat :=
  match v.toNat? with
  | some 0 => .error "--jobs takes a worker count of at least 1 \
      (a decimal numeral); omit the flag for one worker per hardware thread"
  | some n => .ok n
  | none => .error s!"--jobs takes a worker count \
      (a decimal numeral of at least 1), got {Display.str v}"

/-- con-leche: ConLeche/Driver/Cli.lean:104-114 maxNatSizeArg
The maximum `Nat` size, read off the `--max-nat-size=<bytes>` flag: a decimal
byte count, the official kernel's `LEAN_NAT_MAX_SIZE` (the largest `Nat`
numeral the checker takes in or computes; a larger one rejects the
declaration).  A non-numeral is a usage error (exit 3).  Without the flag the
maximum size is the official default, 128 MiB (`maxNatSizeDefault`). -/
def maxNatSizeArg (v : String) : Except String Nat :=
  match v.toNat? with
  | some n => .ok n
  | none => .error s!"--max-nat-size takes a byte count \
      (a decimal numeral), got {Display.str v}"

/-- con-leche: none — the millisecond-to-seconds rendering of the
heartbeat's `t=` field.  con-leche has it as `ConLeche.Cached.msSecs`,
which `scripts/provenance-skip.txt` lists as driver-only rendering the
Rust port does not carry; the arena's driver prints the same line, so it
carries the same three lines of arithmetic. -/
def msSecs (ms : Nat) : String :=
  let s := ms / 1000
  let c := (ms % 1000) / 10
  s!"{s}.{if c < 10 then "0" else ""}{c}"

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:205-215 foldChunks
**THE READ LOOP**: the handle read strictly forward, 4 MiB at a time, each
buffer fed to `Frontend.chunkStep` and then dropped; the first empty read is
its end of file and `Frontend.chunkFinish` closes the stream.  Never seeked,
never re-opened, and no scratch file exists anywhere.  `foldChunks` reads a
handle forward too, through con-leche's `CheckerIO` class, up to the size it
read first; this reads to the first empty read, and there is no class.

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
partial def readFold (h : IO.FS.Handle)
    (st : Frontend.StateD) (carry : ByteArray) (lineNo total chunks : Nat)
    (s : AState) :
    IO (Except CheckError (Except (CheckError × Nat) Frontend.ParseResultD ×
      AState × Nat)) := do
  let buf ← h.read chunkSize
  if buf.isEmpty then
    match (Frontend.chunkFinish st carry lineNo).run s with
    | .error e => pure (.error e)
    | .ok (r, s) => pure (.ok (r, s, chunks))
  else
    match (Frontend.chunkStep st carry lineNo total buf).run s with
    | .error e => pure (.error e)
    | .ok (.error e, s) => pure (.ok (.error e, s, chunks + 1))
    | .ok (.ok (st, carry, lineNo, total), s) =>
      readFold h st carry lineNo total (chunks + 1) s

/-- con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
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
    (pins : List NatOpPinSet) (maxNatSize : Nat) : IO (Except CheckError Nat × Nat × Nat × Nat) := do
  let s0 := AState.init EStore.empty
  match (runPipelineHead).run s0 with
  | .error e => pure (.error e, 0, 0, 0)
  | .ok (.error (e, n), _) => pure (.error (Frontend.atLine e n), 0, 0, 0)
  | .ok (.ok (pre, st), s) =>
    match ← readFold h st .empty 0 0 0 s with
    | .error e => pure (.error e, 0, 0, 0)
    | .ok (.error (e, n), _, chunks) =>
      pure (.error (Frontend.atLine e n), chunks, ← IO.monoMsNow, 0)
    | .ok (.ok r, s, chunks) =>
      let tParse ← IO.monoMsNow
      match (runPipelineTail mode pins maxNatSize pre r).run s with
      | .error e => pure (.error e, chunks, tParse, 0)
      | .ok (v, s') => pure (v, chunks, tParse, s'.store.persCount)

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:400-406 openReadIO
The reader's positional read at `IO`: the file opened by upstream's `openReadIO`
(a regular file, or an exception), its first `off` bytes read and dropped, then
up to `len` bytes, each read repeated until it has them or the file ends.
Upstream reads its handle forward instead (Lean's handles have no positional
read); the reader asks this only for an `.olean` header, so what is dropped is
a few pages at most. -/
partial def readRangeIO (p : System.FilePath) (off len : Nat) : IO ByteArray := do
  let h ← openReadIO p
  let rec go (want : Nat) (acc : ByteArray) : IO ByteArray := do
    if want == 0 then return acc
    let b ← h.read (min want chunkSize.toNat).toUSize
    if b.isEmpty then return acc
    go (want - b.size) (acc ++ b)
  let skipped ← go off .empty
  if skipped.size < off then return .empty
  go len .empty

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:514-529 instCheckerIOIO
The binary's file operations, as the pure functions the reader takes: `IO` run where
it is asked, outside every theorem (`Frontend/Olean/Files.lean`'s note). -/
unsafe def stdFsImpl : Frontend.Olean.OleanFs where
  pathExists p := unsafeBaseIO do
    match ← (p.pathExists : IO Bool).toBaseIO with
    | .ok b => pure (.ok b)
    | .error e => pure (.error (toString e))
  isDir p := unsafeBaseIO do
    match ← (p.isDir : IO Bool).toBaseIO with
    | .ok b => pure (.ok b)
    | .error e => pure (.error (toString e))
  realPath p := unsafeBaseIO do
    match ← (IO.FS.realPath p : IO _).toBaseIO with
    | .ok b => pure (.ok b)
    | .error e => pure (.error (toString e))
  readBinFile p := unsafeBaseIO do
    match ← (IO.FS.readBinFile p : IO _).toBaseIO with
    | .ok b => pure (.ok b)
    | .error e => pure (.error (toString e))
  readRange p off len := unsafeBaseIO do
    match ← (readRangeIO p off len).toBaseIO with
    | .ok b => pure (.ok b)
    | .error e => pure (.error (toString e))
  fileSize p := unsafeBaseIO do
    match ← (CheckerIO.fileSize p : IO Nat).toBaseIO with
    | .ok b => pure (.ok b)
    | .error e => pure (.error (toString e))

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:514-529 instCheckerIOIO
The binary's file operations, opaque to the logic. -/
@[implemented_by stdFsImpl]
opaque stdFs : Frontend.Olean.OleanFs

/-- con-leche: ConLeche/Driver/CheckMain.lean:87-98 readInputG
**The seam on the `.olean` path**: the head of the pipeline, the reader in place of
the chunks' fold, then the tail as the binary runs it on this path: the preparation
with what a record mentions read off the load (`OleanRead.usedOf`), the pins, and the
check phase whose theorem jobs read their values (`checkOleans`, the binary's
`driver::olean_job`).  The roots and constants are interned first.  Deviation: the
twin does not print the read's `read:` lines: its reader is pure, and the file
seam's two note fields are no-ops here (a `Unit`-valued call a pure reader discards
is erased by the compiler). -/
def oleanPipeline (sp : List System.FilePath) (roots : Array Name) (constants : Option (Array Name))
    (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) :
    AM (Except CheckError Nat) := do
  match ← runPipelineHead with
  | .error (e, n) => pure (.error (Frontend.atLine e n))
  | .ok (pre, _) =>
    let rs ← roots.mapM internName
    let cs ← match constants with
      | none => pure none
      | some cs => pure (some (← cs.mapM internName))
    match ← Frontend.Olean.readOleans stdFs (sp : ConLeche.Frontend.Olean.Roots) rs cs false false with
    | .error (e, n) => pure (.error (Frontend.atLine e n))
    | .ok rd =>
      let records := rd.decls.size
      let ds := (← Frontend.prepareD pre rd.decls rd.usedOf).decls
      let ipins ← internAllPins pins maxNatSize
      match ← checkOleans stdFs rd.pins (sp : ConLeche.Frontend.Olean.Roots) rd.values mode ipins ds with
      | .error (e, n) => pure (.error (atDecl e n))
      | .ok _ => pure (.ok records)

/-- con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
The driver on the `.olean` path. -/
def checkMainOlean (sp : List System.FilePath) (roots : Array Name) (constants : Option (Array Name))
    (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) : IO UInt8 := do
  let t0 ← IO.monoMsNow
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let verdict : Except CheckError Nat := match (oleanPipeline sp roots constants mode pins maxNatSize).run (AState.init EStore.empty) with
    | .error e => .error e
    | .ok (r, _) => r
  match verdict with
  | .ok records =>
    IO.println s!"con-ron-lean: accepted {records} declarations ({modeTag})"
    return 0
  | .error e =>
    let now ← IO.monoMsNow
    IO.eprintln s!"con-ron-lean: {e.message} ({modeTag}) t={msSecs (now - t0)}s"
    return e.exitCode

/-- con-leche: ConLeche/Driver/Cli.lean:116-122 synopsis
The invocation forms, printed on their own when there are no arguments.  Of `--schedule` only
`--schedule-commands` is run here (`helpText`). -/
def synopsis : String := String.intercalate "\n" [
  "Usage:",
  "  con-ron-lean [OPTIONS] FILE.ndjson",
  "  con-ron-lean [OPTIONS] --compare CHALLENGE.ndjson SOLUTION.ndjson",
  "  con-ron-lean [OPTIONS] --olean --search-path=DIRS MODULE...",
  "  con-ron-lean [OPTIONS] --olean --search-path=DIRS --compare CHALLENGE SOLUTION"]

/-- con-leche: ConLeche/Driver/Cli.lean:124-125 tryHelp
The line after a usage error. -/
def tryHelp : String := "Try 'con-ron-lean --help' for more information."

/-- con-leche: ConLeche/Driver/Cli.lean:127-175 helpText
The `--help` text: con-leche's, with this binary's name and con-ron's documentation, short on
purpose as con-leche's (one line per option, two at most); con-leche's options of the modes this
binary does not run are listed by name, as usage errors (`unsupported`).  `--jobs` is accepted
and validated, and this binary checks on one worker whatever it says. -/
def helpText : String := String.intercalate "\n" [
  "Check Lean declarations from a lean4export file or from .olean modules.",
  "",
  synopsis,
  "",
  "Options:",
  "  --verified          Check in the mode the soundness theorem covers (default)",
  "  --trusted           Skip the checks only the proof needs; outside the theorem",
  "  --jobs=N            Accepted for the command line's sake; one worker always",
  "  --max-nat-size=N    Largest Nat numeral in bytes (default 134217728)",
  "  --progress[=PACE]   Progress on stderr; PACE is N declarations, P% or Ss",
  "  --compare           Check SOLUTION, then CHALLENGE with its axioms and",
  "                      sorry-holes justified by SOLUTION",
  "  --help              Print this help and exit",
  "  --                  End of options",
  "",
  ".olean input:",
  "  --olean             Read modules and their imports from .olean files",
  "  --search-path=DIRS  Colon-separated .olean directories; repeatable. In a",
  "                      Lake project: \"$(lake env printenv LEAN_PATH)\"",
  "  --trusted-search-path=DIRS",
  "                      Trusted .olean directories (with --compare or --module)",
  "  --constant=NAME     Check only NAME and what it mentions; repeatable",
  "  --check-graph       Check only that the import graph is acyclic",
  "  --module            Check only MODULE's own declarations",
  "  --modular           Check each module of the closure on its own",
  "",
  "Scheduler options (only --schedule-commands is run here):",
  "  --schedule-commands       Print the worker commands (for xargs or parallel)",
  "  --schedule-order=ORDER    shuffled (default) or graph",
  "  --worker-stack-size=SIZE  Thread stack size of the workers (e.g. 8G)",
  "  --schedule                con-leche's scheduler, not run (usage error, 3);",
  "                            with --schedule-commands, -memory, -timeout and",
  "                            -log are ignored",
  "",
  "Exit status:",
  "  0  accepted",
  "  1  rejected: a declaration is invalid",
  "  2  declined: an unsupported feature",
  "  3  error: bad usage, malformed input or an internal failure",
  "",
  "Documentation:",
  "  README.md and OVERVIEW.md of the con-ron repository"]

/-- con-leche: ConLeche/Driver/Cli.lean:177-218 Args
The parsed command line.  `progress = .off` is "no flag given"; `jobs = none`
is "no flag given", one worker per hardware thread. -/
structure Args where
  mode : CheckMode := .verified
  progress : Pace := .off
  jobs : Option Nat := none
  /-- The maximum `Nat` size in bytes (`--max-nat-size=<n>`). -/
  maxNatSize : Nat := maxNatSizeDefault
  /-- `--olean`: the positional arguments are root module names. -/
  olean : Bool := false
  /-- `--search-path=DIR:DIR…`: where `--olean` looks for the files. -/
  searchPath : List System.FilePath := []
  /-- `--constant=NAME`: with `--olean`, the constants to start from. -/
  constants : Array String := #[]
  /-- `--check-graph` (a mode this binary does not run: `unsupported`). -/
  checkGraph : Bool := false
  /-- `--module` (not run here). -/
  module : Bool := false
  /-- `--modular` (not run here). -/
  modular : Bool := false
  /-- the values after `--schedule` of every `--schedule[-OPT=VALUE]` flag, `""` for the bare
  flag -/
  schedule : Array String := #[]
  /-- some `--schedule` flag was given -/
  scheduled : Bool := false
  /-- `--compare`: the two arguments are a challenge and its solution. -/
  compare : Bool := false
  /-- `--trusted-search-path=DIR:DIR…`: with `--compare`, where the challenge is read, and where
  the solution is read first. -/
  trustedPath : List System.FilePath := []
  /-- `--worker-stack-size=SIZE` was given, with a valid size -/
  workerStack : Bool := false
  /-- its value in KiB, which `--schedule-commands` prints as each worker's
  `LEAN_STACK_SIZE_KB` -/
  workerStackKb : Option Nat := none
  files : Array String := #[]
  bad : Option String := none

/-- con-leche: ConLeche/Driver/Cli.lean:234-239 Args.closed
The arguments once all are read: `--worker-stack-size` without `--schedule` is a usage error
(no other run starts a worker). -/
def Args.closed (a : Args) : Args :=
  if a.workerStack && !a.scheduled then
    { a with bad := some "--worker-stack-size takes --schedule" }
  else a

/-- con-leche: ConLeche/Driver/Schedule/Worker.lean:82-94 parseSize
Whether `v` is a `--worker-stack-size=` value the cited `parseArgs` takes: a POSITIVE size
with a unit, `K`, `M`, `G` or `T` (either case).  The size itself is a `--schedule` worker's,
which this binary does not run, so it is not kept. -/
def sizePositive (v : String) : Bool :=
  let unit : Bool := match v.back with
    | 'K' | 'k' | 'M' | 'm' | 'G' | 'g' | 'T' | 't' => true
    | _ => false
  match unit, (v.dropEnd 1).toString.toNat? with
  | true, some (_ + 1) => true
  | _, _ => false

/-- con-leche: ConLeche/Driver/Cli.lean:241-292 parseArgs
The argument parse, clause for clause: the mode flags in either order with
the heartbeat, `=`-carrying spellings after the bare ones, an unknown
`-`-leading word a usage error, everything else a file. -/
def parseArgs : List String → Args → Args
  | [], a => a.closed
  | "--" :: rest, a => { a with files := a.files ++ rest.toArray }.closed
  | "--verified" :: rest, a => parseArgs rest { a with mode := .verified }
  | "--trusted" :: rest, a => parseArgs rest { a with mode := .trusted }
  | "--progress" :: rest, a => parseArgs rest { a with progress := .every 1 }
  | "--olean" :: rest, a => parseArgs rest { a with olean := true }
  | "--check-graph" :: rest, a => parseArgs rest { a with checkGraph := true }
  | "--module" :: rest, a => parseArgs rest { a with module := true }
  | "--modular" :: rest, a => parseArgs rest { a with modular := true }
  | "--compare" :: rest, a => parseArgs rest { a with compare := true }
  | s :: rest, a =>
    if s.startsWith "--progress=" then
      match progressPace (s.drop "--progress=".length).toString with
      | .ok n => parseArgs rest { a with progress := n }
      | .error msg => { a with bad := some msg }
    else if s.startsWith "--jobs=" then
      match jobsCount (s.drop "--jobs=".length).toString with
      | .ok n => parseArgs rest { a with jobs := some n }
      | .error msg => { a with bad := some msg }
    else if s.startsWith "--max-nat-size=" then
      match maxNatSizeArg (s.drop "--max-nat-size=".length).toString with
      | .ok n => parseArgs rest { a with maxNatSize := n }
      | .error msg => { a with bad := some msg }
    else if s == "--jobs" then
      { a with bad := some "--jobs takes a worker count: --jobs=<n>; omit the \
          flag for one worker per hardware thread" }
    else if s.startsWith "--constant=" then
      parseArgs rest { a with constants := a.constants.push (s.drop "--constant=".length).toString }
    else if s.startsWith "--search-path=" then
      parseArgs rest { a with searchPath := a.searchPath ++
        (((s.drop "--search-path=".length).toString.splitOn ":").filter (· != "")).map System.FilePath.mk }
    else if s.startsWith "--trusted-search-path=" then
      let v := (s.drop "--trusted-search-path=".length).toString
      parseArgs rest { a with trustedPath := a.trustedPath ++
        ((v.splitOn ":").filter (· != "")).map System.FilePath.mk }
    else if s.startsWith "--schedule" then
      parseArgs rest { a with schedule := a.schedule.push (s.drop "--schedule".length).toString,
                              scheduled := true }
    else if s.startsWith "--worker-stack-size=" then
      let v := (s.drop "--worker-stack-size=".length).toString
      if sizePositive v then
        parseArgs rest { a with workerStack := true,
                                workerStackKb := ConLeche.Driver.Schedule.parseSize v }
      else { a with bad := some s!"--worker-stack-size takes a size with a unit, K, M, G or T \
        (e.g. 8G), got {Display.str v}" }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {Display.str s}" }
    else parseArgs rest { a with files := a.files.push s }

/-- con-leche: ConLeche/Driver/Cli.lean:220-223 helpWanted
`--help` before any `--`: after a `--` every argument is a file, whatever it is
called. -/
def helpWanted (args : List String) : Bool :=
  (args.takeWhile (· != "--")).contains "--help"

/-- con-leche: none — con-leche prints a command-line path raw
A text that came from outside the input proper (a command-line path, an IO
error, which names that path), for a message: as it is when it holds nothing
a display must escape, else `Display.str` of it.  Deviation from con-leche,
which prints `{file}: {e}` raw (task #131); an ordinary path prints exactly as
con-leche prints it.  The Rust driver's `render::display_path`. -/
def displayPath (s : String) : String :=
  if s.any fun c => c == '\\' || c == '"' || Display.unsafeChar c then Display.str s else s

/-- con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
The driver, which `main` calls in process: read the chunks, run the seam,
print the verdict.  Every VERDICT line names the mode — a `--trusted` run,
the unverified lane, must never be mistaken for a `--verified` one in a
log, whatever it says — and what the heartbeat prints between the steps
touches no verdict, which is why there is one path and not two.  The cited check runs at
`justify = none` and its verdict at `who = ""`: no solution and no module prefix here. -/
def checkMain (file : String) (mode : CheckMode) (pins : List NatOpPinSet)
    (maxNatSize : Nat) (pace : Pace) : IO UInt8 := do
  let t0 ← IO.monoMsNow
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let h? ← try
      let md ← System.FilePath.metadata file
      unless md.type == .file do
        throw (.inappropriateType (some file) 21 "not a regular file")
      pure (some (← IO.FS.Handle.mk file .read))
    catch e => do
      IO.eprintln s!"con-ron-lean: {displayPath file}: {displayPath (toString e)} ({modeTag})"
      pure none
  let some h := h? | return 3
  let (verdict, chunks, tParse, nodes) ← runPipelineIO h mode pins maxNatSize
  if pace.on then
    let tRead ← IO.monoMsNow
    IO.eprintln s!"con-ron-lean: parse done: {chunks} chunks read \
      t={msSecs (tParse - t0)}s; check t={msSecs (tRead - tParse)}s"
    -- the PERSISTENT expression-node count at the end of the run: the parse's
    -- DAG plus what the stream's index added.  The number the Rust twin is
    -- checked against; it costs one field read and is printed only under
    -- --progress.
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

/-! ## `--compare`: a challenge checked with its axioms justified by a solution

The binary's `crates/con-ron/src/compare.rs`, over the twin: the solution checked as any
input, its index kept, then the challenge's records read with the solution
(`sideRecordsGo`; on `--olean` its theorem holes first, `holeRecordsGo`) and checked with it
(`solutionOf`).  Both inputs are read into the one state. -/

/-- con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
**A compared run's verdict**: a failed read or step, the driver's own rejection (a message,
exit 1), the solution's failed check, the challenge's, or the accept with the challenge's
record count, the labels of its justified records and the solution's record count. -/
inductive CmpVerdict where
  | failed (e : CheckError)
  | reject (why : String)
  | solution (e : CheckError)
  | challenge (e : CheckError)
  | accepted (records : Nat) (holes : Array String) (solRecords : Nat)

/-- con-leche: ConLeche/Driver/Run.lean:74-99 checkDeclsIO
**A check phase that keeps its index**: `checkStream` at the solution `J`, the index and the
post-index state back on the accept (the binary's thawed tier). -/
def checkStreamJ (mode : CheckMode) (pins : List INatOpPinSet) (J : Option ISolution)
    (ds : Array IDeclaration) : AM (Except (CheckError × Nat) IStreamIndex) := fun s =>
  match buildIndex ds s with
  | .ok (.ok I, s₁) =>
    match checkJobList mode pins J I ds (List.range ds.size) s₁.worker with
    | .ok (.ok (), _) => .ok (.ok I, s₁)
    | .ok (.error e, _) => .ok (.error e, s₁)
    | .error e => .error e
  | .ok (.error e, s₁) => .ok (.error e, s₁)
  | .error e => .error e

/-- con-leche: ConLeche/Driver/CheckMain.lean:154-177 checkOleansG
**An `--olean` check phase that keeps its index**: `checkOleans` at the solution `J`. -/
def checkOleansJ (fs : Frontend.Olean.OleanFs) (pk : Frontend.Olean.OleanPins)
    (sp : ConLeche.Frontend.Olean.Roots) (values : Array Frontend.Olean.ModRef) (mode : CheckMode)
    (pins : List INatOpPinSet) (J : Option ISolution) (ds : Array IDeclaration) :
    AM (Except (CheckError × Nat) IStreamIndex) := fun s =>
  match buildIndex ds s with
  | .ok (.ok I, s₁) =>
    match checkOleanJobListJ fs pk sp values mode pins J I ds (List.range ds.size) {} s₁.worker with
    | .ok (.ok (), _) => .ok (.ok I, s₁)
    | .ok (.error e, _) => .ok (.error e, s₁)
    | .error e => .error e
  | .ok (.error e, s₁) => .ok (.error e, s₁)
  | .error e => .error e

/-- con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
The accept line's records: `prepared[i]` labelled where `checked[i]` offers a statement. -/
def holesOf (prepared checked : Array IDeclaration) : AM (Array String) := do
  let mut out := #[]
  for (d, c) in prepared.zip checked do
    if (← justifiable c).isSome then out := out.push (← declLabel d)
  pure out

/-- con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
**The compared run after the two parses** (`compare_json`): the solution prepared and
checked, its index kept; the challenge prepared, read with the solution and checked with it. -/
def compareJsonTail (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat)
    (pre : Frontend.PreludeIx) (rC rS : Frontend.ParseResultD) : AM CmpVerdict := do
  let dsS := (← Frontend.prepareD pre rS.decls).decls
  let ipins ← internAllPins pins maxNatSize
  match ← checkStreamJ mode ipins none dsS with
  | .error (e, n) => pure (.solution (atDecl e n))
  | .ok IS =>
    let dsC := (← Frontend.prepareD pre rC.decls).decls
    let recsC := (← sideRecordsGo [] dsC.toList).toArray
    match ← checkStreamJ mode ipins (some (solutionOf IS recsC.toList)) recsC with
    | .error (e, n) => pure (.challenge (atDecl e n))
    | .ok _ => pure (.accepted rC.decls.size (← holesOf dsC recsC) rS.decls.size)

/-- con-leche: ConLeche/Driver/Compare.lean:86-101 fallbackOnly
**Why a challenge module is not on the trusted path**, where the solution's lookup finds it on
the search path: the challenge's closure walked through that lookup, the first module whose
root only the search path holds.  For the message only. -/
def fallbackOnly (trusted : List System.FilePath) (sr : ConLeche.Frontend.Olean.Roots)
    (c : NIdx) : AM (Option String) := fun s =>
  if trusted.isEmpty then .ok (none, s) else
  match (do Frontend.Olean.closureOrder stdFs (← Frontend.Olean.oleanPins) sr #[c]) s with
  | .error _ => .ok (none, s)
  | .ok (order, s') =>
    let why := order.toList.findSome? fun m =>
      match denoteN s'.store.ns m with
      | none => none
      | some n =>
        match Frontend.Olean.rootAt stdFs trusted n.root,
            Frontend.Olean.lookAt stdFs sr.path sr.fallback n.root with
        | .missing, .dir d => some s!"the challenge's module {n} is not on the trusted path \
            ({":".intercalate (trusted.map toString)}); it is in {d}, on the search path, which \
            only the solution reads"
        | _, _ => none
    .ok (why, s')

/-- con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
**`--olean --compare`** (`compare_oleans`): the challenge's closure read through the trusted
lookup alone with its homes, `--constant` names checked to be its own, prepared and its theorem
holes read as axioms; the solution's closure read through the solution's lookup, prepared and
checked; then the challenge's records read with the solution and checked with it. -/
def compareOleanPipeline (trusted path : List System.FilePath) (c s : Name)
    (constants : Option (Array Name)) (mode : CheckMode) (pins : List NatOpPinSet)
    (maxNatSize : Nat) : AM CmpVerdict := do
  match ← runPipelineHead with
  | .error (e, n) => pure (.failed (Frontend.atLine e n))
  | .ok (pre, _) =>
    let ch ← internName c
    let sh ← internName s
    let cs ← match constants with
      | none => pure none
      | some cs => pure (some (← cs.mapM internName))
    let cr : ConLeche.Frontend.Olean.Roots :=
      if trusted.isEmpty then { path := path } else { path := trusted }
    let sr : ConLeche.Frontend.Olean.Roots :=
      if trusted.isEmpty then { path := path } else { path := trusted, fallback := path }
    match ← Frontend.Olean.readOleans stdFs cr #[ch] cs true true with
    | .error (e, n) =>
      match ← fallbackOnly trusted sr ch with
      | some why => pure (.reject why)
      | none => pure (.failed (Frontend.atLine e n))
    | .ok rdC =>
      match ← Frontend.foreignConstant cs ch rdC.homes with
      | some why => pure (.reject why)
      | none =>
        let dsC := (← Frontend.prepareD pre rdC.decls rdC.usedOf).decls
        let holed := (← Frontend.holeRecordsGo rdC.usedOf [] dsC.toList).toArray
        let need := cs.map fun _ => dsC.filterMap Frontend.recKey
        match ← Frontend.Olean.readOleans stdFs sr #[sh] need true false with
        | .error (e, n) => pure (.failed (Frontend.atLine e n))
        | .ok rdS =>
          if rdS.values.any (·.name == ch) then
            pure (.reject s!"{s} does not solve {c}: the solution's closure holds the challenge")
          else
            let dsS := (← Frontend.prepareD pre rdS.decls rdS.usedOf).decls
            let ipins ← internAllPins pins maxNatSize
            match ← checkOleansJ stdFs rdS.pins sr rdS.values mode ipins none dsS with
            | .error (e, n) => pure (.solution (atDecl e n))
            | .ok IS =>
              let recsC := (← sideRecordsGo [] holed.toList).toArray
              match ← checkOleansJ stdFs rdC.pins cr rdC.values mode ipins
                  (some (solutionOf IS recsC.toList)) recsC with
              | .error (e, n) => pure (.challenge (atDecl e n))
              | .ok _ => pure (.accepted rdC.decls.size (← holesOf dsC recsC) rdS.decls.size)

/-- con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
**A compared run's lines and exit code**: the solution's failure prefixed `the solution S: `,
the accept line and one line per justified record. -/
def cmpVerdictIO (modeTag solution : String) (t0 : Nat) : Except CheckError CmpVerdict → IO UInt8
  | .error e | .ok (.failed e) | .ok (.challenge e) => do
    let now ← IO.monoMsNow
    IO.eprintln s!"con-ron-lean: {e.message} ({modeTag}) t={msSecs (now - t0)}s"
    return e.exitCode
  | .ok (.reject why) => do
    IO.eprintln s!"con-ron-lean: {why} ({modeTag})"
    return 1
  | .ok (.solution e) => do
    let now ← IO.monoMsNow
    IO.eprintln s!"con-ron-lean: the solution {solution}: {e.message} ({modeTag}) \
      t={msSecs (now - t0)}s"
    return e.exitCode
  | .ok (.accepted n holes nS) => do
    IO.println s!"con-ron-lean: accepted {n} declarations, {holes.size} axioms justified by the \
      solution {solution} ({nS} declarations accepted) ({modeTag})"
    for h in holes do
      IO.println s!"con-ron-lean: {h} justified by the solution"
    return 0

/-- con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
**`--compare` on two lean4export files**: both parsed into the one state (`readFold`, the
challenge's first), then `compareJsonTail`. -/
def compareJsonMain (c s : String) (mode : CheckMode) (pins : List NatOpPinSet)
    (maxNatSize : Nat) : IO UInt8 := do
  let t0 ← IO.monoMsNow
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let open? (file : String) : IO (Option IO.FS.Handle) := do
    try
      let md ← System.FilePath.metadata file
      unless md.type == .file do
        throw (.inappropriateType (some file) 21 "not a regular file")
      pure (some (← IO.FS.Handle.mk file .read))
    catch e => do
      IO.eprintln s!"con-ron-lean: {displayPath file}: {displayPath (toString e)} ({modeTag})"
      pure none
  let some hC ← open? c | return 3
  let some hS ← open? s | return 3
  let failed (e : CheckError) : IO UInt8 := cmpVerdictIO modeTag s t0 (.ok (.failed e))
  match (runPipelineHead).run (AState.init EStore.empty) with
  | .error e => failed e
  | .ok (.error (e, n), _) => failed (Frontend.atLine e n)
  | .ok (.ok (pre, stC), st) =>
    match ← readFold hC stC .empty 0 0 0 st with
    | .error e => failed e
    | .ok (.error (e, n), _, _) => failed (Frontend.atLine e n)
    | .ok (.ok rC, st, _) =>
      match (Frontend.StateD.init).run st with
      | .error e => failed e
      | .ok (stS, st) =>
        match ← readFold hS stS .empty 0 0 0 st with
        | .error e => failed e
        | .ok (.error (e, n), _, _) => failed (Frontend.atLine e n)
        | .ok (.ok rS, st, _) =>
          cmpVerdictIO modeTag s t0
            ((compareJsonTail mode pins maxNatSize pre rC rS).run st |>.map (·.1))

/-- con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
The driver of `--olean --compare`. -/
def compareOleanMain (trusted path : List System.FilePath) (c s : Name)
    (constants : Option (Array Name)) (mode : CheckMode) (pins : List NatOpPinSet)
    (maxNatSize : Nat) : IO UInt8 := do
  let t0 ← IO.monoMsNow
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  cmpVerdictIO modeTag (toString s) t0
    ((compareOleanPipeline trusted path c s constants mode pins maxNatSize).run
      (AState.init EStore.empty) |>.map (·.1))

/-- con-leche: none — a usage error's two lines (con-leche writes them out at each site of
`runArgs`): the message, then the pointer to `--help`; exit 3. -/
def usageError (msg : String) : IO UInt8 := do
  IO.eprintln s!"con-ron-lean: {msg}"
  IO.eprintln tryHelp
  return 3

/-- con-leche: none — the modes con-ron does not run
A mode this binary does not run, once con-leche's own usage checks have passed: a usage error
(exit 3), never a silent run of another mode. -/
def unsupported (mode : String) : IO UInt8 :=
  usageError s!"{mode} is not supported by con-ron-lean"

/-- con-leche: ConLeche/Driver/Graph.lean:240-251 checkGraphG
A graph walk's line and exit code: the accept line on stdout, or the error's on stderr. -/
def graphVerdictIO : Except CheckError (Array Modular.Node) → IO UInt8
  | .error e => do
    IO.eprintln s!"con-ron-lean: graph: {e.message}"
    return e.exitCode
  | .ok C => do
    IO.println s!"con-ron-lean: graph: acyclic: {C.size} modules, \
      {C.foldl (· + ·.2.size) 0} import edges"
    return 0

/-- con-leche: ConLeche/Driver/CompareModule.lean:36-47 chalWalk
**The challenge's closure through the trusted path alone** (`--trusted-search-path`, its verdict
only): where a module of it is not there, why (invalid where the search path holds it); none
where the walk succeeds or no trusted path is given. -/
def chalWalk (trusted path : List System.FilePath) (pk : Frontend.Olean.OleanPins) (c : NIdx) :
    AM (Option CheckError) := fun s =>
  if trusted.isEmpty then .ok (none, s) else
  let sr : ConLeche.Frontend.Olean.Roots := { path := trusted, fallback := path }
  match Modular.chalWalk stdFs pk { path := trusted } c s with
  | .ok (_, s') => .ok (none, s')
  | .error e =>
    match fallbackOnly trusted sr c s with
    | .ok (some why, s') => .ok (some (.invalid why), s')
    | _ => .ok (some e, s)

/-- con-leche: ConLeche/Driver/Dispatch.lean:63-87 runReq
con-leche: ConLeche/Driver/CompareModule.lean:61-71 checkGraphCmpG
**The graph check** (`--check-graph`): the roots' closure, its graph checked (`graphOf`); with
`cmp` (a challenge, the one root, and its solution) the challenge's closure through the trusted
path first (`chalWalk`), then both closures through the solution's lookup, the solution added to
the challenge's header. -/
def graphPipeline (trusted path : List System.FilePath) (roots : List Name) (cmp : Option Name) :
    AM (Array Modular.Node) := do
  internReservedPins
  let pk ← Frontend.Olean.oleanPins
  let rs ← roots.mapM internName
  match cmp, rs with
  | some s, [c] =>
    let sh ← internName s
    if let some e ← chalWalk trusted path pk c then fail e
    let sr : ConLeche.Frontend.Olean.Roots :=
      if trusted.isEmpty then { path := path } else { path := trusted, fallback := path }
    Modular.graphOf stdFs pk sr [c] (some (c, sh))
  | _, _ => Modular.graphOf stdFs pk { path := path } rs none

/-- con-leche: ConLeche/Driver/Schedule.lean:56-111 scheduleG
con-leche: ConLeche/Driver/Schedule/Run.lean:637-647 printCommands
**`--schedule[-OPT=V]`**: the settings read (upstream's `Opts.parse`); without
`--schedule-commands` the scheduler, which this binary does not run (a usage error); with it the
root's closure by the graph check and the commands that check it, on stdout, the modules in the
start order (upstream's `commandLines`, `shuffle`, `workerArgs`). -/
def scheduleMain (a : Args) (root : Name) (cmp : Option Name) : IO UInt8 := do
  if let .percent _ := a.progress then
    IO.eprintln "con-ron-lean: --schedule takes --progress=N (milliseconds) or --progress=Ss, \
      not a percentage"
    return 3
  match ConLeche.Driver.Schedule.Opts.parse a.schedule.toList { stackKb := a.workerStackKb } with
  | .error msg =>
    IO.eprintln s!"con-ron-lean: {msg}"
    return 3
  | .ok o =>
    if !o.commands then
      return ← unsupported (if cmp.isSome then "--olean --schedule --compare" else "--olean --schedule")
    let tp := if cmp.isSome then a.trustedPath else []
    let run : AM (Array Name) := do
      let C ← graphPipeline tp a.searchPath [root] cmp
      C.mapM fun e => fun s => match denoteN s.store.ns e.1 with
        | some n => .ok (n, s)
        | none => .error (.internal "a module of the closure does not denote")
    match run.run (AState.init EStore.empty) with
    | .error e =>
      IO.eprintln s!"con-ron-lean: graph: {e.message}"
      return e.exitCode
    | .ok (mods, _) =>
      let dirs := ":".intercalate (a.searchPath.map toString)
      let paths := if cmp.isSome then
          #["--trusted-search-path=" ++ ":".intercalate (tp.map toString), "--search-path=" ++ dirs]
        else ConLeche.Driver.Schedule.pathArgs "" dirs
      let args (m : Name) : Array String :=
        match cmp with
        | some s => if m == root then ConLeche.Driver.Schedule.cmpWorkerArgs a.mode a.maxNatSize
            paths a.jobs root s
          else ConLeche.Driver.Schedule.workerArgs a.mode a.maxNatSize paths a.jobs m
        | none => ConLeche.Driver.Schedule.workerArgs a.mode a.maxNatSize paths a.jobs m
      let app ← IO.appPath
      let order := if o.shuffled then ConLeche.Driver.Schedule.shuffle
          ConLeche.Driver.Schedule.spell mods.toList else mods.toList
      for l in ConLeche.Driver.Schedule.commandLines app.toString paths root cmp order args
          o.stackKb do
        IO.println l
      return 0

/-- con-leche: ConLeche/Driver/Worker.lean:346-356 tagKind
A stored constant's kind, by its tag, for the messages. -/
def tagKind : Nat → String
  | 0 => "axiom" | 1 => "definition" | 2 => "theorem" | 3 => "opaque constant"
  | 4 => "quotient constant" | 5 => "inductive type" | 6 => "constructor" | 7 => "recursor"
  | _ => "constant"

/-- con-leche: ConLeche/Driver/Worker.lean:358-369 copyLine
**A copy, for the report**: a hole and the kind of what justifies it, or a constant the
challenge restates, with the module it is read from. -/
def copyLine (w : Modular.WorkerRead) (owner : Std.HashMap NIdx Nat) (d : IDeclaration) :
    AM String := do
  let some n := Frontend.recKey d | return ""
  let h ← match owner[n]? with
    | some k => match w.reach.homes[k]? with
      | some h => pure (toString (← readName h))
      | none => pure "[anonymous]"
    | none => pure "[anonymous]"
  let tag := ((w.reads.index.first[n]?).bind w.reads.index.at |>.map (·.tag)).getD 8
  let uses := Modular.ownUsesOf w.home.constants (Modular.ownUsesAt w.home.constants)
  let nt := toString (← readName n)
  if ← Modular.isHoleRec uses d then
    let label := match d with
      | .axiomDecl _ => "axiom"
      | d => s!"{Frontend.recKind d} := sorry"
    pure s!"hole {nt} ({label}) justified by {h}'s {tagKind tag}"
  else pure s!"{Frontend.recKind d} {nt}: {h}'s {tagKind tag}"

/-- con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
**What a worker's run gives**: its phases' failure (`read`), its jobs' (`jobs`, over the
records `ds`), or the accept: the own records' count and the copies' lines. -/
inductive WorkerVerdict where
  | read (e : CheckError)
  | jobs (e : CheckError)
  | accepted (n : Nat) (copies : Array String) (hoisted : Array String)

/-- con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
**The worker at module `m`** from fresh start values (`AState.init EStore.empty`): the reserved
pins, the names, the pin walk, phases 1-4 (`workerRead`), the index over the context and the own
records, the inferred flags, the own records' jobs from `start`; with `cmp`, the compare worker
(`import all` of the solution added to the header) and its copies' lines. -/
def workerPipeline (sp : ConLeche.Frontend.Olean.Roots) (m : Name) (cmp : Option Name)
    (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) : AM WorkerVerdict := do
  internReservedPins
  let mh ← internName m
  let x ← match cmp with
    | none => pure #[]
    | some s => pure #[Modular.solutionImport (← internName s)]
  let ipins ← internAllPins pins maxNatSize
  match ← Modular.workerRead stdFs sp ipins mh x with
  | .error (e, _) => pure (.read e)
  | .ok w =>
    let hoisted ← w.hoisted.mapM fun h => do pure (toString (← readName h))
    let ds := Modular.workerDecls w
    match ← buildIndex ds with
    | .error (e, n) => pure (.jobs (atDecl e n))
    | .ok I =>
      Modular.inferFlags I w.reach.ctx w.reach.pending
      match ← (fun s => checkOleanJobListJ stdFs w.pins sp w.values mode ipins none I ds
          (List.range' w.start (ds.size - w.start)) {} s) with
      | .error (e, n) => pure (.jobs (atDecl e n))
      | .ok () =>
        let cs ← Modular.copyRecs x w.reads.index w.emitted
        let owner ← Modular.ownerMap w.reach.ctx.toList
        let lines ← cs.mapM (copyLine w owner)
        pure (.accepted w.own.size (if x.isEmpty then #[] else lines) hoisted)

/-- con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
A worker's lines and exit code; `alone`: the process's one check, else its lines name it. -/
def workerMain (sp : ConLeche.Frontend.Olean.Roots) (m : Name) (cmp : Option Name)
    (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) (alone : Bool) :
    IO UInt8 := do
  let t0 ← IO.monoMsNow
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let who := if alone then "" else s!"module {m}: "
  match (workerPipeline sp m cmp mode pins maxNatSize).run (AState.init EStore.empty) with
  | .error e | .ok (.read e, _) =>
    IO.eprintln s!"con-ron-lean: module {m}: {e.message} ({modeTag})"
    return e.exitCode
  | .ok (.jobs e, _) =>
    let now ← IO.monoMsNow
    IO.eprintln s!"con-ron-lean: {who}{e.message} ({modeTag}) t={msSecs (now - t0)}s"
    return e.exitCode
  | .ok (.accepted n copies hoisted, _) =>
    if hoisted.size > 0 then
      IO.eprintln s!"con-ron-lean: {who}{hoisted.size} declarations hoisted ahead of the pinned \
        Nat operations they ground: {", ".intercalate hoisted.toList}"
    IO.println s!"con-ron-lean: {who}accepted {n} declarations ({modeTag})"
    if cmp.isSome then
      IO.println s!"con-ron-lean: {who}{copies.size} declarations of {m} are the loaded \
        constants of their names"
      for l in copies do IO.println s!"con-ron-lean: {l}"
    return 0

/-- con-leche: ConLeche/Driver/Dispatch.lean:63-87 runReq
con-leche: ConLeche/Driver/Modular.lean:90-137 checkModularG
**`--olean --module [--compare]` and `--olean --modular [--compare]`**: the root's (a compared
run's challenge's) closure walked through the trusted path alone where one is given; for
`--modular` the graph through the solution's lookup, then every module of it in the graph's order,
each its worker from fresh start values (`workerMain`, the challenge's the compare worker); the
run's verdict: 0 when every module's is, else the first failing module's code. -/
def modularMain (a : Args) (root : Name) (cmp : Option Name) (all : Bool) : IO UInt8 := do
  let modeTag : String := match a.mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let pins := ConLeche.natOpPinSets
  let sr : ConLeche.Frontend.Olean.Roots :=
    if a.trustedPath.isEmpty then { path := a.searchPath }
    else { path := a.trustedPath, fallback := a.searchPath }
  let pre : AM (Array Name) := do
    internReservedPins
    let pk ← Frontend.Olean.oleanPins
    let c ← internName root
    if cmp.isSome then
      if let some e ← chalWalk a.trustedPath a.searchPath pk c then fail e
    if !all then return #[root]
    let x ← match cmp with
      | some s => pure (some (c, ← internName s))
      | none => pure none
    let C ← Modular.graphOf stdFs pk sr [c] x
    C.mapM fun e => readName e.1
  match pre.run (AState.init EStore.empty) with
  | .error e =>
    IO.eprintln s!"con-ron-lean: graph: {e.message}"
    return e.exitCode
  | .ok (mods, _) =>
    if !all then return ← workerMain sr root cmp a.mode pins a.maxNatSize true
    let mut failed : Array (Name × UInt8) := #[]
    for m in mods do
      let c ← workerMain sr m (if m == root then cmp else none) a.mode pins a.maxNatSize false
      if c != 0 then failed := failed.push (m, c)
    match failed[0]? with
    | none =>
      IO.println s!"con-ron-lean: accepted {mods.size} modules ({modeTag})"
      return 0
    | some (m, c) =>
      IO.eprintln s!"con-ron-lean: {failed.size} of {mods.size} modules not accepted; the first in \
        the graph's order: {m} ({modeTag})"
      return c

/-- con-leche: ConLeche/Driver/Cli.lean:302-521 runArgs
`--check-graph`'s usage checks, con-leche's in its order, then the graph check
(`graphPipeline`). -/
def checkGraphUsage (a : Args) : IO UInt8 := do
  if a.olean || a.module || !a.constants.isEmpty || (!a.trustedPath.isEmpty && !a.compare) then
    return ← usageError "--check-graph takes none of --olean, --module and --constant, and \
      --trusted-search-path only with --compare"
  if a.files.isEmpty || (a.searchPath.isEmpty && a.trustedPath.isEmpty) then
    return ← usageError "--check-graph takes one or more module names and a --search-path=DIRS"
  if let some m := a.files.find? (fun f => (Frontend.Olean.parseModName f).isNone) then
    return ← usageError s!"not a module name: {Display.str m}"
  if a.compare then
    match (a.files.filterMap Frontend.Olean.parseModName).toList with
    | [c, s] =>
      if c == s then
        return ← usageError "--compare takes two different modules, a challenge and its solution"
      return ← graphVerdictIO ((graphPipeline a.trustedPath a.searchPath [c] (some s)).run
        (AState.init EStore.empty) |>.map (·.1))
    | _ => return ← usageError "--check-graph --compare takes two module names, a challenge and \
        its solution"
  graphVerdictIO ((graphPipeline [] a.searchPath (a.files.filterMap
    Frontend.Olean.parseModName).toList none).run (AState.init EStore.empty) |>.map (·.1))

/-- con-leche: Main.lean:56-103 main
con-leche: ConLeche/Driver/Cli.lean:302-521 runArgs
`--help` before any `--` prints the help on stdout and exits 0, reading
nothing.  A bad flag prints its message and a pointer to `--help` on stderr
and exits 3; no arguments prints the invocation forms and the pointer; more than
one file is a usage error.  Everything else runs the checker IN THIS PROCESS. -/
def main (args : List String) : IO UInt8 := do
  if helpWanted args then
    IO.println helpText
    return 0
  let a := parseArgs args {}
  if let some msg := a.bad then
    IO.eprintln s!"con-ron-lean: {msg}"
    IO.eprintln tryHelp
    return 3
  let pins := ConLeche.natOpPinSets
  if a.checkGraph then
    return ← checkGraphUsage a
  if a.olean then
    if a.files.isEmpty || (a.searchPath.isEmpty && a.trustedPath.isEmpty) then
      IO.eprintln "con-ron-lean: --olean takes one or more module names and a \
        --search-path=DIRS"
      IO.eprintln tryHelp
      return 3
    if let some m := a.files.find? (fun f => (Frontend.Olean.parseModName f).isNone) then
      IO.eprintln s!"con-ron-lean: not a module name: {Display.str m}"
      IO.eprintln tryHelp
      return 3
    if let some c := a.constants.find? (fun c => (Frontend.Olean.parseConstName c).isNone) then
      IO.eprintln s!"con-ron-lean: not a constant's name: {Display.str c}"
      IO.eprintln tryHelp
      return 3
    let roots := a.files.filterMap Frontend.Olean.parseModName
    if a.compare then
      match roots.toList with
      | [c, s] =>
        if c == s then
          return ← usageError "--compare takes two different modules, a challenge and its solution"
        if a.module || a.modular || a.scheduled then
          if !a.constants.isEmpty || (a.module && a.scheduled) ||
              (a.modular && (a.module || a.scheduled)) then
            return ← usageError "--compare with --module, --modular or --schedule takes one of \
              them, and no --constant"
          if a.module then return ← modularMain a c (some s) false
          if a.modular then return ← modularMain a c (some s) true
          return ← scheduleMain a c (some s)
        let cs := if a.constants.isEmpty then none
          else some (a.constants.filterMap Frontend.Olean.parseConstName)
        return ← compareOleanMain a.trustedPath a.searchPath c s cs a.mode pins a.maxNatSize
      | _ => return ← usageError "--compare takes two module names, a challenge and its solution"
    if !a.trustedPath.isEmpty && (!a.module || a.modular || a.scheduled) then
      return ← usageError "--trusted-search-path takes --compare or --module"
    if a.scheduled then
      if roots.size != 1 || !a.constants.isEmpty || a.module || a.modular then
        return ← usageError "--schedule takes one module name, and none of --constant, --module \
          and --modular"
      return ← scheduleMain a roots[0]! none
    if a.modular then
      if roots.size != 1 || !a.constants.isEmpty || a.module then
        return ← usageError "--modular takes one module name, and neither --constant nor --module"
      return ← modularMain a roots[0]! none true
    if a.module then
      if roots.size != 1 || !a.constants.isEmpty then
        return ← usageError "--module takes one module name and no --constant"
      return ← modularMain a roots[0]! none false
    let cs := if a.constants.isEmpty then none
      else some (a.constants.filterMap Frontend.Olean.parseConstName)
    return ← checkMainOlean a.searchPath roots cs a.mode pins a.maxNatSize
  if a.compare then
    if !a.searchPath.isEmpty || !a.constants.isEmpty || a.module || a.modular || a.scheduled ||
        !a.trustedPath.isEmpty then
      return ← usageError "--compare on two lean4export files takes none of --search-path, \
        --trusted-search-path, --constant, --module, --modular and --schedule (they take --olean)"
    match a.files.toList with
    | [c, s] =>
      if c == s then
        return ← usageError "--compare takes two different files, a challenge and its solution"
      return ← compareJsonMain c s a.mode pins a.maxNatSize
    | _ => return ← usageError "--compare takes two files, a challenge and its solution"
  if !a.searchPath.isEmpty || !a.constants.isEmpty || a.module || a.modular || a.scheduled ||
      !a.trustedPath.isEmpty then
    return ← usageError "--search-path, --trusted-search-path, --constant, --module, --modular \
      and --schedule take --olean"
  match a.files.toList with
  | [file] =>
    checkMain file a.mode pins a.maxNatSize a.progress
  | [] =>
    IO.eprintln synopsis
    IO.eprintln tryHelp
    return 3
  | _ =>
    IO.eprintln "con-ron-lean: takes one input file"
    IO.eprintln tryHelp
    return 3

end ConRon.Arena

-- (The top-level `main` Lake's `con-ron-lean` executable needs lives in
-- `ConRon/Arena/Exe.lean`, not here: task #97-COMPOSE found that a top-level
-- `main` in this module collides with `ConRon/Dump/Pins.lean`'s the moment
-- one file imports both this module and the pin dump, as the capstone's
-- import closure once did.)
