module

public import ConRon.Arena.Frontend.Prelude
public import ConRon.Arena.Frontend.Olean.Records
public import ConRon.Arena.Checker
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

/-- con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
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

/-- con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
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
def runPipelineTail (mode : CheckMode) (pins : List NatOpPinSet)
    (pre : Frontend.PreludeIx) (r : Frontend.ParseResultD) :
    AM (Except CheckError Nat) := do
  -- The verdict number is read HERE, before the fold, so that `r` dies at
  -- `preparePrelude` instead of being pinned across the whole check (DESIGN
  -- §8.4: decide the rare branch, and read what a later line needs, BEFORE
  -- the expensive step).
  let records := r.decls.size
  let ds ← Frontend.preparePrelude pre r.decls
  let ipins ← internAllPins pins
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

/-- con-leche: none — the millisecond-to-seconds rendering of the
heartbeat's `t=` field.  con-leche has it as `ConLeche.Cached.msSecs`,
which `scripts/provenance-skip.txt` lists as driver-only rendering the
Rust port does not carry; the arena's driver prints the same line, so it
carries the same three lines of arithmetic. -/
def msSecs (ms : Nat) : String :=
  let s := ms / 1000
  let c := (ms % 1000) / 10
  s!"{s}.{if c < 10 then "0" else ""}{c}"

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:179-187 foldChunks
**THE READ LOOP**: the handle read strictly forward, 4 MiB at a time, each
buffer fed to `Frontend.chunkStep` and then dropped; the first empty read is
its end of file and `Frontend.chunkFinish` closes the stream.  Never seeked,
never re-opened, and no scratch file exists anywhere.  Deviation from
`foldChunks`, whose reads are positional through con-leche's `CheckerIO` class:
these are sequential and forward, and there is no class.

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

/-- con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
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
      match (runPipelineTail mode pins pre r).run s with
      | .error e => pure (.error e, chunks, tParse, 0)
      | .ok (v, s') => pure (v, chunks, tParse, s'.store.persCount)

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:449-461 instCheckerIOIO
The binary's file operations, as the pure functions the reader takes: `IO` run where
it is asked, outside every theorem (`Frontend/Olean/Files.lean`'s note). -/
unsafe def stdFsImpl : Frontend.Olean.OleanFs where
  pathExists p := unsafeBaseIO do
    match ← (p.pathExists : IO Bool).toBaseIO with
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
    match ← (CheckerIO.readRange p off len : IO ByteArray).toBaseIO with
    | .ok b => pure (.ok b)
    | .error e => pure (.error (toString e))
  fileSize p := unsafeBaseIO do
    match ← (CheckerIO.fileSize p : IO Nat).toBaseIO with
    | .ok b => pure (.ok b)
    | .error e => pure (.error (toString e))

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:449-461 instCheckerIOIO
The binary's file operations, opaque to the logic. -/
@[implemented_by stdFsImpl]
opaque stdFs : Frontend.Olean.OleanFs

/-- con-leche: ConLeche/Driver/CheckMain.lean:87-98 readInputG
**The seam on the `.olean` path**: the head of the pipeline, the reader in place of
the chunks' fold, the tail.  The roots and constants are interned first.
Deviation: the twin reads every theorem's value up front (`readOleansFull`,
upstream's own eager read), where the binary reads each in its job
(`driver::olean_job`, con-leche's `oleanJobRun`); upstream's `buildIndex_fill`
says the index is the same at any values. -/
def oleanPipeline (sp : List System.FilePath) (roots : Array Name) (constants : Option (Array Name))
    (mode : CheckMode) (pins : List NatOpPinSet) : AM (Except CheckError Nat) := do
  match ← runPipelineHead with
  | .error (e, n) => pure (.error (Frontend.atLine e n))
  | .ok (pre, _) =>
    let rs ← roots.mapM internName
    let cs ← match constants with
      | none => pure none
      | some cs => pure (some (← cs.mapM internName))
    match ← Frontend.Olean.readOleansFull stdFs sp rs cs with
    | .error (e, n) => pure (.error (Frontend.atLine e n))
    | .ok ds => runPipelineTail mode pins pre ⟨ds⟩

/-- con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
The driver on the `.olean` path. -/
def checkMainOlean (sp : List System.FilePath) (roots : Array Name) (constants : Option (Array Name))
    (mode : CheckMode) (pins : List NatOpPinSet) : IO UInt8 := do
  let t0 ← IO.monoMsNow
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let verdict : Except CheckError Nat := match (oleanPipeline sp roots constants mode pins).run (AState.init EStore.empty) with
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

/-- con-leche: ConLeche/Driver/Cli.lean:104-108 synopsis
The invocation forms, printed on their own when there are no arguments. -/
def synopsis : String := String.intercalate "\n" [
  "Usage:",
  "  con-ron-lean [OPTIONS] [--] FILE.ndjson",
  "  con-ron-lean [OPTIONS] --olean --search-path=DIRS [--] MODULE..."]

/-- con-leche: ConLeche/Driver/Cli.lean:110-111 tryHelp
The line after a usage error. -/
def tryHelp : String := "Try 'con-ron-lean --help' for more information."

/-- con-leche: ConLeche/Driver/Cli.lean:113-141 helpText
The `--help` text: con-leche's, with this binary's name, its one flag of its own
(`--no-pins`) and con-ron's documentation.  `--jobs` is accepted and validated,
and this binary checks on one worker whatever it says. -/
def helpText : String := String.intercalate "\n" [
  "Check Lean declarations from a lean4export file or from .olean modules.",
  "",
  synopsis,
  "",
  "Options:",
  "  --verified          Check in the mode the soundness theorem covers (default)",
  "  --trusted           Skip the checks only the proof needs; outside the theorem",
  "  --jobs=N            Accepted for the command line's sake; one worker always",
  "  --progress[=PACE]   Report progress on stderr: PACE is N declarations",
  "                      (default 1), P% of each phase, or Ss seconds",
  "  --no-pins           Testing only: check with no Nat pin list",
  "  --help              Print this help and exit",
  "  --                  End of options",
  "",
  ".olean input:",
  "  --olean             Read modules and their import closure from .olean files",
  "  --search-path=DIRS  Colon-separated .olean directories; repeatable",
  "  --constant=NAME     Check only NAME and what it mentions; repeatable",
  "",
  "Exit status:",
  "  0  accepted",
  "  1  rejected: a declaration is invalid",
  "  2  declined: an unsupported feature",
  "  3  error: bad usage, malformed input or an internal failure",
  "",
  "Documentation:",
  "  README.md and OVERVIEW.md of the con-ron repository"]

/-- con-leche: ConLeche/Driver/Cli.lean:143-159 Args
The parsed command line.  `progress = .off` is "no flag given"; `jobs = none`
is "no flag given", one worker per hardware thread. -/
structure Args where
  mode : CheckMode := .verified
  progress : Pace := .off
  jobs : Option Nat := none
  noPins : Bool := false
  /-- `--olean`: the positional arguments are root module names. -/
  olean : Bool := false
  /-- `--search-path=DIR:DIR…`: where `--olean` looks for the files. -/
  searchPath : List System.FilePath := []
  /-- `--constant=NAME`: with `--olean`, the constants to start from. -/
  constants : Array String := #[]
  files : Array String := #[]
  bad : Option String := none

/-- con-leche: ConLeche/Driver/Cli.lean:175-209 parseArgs
The argument parse, clause for clause: the mode flags in either order with
the heartbeat, `=`-carrying spellings after the bare ones, an unknown
`-`-leading word a usage error, everything else a file. -/
def parseArgs : List String → Args → Args
  | [], a => a
  | "--" :: rest, a => { a with files := a.files ++ rest.toArray }
  | "--verified" :: rest, a => parseArgs rest { a with mode := .verified }
  | "--trusted" :: rest, a => parseArgs rest { a with mode := .trusted }
  | "--progress" :: rest, a => parseArgs rest { a with progress := .every 1 }
  | "--no-pins" :: rest, a => parseArgs rest { a with noPins := true }
  | "--olean" :: rest, a => parseArgs rest { a with olean := true }
  | s :: rest, a =>
    if s.startsWith "--progress=" then
      match progressPace (s.drop "--progress=".length).toString with
      | .ok n => parseArgs rest { a with progress := n }
      | .error msg => { a with bad := some msg }
    else if s.startsWith "--jobs=" then
      match jobsCount (s.drop "--jobs=".length).toString with
      | .ok n => parseArgs rest { a with jobs := some n }
      | .error msg => { a with bad := some msg }
    else if s == "--jobs" then
      { a with bad := some "--jobs takes a worker count: --jobs=<n>; omit the \
          flag for one worker per hardware thread" }
    else if s.startsWith "--constant=" then
      parseArgs rest { a with constants := a.constants.push (s.drop "--constant=".length).toString }
    else if s.startsWith "--search-path=" then
      parseArgs rest { a with searchPath := a.searchPath ++
        (((s.drop "--search-path=".length).toString.splitOn ":").filter (· != "")).map System.FilePath.mk }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {Display.str s}" }
    else parseArgs rest { a with files := a.files.push s }

/-- con-leche: ConLeche/Driver/Cli.lean:161-164 helpWanted
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

/-- con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
The driver, which `main` calls in process: read the chunks, run the seam,
print the verdict.  Every VERDICT line names the mode — a `--trusted` run,
the unverified lane, must never be mistaken for a `--verified` one in a
log, whatever it says — and what the heartbeat prints between the steps
touches no verdict, which is why there is one path and not two. -/
def checkMain (file : String) (mode : CheckMode) (pins : List NatOpPinSet)
    (pace : Pace) : IO UInt8 := do
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
  let (verdict, chunks, tParse, nodes) ← runPipelineIO h mode pins
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

/-- con-leche: Main.lean:32-91 main
con-leche: ConLeche/Driver/Cli.lean:219-304 runArgs
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
  let pins := if a.noPins then [] else ConLeche.natOpPinSets
  if a.olean then
    if a.files.isEmpty || a.searchPath.isEmpty then
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
    let cs := if a.constants.isEmpty then none
      else some (a.constants.filterMap Frontend.Olean.parseConstName)
    return ← checkMainOlean a.searchPath (a.files.filterMap Frontend.Olean.parseModName) cs a.mode pins
  if !a.searchPath.isEmpty || !a.constants.isEmpty then
    IO.eprintln "con-ron-lean: --search-path and --constant take --olean"
    IO.eprintln tryHelp
    return 3
  match a.files.toList with
  | [file] =>
    checkMain file a.mode pins a.progress
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
