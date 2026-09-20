import ConRon.Arena.Frontend.Prelude

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
pipe.  con-leche folds the parse step INTO that loop; the pure meaning of
its loop is `parseChunks` of the chunks the handle handed out, which is
why the seam takes the chunk LIST.  Reading them into a list first is the
stub's simplification and P2e's to undo: the loop it grows is
`parseExportHandleD`'s, and what it computes is `runPipeline` of the same
list (con-leche's `parseChunks_eq_parseExportD`).
-/

namespace ConRon.Arena

/-- con-leche: ConLeche/Kernel/Env.lean:20-62 CheckMode
The checking mode, verbatim (DESIGN.md §8's census class (P): pure data,
no term inside, copied rather than twinned).  The verified mode is the one
the capstones are about; the trusted mode is the same bodies with the
certification-only work switched off.  P2d moves this to the `Env` twin. -/
inductive CheckMode where
  | verified
  | trusted
  deriving DecidableEq, Repr

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

/-- con-leche: ConLeche/Kernel/NatOpPinSet.lean:28-51 NatOpPinSet
One toolchain's `Nat`-operation pins.

**Not yet the twin.**  con-leche's record holds sixteen `Expr` fields —
eight pinned defining expressions and eight certificate-proof lists — so
its twin is §8's census class (T): the same sixteen fields over `EIdx`
handles into the persistent tier, decoded into the store at parse time.
There is no store yet, so what stands here is the one field that is not a
term (the toolchain string, which the decline message names) and a note
saying so.  P2d replaces it whole. -/
structure NatOpPinSet where
  toolchain : String

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
The pin variants the binary hands the checker, in the order the install
gate tries them: con-leche splices one per committed dump with the
`#load_natop_pins` elaborator cited here, so the list has no source range
of its own and the command pinned above is what it is generated from.  The
arena decodes the same dumps into the persistent tier at P2d; until then
the list is empty, which is exactly `--no-pins` and declines every stream
that defines `Nat.div`. -/
def natOpPinSets : List NatOpPinSet := []

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
`EStore`, and the prepared record list is built.  What is still a stub is the
FOLD, so a run that parses cleanly ends in a decline that names the count it
would have checked.  Every verdict the frontend itself reaches — a malformed
line, a rebound index, an `unsafe` declaration, a block whose redundant
fields contradict its own records, a mutual or nested block the declining
modeller turns away — is already this function's answer, with con-leche's own
exit code.

P2c (the `Core` knot) and P2d (the checker and the declaration check) replace
the last three lines; the driver below is already what it will be. -/
def runPipelineM (md : Frontend.Modeller) (chunks : List ByteArray) :
    AM (Except (CheckError × Nat) (Nat × Nat × Nat × Nat)) := do
  match ← Frontend.builtinPreludeE md with
  | .error e => pure (.error e)
  | .ok pre =>
    match ← Frontend.parseChunks md chunks with
    | .error e => pure (.error e)
    | .ok r =>
      let _ ← Frontend.preparePrelude pre r.decls
      let s ← get
      pure (.ok (r.decls.size - r.genRecords,
        s.store.nodeCount, s.store.ls.nodeCount, s.store.ns.nodeCount))

/-- con-leche: Main.lean:461-711 checkMain
**THE SEAM ITSELF**: `runPipelineM` run at the empty store, with the parse's
own `(CheckError × Nat)` position folded into the message (`Frontend.atLine`)
because this signature has no position channel. -/
def runPipeline (chunks : List ByteArray) (_mode : CheckMode)
    (_pins : List NatOpPinSet) : Except CheckError Nat :=
  match (runPipelineM Frontend.declineModeller chunks).run (AState.init EStore.empty) with
  | .error e => .error e
  | .ok (.error (e, n), _) => .error (Frontend.atLine e n)
  | .ok (.ok (records, nE, nL, nN), _) =>
    .error (.notImplemented
      s!"arena checker: fold not yet implemented ({records} declarations parsed; \
        store: {nE} expression, {nL} level, {nN} name nodes)")

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
The input's chunks, in order: the handle read strictly forward, 4 MiB at a
time, stopping at the first empty read (its end of file).  Never seeked,
never re-opened, never asked for its size — so the source may be a pipe,
and no scratch file exists anywhere (con-leche's task #180).

con-leche interleaves the parse step with these reads and so never holds
the whole input; this reads them into a list first, which is the stub's
simplification (see the module note) and P2e's to undo. -/
partial def readChunks (h : IO.FS.Handle) (acc : Array ByteArray) :
    IO (List ByteArray) := do
  let buf ← h.read chunkSize
  if buf.isEmpty then return acc.toList else readChunks h (acc.push buf)

/-- con-leche: Main.lean:714-944 usage
The usage text, on stdout under `--help` and on stderr before a usage
error.  It is con-leche's, shortened to what this binary actually has and
saying plainly what it does not: the shape and the vocabulary are the same
so that a script written against one reads against the other. -/
def usage : String := String.intercalate "\n" [
  "usage: con-ron-lean [--verified|--trusted] [--jobs=<n>] [--progress[=<stride>]] FILE.ndjson",
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
  "STATUS.  The FRONTEND is real: the input is parsed into the arena's",
  "persistent tier and every verdict the parse itself reaches -- a malformed",
  "line, a rebound index, an unsafe declaration, an inductive block whose",
  "redundant fields contradict its own records -- is this binary's answer,",
  "with con-leche's exit code.  The FOLD is not written yet, so a stream that",
  "parses cleanly ends in a decline (exit 2) naming the declaration count it",
  "would have checked.  DESIGN.md section 8.6's P2f gate is run through this",
  "command line."]

/-- con-leche: Main.lean:946-960 Args
The parsed command line.  `progress = 0` is "no flag given"; `jobs = none`
is "no flag given", one worker per hardware thread. -/
structure Args where
  mode : CheckMode := .verified
  progress : Nat := 0
  jobs : Option Nat := none
  noMark : Bool := false
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
def checkMain (file : String) (mode : CheckMode) (stride : Nat) : IO UInt32 := do
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
  let chunks ← readChunks h #[]
  let tRead ← IO.monoMsNow
  if stride > 0 then
    IO.eprintln s!"con-ron-lean: read done: {chunks.length} chunks \
      t={msSecs (tRead - t0)}s"
    (← IO.getStderr).flush
  match runPipeline chunks mode natOpPinSets with
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
  | [file] => checkMain file a.mode a.progress
  | _ =>
    IO.eprintln usage
    return 3

end ConRon.Arena

/-- con-leche: Main.lean:992-1019 main
Lake's entry point.  A `lean_exe`'s root module must declare a TOP-LEVEL
`main`, and the driver above lives in the `ConRon.Arena` namespace with the
rest of (B), so this forwards to it — the arrangement `ConRon/Gen/Main.lean`
already uses. -/
def main (args : List String) : IO UInt32 := ConRon.Arena.main args
