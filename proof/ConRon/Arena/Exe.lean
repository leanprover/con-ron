module

public import ConRon.Arena.Main

@[expose] public section

/-!
# `con-ron-lean`'s entry point

The root of Lake's `con-ron-lean` executable, and nothing else.  It is its own
module so that `ConRon/Arena/Main.lean` — which the `ConRon.Arena` root
imports — declares no top-level `main`: two modules that do
(`ConRon/Dump/Pins.lean` is the other) cannot sit in one import closure, and
the root has to stay importable by any closure (task #97-COMPOSE).
-/

/-- con-leche: Main.lean:32-54 flushStdoutStderr
The flush before the exit: both streams, and the exit code — `code`, or 3 if the
flush fails (con-leche task #490): a run whose output did not get out has no
verdict anyone read.  The message is best-effort. -/
def flushStdoutStderr (code : UInt8) : IO UInt8 := do
  try
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    pure code
  catch e =>
    try IO.eprintln s!"con-ron-lean: cannot write the output: {e}" catch _ => pure ()
    pure 3

/-- con-leche: Main.lean:56-103 main
con-leche: ConLeche/Driver/Cli.lean:239-324 runArgs
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove Exe.main_bridge, then delete this line
Lake's entry point.  A `lean_exe`'s root module must declare a TOP-LEVEL
`main`, and the driver (`ConRon/Arena/Main.lean`) lives in the `ConRon.Arena` namespace with the
rest of (B), so this forwards to it.  Around it, con-leche's `runArgs`/`main` split: an uncaught IO
error is exit 3, never a reject (con-leche task #335), and the process ends
right after the verdict with the two streams flushed (`flushStdoutStderr`, 3 if
that fails), without unwinding the heap (task #336). -/
def main (args : List String) : IO Unit := do
  let code ← try ConRon.Arena.main args catch e => do
    (try IO.eprintln s!"con-ron-lean: internal error: {ConRon.Arena.displayPath (toString e)}" catch _ => pure ())
    pure 3
  let code ← flushStdoutStderr code
  IO.Process.exit code
