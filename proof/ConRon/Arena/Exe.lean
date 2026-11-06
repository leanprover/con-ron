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

/-- con-leche: Main.lean:32-91 main
con-leche: ConLeche/Driver/Cli.lean:219-304 runArgs
Lake's entry point.  A `lean_exe`'s root module must declare a TOP-LEVEL
`main`, and the driver (`ConRon/Arena/Main.lean`) lives in the `ConRon.Arena` namespace with the
rest of (B), so this forwards to it.  Around it, con-leche's `runArgs`/`main` split: an uncaught IO
error is exit 3, never a reject (con-leche task #335), and the process ends
right after the verdict with the two streams flushed, without unwinding the
heap (task #336). -/
def main (args : List String) : IO Unit := do
  let code ← try ConRon.Arena.main args catch e => do
    (try IO.eprintln s!"con-ron-lean: internal error: {ConRon.Arena.displayPath (toString e)}" catch _ => pure ())
    pure 3
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit code
