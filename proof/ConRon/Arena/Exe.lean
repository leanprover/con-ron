import ConRon.Arena.Main

/-!
# `con-ron-lean`'s entry point

The root of Lake's `con-ron-lean` executable, and nothing else.  It is its own
module so that `ConRon/Arena/Main.lean` — which Theorem 1's byte-level
capstone imports for `runPipeline` — declares no top-level `main`: two
modules that do (`ConRon/Dump/Pins.lean` is the other) cannot sit in one
import closure, and `ConRon/Capstone.lean` is exactly such a closure (task
#97-COMPOSE).
-/

/-- con-leche: Main.lean:430-487 main
con-leche: Main.lean:360-428 run
Lake's entry point.  A `lean_exe`'s root module must declare a TOP-LEVEL
`main`, and the driver (`ConRon/Arena/Main.lean`) lives in the `ConRon.Arena` namespace with the
rest of (B), so this forwards to it — the arrangement `ConRon/Gen/Main.lean`
already uses.  Around it, con-leche's `run`/`main` split: an uncaught IO
error is exit 3, never a reject (con-leche task #335), and the process ends
right after the verdict with the two streams flushed, without unwinding the
heap (task #336). -/
def main (args : List String) : IO UInt32 := do
  let code ← try ConRon.Arena.main args catch e => do
    (try IO.eprintln s!"con-ron-lean: internal error: {e}" catch _ => pure ())
    pure 3
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit code.toUInt8
