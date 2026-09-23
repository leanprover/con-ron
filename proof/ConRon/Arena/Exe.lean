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

/-- con-leche: Main.lean:992-1019 main
Lake's entry point.  A `lean_exe`'s root module must declare a TOP-LEVEL
`main`, and the driver (`ConRon/Arena/Main.lean`) lives in the `ConRon.Arena` namespace with the
rest of (B), so this forwards to it — the arrangement `ConRon/Gen/Main.lean`
already uses. -/
def main (args : List String) : IO UInt32 := ConRon.Arena.main args
