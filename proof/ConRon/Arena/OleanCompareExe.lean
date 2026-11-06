module

public import ConRon.Arena.OleanCompare

@[expose] public section

/-!
# `con-ron-lean-olean-compare`'s entry point

The root of Lake's executable, and nothing else, for `Exe.lean`'s reason: a module
declaring a top-level `main` cannot sit in another's import closure.
-/

/-- con-leche: OleanCompare.lean:150-204 main
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove OleanCompareExe.main_bridge, then delete this line
Lake's entry point. -/
def main (args : List String) : IO UInt32 := do
  let c ← ConRon.Arena.OleanCompare.main args
  return c.toUInt32
