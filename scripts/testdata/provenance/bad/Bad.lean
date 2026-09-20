/-!
The other half of the fixture (see `good/Good.lean`): every finding the Lean
side of the gate must raise, one per declaration.  `provenance-selftest.py`
asserts the exact set, so a finding that stops being raised — or one that
starts being raised twice — fails the gate.
-/

namespace ConRon.ArenaFixture

/-- con-leche: ConLeche/Kernel/NoSuchFile.lean:1-2 nothing
MISSING: the cited file is not in the pinned con-leche. -/
def badMissingFile : Nat := 0

/-- con-leche: ConLeche/Kernel/Name.lean:900000-900001 Name
RANGE: the cited lines are outside the file. -/
def badRange : Nat := 1

/-- con-leche: ConLeche/Kernel/Name.lean:1-3 Name
NODECL: lines 1-3 are the module header, and declare nothing. -/
def badNoDecl : Nat := 2

/-- con-leche: @@#Name.beq@@ Name
NAME: the range is a real declaration's (`Name.beq`'s), but the name cited
is another declaration's. -/
def badName : Nat := 3

/-- con-leche: this is not a citation and not a `none`
MALFORMED: the body parses as neither form. -/
def badMalformed : Nat := 4

/-- UNCITED: a `def` with a doc comment and no `con-leche:` line at all. -/
def badUncited : Nat := 5

/-- con-leche: @@Name@@ -/
-- con-leche: CHANGED since deadbeef — re-port, re-test, re-prove Bad.badMarked_bridge, then delete this line
def badMarked : Nat := 6

end ConRon.ArenaFixture
