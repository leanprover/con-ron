/-!
A FIXTURE, not a module of the arena checker: `scripts/provenance-selftest.py`
copies it, substitutes its placeholders with the citation bodies
`provenance.py locate` computes at the *current* pin (so a con-leche bump
cannot rot the fixture), and runs `provenance.py check` over the copy.

This half must come out CLEAN.  It exercises every shape the Lean side of the
gate accepts: a one-line citation, a citation that opens a multi-line doc
comment, two citations on one item, an explicit `none`, and a `theorem` with
no citation at all (the arena's own verification is not a port of anything).
-/

namespace ConRon.ArenaFixture

/-- con-leche: @@Name@@ -/
structure GoodOneLine where
  n : Nat

/-- con-leche: @@Name@@
The citation opens the doc comment and the prose follows it: the shape most
twins are written in, since the delta from the cited code belongs right
here. -/
def goodMultiLine (x : Nat) : Nat := x

/-- con-leche: @@Name@@
con-leche: @@Name.beq@@
A twin that merges two con-leche declarations lists both, one per line — the
second as a bare `con-leche:` line inside the doc comment. -/
def goodTwoCitations (x : Nat) : Nat := x

/-- con-leche: none — the store's own handle arithmetic, which con-leche has
no counterpart of (DESIGN.md §8.3). -/
abbrev GoodNone := UInt32

/-- The arena's own verification (DESIGN.md §8.6 P2a: "the arena's own
verification lives beside it"), so no citation is required. -/
theorem good_uncited_theorem : True := trivial

/-- con-leche: @@Name@@
A cited theorem is checked like any other citation; it is only the
REQUIREMENT that is lifted for theorems, not the check. -/
theorem good_cited_theorem : True := trivial

end ConRon.ArenaFixture
