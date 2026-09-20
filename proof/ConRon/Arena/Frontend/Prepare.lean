/-
# `ConRon.Arena.Frontend.Prepare` — what happens between the file and the fold
(task #97e)

con-leche's `ConLeche/Frontend/Prepare.lean`, over handles.  `preparePrelude`
is total and pure — no record of the stream is dropped, rewritten or retagged
— and it does two things:

1. **the prelude's declarations first**, the stream's OWN copy of each where
   the stream has one and a synthesised one only where it has none, so a
   stream that declares the toolchain's `Bool` is checked on its own `Bool`
   record;
2. **the ground hoist**: a pinned `Nat` operation's stream-certified
   structural ground is moved ahead of it when the stream declares it later.

Moving a record earlier can only reject, never accept, which is why the spec
con-leche proves is as simple as it is:

    ∃ extra, (∀ d ∈ extra, d ∈ prelude) ∧
      (preparePrelude ds).toList.Perm (ds.toList ++ extra)

**Step 2 is a placeholder in task #97e part 1** (`hoistNatOpGround` below).
The direction is the safe one: con-leche's own argument for the hoist is that
*not* moving a pinned operation's ground ahead of it makes the operation's
install DECLINE, so an identity hoist can only turn an accept into a decline
and never the other way round.  Part 2 ports
`ConLeche/Frontend/NatOpGround.lean` proper, into a module of its own.

**Where the monad comes from.**  Only `preludeKey`, whose `.anonymous`
fall-through has to be interned, and the two functions that call it; `pick`
and `declares` are pure, exactly as con-leche's are, because
`IDeclaration.names` is (`Arena/Env.lean`'s `IProjTable.tableName` note).
Nothing in this module reads or writes a term.
-/
import ConRon.Arena.Frontend.ExportC
import ConRon.Arena.Frontend.NatOpGround

namespace ConRon.Arena.Frontend

open ConLeche

/-! ## The prelude -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:83-88 PreludeIx — the built-in
prelude: its records, in the order the committed file declares them.
Dependency-correct by construction — it is an export of the toolchain's own
environment — which is what makes it usable as the front of every prepared
stream. -/
structure PreludeIx where
  decls : Array IDeclaration := #[]

/-- con-leche: ConLeche/Frontend/Prepare.lean:90-93 preludeKey — the name a
prelude record is looked up by: the block's type former, the quotient
constant, the axiom.  con-leche's `.anonymous` fall-through is the interned
anonymous name. -/
def preludeKey (d : IDeclaration) : AM NIdx := do
  match d.names.head? with
  | some n => pure n
  | none => internNNode .anonymous

/-! ## Pulling the stream's own copy out

A prelude declaration the stream declares itself is MOVED, not duplicated: the
stream's record is what the fold checks, and it must appear exactly once.  A
stream is millions of records long, so nothing here rebuilds it as a list.

con-leche keeps a `List` SPECIFICATION beside the array implementation
(`pickSpec`, `frontSpec`) that its own lemmas are stated over; the Rust port
skips both (`scripts/provenance-skip.txt`) and so does (B) — a specification
for a proof that is not written yet is best written with it (DESIGN §8.6's
reordering: code first, proofs later). -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:109-110 declares — the name-test
a record is picked by. -/
def declares (n : NIdx) (d : IDeclaration) : Bool := d.names.contains n

/-- con-leche: ConLeche/Frontend/Prepare.lean:121-124 pick — the first record
declaring `n`, and the array without it.  `Array.eraseIdxIfInBounds` is
`List.eraseIdx`'s twin, and the out-of-range case — `findIdx` returns the size
when no record declares the name — is exactly "the stream does not declare it,
nothing is erased".

PURE, like con-leche's: `IDeclaration.names` is pure because
`IConstantInfo.name` is (`Arena/Env.lean`'s `tableName` note), which is what
keeps `findIdx`'s predicate a predicate.  A stream is millions of records
long, and this runs once per prelude record over all of them. -/
def pick (n : NIdx) (ds : Array IDeclaration) :
    Option IDeclaration × Array IDeclaration :=
  let i := ds.findIdx (declares n)
  (ds[i]?, ds.eraseIdxIfInBounds i)

/-- con-leche: ConLeche/Frontend/Prepare.lean:126-135 frontOf — the front of
the prepared stream (the prelude's declarations, each one the stream's own copy
where the stream has one) and the rest of the stream, in the stream's order. -/
def frontOf (acc : Array IDeclaration) :
    List IDeclaration → Array IDeclaration →
    AM (Array IDeclaration × Array IDeclaration)
  | [], ds => pure (acc, ds)
  | p :: ps, ds => do
    let (m, ds') := pick (← preludeKey p) ds
    frontOf (acc.push (m.getD p)) ps ds'

/-! ## The ground hoist -/

/-! ## The ground hoist — **no longer a placeholder** (task #97d)

Task #97e part 1 shipped the identity here, because the pass needs the
kernel's `natOpNames`/`natDivModNames`/`natOpDeps` name lists and the arena
had no twin of them until P2d interned the pins.  It has them now, and the
real pass is `Arena/Frontend/NatOpGround.lean`'s `hoistNatOpGround`, a module
of its own exactly as con-leche's is.  `prepareD` below calls it. -/

/-! ## The prepared stream -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:148-157 Prepared — the prepared
stream and the driver's receipts. -/
structure Prepared where
  /-- the prelude's declarations, then the rest of the stream -/
  decls : Array IDeclaration
  /-- how many prelude records the stream did not declare and this step
  synthesised -/
  synthesised : Nat := 0
  /-- the records moved ahead of a pinned `Nat` operation they ground -/
  hoisted : Array NIdx := #[]

/-- con-leche: ConLeche/Frontend/Prepare.lean:159-163 prepareD —
`preparePrelude`, with its receipts. -/
def prepareD (pre : PreludeIx) (ds : Array IDeclaration) : AM Prepared := do
  let (front, rest) ← frontOf #[] pre.decls.toList ds
  let (decls, hoisted) ← hoistNatOpGround (front ++ rest)
  pure ⟨decls, decls.size - ds.size, hoisted⟩

/-- con-leche: ConLeche/Frontend/Prepare.lean:165-172 preparePrelude — the
parsed stream, prepared for the fold: the prelude's declarations first (the
stream's own copies where it has them), the rest of the stream after them,
every pinned `Nat` operation's stream-certified ground ahead of it.  An array
in and an array out, the shape the parse returns and the fold consumes. -/
def preparePrelude (pre : PreludeIx) (ds : Array IDeclaration) :
    AM (Array IDeclaration) := do
  pure (← prepareD pre ds).decls

end ConRon.Arena.Frontend
