/-
# `ConRon.Arena.Intern` — con-leche's pinned VALUES into the store

DESIGN §8.3, lesson 4 ("intern the representation, not the algorithm") applied
to the checker's PINNED DATA.

Three families of con-leche declaration are pure `Expr` / `ConstantInfo`
*values* written out by hand or spliced by an elaborator, and nothing about
them is an algorithm:

* the basis blocks (`ConLeche/Kernel/Basis*.lean`, `BasisKind.declsA` — the
  annotated `Eq`, `Nat`, `PUnit`, `Empty`, `False` and `Quot` pins);
* the standard- and compiler-trust axiom pins (`ConLeche/Kernel/StdAxioms.lean`,
  `ConLeche/Kernel/TrustAxioms.lean`, `ConLeche/Kernel/TrustPins.lean`);
* the `Nat`-operation pin variants (`ConLeche/Kernel/NatOpPins.lean`'s
  `natOpPinSets`, sixteen `Expr` fields each).

A handle twin of one of these would be the same tree spelled with `internE`
instead of `Expr.app`, and nothing would be gained: DESIGN §8.7's ruling is
that (B) IMPORTS con-leche's representation-free data rather than copying it.
So the twins above this module (`Arena/Basis.lean`, `Arena/StdAxioms.lean`,
`Arena/TrustAxioms.lean`, `Arena/NatOpPinSet.lean`) are one line each: the
con-leche constant, interned.

**The walk is task #97e part 2's** (`Arena/Frontend/Readback.lean`), which
needs exactly the same direction for the modeller seam and wrote it MEMOISED
— a value read back out of a handle DAG is a tree whose subterms are shared by
Lean's own pointers, and re-interning it structurally would walk each shared
subterm once per occurrence.  What this module adds is the fresh-memo entry
points the pin modules call, so that neither side owns the other's memo.

**The tier matters.**  A pin interned while the scratch tier is live would go
with the tier, and the environment would hold a dangling handle.  DESIGN §8.6
P2d says the pins are interned "at startup — a one-time tree walk", i.e. into
the PERSISTENT tier, and `Arena/Checker.lean`'s `internAllPins` is that
startup: after it every pin node is in the persistent cons table, so a later
`intern` of the same node — whatever tier is live — probes persistent first
and hands back the persistent handle (DESIGN §8.3: "`intern` probes the
persistent table, then the scratch one").
-/
import ConRon.Arena.Frontend.Readback

namespace ConRon.Arena

open ConLeche

/-- con-leche: none — intern a transient term at a fresh memo. -/
def internExpr (e : ConLeche.Expr) : AM EIdx := Frontend.internExpr e

/-- con-leche: none — intern a list of transient terms at a fresh memo. -/
def internExprList (es : List ConLeche.Expr) : AM (List EIdx) := do
  pure (← Frontend.internExprList ∅ es).2

/-- con-leche: none — intern a transient `ConstantVal` at a fresh memo. -/
def internCV (cv : ConstantVal) : AM IConstantVal := do
  pure (← Frontend.internCV ∅ cv).2

/-- con-leche: none — intern a transient `ConstantInfo` at a fresh memo. -/
def internCI (ci : ConstantInfo) : AM IConstantInfo := do
  pure (← Frontend.internCI ∅ ci).2

/-- con-leche: none — intern a block of transient `ConstantInfo`s at ONE
memo, so that the sharing between a block's members survives. -/
def internCIList (cs : List ConstantInfo) : AM (List IConstantInfo) := do
  pure (← Frontend.internCIList ∅ cs).2

end ConRon.Arena
