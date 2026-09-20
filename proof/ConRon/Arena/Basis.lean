/-
# `ConRon.Arena.Basis` — the pinned basis blocks, over handles

The twin of `ConLeche/Kernel/Basis.lean` and `ConLeche/Kernel/BasisA.lean`:
the constants of the six pinned blocks (`Eq`, `Nat`, `PUnit`, `Empty`,
`False`, `Quot`) and the two tests that recognise a stream record as one of
them.

**The blocks are con-leche's values, interned** (`Arena/Intern.lean`'s module
note, and DESIGN §8.6 P2d: "intern con-leche's `BasisKind.declsA` at
startup").  `ConLeche/Kernel/Basis/{Names,Builder,Empty,Eq,False,Nat,PUnit,
Quot}.lean` are ~80 declarations of pure `Expr` and `ConstantInfo` data,
hand-written against the toolchain's `Init.Prelude` through a builder whose
every helper is one `Expr` constructor.  A handle twin of them would be the
same trees spelled with `internE`, and DESIGN §8.7's ruling is that (B)
imports con-leche's representation-free data rather than copying it.  What
IS a twin here is the two recognisers, which read the environment and
compare with `Arena/Canon.lean`'s lockstep comparisons.

**`decls` versus `declsA`.**  con-leche's `BasisKind.decls` is the RAW block
(the frontend used to match incoming records against it); `BasisKind.declsA`
is the ANNOTATED one the install actually stores.  Both are twinned, because
`basisPinHit` compares against the annotated block (`canonEqList block
k.decls` at con-leche's `Basis.lean:71` reads `decls`, and `checkBasisDecl`
installs `declsA`) and the arena must keep the two apart exactly as
con-leche does.
-/
import ConRon.Arena.TrustAxioms

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Basis.lean:40-47 BasisKind.decls — the RAW
constants of one basis block, in dependency order, interned. -/
def BasisKind.decls (k : BasisKind) : AM (List IConstantInfo) :=
  internCIList (ConLeche.BasisKind.decls k)

/-- con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA — the
ANNOTATED constants of one basis block, in dependency order, interned.  This
is what `checkBasisDecl` installs. -/
def BasisKind.declsA (k : BasisKind) : AM (List IConstantInfo) :=
  internCIList (ConLeche.BasisKind.declsA k)

/-- con-leche: none — the names of a block's members, for `basisPinHit`'s
name pre-filter.  `IConstantInfo.name` is pure (task #97e), so this is a
plain `List.map`. -/
def blockNames (block : List IConstantInfo) : List NIdx :=
  block.map (·.name)

/-- con-leche: ConLeche/Kernel/Basis.lean:60-71 basisPinHit — **the basis-pin
match**, with con-leche's task-#215 NAME pre-filter in front: `canon` renames
only level parameters, so a block can match a pin only when its members' names
are the pin's, member for member, and that test is a handful of handle
comparisons.

The five kinds are tried in con-leche's order; `.quotK` is deliberately not
among them (a quotient block arrives as four `quotDecl` records, which
`quotPinHit` decides). -/
def basisPinHitGo (block : List IConstantInfo) :
    List BasisKind → AM (Option BasisKind)
  | [] => pure none
  | k :: ks => do
    let pinned ← ConRon.Arena.BasisKind.decls k
    if blockNames pinned == blockNames block then
      if ← canonEqList block pinned then pure (some k) else pure none
    else basisPinHitGo block ks

/-- con-leche: ConLeche/Kernel/Basis.lean:60-71 basisPinHit — the five pinned
blocks, in con-leche's order.  con-leche writes `[…].find? …` with a closure;
DESIGN §3.4's rule for a `List` recursion is a helper, so the search is
`basisPinHitGo`.  `find?` stops at the FIRST kind whose names match and then
`filter`s by the canonical comparison — i.e. a name match that fails the
comparison is `none`, not "try the next kind", which is what the helper's
`then` branch spells. -/
def basisPinHit (block : List IConstantInfo) : AM (Option BasisKind) :=
  basisPinHitGo block [BasisKind.eqK, .natK, .punitK, .emptyK, .falseK]

/-- con-leche: ConLeche/Kernel/Basis.lean:73-78 quotPinHit — **the
quotient-pin match**: the record is the pinned package's constant at the slot
it declares itself at, compared at `toConstantVal`. -/
def quotPinHit (k : QuotKind) (cv : IConstantVal) : AM Bool := do
  let blk ← ConRon.Arena.BasisKind.decls .quotK
  match blk[k.slot]? with
  | some ci => do
    let pcv ← ci.toConstantVal
    cv.canonEq pcv
  | none => pure false

end ConRon.Arena
