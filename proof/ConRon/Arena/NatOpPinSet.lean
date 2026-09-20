/-
# `ConRon.Arena.NatOpPinSet` — one toolchain's `Nat`-operation pins, over handles

The twin of `ConLeche/Kernel/NatOpPinSet.lean` (the record) and of
`ConLeche/Kernel/NatOpPins.lean` (the `#load_natop_pins` splice that fills
it, one variant per committed dump under con-leche's `pins/`).

Sixteen of the record's seventeen fields carry terms — eight pinned defining
expressions and eight certificate-proof lists — so the record is DESIGN §8's
census class (T) and its twin is the same seventeen fields with `Expr ↦ EIdx`.
The pin DATA itself is con-leche's: DESIGN §8.6 P2d says to "intern con-leche's
`natOpPinSets` `Expr`s into the persistent tier at startup — a one-time tree
walk", which is `internPinSets` below, called by `Arena/Checker.lean`'s
`internAllPins`.  `Modeller`-style indirection is explicitly NOT wanted here:
the pins are data the checker reads, not a seam.
-/
import ConRon.Arena.Basis
import ConLeche.Kernel.NatOpPins

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/NatOpPinSet.lean:28-51 NatOpPinSet — the pins
of one toolchain: eight pinned defining expressions and eight
certificate-proof lists, in the order of `natDivModNames`' family (`div`,
`mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`), plus the
toolchain string for diagnostics. -/
structure INatOpPinSet where
  /-- The generating toolchain, named in the decline message when no variant
  matches. -/
  toolchain : String
  divPin : EIdx
  modPin : EIdx
  gcdPin : EIdx
  landPin : EIdx
  lorPin : EIdx
  xorPin : EIdx
  shiftLeftPin : EIdx
  shiftRightPin : EIdx
  divProofs : List EIdx
  modProofs : List EIdx
  gcdProofs : List EIdx
  landProofs : List EIdx
  lorProofs : List EIdx
  xorProofs : List EIdx
  shiftLeftProofs : List EIdx
  shiftRightProofs : List EIdx

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _ — intern one pin
variant: the one-time tree walk of DESIGN §8.6 P2d, sixteen terms deep. -/
def internPinSet (ps : NatOpPinSet) : AM INatOpPinSet := do
  let dp ← internExpr ps.divPin
  let mp ← internExpr ps.modPin
  let gp ← internExpr ps.gcdPin
  let lap ← internExpr ps.landPin
  let lop ← internExpr ps.lorPin
  let xp ← internExpr ps.xorPin
  let slp ← internExpr ps.shiftLeftPin
  let srp ← internExpr ps.shiftRightPin
  let dc ← internExprList ps.divProofs
  let mc ← internExprList ps.modProofs
  let gc ← internExprList ps.gcdProofs
  let lac ← internExprList ps.landProofs
  let loc ← internExprList ps.lorProofs
  let xc ← internExprList ps.xorProofs
  let slc ← internExprList ps.shiftLeftProofs
  let src ← internExprList ps.shiftRightProofs
  pure ⟨ps.toolchain, dp, mp, gp, lap, lop, xp, slp, srp,
    dc, mc, gc, lac, loc, xc, slc, src⟩

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _ — intern the variant
LIST, in the order the install gate tries them. -/
def internPinSets : List NatOpPinSet → AM (List INatOpPinSet)
  | [] => pure []
  | ps :: rest => do
    let h ← internPinSet ps
    let hs ← internPinSets rest
    pure (h :: hs)

end ConRon.Arena
