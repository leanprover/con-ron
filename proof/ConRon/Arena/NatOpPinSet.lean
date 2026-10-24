/-
# `ConRon.Arena.NatOpPinSet` — one toolchain's `Nat`-operation pins, over handles

The twin of `ConLeche/Kernel/NatOpPinSet.lean` (the record) and of
`ConLeche/Kernel/NatOpPins.lean` (the `#load_natop_pins` splice that fills
it, one variant per committed dump under con-leche's `pins/`).

Twenty-four of the record's twenty-five fields carry terms — eight pinned
defining expressions, eight certificate-proof lists and eight type-pin lists —
so the record is DESIGN §8's census class (T) and its twin is the same
twenty-five fields with `Expr ↦ EIdx` and `Name ↦ NIdx`.
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

/-- con-leche: ConLeche/Kernel/NatOpPinSet.lean:35-68 NatOpPinSet — the pins
of one toolchain: eight pinned defining expressions, eight certificate-proof
lists and eight type-pin lists, in the order of `natDivModNames`' family
(`div`, `mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`), plus
the toolchain string for diagnostics.  A type pin `(n, ty)` says that the
constant `n`, which the operation's certificates use, has type `ty` in that
toolchain. -/
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
  divTypePins : List (NIdx × EIdx)
  modTypePins : List (NIdx × EIdx)
  gcdTypePins : List (NIdx × EIdx)
  landTypePins : List (NIdx × EIdx)
  lorTypePins : List (NIdx × EIdx)
  xorTypePins : List (NIdx × EIdx)
  shiftLeftTypePins : List (NIdx × EIdx)
  shiftRightTypePins : List (NIdx × EIdx)

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _ — one type-pin list:
each name and each type interned, in list order. -/
def internTypePins : List (ConLeche.Name × ConLeche.Expr) → AM (List (NIdx × EIdx))
  | [] => pure []
  | p :: rest => do
    let n ← internName p.1
    let t ← internExpr p.2
    let r ← internTypePins rest
    pure ((n, t) :: r)

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _ — the eight type-pin
lists, written into the record the sixteen term fields built (its type-pin
fields empty until here). -/
def internPinSetTypePins (ps : NatOpPinSet) (s : INatOpPinSet) : AM INatOpPinSet := do
  let dtp ← internTypePins ps.divTypePins
  let mtp ← internTypePins ps.modTypePins
  let gtp ← internTypePins ps.gcdTypePins
  let latp ← internTypePins ps.landTypePins
  let lotp ← internTypePins ps.lorTypePins
  let xtp ← internTypePins ps.xorTypePins
  let sltp ← internTypePins ps.shiftLeftTypePins
  let srtp ← internTypePins ps.shiftRightTypePins
  pure { s with
    divTypePins := dtp
    modTypePins := mtp
    gcdTypePins := gtp
    landTypePins := latp
    lorTypePins := lotp
    xorTypePins := xtp
    shiftLeftTypePins := sltp
    shiftRightTypePins := srtp }

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _ — intern one pin
variant: the one-time tree walk of DESIGN §8.6 P2d, twenty-four fields
deep. -/
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
  internPinSetTypePins ps ⟨ps.toolchain, dp, mp, gp, lap, lop, xp, slp, srp,
    dc, mc, gc, lac, loc, xc, slc, src, [], [], [], [], [], [], [], []⟩

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _ — intern the variant
LIST, in the order the install gate tries them. -/
def internPinSets : List NatOpPinSet → AM (List INatOpPinSet)
  | [] => pure []
  | ps :: rest => do
    let h ← internPinSet ps
    let hs ← internPinSets rest
    pure (h :: hs)

end ConRon.Arena
