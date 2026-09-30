/-
`ConRon.Refine.PinsAbs` — the abstractions of the embedded pin text and of the
decoder's state (tasks #43, #64).

Task #43 put `absText`/`absNatOpPinSet`/`absPins` and the `absText_toStr`
bridge at the top of `ConRon/Refine/Pins.lean`, when that file was four
statements long.  Task #64 split them out so that the two halves of
`pins_decode_refines` — the model against `ConRon.Refine.PinsDec` and
`PinsDec` against `ConRon.Dump.parsePins` — can both import them without
importing each other; `Refine/Pins.lean`, which
stated the composition, is deleted (task #105: nothing used it).

Nothing here is new except `bytesOf` (the model's `&[u8]` as `PinsDec.Bytes`)
and `absTables` (the decoder's five id-space `Vec`s as `PinsDec.Tables`),
which are what the refinement's induction is stated over.
-/
import ConRon.Refine.Expr
import ConRon.Refine.PinsDec
import ConLeche.Kernel.NatOpPins

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/-! ## The abstractions -/

/-- A pin variant of the model as `ConLeche.NatOpPinSet`
(`ConLeche/Kernel/NatOpPinSet.lean:26-49`): the toolchain string, the eight
pinned defining expressions and the eight certificate lists, field for field,
through the abstractions of `ConRon/Refine/Abs.lean`. -/
def absNatOpPinSet (s : nat_op_pins.NatOpPinSet) : ConLeche.NatOpPinSet :=
  { toolchain := absString s.toolchain
    divPin := absExpr s.div_pin
    modPin := absExpr s.mod_pin
    gcdPin := absExpr s.gcd_pin
    landPin := absExpr s.land_pin
    lorPin := absExpr s.lor_pin
    xorPin := absExpr s.xor_pin
    shiftLeftPin := absExpr s.shift_left_pin
    shiftRightPin := absExpr s.shift_right_pin
    divProofs := absExprs s.div_proofs
    modProofs := absExprs s.mod_proofs
    gcdProofs := absExprs s.gcd_proofs
    landProofs := absExprs s.land_proofs
    lorProofs := absExprs s.lor_proofs
    xorProofs := absExprs s.xor_proofs
    shiftLeftProofs := absExprs s.shift_left_proofs
    shiftRightProofs := absExprs s.shift_right_proofs }

/-- The pin list: a `Vec<NatOpPinSet>` as `List ConLeche.NatOpPinSet`, in file
order — which is the order `checkDivModPinLoop` tries the variants in, so the
order is part of the statement. -/
def absPins (ps : alloc.vec.Vec nat_op_pins.NatOpPinSet) :
    List ConLeche.NatOpPinSet :=
  ps.val.map absNatOpPinSet

/-! ## The decoder's byte string and state

The two abstractions `Refine/PinsBytes.lean`'s induction is stated over.  Both
are plain `map`s: the refinement never needs a well-formedness side condition,
because every value a record installs is built by a *smart constructor* whose
own refinement lemma (`Refine/{Name,Level,PropWhen,Expr}.lean`) already says
what it abstracts to. -/

/-- The model's byte slice as `PinsDec.Bytes`.  Aeneas models `Str` as
`Slice U8` and `str::as_bytes` as the identity (`Generated/FunsExternal.lean`),
so this is the same list for a `&str` and for the `&[u8]` the decoder walks. -/
def bytesOf (t : Slice Std.U8) : PinsDec.Bytes := t.val.map (fun b => b.val)

/-- `kernel::pins_decode::Tables` as `PinsDec.Tables`: one `Vec` per id space,
read through the abstraction of its element type, in emission order. -/
def absTables (tb : pins_decode.Tables) : PinsDec.Tables :=
  { names := tb.names.val.map absName
    levels := tb.levels.val.map absLevel
    pws := tb.pws.val.map absPropWhen
    exprs := tb.exprs.val.map absExpr
    sets := tb.sets.val.map absNatOpPinSet }

@[simp] theorem bytesOf_length (t : Slice Std.U8) : (bytesOf t).length = t.length := by
  simp [bytesOf, Slice.length]

end ConRon.Refine
