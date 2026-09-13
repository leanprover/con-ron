/-
`ConRon.Refine.PinsAbs` — the abstractions of the embedded pin text and of the
decoder's state (tasks #43, #64).

Task #43 put `absText`/`absNatOpPinSet`/`absPins` and the `absText_toStr`
bridge at the top of `ConRon/Refine/Pins.lean`, when that file was four
statements long.  Task #64 split them out so that the two halves of
`pins_decode_refines` — the model against `ConRon.Refine.PinsDec` and
`PinsDec` against `ConRon.Dump.parsePins` — can both import them without
importing each other; `Refine/Pins.lean` still *states* everything and is
still where a reader starts.

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

/-- A `&str` of the model as a Lean `String`.  Aeneas models `Str` as
`Slice U8` (`Aeneas/Std/StringDef.lean`) and a `&str` *constant* as
`toStr "…"`, so this is the left inverse of `toStr` on the constant: the bytes
are UTF-8 by construction, and `String.fromUTF8?` is total on them.  A
malformed byte string abstracts to `""`, which no statement below relies on —
`absText (toStr s) = s` (`absText_toStr`) is what is used, and that is generic
in `s`. -/
def absText (t : Str) : String :=
  match String.fromUTF8? ⟨(t.val.map (fun b => UInt8.ofNat b.val)).toArray⟩ with
  | some s => s
  | none => ""

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

/-! ## The bridge to the embedded text

`PINS_TEXT` is `toStr "<the 532 456-byte literal>"` in the generated model, so
`absText PINS_TEXT` is *definitionally* `absText (toStr pinsTextLean)` for the
Lean string literal `pinsTextLean` — a `delta` step and no computation.  What
makes that useful is that `absText (toStr s) = s` holds **generically**: it is
`Slice.from_val` (the `Slice` bound is a *parameter* of `toStr`, so reading the
list back never touches it) followed by `String.fromUTF8?_toByteArray`.  The
alternative — evaluating anything about the literal — is what the measurement
in `pins_text_decodes` rules out. -/

/-- `ByteArray.toList` is its array's list.  Lean 4.33's core defines
`ByteArray.toList` as a reverse-accumulating loop and proves nothing about it
(Aeneas hits the same wall and proves the sibling `length_toList` by hand in
`Aeneas/Std/String.lean`), so the loop invariant is spelled out here: at index
`i` with accumulator `r`, the loop yields `r.reverse ++ drop i`. -/
theorem ByteArray.toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  have h : ∀ i r, ByteArray.toList.loop b i r
      = r.reverse ++ b.data.toList.drop i := by
    intro i r
    fun_induction ByteArray.toList.loop b i r with
    | case1 i r hi ih =>
      rw [ih]; simp
      have hlt : i < b.data.toList.length := by rw [Array.length_toList]; exact hi
      rw [List.drop_eq_getElem_cons hlt]
      have : b.data[i]! = b.data[i]'(by rw [← Array.length_toList]; exact hlt) :=
        getElem!_pos b.data i (by rw [← Array.length_toList]; exact hlt)
      simp [ByteArray.get!, this]
    | case2 i r hi => simp; omega
  rw [ByteArray.toList]
  simpa using h 0 []

/-- The byte a `U8` of the model abstracts to is the byte it was made from:
`toStr`'s `UInt8 → U8` map is undone by `absText`'s `U8 → UInt8` one. -/
@[simp] theorem u8_ofNat_val (a : UInt8) :
    UInt8.ofNat (a.toBitVec#uscalar : U8).val = a := by
  unfold Std.UScalar.val; simp [UInt8.ofNat]

/-- Decoding a string's own UTF-8 gives the string back.  `String` is a
structure over a `ByteArray` with a validity field in 4.33, so this is
`dif_pos` on that field. -/
theorem String.fromUTF8?_toByteArray (s : String) :
    String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]

/-- **`absText` undoes `toStr`**, for every string and independently of how the
`toStr` bound was proved — the bound is a *parameter*, and `Slice.from_val`
reads the list back without looking at it.  This is the one lemma that turns a
statement about the Rust constant into a statement about a Lean string literal
at **zero** kernel cost: `PINS_TEXT` is by definition `toStr "…"`, so
`absText PINS_TEXT` is that literal after one `delta` step and nothing is ever
evaluated. -/
theorem absText_toStr (s : String) (h : s.toByteArray.size ≤ U32.max) :
    absText (toStr s h) = s := by
  unfold absText toStr
  simp [Slice.from_val, ByteArray.toList_eq, Function.comp_def]
  -- `{ data := s.toByteArray.data }` *is* `s.toByteArray` (structure eta), which
  -- `show` sees and `rw` cannot: the hidden validity proof depends on it.
  show (match String.fromUTF8? s.toByteArray with | some s => s | none => "") = s
  rw [String.fromUTF8?_toByteArray]


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
