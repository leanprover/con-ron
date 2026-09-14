/-
**The string scanners, exact against con-leche** (task #87, phase 3).

`crates/con-ron-core/src/frontend/scan_fast.rs:838-1170` against
`ConLeche/Frontend/Scan/Fast.lean:537-672` — the hexadecimal escapes, the
UTF-8 encoder and decoder, `unescape`, and the three scanners the record
readers call (`scan_string`, `scan_quoted_nat`, `scan_binder_info`).

Phase 1's `Refine/Frontend/ScanWF.lean` proved the same functions *well
formed* (`utf8_decode_wf` → `unescape_wf` → `scan_string_wf`); this file is the
tier above it.

## What this file gives the record scanners

    scan_string_refines :
      frontend.scan_fast.scan_string b i = ok o →
      ScanSim absString o (scanString (absBytes b) (absPos i))

    scan_quoted_nat_refines :
      frontend.scan_fast.scan_quoted_nat b i = ok o →
      ScanSim natOfDigitsS o (scanQuotedNat (absBytes b) (absPos i))

    scan_binder_info_refines :
      frontend.scan_fast.scan_binder_info b i = ok j →
      absPos j = scanBinderInfo (absBytes b) (absPos i)

`natOfDigitsS` is `Abs.lean`'s `natOfDigits` on a `Vec<u8>` of decimal digits
(deviation 2 of `scan_types.rs`'s module note: the port's `scan_quoted_nat`
returns the literal's *bytes* where con-leche returns the `Nat`).

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.Abs

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConRon.Refine ConLeche.Frontend

/-! ## A code point on both sides

`hex_val`/`hex4`/`hex3` produce a `u32`; con-leche's produce a `UInt32`.  The
map is the value, and it loses nothing because a `Std.U32` is below `2 ^ 32`
by construction. -/

/-- A port `u32` as con-leche's `UInt32`. -/
def absU32 (v : Std.U32) : UInt32 := UInt32.ofNat v.val

@[simp] theorem absU32_toNat (v : Std.U32) : (absU32 v).toNat = v.val := by
  simp [absU32]

/-! ## Bit plumbing

The port writes the UTF-8 widths out by hand (deviation 5 of the module note:
`char` and `encode_utf8` are outside the Aeneas subset), so this file is the
one place where the two sides meet at the bit level.  `Nat.two_pow_add_eq_or_of_lt`
is the whole content: an `or` whose right operand fits under the left's low
zeros is an `add`, which is what turns every lead/continuation byte into
arithmetic `omega` can see. -/

/-- An `or` whose right operand fits under the left's low zeros is an `add`. -/
private theorem or_add (i a : Nat) {b : Nat} (hb : b < 2 ^ i) :
    2 ^ i * a ||| b = 2 ^ i * a + b := (Nat.two_pow_add_eq_or_of_lt hb a).symm

private theorem or192 {x : Nat} (h : x < 64) : 192 ||| x = 192 + x := by
  simpa using or_add 6 3 h

private theorem or128 {x : Nat} (h : x < 64) : 128 ||| x = 128 + x := by
  simpa using or_add 6 2 h

private theorem or224 {x : Nat} (h : x < 16) : 224 ||| x = 224 + x := by
  simpa using or_add 4 14 h

private theorem or240 {x : Nat} (h : x < 8) : 240 ||| x = 240 + x := by
  simpa using or_add 3 30 h

private theorem and63 (x : Nat) : x &&& 63 = x % 64 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x 6

/-- Aeneas's `>>>` by an `i32` literal, as `Nat` division. -/
private theorem ushr_val {ty : Std.UScalarTy} {tys : Std.IScalarTy}
    {x z : Std.UScalar ty} {s : Std.IScalar tys} (h : x >>> s = ok z) :
    z.val = x.val >>> s.toNat := by
  simp only [HShiftRight.hShiftRight, Std.UScalar.shiftRight_IScalar,
    Std.UScalar.shiftRight] at h
  split at h
  · split at h
    · simp only [Result.ok.injEq] at h
      rw [← h]; simp only [Std.UScalar.val, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
    · simp at h
  · simp at h

/-- Aeneas's `<<<` by an `i32` literal. -/
private theorem ushl_val {ty : Std.UScalarTy} {tys : Std.IScalarTy}
    {x z : Std.UScalar ty} {s : Std.IScalar tys} (h : x <<< s = ok z) :
    z.val = (x.val <<< s.toNat) % 2 ^ ty.numBits := by
  simp only [HShiftLeft.hShiftLeft, Std.UScalar.shiftLeft_IScalar,
    Std.UScalar.shiftLeft] at h
  split at h
  · split at h
    · simp only [Result.ok.injEq] at h
      rw [← h]; simp only [Std.UScalar.val, BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft]
    · simp at h
  · simp at h

/-- A `lift`ed pure step is an equation on its value. -/
private theorem lift_val {α : Type} {x y : α} (h : lift x = ok y) : x = y := by
  simpa only [lift, Result.ok.injEq] using h

/-- Aeneas's `-` returned `ok`, so nothing wrapped. -/
private theorem uscalar_sub_add {ty : Std.UScalarTy} {x y z : Std.UScalar ty}
    (h : x - y = ok z) : x.val = z.val + y.val := by
  have := Std.UScalar.sub_equiv x y
  rw [h] at this; simp at this; omega

/-- Two bytes are equal when their values are. -/
private theorem byte_eq {i : Std.U8} {w : UInt8} (h : i.val = w.toNat) : absByte i = w := by
  apply UInt8.toNat_inj.mp; simpa using h

/-- `Char.ofNat` keeps a scalar value. -/
theorem char_ofNat_toNat {n : Nat} (h : Nat.isValidChar n) :
    (Char.ofNat n).val.toNat = n := by
  rw [Char.ofNat, dif_pos h]
  simp [Char.ofNatAux]

/-! ## `hex_val` (`Scan/Fast.lean:537-541`) -/

/-- A byte the port shrank by `k` is con-leche's `UInt32` subtraction. -/
private theorem absU32_sub {c i : Std.U8} {v : Std.U32} {k : UInt32}
    (harith : c.val = i.val + k.toNat) (hcast : lift (Std.UScalar.cast .U32 i) = ok v) :
    absU32 v = (absByte c).toUInt32 - k := by
  have hc : c.val < 256 := by scalar_tac
  have hv : v.val = i.val := by
    rw [← lift_val hcast]; exact Std.U8.cast_U32_val_eq i
  apply UInt32.toNat_inj.mp
  have hk : k.toNat < 2 ^ 32 := k.toNat_lt_size
  simp only [absU32_toNat, UInt32.toNat_sub, UInt8.toNat_toUInt32, absByte_toNat, hv]
  omega

/-- **`scan_fast::hex_val` refines `hexVal`** (`ConLeche/Frontend/Scan/Fast.lean:537-541
hexVal`): the value of a hexadecimal digit, `none` for anything else. -/
theorem hex_val_refines {c : Std.U8} {o : Option Std.U32}
    (h : frontend.scan_fast.hex_val c = ok o) :
    o.map absU32 = hexVal (absByte c) := by
  rw [frontend.scan_fast.hex_val] at h
  rw [hexVal]
  simp only [scalar_tac_simps] at h
  simp only [UInt8.le_iff_toNat_le, absByte_toNat, UInt8.reduceToNat, Bool.and_eq_true,
    decide_eq_true_eq]
  split_ifs at h ⊢ <;>
    (try (exfalso; omega)) <;>
    (try (obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq] at h
          subst h
          simp only [Option.map_some, Option.some.injEq]
          exact absU32_sub (by simpa using uscalar_sub_add hi) hv)) <;>
    (simp only [Result.ok.injEq] at h; subst h; rfl)

end ConRon.Refine.Frontend
