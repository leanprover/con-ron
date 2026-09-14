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
import ConRon.Refine.Frontend.ScanKit

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConRon.Refine ConLeche.Frontend

/-! ## A code point on both sides

`hex_val`/`hex4`/`hex3` produce a `u32`; con-leche's produce a `UInt32`.  The
map is the value, and it loses nothing because a `Std.U32` is below `2 ^ 32`
by construction. -/

/-- A port `u32` as con-leche's `UInt32`.  Spelled on the bit vector rather
than on the value so that `absU32_or`/`absU32_and` hold by `rfl`, which is what
the object-member step of `Refine/Frontend/ScanObj.lean` is built on. -/
def absU32 (n : Std.U32) : UInt32 := UInt32.ofBitVec n.bv

@[simp] theorem absU32_toNat (v : Std.U32) : (absU32 v).toNat = v.val := rfl

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

/-! ## `utf8_of` (`Scan/Fast.lean:559-560`)

The port appends the UTF-8 bytes of a code point by hand where con-leche takes
`(String.singleton (Char.ofNat v)).toUTF8`; `String.utf8EncodeChar` is the
toolchain's own four-way split of the same arithmetic, so the two meet there.
The hypothesis is that the value IS a scalar value — the port's own comment
("every value that reaches here is a scalar value") — and `unescape_bytes`
below discharges it at every call site. -/

/-- `lift`ed `|||`, as a `Nat` disjunction. -/
private theorem or_lift_val {ty : Std.UScalarTy} {x y z : Std.UScalar ty}
    (h : lift (x ||| y) = ok z) : z.val = x.val ||| y.val := by
  rw [← lift_val h]; exact Std.UScalar.val_or x y

/-- `lift`ed `&&&`, as a `Nat` conjunction. -/
private theorem and_lift_val {ty : Std.UScalarTy} {x y z : Std.UScalar ty}
    (h : lift (x &&& y) = ok z) : z.val = x.val &&& y.val := by
  rw [← lift_val h]; exact Std.UScalar.val_and x y

/-- `lift`ed `as u8`, as a `Nat` truncation. -/
private theorem cast8_lift_val {x : Std.U32} {z : Std.U8}
    (h : lift (Std.UScalar.cast .U8 x) = ok z) : z.val = x.val % 256 := by
  rw [← lift_val h, Std.UScalar.cast_val_eq]; rfl

/-- The port's byte and con-leche's agree when their values do mod 256. -/
private theorem byte_ofNat {i : Std.U8} {n : Nat} (h : i.val = n % 256) :
    absByte i = UInt8.ofNat n := by
  apply UInt8.toNat_inj.mp
  rw [absByte_toNat, h]
  simp

/-- **`scan_fast::utf8_of` appends con-leche's UTF-8 bytes** (`Scan/Fast.lean:559-560
utf8Of`), in the list form the `unescape_bytes` loop reasons with. -/
theorem utf8_of_bytes {acc out : alloc.vec.Vec Std.U8} {val : Std.U32}
    (hv : Nat.isValidChar val.val)
    (h : frontend.scan_fast.utf8_of acc val = ok out) :
    out.val.map absByte
      = acc.val.map absByte ++ String.utf8EncodeChar (Char.ofNat val.val) := by
  have hvn : (Char.ofNat val.val).val.toNat = val.val := char_ofNat_toNat hv
  have hlt : val.val < 1114112 := by
    rcases hv with hv | hv <;> omega
  rw [frontend.scan_fast.utf8_of] at h
  simp only [scalar_tac_simps] at h
  simp only [String.utf8EncodeChar, hvn]
  split_ifs at h ⊢ <;> (try (exfalso; omega))
  · -- ASCII: one byte, the value itself
    obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
    rw [vec_push_val h, List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    exact byte_ofNat (cast8_lift_val hi)
  · -- two bytes: a five-bit lead and a six-bit tail
    obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨acc1, ha1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
    have e2 : i2.val = (val.val / 64 % 32 + 192) % 256 := by
      rw [cast8_lift_val hi2, or_lift_val hi1, ushr_val hi]
      simp only [scalar_tac_simps, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      rw [or192 (by omega)]; omega
    have e5 : i5.val = (val.val % 64 + 128) % 256 := by
      rw [cast8_lift_val hi5, or_lift_val hi4, and_lift_val hi3]
      simp only [scalar_tac_simps, and63]
      rw [or128 (by omega)]; omega
    rw [vec_push_val h, vec_push_val ha1]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [byte_ofNat e2, byte_ofNat e5]
  · -- three bytes: a four-bit lead and two six-bit tails
    obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨acc1, ha1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨j3, hj3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨j4, hj4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨j5, hj5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨j6, hj6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨acc2, ha2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨k3, hk3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨k4, hk4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨k5, hk5, h⟩ := bind_eq_ok_iff.mp h
    have e2 : i2.val = (val.val / 4096 % 16 + 224) % 256 := by
      rw [cast8_lift_val hi2, or_lift_val hi1, ushr_val hi]
      simp only [scalar_tac_simps, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      rw [or224 (by omega)]; omega
    have e6 : j6.val = (val.val / 64 % 64 + 128) % 256 := by
      rw [cast8_lift_val hj6, or_lift_val hj5, and_lift_val hj4, ushr_val hj3]
      simp only [scalar_tac_simps, Nat.shiftRight_eq_div_pow, Nat.reducePow, and63]
      rw [or128 (by omega)]; omega
    have e5 : k5.val = (val.val % 64 + 128) % 256 := by
      rw [cast8_lift_val hk5, or_lift_val hk4, and_lift_val hk3]
      simp only [scalar_tac_simps, and63]
      rw [or128 (by omega)]; omega
    rw [vec_push_val h, vec_push_val ha2, vec_push_val ha1]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [byte_ofNat e2, byte_ofNat e6, byte_ofNat e5]
  · -- four bytes: a three-bit lead and three six-bit tails
    obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨acc1, ha1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨j3, hj3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨j4, hj4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨j5, hj5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨j6, hj6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨acc2, ha2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m3, hm3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m4, hm4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m5, hm5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m6, hm6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨acc3, ha3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨k3, hk3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨k4, hk4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨k5, hk5, h⟩ := bind_eq_ok_iff.mp h
    have e2 : i2.val = (val.val / 262144 % 8 + 240) % 256 := by
      rw [cast8_lift_val hi2, or_lift_val hi1, ushr_val hi]
      simp only [scalar_tac_simps, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      rw [or240 (by omega)]; omega
    have e6 : j6.val = (val.val / 4096 % 64 + 128) % 256 := by
      rw [cast8_lift_val hj6, or_lift_val hj5, and_lift_val hj4, ushr_val hj3]
      simp only [scalar_tac_simps, Nat.shiftRight_eq_div_pow, Nat.reducePow, and63]
      rw [or128 (by omega)]; omega
    have e7 : m6.val = (val.val / 64 % 64 + 128) % 256 := by
      rw [cast8_lift_val hm6, or_lift_val hm5, and_lift_val hm4, ushr_val hm3]
      simp only [scalar_tac_simps, Nat.shiftRight_eq_div_pow, Nat.reducePow, and63]
      rw [or128 (by omega)]; omega
    have e5 : k5.val = (val.val % 64 + 128) % 256 := by
      rw [cast8_lift_val hk5, or_lift_val hk4, and_lift_val hk3]
      simp only [scalar_tac_simps, and63]
      rw [or128 (by omega)]; omega
    rw [vec_push_val h, vec_push_val ha3, vec_push_val ha2, vec_push_val ha1]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [byte_ofNat e2, byte_ofNat e6, byte_ofNat e7, byte_ofNat e5]

/-- con-leche's `utf8Of` is the toolchain's own one-character encoding
(`Scan/Fast.lean:559-560`). -/
theorem utf8Of_eq (v : Std.U32) :
    utf8Of (absU32 v) = (String.utf8EncodeChar (Char.ofNat v.val)).toByteArray := by
  rw [utf8Of, absU32_toNat, String.singleton_eq_ofList, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList, List.utf8Encode_singleton]

/-- **`scan_fast::utf8_of` refines `utf8Of`** (`Scan/Fast.lean:559-560 utf8Of`). -/
theorem utf8_of_refines {acc out : alloc.vec.Vec Std.U8} {val : Std.U32}
    (hv : Nat.isValidChar val.val)
    (h : frontend.scan_fast.utf8_of acc val = ok out) :
    absChunk out = absChunk acc ++ utf8Of (absU32 val) := by
  rw [utf8Of_eq, absChunk, absChunk]
  ext1
  simp [utf8_of_bytes hv h, List.data_toByteArray]

/-! ## `hex4`, `hex3` (`Scan/Fast.lean:543-557`)

The port steps the cursor with `j + 1`, `j + 2`, `j + 3` where the Lean writes
`j + 1`, `j + 1 + 1`, `j + 1 + 1 + 1`; a step the port returned `ok` for did
not overflow, so the two agree (`Abs.lean`'s `absPos_add_one`, and its two
iterates below). -/

/-- One machine-word step inside the array. -/
private theorem usize_succ (p : USize) (h : p.toNat + 1 < USize.size) :
    (p + 1).toNat = p.toNat + 1 := by
  have h1 : ((1 : USize)).toNat = 1 := by simp
  rw [USize.toNat_add, h1]
  exact Nat.mod_eq_of_lt h

/-- The port's `+ 2` as con-leche's two steps. -/
private theorem absPos_add_two {i j : Std.Usize} (h : i + 2#usize = ok j) :
    absPos j = absPos i + 1 + 1 := by
  have hv : j.val = i.val + 2 := by have := HashMap.uscalar_add_eq h; scalar_tac
  have hb : j.val < USize.size := usize_val_lt_size j
  have s1 : (absPos i + 1).toNat = i.val + 1 := by
    rw [usize_succ _ (by rw [absPos_toNat]; omega), absPos_toNat]
  apply USize.toNat_inj.mp
  rw [usize_succ _ (by rw [s1]; omega), s1, absPos_toNat, hv]

/-- The port's `+ 3` as con-leche's three steps. -/
private theorem absPos_add_three {i j : Std.Usize} (h : i + 3#usize = ok j) :
    absPos j = absPos i + 1 + 1 + 1 := by
  have hv : j.val = i.val + 3 := by have := HashMap.uscalar_add_eq h; scalar_tac
  have hb : j.val < USize.size := usize_val_lt_size j
  have s1 : (absPos i + 1).toNat = i.val + 1 := by
    rw [usize_succ _ (by rw [absPos_toNat]; omega), absPos_toNat]
  have s2 : (absPos i + 1 + 1).toNat = i.val + 2 := by
    rw [usize_succ _ (by rw [s1]; omega), s1]
  apply USize.toNat_inj.mp
  rw [usize_succ _ (by rw [s2]; omega), s2, absPos_toNat, hv]

/-- The port's `|||`, as con-leche's. -/
private theorem absU32_or {x y z : Std.U32} (h : lift (x ||| y) = ok z) :
    absU32 z = absU32 x ||| absU32 y := by
  apply UInt32.toNat_inj.mp
  rw [absU32_toNat, or_lift_val h, UInt32.toNat_or, absU32_toNat, absU32_toNat]

/-- The port's `<<<` by a literal, as con-leche's. -/
private theorem absU32_shl {v z : Std.U32} {k : Std.I32} {w : UInt32} {n : Nat}
    (h : v <<< k = ok z) (hk : Std.IScalar.toNat k = n) (hw : w.toNat = n)
    (hn : n < 32) : absU32 z = absU32 v <<< w := by
  apply UInt32.toNat_inj.mp
  rw [absU32_toNat, ushl_val h, hk, UInt32.toNat_shiftLeft, absU32_toNat, hw,
    Nat.mod_eq_of_lt hn]
  rfl

/-- **`scan_fast::hex4` refines `hex4`** (`Scan/Fast.lean:543-549 hex4`). -/
theorem hex4_refines {b : Slice Std.U8} {j : Std.Usize} {o : Option Std.U32}
    (h : frontend.scan_fast.hex4 b j = ok o) :
    o.map absU32 = hex4 (absBytes b) (absPos j) := by
  rw [frontend.scan_fast.hex4] at h
  rw [hex4]
  obtain ⟨c0, hc0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q0, hq0, h⟩ := bind_eq_ok_iff.mp h
  rw [show byteAt (absBytes b) (absPos j) = absByte c0 from (byte_at_refines hc0).symm,
    ← hex_val_refines hq0]
  cases q0 with
  | none => simp only [Option.map_none]; simpa using h.symm
  | some x =>
  simp only [Option.map_some]
  obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q1, hq1, h⟩ := bind_eq_ok_iff.mp h
  rw [show byteAt (absBytes b) (absPos j + 1) = absByte c1 from by
        rw [← absPos_add_one hp1]; exact (byte_at_refines hc1).symm,
    ← hex_val_refines hq1]
  cases q1 with
  | none => simp only [Option.map_none]; simpa using h.symm
  | some x1 =>
  simp only [Option.map_some]
  obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c2, hc2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
  rw [show byteAt (absBytes b) (absPos j + 1 + 1) = absByte c2 from by
        rw [← absPos_add_two hp2]; exact (byte_at_refines hc2).symm,
    ← hex_val_refines hq2]
  cases q2 with
  | none => simp only [Option.map_none]; simpa using h.symm
  | some x2 =>
  simp only [Option.map_some]
  obtain ⟨p3, hp3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c3, hc3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q3, hq3, h⟩ := bind_eq_ok_iff.mp h
  rw [show byteAt (absBytes b) (absPos j + 1 + 1 + 1) = absByte c3 from by
        rw [← absPos_add_three hp3]; exact (byte_at_refines hc3).symm,
    ← hex_val_refines hq3]
  cases q3 with
  | none => simp only [Option.map_none]; simpa using h.symm
  | some x3 =>
  simp only [Option.map_some]
  obtain ⟨s12, hs12, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s8, hs8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨u1, hu1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, hs4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨u2, hu2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨u3, hu3, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  simp only [Option.map_some]
  rw [absU32_or hu3, absU32_or hu2, absU32_or hu1,
    absU32_shl (w := 12) (n := 12) hs12 (by simp) (by simp) (by omega),
    absU32_shl (w := 8) (n := 8) hs8 (by simp) (by simp) (by omega),
    absU32_shl (w := 4) (n := 4) hs4 (by simp) (by simp) (by omega)]
  rfl

/-- **`scan_fast::hex3` refines `hex3`** (`Scan/Fast.lean:551-557 hex3`). -/
theorem hex3_refines {b : Slice Std.U8} {j : Std.Usize} {o : Option Std.U32}
    (h : frontend.scan_fast.hex3 b j = ok o) :
    o.map absU32 = hex3 (absBytes b) (absPos j) := by
  rw [frontend.scan_fast.hex3] at h
  rw [hex3]
  obtain ⟨c0, hc0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q0, hq0, h⟩ := bind_eq_ok_iff.mp h
  rw [show byteAt (absBytes b) (absPos j) = absByte c0 from (byte_at_refines hc0).symm,
    ← hex_val_refines hq0]
  cases q0 with
  | none => simp only [Option.map_none]; simpa using h.symm
  | some x =>
  simp only [Option.map_some]
  obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q1, hq1, h⟩ := bind_eq_ok_iff.mp h
  rw [show byteAt (absBytes b) (absPos j + 1) = absByte c1 from by
        rw [← absPos_add_one hp1]; exact (byte_at_refines hc1).symm,
    ← hex_val_refines hq1]
  cases q1 with
  | none => simp only [Option.map_none]; simpa using h.symm
  | some x1 =>
  simp only [Option.map_some]
  obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c2, hc2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
  rw [show byteAt (absBytes b) (absPos j + 1 + 1) = absByte c2 from by
        rw [← absPos_add_two hp2]; exact (byte_at_refines hc2).symm,
    ← hex_val_refines hq2]
  cases q2 with
  | none => simp only [Option.map_none]; simpa using h.symm
  | some x2 =>
  simp only [Option.map_some]
  obtain ⟨s8, hs8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, hs4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨u1, hu1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨u2, hu2, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  simp only [Option.map_some]
  rw [absU32_or hu2, absU32_or hu1,
    absU32_shl (w := 8) (n := 8) hs8 (by simp) (by simp) (by omega),
    absU32_shl (w := 4) (n := 4) hs4 (by simp) (by simp) (by omega)]
  rfl

/-! ## `scan_quoted_nat`: the digit run (`Scan/Fast.lean:649-655`)

Deviation 2 of `scan_types.rs`'s module note: the port's `scan_quoted_nat`
returns the literal's decimal **bytes** where con-leche's returns the `Nat`.
`export_c` turns them into a `ron::Nat` with `nat_decimal::from_decimal`,
which accepts only a run of decimal digits — so the scanner owes the run's
shape, and it is `skip_digits`' own invariant. -/

/-- A slice read, as a `getElem?` equation. -/
private theorem index_getElem? {t : Slice Std.U8} {i : Std.Usize} {x : Std.U8}
    (h : Slice.index_usize t i = ok x) : t.val[i.val]? = some x := by
  rw [Slice.index_usize] at h
  rcases hi : t.val[i.val]? with _ | y
  · rw [show t[i]? = t.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show t[i]? = t.val[i.val]? from rfl, hi] at h
    exact congrArg some (Result.ok_injective h)

/-- A slice read at an in-range index, in the forward `= ok` form. -/
private theorem index_ok {t : Slice Std.U8} {i : Std.Usize} {x : Std.U8}
    (hi : i.val < t.val.length) (h : Slice.index_usize t i = ok x) :
    x = t.val[i.val] := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec t i hi)
  rw [hy] at h
  simp only [Result.ok.injEq] at h
  rw [← h, hyv]

/-- `is_digit`, as the `Nat` range. -/
private theorem is_digit_val {c : Std.U8} {w : Bool}
    (h : frontend.scan_fast.is_digit c = ok w) :
    w = true ↔ (48 ≤ c.val ∧ c.val ≤ 57) := by
  rw [is_digit_refines h, isDigit]
  simp

/-- The digit run `skip_digits` walked over. -/
private theorem skip_digits_loop_digits {b : Slice Std.U8} (f : Nat) :
    ∀ (i j : Std.Usize), b.val.length - i.val ≤ f →
      frontend.scan_fast.skip_digits_loop b i = ok j →
      i.val ≤ j.val ∧ ∀ (m : Nat) (hm : m < b.val.length), i.val ≤ m → m < j.val →
        48 ≤ (b.val[m]).val ∧ (b.val[m]).val ≤ 57 := by
  induction f with
  | zero =>
    intro i j hf h
    rw [frontend.scan_fast.skip_digits_loop.eq_def] at h
    rw [if_neg (show ¬ (i < Slice.len b) by scalar_tac)] at h
    have hij : i = j := by simpa using h
    subst hij
    exact ⟨le_refl _, fun m hm h1 h2 => absurd h2 (by omega)⟩
  | succ f ih =>
    intro i j hf h
    rw [frontend.scan_fast.skip_digits_loop.eq_def] at h
    by_cases hlt : i < Slice.len b
    · rw [if_pos hlt] at h
      have hi : i.val < b.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
      have hc' : c = b.val[i.val] := index_ok hi hc
      by_cases hwt : w = true
      · rw [if_pos hwt] at h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hv := usize_add_one_inv hi3
        obtain ⟨hle, hall⟩ := ih i3 j (by omega) h
        refine ⟨by omega, ?_⟩
        intro m hm h1 h2
        by_cases hmi : m = i.val
        · subst hmi; rw [← hc']; exact (is_digit_val hw).mp hwt
        · exact hall m hm (by omega) h2
      · rw [if_neg hwt] at h
        have hij : i = j := by simpa using h
        subst hij
        exact ⟨le_refl _, fun m hm h1 h2 => absurd h2 (by omega)⟩
    · rw [if_neg hlt] at h
      have hij : i = j := by simpa using h
      subst hij
      exact ⟨le_refl _, fun m hm h1 h2 => absurd h2 (by omega)⟩

/-- **`skip_digits` walks over decimal digits only.** -/
theorem skip_digits_digits {b : Slice Std.U8} {i j : Std.Usize}
    (h : frontend.scan_fast.skip_digits b i = ok j) :
    i.val ≤ j.val ∧ ∀ (m : Nat) (hm : m < b.val.length), i.val ≤ m → m < j.val →
      48 ≤ (b.val[m]).val ∧ (b.val[m]).val ≤ 57 :=
  skip_digits_loop_digits (b.val.length - i.val) i j (le_refl _) h

/-- The port's `&b[st..en]`, inverted. -/
private theorem range_index_val {b s : Slice Std.U8} {st en : Std.Usize}
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := st, «end» := en } = ok s) :
    st.val ≤ en.val ∧ en.val ≤ b.val.length ∧ s.val = List.slice st.val en.val b.val := by
  rw [Slice.index_SliceIndexRangeUsizeSliceInst,
    core.slice.index.SliceIndexRangeUsizeSlice.index] at h
  split at h
  · rename_i hc
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [Result.ok.injEq] at h
    rw [← h]; simp
  · exact absurd h fail_not_ok

/-- `to_vec` of a byte slice copies it. -/
private theorem to_vec_val {s : Slice Std.U8} {v : alloc.vec.Vec Std.U8}
    (h : alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok v) : v.val = s.val := by
  have hc : ∀ x ∈ s.val, core.clone.CloneU8.clone x = ok x := by intro x _; rfl
  obtain ⟨y, hy, hyv⟩ :=
    WP.spec_imp_exists (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s hc)
  rw [h] at hy
  have hvy : v = y := by simpa using hy
  rw [hvy, hyv]
  rfl

/-- **Every byte `scan_quoted_nat` returns is a decimal digit**, and there is
at least one — `skip_digits`' own invariant.  This is what makes
`nat_decimal::from_decimal` succeed on a `natVal` literal the scanner
accepted. -/
theorem scan_quoted_nat_digits {b : Slice Std.U8} {i : Std.Usize}
    {ds : alloc.vec.Vec Std.U8} {e : Std.Usize}
    (h : frontend.scan_fast.scan_quoted_nat b i = ok (.Ok (ds, e))) :
    ds.val ≠ [] ∧ ∀ c ∈ ds.val, 48 ≤ c.val ∧ c.val ≤ 57 := by
  rw [frontend.scan_fast.scan_quoted_nat] at h
  obtain ⟨c0, hc0, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · simp [frontend.scan_fast.err] at h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · simp [frontend.scan_fast.err] at h
  rename_i hne
  obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · simp [frontend.scan_fast.err] at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hds, -⟩ := h
  obtain ⟨hle, hall⟩ := skip_digits_digits he1
  obtain ⟨h1, h2, h3⟩ := range_index_val hs
  have hval : ds.val = List.slice i2.val e1.val b.val := by
    rw [← hds, to_vec_val hv, h3]
  have hlen : ds.val.length = e1.val - i2.val := by
    rw [hval, List.slice_length]; omega
  have hne' : i2.val ≠ e1.val := fun hc => hne (by scalar_tac)
  refine ⟨by intro hc; rw [hc] at hlen; simp at hlen; omega, ?_⟩
  intro c hcm
  obtain ⟨m, hm, hme⟩ := List.getElem_of_mem hcm
  have hm2 : i2.val + m < e1.val := by rw [hlen] at hm; omega
  have hmb : i2.val + m < b.val.length := by omega
  have hq : (List.slice i2.val e1.val b.val)[m]? = b.val[i2.val + m]? :=
    List.getElem?_slice i2.val e1.val m b.val ⟨by omega, by omega⟩
  rw [← hval, List.getElem?_eq_getElem hm, List.getElem?_eq_getElem hmb] at hq
  have heq : ds.val[m]'hm = b.val[i2.val + m]'hmb := Option.some.inj hq
  rw [← hme, heq]
  exact hall (i2.val + m) hmb (by omega) hm2

/-! ## `nat_decimal`: the `natVal` literal's value

`crates/con-ron-core/src/frontend/nat_decimal.rs` — no con-leche counterpart:
con-leche's `readNat` produces a Lean `Nat` straight from the digits, and the
port has to read them into its own bignum (`ron::nat`).  This section is what
`export_c::parse_expr_rec_d` needs to close the `natVal` deviation:

    from_decimal_refines :
      frontend.nat_decimal.from_decimal ds = ok (some n) →
      Nat.toNat n = digitsVal ds.val ∧ Nat.NatWF n

and `digitsVal ds.val` is `Abs.lean`'s `natOfDigits ⟨ds⟩` (`natOfDigits_eq`).
The value identity needs **no** side condition: the port's `digits[i] - 48` is
a `u8` subtraction, so a run that returned `ok` had every byte at `48` or
above, and `digitsVal`'s `c.val - 48` is the same `Nat` subtraction.  What the
digits *are* matters only for `from_decimal` not returning `none`, which is
`scan_quoted_nat_digits` above. -/

section NatDecimal

open ConRon.Refine.Nat (limbsToNat toNat NatWF limbsToNat_nil limbsToNat_cons)

/-- The decimal value of a list of digit bytes — `Abs.lean`'s `natOfDigits`,
on the list. -/
def digitsVal (l : List Std.U8) : Nat := l.foldl (fun a c => a * 10 + (c.val - 48)) 0

theorem natOfDigits_eq (ds : alloc.vec.Vec Std.U8) : natOfDigits ds = digitsVal ds.val := rfl

/-- Reading `l` into an accumulator shifts the accumulator by `10 ^ |l|`. -/
theorem foldl_digits (l : List Std.U8) : ∀ a : Nat,
    l.foldl (fun a c => a * 10 + (c.val - 48)) a = a * 10 ^ l.length + digitsVal l := by
  induction l with
  | nil => intro a; simp [digitsVal]
  | cons c l ih =>
    intro a
    simp only [List.foldl_cons, List.length_cons, digitsVal] at *
    rw [ih (a * 10 + (c.val - 48)), ih (0 * 10 + (c.val - 48))]
    ring

theorem digitsVal_cons (c : Std.U8) (l : List Std.U8) :
    digitsVal (c :: l) = (c.val - 48) * 10 ^ l.length + digitsVal l := by
  conv_lhs => rw [digitsVal, List.foldl_cons, foldl_digits]
  simp

theorem digitsVal_append (l₁ l₂ : List Std.U8) :
    digitsVal (l₁ ++ l₂) = digitsVal l₁ * 10 ^ l₂.length + digitsVal l₂ := by
  conv_lhs => rw [digitsVal, List.foldl_append]
  rw [← digitsVal, foldl_digits l₂ (digitsVal l₁)]

/-! ### `mul_add_small`: `limbs := limbs * m + a`

`nat_decimal.rs:40-56`, which is `ron::nat::mul_u64_from`'s loop with the
initial carry set to `a` and the carry returned rather than pushed.  The
invariant is `Refine/Nat.lean`'s `mul_u64_from_val`, with the pending carry
carried in the statement. -/

private theorem mul_add_small_loop_val (limbs : alloc.vec.Vec Std.U64) (m : Std.U64)
    (n : Std.Usize) (hn : n.val = limbs.val.length) :
    ∀ (d : Nat) (i : Std.Usize) (carry : Std.U64) (out o : alloc.vec.Vec Std.U64)
      (c' : Std.U64), limbs.val.length - i.val ≤ d →
      frontend.nat_decimal.mul_add_small_loop limbs m n out carry i = ok (o, c') →
      limbsToNat o.val + 2 ^ (64 * o.val.length) * c'.val
        = limbsToNat out.val + 2 ^ (64 * out.val.length) *
            (m.val * limbsToNat (limbs.val.drop i.val) + carry.val) := by
  have base : ∀ (i : Std.Usize) (carry : Std.U64) (out o : alloc.vec.Vec Std.U64)
      (c' : Std.U64), limbs.val.length ≤ i.val →
      frontend.nat_decimal.mul_add_small_loop limbs m n out carry i = ok (o, c') →
      limbsToNat o.val + 2 ^ (64 * o.val.length) * c'.val
        = limbsToNat out.val + 2 ^ (64 * out.val.length) *
            (m.val * limbsToNat (limbs.val.drop i.val) + carry.val) := by
    intro i carry out o c' hni h
    rw [frontend.nat_decimal.mul_add_small_loop.eq_def,
      if_neg (show ¬ (i < n) by scalar_tac)] at h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    rw [List.drop_eq_nil_of_le hni, ← h.1, ← h.2]
    simp [limbsToNat_nil]
  intro d
  induction d with
  | zero => intro i carry out o c' hd h; exact base i carry out o c' (by omega) h
  | succ d ih =>
    intro i carry out o c' hd h
    rcases Nat.lt_or_ge i.val limbs.val.length with hin | hin
    · rw [frontend.nat_decimal.mul_add_small_loop.eq_def,
        if_pos (show i < n by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨x1, hx1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨x2, hx2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨x3, hx3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨lo, hlo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hi64, hhi, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
      have hx' : x = limbs.val[i.val] := by
        have hg := ExprOps.vec_index_getElem? hx
        rw [List.getElem?_eq_getElem hin, Option.some.injEq] at hg
        exact hg.symm
      have hxv : x1.val = x.val := by
        rw [← lift_val hx1, Std.UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      have hmv : x2.val = m.val := by
        rw [← lift_val hx2, Std.UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      have hcv : x3.val = carry.val := by
        rw [← lift_val hx3, Std.UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      have hpv : p.val = x.val * m.val := by
        have := (Nat.umul_val hp).2; rw [hxv, hmv] at this; exact this
      have htv : t.val = x.val * m.val + carry.val := by
        have := Nat.uadd_val ht; rw [hpv, hcv] at this; exact this
      have hsv : s.val = t.val / 2 ^ 64 := by
        have := (Nat.ushiftRightI_val hs).2; simpa using this
      have hlov : lo.val = t.val % 2 ^ 64 := by
        rw [← lift_val hlo]; exact Std.UScalar.cast_val_eq _ _
      have hhiv : hi64.val = s.val := by
        rw [← lift_val hhi, Std.UScalar.cast_val_eq]
        refine Nat.mod_eq_of_lt ?_
        rw [hsv, htv]
        have hx64 : x.val < 2 ^ 64 := by scalar_tac
        have hm64 : m.val < 2 ^ 64 := by scalar_tac
        have hc64 : carry.val < 2 ^ 64 := by scalar_tac
        refine Nat.div_lt_of_lt_mul ?_
        calc x.val * m.val + carry.val
            < (2 ^ 64 - 1) * (2 ^ 64 - 1) + 2 ^ 64 := by
              exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul (by omega) (by omega)) hc64
          _ ≤ 2 ^ 64 * 2 ^ 64 := by
              have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := Nat.pow_two_64
              rw [h64]; omega
      have hword : lo.val + 2 ^ 64 * hi64.val = m.val * x.val + carry.val := by
        rw [hlov, hhiv, hsv, htv]
        have := Nat.mod_add_div (x.val * m.val + carry.val) (2 ^ 64)
        rw [Nat.mul_comm m.val]
        omega
      have hi7v : i7.val = i.val + 1 := by have := Nat.uadd_val hi7; simpa using this
      have hIH := ih i7 hi64 out1 o c' (by omega) h
      rw [vec_push_val hout1, hi7v] at hIH
      simp only [List.length_append, List.length_cons, List.length_nil,
        Nat.limbsToNat_append, limbsToNat_cons, limbsToNat_nil,
        Nat.mul_zero, Nat.add_zero] at hIH
      rw [show 64 * (out.val.length + (0 + 1)) = 64 * out.val.length + 64 by omega,
        Nat.pow_add] at hIH
      rw [List.drop_eq_getElem_cons hin, limbsToNat_cons, ← hx']
      exact Nat.shl_step_arith _ _ _ _ _ _ _ _ _ _ hIH hword
    · exact base i carry out o c' hin h

/-- **`nat_decimal::mul_add_small` is `limbs * m + a`** (`nat_decimal.rs:40-56`). -/
theorem mul_add_small_val {limbs out : alloc.vec.Vec Std.U64} {m a : Std.U64}
    (h : frontend.nat_decimal.mul_add_small limbs m a = ok out) :
    limbsToNat out.val = m.val * limbsToNat limbs.val + a.val := by
  rw [frontend.nat_decimal.mul_add_small] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨o, c'⟩, hloop, h⟩ := bind_eq_ok_iff.mp h
  have hkey := mul_add_small_loop_val limbs m (alloc.vec.Vec.len limbs) (by scalar_tac)
    limbs.val.length 0#usize a (alloc.vec.Vec.with_capacity Std.U64 i) o c'
    (by omega) hloop
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  rw [h0] at hkey
  simp only [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
    limbsToNat_nil, List.length_nil, Nat.mul_zero, pow_zero, Nat.one_mul,
    Nat.zero_add, List.drop_zero] at hkey
  replace h : (if (c' != 0#u64) = true then alloc.vec.Vec.push o c' else ok o) = ok out := h
  split at h
  · rw [vec_push_val h, Nat.limbsToNat_append]
    simp only [limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero]
    exact hkey
  · rename_i hz
    have hzv : c'.val = 0 := by scalar_tac
    simp only [Result.ok.injEq] at h
    rw [← h]
    rw [hzv, Nat.mul_zero, Nat.add_zero] at hkey
    exact hkey

/-! ### The chunk loops -/

/-- The inner loop: nineteen digits at a time into a machine word.  The `u8`
subtraction is what makes `digitsVal`'s `c.val - 48` the same `Nat`. -/
private theorem chunk_loop_val (digits : Slice Std.U8) (i k : Std.Usize) :
    ∀ (d : Nat) (j : Std.Usize) (chunk pow c' p' : Std.U64), k.val - j.val ≤ d →
      j.val ≤ k.val → i.val + k.val ≤ digits.val.length →
      frontend.nat_decimal.from_decimal_go_loop0_loop0 digits i k chunk pow j
        = ok (c', p') →
      c'.val = chunk.val * 10 ^ (k.val - j.val)
          + digitsVal (((digits.val.drop (i.val + j.val)).take (k.val - j.val)))
        ∧ p'.val = pow.val * 10 ^ (k.val - j.val) := by
  intro d
  induction d with
  | zero =>
    intro j chunk pow c' p' hd hjk hik h
    rw [frontend.nat_decimal.from_decimal_go_loop0_loop0.eq_def,
      if_neg (show ¬ (j < k) by scalar_tac)] at h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    rw [show k.val - j.val = 0 by omega]
    simp [← h.1, ← h.2, digitsVal]
  | succ d ih =>
    intro j chunk pow c' p' hd hjk hik h
    rcases Nat.lt_or_ge j.val k.val with hjk' | hjk'
    · rw [frontend.nat_decimal.from_decimal_go_loop0_loop0.eq_def,
        if_pos (show j < k by scalar_tac)] at h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨a3, ha3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨a4, ha4, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨a5, ha5, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨chunk1, hchunk1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨pow1, hpow1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j1, hj1, h⟩ := bind_eq_ok_iff.mp h
      have ha1v : a1.val = chunk.val * 10 := by
        have := (Nat.umul_val ha1).2; simpa using this
      have ha2v : a2.val = i.val + j.val := by have := Nat.uadd_val ha2; simpa using this
      have hidx : i.val + j.val < digits.val.length := by omega
      have ha3' : a3 = digits.val[i.val + j.val]'hidx := by
        have hg := index_getElem? ha3
        rw [ha2v, List.getElem?_eq_getElem hidx, Option.some.injEq] at hg
        exact hg.symm
      have ha4v : a3.val = a4.val + 48 := by
        have := uscalar_sub_add ha4; simpa using this
      have ha5v : a5.val = a4.val := by
        rw [← lift_val ha5]; exact Std.U8.cast_U64_val_eq a4
      have hchunkv : chunk1.val = chunk.val * 10 + (a3.val - 48) := by
        have := Nat.uadd_val hchunk1; rw [ha1v, ha5v] at this; omega
      have hpowv : pow1.val = pow.val * 10 := by
        have := (Nat.umul_val hpow1).2; simpa using this
      have hj1v : j1.val = j.val + 1 := by have := Nat.uadd_val hj1; simpa using this
      obtain ⟨hc, hp⟩ := ih j1 chunk1 pow1 c' p' (by omega) (by omega) hik h
      rw [hj1v] at hc hp
      have hdrop : (digits.val.drop (i.val + j.val)).take (k.val - j.val)
          = digits.val[i.val + j.val]'hidx ::
            (digits.val.drop (i.val + (j.val + 1))).take (k.val - (j.val + 1)) := by
        rw [show i.val + (j.val + 1) = (i.val + j.val) + 1 by omega,
          List.drop_eq_getElem_cons hidx,
          show k.val - j.val = (k.val - (j.val + 1)) + 1 by omega, List.take_succ_cons]
      have hlen : ((digits.val.drop (i.val + (j.val + 1))).take (k.val - (j.val + 1))).length
          = k.val - (j.val + 1) := by
        rw [List.length_take, List.length_drop]; omega
      constructor
      · rw [hc, hchunkv, hdrop, digitsVal_cons, hlen, ← ha3',
          show k.val - j.val = (k.val - (j.val + 1)) + 1 by omega, pow_succ]
        ring
      · rw [hp, hpowv, show k.val - j.val = (k.val - (j.val + 1)) + 1 by omega, pow_succ]
        ring
    · rw [frontend.nat_decimal.from_decimal_go_loop0_loop0.eq_def,
        if_neg (show ¬ (j < k) by scalar_tac)] at h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      rw [show k.val - j.val = 0 by omega]
      simp [← h.1, ← h.2, digitsVal]

/-- The outer loop: one `mul_add_small` per chunk. -/
private theorem from_decimal_go_loop_val (digits : Slice Std.U8) (n : Std.Usize)
    (hn : n.val = digits.val.length) :
    ∀ (d : Nat) (i : Std.Usize) (acc out : alloc.vec.Vec Std.U64), n.val - i.val ≤ d →
      i.val ≤ n.val →
      frontend.nat_decimal.from_decimal_go_loop0 digits n acc i = ok out →
      limbsToNat out.val
        = limbsToNat acc.val * 10 ^ (n.val - i.val) + digitsVal (digits.val.drop i.val) := by
  intro d
  induction d with
  | zero =>
    intro i acc out hd hin h
    rw [frontend.nat_decimal.from_decimal_go_loop0.eq_def,
      if_neg (show ¬ (i < n) by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    rw [← h, show n.val - i.val = 0 by omega,
      List.drop_eq_nil_of_le (by omega)]
    simp [digitsVal]
  | succ d ih =>
    intro i acc out hd hin h
    rcases Nat.lt_or_ge i.val n.val with hlt | hge
    · rw [frontend.nat_decimal.from_decimal_go_loop0.eq_def,
        if_pos (show i < n by scalar_tac)] at h
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨⟨chunk, pow⟩, hcl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨limbs1, hml, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hkv : k.val = n.val - i.val := by have := uscalar_sub_add hk; omega
      have hk1v : k1.val ≤ k.val ∧ 1 ≤ k1.val := by
        rw [frontend.nat_decimal.CHUNK_DIGITS] at hk1
        split at hk1 <;> rename_i hgt <;>
          simp only [Result.ok.injEq] at hk1 <;> rw [← hk1] <;> constructor <;> scalar_tac
      have hi1v : i1.val = i.val + k1.val := by have := Nat.uadd_val hi1; simpa using this
      obtain ⟨hc, hp⟩ := chunk_loop_val digits i k1 k1.val 0#usize 0#u64 1#u64 chunk pow
        (by scalar_tac) (by scalar_tac) (by omega) hcl
      have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
      rw [h0] at hc hp
      simp only [Nat.sub_zero, Nat.add_zero] at hc hp
      have hcv : chunk.val = digitsVal ((digits.val.drop i.val).take k1.val) := by
        rw [hc]
        simp only [show (0#u64 : Std.U64).val = 0 from by scalar_tac, Nat.zero_mul,
          Nat.zero_add]
      have hpv : pow.val = 10 ^ k1.val := by
        rw [hp]
        simp only [show (1#u64 : Std.U64).val = 1 from by scalar_tac, Nat.one_mul]
      have hmlv := mul_add_small_val hml
      have hIH := ih i1 limbs1 out (by omega) (by omega) h
      rw [hi1v, hmlv, hcv] at hIH
      rw [hIH]
      have hsplit : digits.val.drop i.val
          = (digits.val.drop i.val).take k1.val ++ (digits.val.drop (i.val + k1.val)) := by
        rw [← List.drop_drop]
        exact (List.take_append_drop k1.val (digits.val.drop i.val)).symm
      have hlen : (digits.val.drop (i.val + k1.val)).length = n.val - (i.val + k1.val) := by
        rw [List.length_drop]; omega
      rw [hpv]
      conv_rhs => rw [hsplit]
      rw [digitsVal_append, hlen,
        show n.val - i.val = k1.val + (n.val - (i.val + k1.val)) by omega, pow_add]
      ring
    · rw [frontend.nat_decimal.from_decimal_go_loop0.eq_def,
        if_neg (show ¬ (i < n) by scalar_tac)] at h
      simp only [Result.ok.injEq] at h
      rw [← h, show n.val - i.val = 0 by omega, List.drop_eq_nil_of_le (by omega)]
      simp [digitsVal]

/-- **`nat_decimal::from_decimal` reads the literal's value** — the accept
direction, which needs no side condition: the port's `digits[i] - 48` is a
`u8` subtraction, so a run that returned `ok` had every byte at `48` or above,
and `digitsVal`'s `c.val - 48` is the same `Nat` subtraction. -/
theorem from_decimal_refines {ds : Slice Std.U8} {n : ron.nat.Nat}
    (h : frontend.nat_decimal.from_decimal ds = ok (some n)) :
    toNat n = digitsVal ds.val ∧ NatWF n := by
  rw [frontend.nat_decimal.from_decimal] at h
  split at h
  · simp at h
  obtain ⟨bb, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, Option.some.injEq] at h
    subst h
    rw [frontend.nat_decimal.from_decimal_go] at hv
    have hkey := from_decimal_go_loop_val ds (Slice.len ds) (by scalar_tac)
      ds.val.length 0#usize (alloc.vec.Vec.new Std.U64) v (by scalar_tac) (by scalar_tac) hv
    have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
    rw [h0] at hkey
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil, Nat.zero_mul,
      Nat.zero_add, List.drop_zero] at hkey
    obtain ⟨hnv, hwf⟩ := Nat.norm_refines hw
    exact ⟨by rw [hnv, hkey], hwf⟩
  · simp at h

end NatDecimal

end ConRon.Refine.Frontend

