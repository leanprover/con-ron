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

/-- The port's `lift`ed `|||`, as con-leche's. -/
private theorem absU32_lift_or {x y z : Std.U32} (h : lift (x ||| y) = ok z) :
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
  rw [absU32_lift_or hu3, absU32_lift_or hu2, absU32_lift_or hu1,
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
  rw [absU32_lift_or hu2, absU32_lift_or hu1,
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

/-! ### Completeness: the port accepts every literal the scanner produced

`export_c::parse_expr_rec_d` turns a `from_decimal` `none` into a `LineErr`,
and con-leche's `parseExprRecD` on a `.natVal` **cannot fail** — so a `none`
the proof could not rule out would be the port claiming con-leche rejects a
literal it accepts, which is the shape of a port bug.  It cannot happen:
`scan_quoted_nat` hands over a non-empty run of decimal digits, and on such a
run every step of `from_decimal` is in range.

The one non-obvious bound is the `Vec::push`: the limb count never exceeds the
number of digits consumed (`limbs.val.length ≤ i.val`), and a push only
happens while `i < n`, so `length + 1 ≤ n ≤ Usize.max`. -/


private theorem uadd_ok {ty : Std.UScalarTy} {x y : Std.UScalar ty}
    (h : x.val + y.val ≤ Std.UScalar.max ty) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val :=
  WP.spec_imp_exists (Std.UScalar.add_spec h)

private theorem umul_ok {ty : Std.UScalarTy} {x y : Std.UScalar ty}
    (h : x.val * y.val ≤ Std.UScalar.max ty) :
    ∃ z, x * y = ok z ∧ z.val = x.val * y.val :=
  WP.spec_imp_exists (Std.UScalar.mul_spec h)

private theorem usub_ok {ty : Std.UScalarTy} {x y : Std.UScalar ty}
    (h : y.val ≤ x.val) : ∃ z, x - y = ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (Std.UScalar.sub_spec h)
  exact ⟨z, hz, hzv.1⟩

private theorem push_ok {α : Type} (v : alloc.vec.Vec α) (x : α)
    (h : v.val.length < Std.Usize.max) :
    ∃ w, alloc.vec.Vec.push v x = ok w ∧ w.val = v.val ++ [x] :=
  WP.spec_imp_exists (alloc.vec.Vec.push_spec v x h)

private theorem vec_index_ok {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize)
    (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i
      = ok (v.val[i.val]'h) := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i h)
  rw [show alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i
      = alloc.vec.Vec.index_usize v i from alloc.vec.Vec.index_slice_index v i, hy, hyv]

/-! #### `all_digits` -/

private theorem all_digits_loop_ok (digits : Slice Std.U8) (n : Std.Usize)
    (hn : n.val = digits.val.length)
    (hd : ∀ (m : Nat) (hm : m < digits.val.length),
      48 ≤ (digits.val[m]).val ∧ (digits.val[m]).val ≤ 57) :
    ∀ (d : Nat) (i : Std.Usize), n.val - i.val ≤ d →
      frontend.nat_decimal.all_digits_loop digits n i = ok true := by
  intro d
  induction d with
  | zero =>
    intro i hd'
    rw [frontend.nat_decimal.all_digits_loop.eq_def,
      if_neg (show ¬ (i < n) by scalar_tac)]
  | succ d ih =>
    intro i hd'
    rcases Nat.lt_or_ge i.val n.val with hlt | hge
    · have hi : i.val < digits.val.length := by omega
      obtain ⟨hlo, hhi⟩ := hd i.val hi
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := Slice.length_ineq digits; omega
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      rw [frontend.nat_decimal.all_digits_loop.eq_def,
        if_pos (show i < n by scalar_tac)]
      simp only [slice_index_ok hi, bind_tc_ok,
        if_neg (show ¬ (digits.val[i.val] < 48#u8) by scalar_tac),
        if_neg (show ¬ (digits.val[i.val] > 57#u8) by scalar_tac), hw]
      exact ih w (by omega)
    · rw [frontend.nat_decimal.all_digits_loop.eq_def,
        if_neg (show ¬ (i < n) by scalar_tac)]

private theorem all_digits_ok (digits : Slice Std.U8)
    (hd : ∀ (m : Nat) (hm : m < digits.val.length),
      48 ≤ (digits.val[m]).val ∧ (digits.val[m]).val ≤ 57) :
    frontend.nat_decimal.all_digits digits = ok true := by
  rw [frontend.nat_decimal.all_digits]
  exact all_digits_loop_ok digits (Slice.len digits) (by scalar_tac) hd
    digits.val.length 0#usize (by scalar_tac)

/-! #### The chunk loop: nineteen digits fit in a `u64` -/

private theorem chunk_loop_ok (digits : Slice Std.U8) (i k : Std.Usize) (hk : k.val ≤ 19)
    (hik : i.val + k.val ≤ digits.val.length)
    (hd : ∀ (m : Nat) (hm : m < digits.val.length),
      48 ≤ (digits.val[m]).val ∧ (digits.val[m]).val ≤ 57) :
    ∀ (d : Nat) (j : Std.Usize) (chunk pow : Std.U64), k.val - j.val ≤ d → j.val ≤ k.val →
      chunk.val < 10 ^ j.val → pow.val = 10 ^ j.val →
      ∃ c' p', frontend.nat_decimal.from_decimal_go_loop0_loop0 digits i k chunk pow j
        = ok (c', p') := by
  intro d
  induction d with
  | zero =>
    intro j chunk pow hd' hjk hc hp
    exact ⟨chunk, pow, by
      rw [frontend.nat_decimal.from_decimal_go_loop0_loop0.eq_def,
        if_neg (show ¬ (j < k) by scalar_tac)]⟩
  | succ d ih =>
    intro j chunk pow hd' hjk hc hp
    rcases Nat.lt_or_ge j.val k.val with hjk' | hjk'
    · have hj18 : j.val ≤ 18 := by omega
      have hpow18 : (10 : Nat) ^ j.val ≤ 1000000000000000000 := by
        have h1 : (10 : Nat) ^ j.val ≤ 10 ^ 18 := Nat.pow_le_pow_right (by omega) hj18
        have h2 : (10 : Nat) ^ 18 = 1000000000000000000 := by norm_num
        omega
      have hidx : i.val + j.val < digits.val.length := by omega
      obtain ⟨hlo, hhi⟩ := hd (i.val + j.val) hidx
      have hlen : digits.val.length ≤ Std.Usize.max := Slice.length_ineq digits
      obtain ⟨a1, ha1, ha1v⟩ := umul_ok (x := chunk) (y := 10#u64) (by scalar_tac)
      obtain ⟨a2, ha2, ha2v⟩ := uadd_ok (x := i) (y := j) (by scalar_tac)
      have hidx2 : a2.val < digits.val.length := by omega
      have hdig : (digits.val[a2.val]'hidx2) = (digits.val[i.val + j.val]'hidx) := by
        simp only [ha2v]
      have hdlo : 48 ≤ (digits.val[a2.val]'hidx2).val := by rw [hdig]; exact hlo
      have hdhi : (digits.val[a2.val]'hidx2).val ≤ 57 := by rw [hdig]; exact hhi
      obtain ⟨a4, ha4, ha4v⟩ :=
        usub_ok (x := digits.val[a2.val]'hidx2) (y := 48#u8) (by scalar_tac)
      have hcastv : (Std.UScalar.cast .U64 a4).val = a4.val := Std.U8.cast_U64_val_eq a4
      have ha4v' : a4.val ≤ 9 := by scalar_tac
      obtain ⟨chunk1, hchunk1, hchunk1v⟩ :=
        uadd_ok (x := a1) (y := Std.UScalar.cast .U64 a4) (by
          rw [hcastv, ha1v]; scalar_tac)
      obtain ⟨pow1, hpow1, hpow1v⟩ := umul_ok (x := pow) (y := 10#u64) (by scalar_tac)
      obtain ⟨j1, hj1, hj1v⟩ := usize_add_ok (i := j) (by
        have := Slice.length_ineq digits; omega)
      obtain ⟨c', p', hrec⟩ := ih j1 chunk1 pow1 (by omega) (by omega)
        (by
          rw [hchunk1v, hcastv, ha1v, hj1v, pow_succ]
          have h10 : ((10#u64 : Std.U64)).val = 10 := by scalar_tac
          rw [h10]; omega)
        (by
          rw [hpow1v, hj1v, pow_succ, hp]
          have h10 : ((10#u64 : Std.U64)).val = 10 := by scalar_tac
          rw [h10])
      refine ⟨c', p', ?_⟩
      rw [frontend.nat_decimal.from_decimal_go_loop0_loop0.eq_def,
        if_pos (show j < k by scalar_tac)]
      simp only [ha1, ha2, slice_index_ok hidx2, ha4, hchunk1, hpow1, hj1,
        bind_tc_ok, lift]
      exact hrec
    · exact ⟨chunk, pow, by
        rw [frontend.nat_decimal.from_decimal_go_loop0_loop0.eq_def,
          if_neg (show ¬ (j < k) by scalar_tac)]⟩

/-! #### `mul_add_small` -/

private theorem mul_add_small_loop_ok (limbs : alloc.vec.Vec Std.U64) (m : Std.U64)
    (n : Std.Usize) (hn : n.val = limbs.val.length) :
    ∀ (d : Nat) (i : Std.Usize) (carry : Std.U64) (out : alloc.vec.Vec Std.U64),
      limbs.val.length - i.val ≤ d → out.val.length = i.val →
      i.val ≤ limbs.val.length →
      ∃ o c', frontend.nat_decimal.mul_add_small_loop limbs m n out carry i = ok (o, c')
        ∧ o.val.length = limbs.val.length := by
  intro d
  induction d with
  | zero =>
    intro i carry out hd hlen hile
    refine ⟨out, carry, ?_, by omega⟩
    rw [frontend.nat_decimal.mul_add_small_loop.eq_def,
      if_neg (show ¬ (i < n) by scalar_tac)]
  | succ d ih =>
    intro i carry out hd hlen hile
    rcases Nat.lt_or_ge i.val limbs.val.length with hin | hin
    · have hvmax : limbs.val.length ≤ Std.Usize.max := by scalar_tac
      have hx64 : (limbs.val[i.val]'hin).val ≤ 18446744073709551615 := by scalar_tac
      have hm64 : m.val ≤ 18446744073709551615 := by scalar_tac
      have hc64 : carry.val ≤ 18446744073709551615 := by scalar_tac
      have hcast1 : (Std.UScalar.cast .U128 (limbs.val[i.val]'hin)).val
          = (limbs.val[i.val]'hin).val := by
        rw [Std.UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
      have hcast2 : (Std.UScalar.cast .U128 m).val = m.val := by
        rw [Std.UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
      have hcast3 : (Std.UScalar.cast .U128 carry).val = carry.val := by
        rw [Std.UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
      have hprod : (limbs.val[i.val]'hin).val * m.val
          ≤ 340282366920938463426481119284349108225 :=
        Nat.mul_le_mul hx64 hm64
      obtain ⟨p, hp, hpv⟩ := umul_ok
        (x := Std.UScalar.cast .U128 (limbs.val[i.val]'hin))
        (y := Std.UScalar.cast .U128 m) (by rw [hcast1, hcast2]; scalar_tac)
      obtain ⟨t, ht, htv⟩ := uadd_ok (x := p) (y := Std.UScalar.cast .U128 carry) (by
        rw [hpv, hcast1, hcast2, hcast3]; scalar_tac)
      obtain ⟨out1, hout1, hout1v⟩ := push_ok out (Std.UScalar.cast .U64 t) (by omega)
      obtain ⟨sh, hsh, -⟩ :=
        WP.spec_imp_exists (Std.UScalar.ShiftRight_IScalar_spec t (64#i32)
          (by scalar_tac) (by scalar_tac))
      obtain ⟨i7, hi7, hi7v⟩ := usize_add_ok (i := i) (by omega)
      obtain ⟨o, c', hrec, holen⟩ := ih i7 (Std.UScalar.cast .U64 sh) out1 (by omega)
        (by rw [hout1v]; simp only [List.length_append, List.length_cons,
              List.length_nil]; omega) (by omega)
      refine ⟨o, c', ?_, holen⟩
      rw [frontend.nat_decimal.mul_add_small_loop.eq_def,
        if_pos (show i < n by scalar_tac)]
      simp only [vec_index_ok limbs i hin, hp, ht, hout1, hsh, hi7, bind_tc_ok, lift]
      exact hrec
    · refine ⟨out, carry, ?_, by omega⟩
      rw [frontend.nat_decimal.mul_add_small_loop.eq_def,
        if_neg (show ¬ (i < n) by scalar_tac)]

/-- **`mul_add_small` succeeds** whenever one more limb fits. -/
private theorem mul_add_small_ok (limbs : alloc.vec.Vec Std.U64) (m a : Std.U64)
    (h : limbs.val.length < Std.Usize.max) :
    ∃ out, frontend.nat_decimal.mul_add_small limbs m a = ok out
      ∧ out.val.length ≤ limbs.val.length + 1 := by
  obtain ⟨i, hi, hiv⟩ := usize_add_ok (i := alloc.vec.Vec.len limbs) (by scalar_tac)
  obtain ⟨o, c', hloop, holen⟩ := mul_add_small_loop_ok limbs m (alloc.vec.Vec.len limbs)
    (by scalar_tac) limbs.val.length 0#usize a (alloc.vec.Vec.with_capacity Std.U64 i)
    (by omega) (by
      simp only [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
        List.length_nil]
      scalar_tac) (by scalar_tac)
  rw [frontend.nat_decimal.mul_add_small]
  simp only [hi, hloop, bind_tc_ok]
  by_cases hz : (c' != 0#u64) = true
  · obtain ⟨w, hw, hwv⟩ := push_ok o c' (by omega)
    refine ⟨w, ?_, ?_⟩
    · show (if (c' != 0#u64) = true then alloc.vec.Vec.push o c' else ok o) = ok w
      rw [if_pos hz, hw]
    · rw [hwv]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  · refine ⟨o, ?_, by omega⟩
    show (if (c' != 0#u64) = true then alloc.vec.Vec.push o c' else ok o) = ok o
    rw [if_neg hz]

/-! #### The outer loop, `norm`, and `from_decimal` -/

private theorem from_decimal_go_loop_ok (digits : Slice Std.U8) (n : Std.Usize)
    (hn : n.val = digits.val.length)
    (hd : ∀ (m : Nat) (hm : m < digits.val.length),
      48 ≤ (digits.val[m]).val ∧ (digits.val[m]).val ≤ 57) :
    ∀ (d : Nat) (i : Std.Usize) (limbs : alloc.vec.Vec Std.U64), n.val - i.val ≤ d →
      i.val ≤ n.val → limbs.val.length ≤ i.val →
      ∃ out, frontend.nat_decimal.from_decimal_go_loop0 digits n limbs i = ok out := by
  intro d
  induction d with
  | zero =>
    intro i limbs hd' hin hll
    exact ⟨limbs, by
      rw [frontend.nat_decimal.from_decimal_go_loop0.eq_def,
        if_neg (show ¬ (i < n) by scalar_tac)]⟩
  | succ d ih =>
    intro i limbs hd' hin hll
    rcases Nat.lt_or_ge i.val n.val with hlt | hge
    · have hnmax : digits.val.length ≤ Std.Usize.max := Slice.length_ineq digits
      obtain ⟨k, hk, hkv⟩ := usub_ok (x := n) (y := i) (by omega)
      obtain ⟨k1, hk1e, hk1lo, hk1hi, hk1le⟩ :
          ∃ k1 : Std.Usize,
            (if k > frontend.nat_decimal.CHUNK_DIGITS
              then ok frontend.nat_decimal.CHUNK_DIGITS else ok k) = ok k1
            ∧ 1 ≤ k1.val ∧ k1.val ≤ 19 ∧ k1.val ≤ k.val := by
        rw [frontend.nat_decimal.CHUNK_DIGITS]
        by_cases hgt : k > 19#usize
        · exact ⟨19#usize, by rw [if_pos hgt], by scalar_tac, by scalar_tac, by scalar_tac⟩
        · exact ⟨k, by rw [if_neg hgt], by omega, by scalar_tac, le_rfl⟩
      obtain ⟨chunk, pow, hcl⟩ := chunk_loop_ok digits i k1 hk1hi (by omega) hd
        k1.val 0#usize 0#u64 1#u64 (by scalar_tac) (by scalar_tac)
        (by
          have h0 : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
          have h0' : ((0#u64 : Std.U64)).val = 0 := by scalar_tac
          rw [h0, h0']; simp)
        (by
          have h0 : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
          have h1 : ((1#u64 : Std.U64)).val = 1 := by scalar_tac
          rw [h0, h1]; simp)
      obtain ⟨limbs1, hml, hmllen⟩ := mul_add_small_ok limbs pow chunk (by omega)
      obtain ⟨i1, hi1, hi1v⟩ := uadd_ok (x := i) (y := k1) (by scalar_tac)
      obtain ⟨out, hout⟩ := ih i1 limbs1 (by omega) (by omega) (by omega)
      refine ⟨out, ?_⟩
      rw [frontend.nat_decimal.from_decimal_go_loop0.eq_def,
        if_pos (show i < n by scalar_tac)]
      simp only [hk, hk1e, hcl, bind_tc_ok]
      show (do let limbs1 ← frontend.nat_decimal.mul_add_small limbs pow chunk
               let i1 ← i + k1
               frontend.nat_decimal.from_decimal_go_loop0 digits n limbs1 i1) = ok out
      simp only [hml, hi1, bind_tc_ok]
      exact hout
    · exact ⟨limbs, by
        rw [frontend.nat_decimal.from_decimal_go_loop0.eq_def,
          if_neg (show ¬ (i < n) by scalar_tac)]⟩

private theorem sig_len_ok (v : alloc.vec.Vec Std.U64) :
    ∀ (d : Nat) (k : Std.Usize), k.val ≤ d → k.val ≤ v.val.length →
      ∃ s, ron.nat.sig_len v k = ok s ∧ s.val ≤ k.val := by
  intro d
  induction d with
  | zero =>
    intro k hd hkv
    exact ⟨0#usize, by rw [ron.nat.sig_len, if_pos (show k = 0#usize by scalar_tac)],
      by scalar_tac⟩
  | succ d ih =>
    intro k hd hkv
    by_cases hz : k = 0#usize
    · exact ⟨0#usize, by rw [ron.nat.sig_len, if_pos hz], by scalar_tac⟩
    · have hk0 : 0 < k.val := by
        by_contra hcon
        exact hz (by scalar_tac)
      obtain ⟨i, hi, hiv⟩ := usub_ok (x := k) (y := 1#usize) (by scalar_tac)
      have hilt : i.val < v.val.length := by scalar_tac
      rw [ron.nat.sig_len, if_neg hz]
      simp only [hi, vec_index_ok v i hilt, bind_tc_ok]
      by_cases hnz : (v.val[i.val]'hilt != 0#u64) = true
      · exact ⟨k, by rw [if_pos hnz], le_rfl⟩
      · obtain ⟨s, hs, hsv⟩ := ih i (by scalar_tac) (by omega)
        exact ⟨s, by rw [if_neg hnz, hs], by scalar_tac⟩

private theorem copy_from_ok (v : alloc.vec.Vec Std.U64) (e : Std.Usize) :
    ∀ (d : Nat) (i : Std.Usize) (out : alloc.vec.Vec Std.U64), e.val - i.val ≤ d →
      out.val.length + (e.val - i.val) ≤ Std.Usize.max →
      ∃ w, ron.nat.copy_from v i e out = ok w := by
  intro d
  induction d with
  | zero =>
    intro i out hd hb
    exact ⟨out, by rw [ron.nat.copy_from, if_pos (show i ≥ e by scalar_tac)]⟩
  | succ d ih =>
    intro i out hd hb
    by_cases hie : i ≥ e
    · exact ⟨out, by rw [ron.nat.copy_from, if_pos hie]⟩
    · by_cases hiv : i ≥ alloc.vec.Vec.len v
      · exact ⟨out, by rw [ron.nat.copy_from, if_neg hie, if_pos hiv]⟩
      · have hilt : i.val < v.val.length := by scalar_tac
        have hlt : i.val < e.val := by scalar_tac
        obtain ⟨out1, hout1, hout1v⟩ := push_ok out (v.val[i.val]'hilt) (by omega)
        obtain ⟨i3, hi3, hi3v⟩ := usize_add_ok (i := i) (by scalar_tac)
        obtain ⟨w, hw⟩ := ih i3 out1 (by omega) (by
          rw [hout1v]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)
        refine ⟨w, ?_⟩
        rw [ron.nat.copy_from, if_neg hie, if_neg hiv]
        simp only [vec_index_ok v i hilt, hout1, hi3, bind_tc_ok]
        exact hw

private theorem norm_ok (limbs : alloc.vec.Vec Std.U64) :
    ∃ n, ron.nat.norm limbs = ok n := by
  obtain ⟨s, hs, hsv⟩ := sig_len_ok limbs limbs.val.length (alloc.vec.Vec.len limbs)
    (by scalar_tac) (by scalar_tac)
  rw [ron.nat.norm]
  simp only [hs, bind_tc_ok]
  by_cases heq : s = alloc.vec.Vec.len limbs
  · exact ⟨{ limbs := limbs }, by rw [if_pos heq]⟩
  · obtain ⟨w, hw⟩ := copy_from_ok limbs s s.val 0#usize (alloc.vec.Vec.new Std.U64)
      (by scalar_tac) (by
        simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil]
        scalar_tac)
    exact ⟨{ limbs := w }, by rw [if_neg heq]; simp only [hw, bind_tc_ok]⟩

/-- **`nat_decimal::from_decimal` accepts every non-empty run of decimal
digits.**  With `scan_quoted_nat_digits` this rules out the `none` arm at the
one call site, so `export_c` never reports `BadNatVal` for a literal the
scanner accepted — which is what keeps the port from claiming con-leche
rejects a `natVal` con-leche in fact reads. -/
theorem from_decimal_ok {ds : Slice Std.U8} (hne : ds.val ≠ [])
    (hd : ∀ c ∈ ds.val, 48 ≤ c.val ∧ c.val ≤ 57) :
    ∃ n, frontend.nat_decimal.from_decimal ds = ok (some n) := by
  have hd' : ∀ (m : Nat) (hm : m < ds.val.length),
      48 ≤ (ds.val[m]).val ∧ (ds.val[m]).val ≤ 57 :=
    fun m hm => hd _ (List.getElem_mem hm)
  have hlen : 0 < ds.val.length := by
    rcases hv : ds.val with _ | ⟨c, l⟩
    · exact absurd hv hne
    · simp
  rw [frontend.nat_decimal.from_decimal,
    if_neg (show ¬ (Slice.len ds = 0#usize) by scalar_tac)]
  simp only [all_digits_ok ds hd', bind_tc_ok]
  obtain ⟨v, hv⟩ := from_decimal_go_loop_ok ds (Slice.len ds) (by scalar_tac) hd'
    ds.val.length 0#usize (alloc.vec.Vec.new Std.U64) (by scalar_tac) (by scalar_tac)
    (by simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil]; omega)
  rw [frontend.nat_decimal.from_decimal_go]
  obtain ⟨n, hn⟩ := norm_ok v
  exact ⟨n, by simp only [hv, hn, bind_tc_ok, if_true]⟩

end NatDecimal


/-! ## `scan_string` (`Scan/Fast.lean:627-647`)

`scanString` slices the body out and hands it to `unescape`, or validates it
with `String.fromUTF8?`; the port does exactly the same, with `utf8_decode`
standing for `String.fromUTF8?` and `unescape` split into a byte pass and a
decode (deviation 1 of `scan_fast.rs`'s module note: Aeneas copies the code
after a loop into every one of its exits).

The two pieces the split costs are stated as `Prop`s rather than proved here —
see the note on each, and the file's closing census. -/

/-- **What the port's UTF-8 decoder owes con-leche.**  `scan_fast::utf8_decode`
has no con-leche counterpart: it stands for Lean's own `String.fromUTF8?`,
which `scanString` and `unescape` call on the bytes they have collected.  So
the agreement is a statement about a *primitive*, not a loop-for-loop
refinement of a ported function, and it is the one piece of this file that is
not a correspondence between two written-out recursions. -/
def Utf8DecodeSpec : Prop :=
  ∀ (b : Slice Std.U8) (j e : Std.Usize) (o : Option (alloc.vec.Vec Std.U32)),
    frontend.scan_fast.utf8_decode b j e = ok o →
    o.map absString = String.fromUTF8? ((absBytes b).extract j.val e.val)

/-- **What the port's two-pass `unescape` owes con-leche's one-pass one.**
`unescape_bytes` collects the bytes and `unescape` validates them; con-leche's
`unescape` interleaves the two. -/
def UnescapeSpec : Prop :=
  ∀ (b : Slice Std.U8) (j e : Std.Usize) (o : Option (alloc.vec.Vec Std.U32)),
    frontend.scan_fast.unescape b j e = ok o →
    o.map absString = unescape (absBytes b) (absPos j) (absPos e) ByteArray.empty

/-- The port's `&b[st..en]` as con-leche's `ByteArray.extract`. -/
theorem absBytes_range {b body : Slice Std.U8} {st en : Std.Usize}
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := st, «end» := en } = ok body) :
    absBytes body = (absBytes b).extract st.val en.val := by
  obtain ⟨h1, h2, h3⟩ := range_index_val h
  ext1
  simp [absBytes, h3, List.slice, List.map_take, List.map_drop,
    List.extract_eq_take_drop]

/-- A slice's length as con-leche's `ByteArray.usize`. -/
theorem absPos_len {s : Slice Std.U8} : absPos (Slice.len s) = (absBytes s).usize := by
  apply USize.toNat_inj.mp
  rw [absPos_toNat, absBytes_usize]
  scalar_tac

/-- The port's `0` position is con-leche's. -/
theorem absPos_zero : absPos (0#usize) = (0 : USize) := by
  apply USize.toNat_inj.mp
  rw [absPos_toNat]
  simp

/-- **`scan_fast::scan_string` refines `scanString`** (`Scan/Fast.lean:627-647
scanString`), under the two `Prop`s above. -/
theorem scan_string_refines (hu : Utf8DecodeSpec) (hun : UnescapeSpec)
    {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec Std.U32) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_string b i = ok o) :
    ScanSim absString o (scanString (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_string] at h
  rw [scanString]
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [show byteAt (absBytes b) (absPos i) = absByte c from (byte_at_refines hc).symm]
  split at h
  · -- not a quote
    rename_i hne
    rw [if_pos (show (absByte c != 34) = true by
      simp only [bne_iff_ne, ne_eq, absByte_eq_iff, UInt8.reduceToNat]
      scalar_tac)]
    rw [frontend.scan_fast.err] at h
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err (ScanErrSim.mk rfl (by first | rfl | rw [absPos_toNat]))
  · rename_i heq
    rw [if_neg (show ¬ ((absByte c != 34) = true) by
      simp only [bne_iff_ne, ne_eq, absByte_eq_iff, UInt8.reduceToNat, not_not]
      scalar_tac)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2, ← str_close_refines he]
    split at h
    · -- unterminated
      rename_i hz
      rw [if_pos (show (absPos e == 0) = true by
        simp only [beq_iff_eq]
        apply USize.toNat_inj.mp
        rw [absPos_toNat]
        simp only [USize.toNat_ofNat, Nat.zero_mod]
        scalar_tac)]
      rw [frontend.scan_fast.err] at h
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact ScanSim.err (ScanErrSim.mk rfl (by first | rfl | rw [absPos_toNat]))
    · rename_i hnz
      rw [if_neg (show ¬ ((absPos e == 0) = true) by
        simp only [beq_iff_eq]
        intro hcon
        exact hnz (by
          have hz := congrArg USize.toNat hcon
          rw [absPos_toNat] at hz
          simp only [USize.toNat_ofNat, Nat.zero_mod] at hz
          scalar_tac))]
      obtain ⟨esc, hesc, h⟩ := bind_eq_ok_iff.mp h
      rw [← has_escape_refines hesc]
      split at h
      · -- the escaped path
        rename_i hesct
        rw [if_pos hesct]
        obtain ⟨body, hbody, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        have hqa := hun body 0#usize (Slice.len body) q hq
        rw [absPos_zero, absPos_len, absBytes_range hbody] at hqa
        simp only [absPos_toNat]
        cases q with
        | none =>
          rw [← hqa]
          simp only [Option.map_none]
          rw [frontend.scan_fast.err] at h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ScanSim.err (ScanErrSim.mk rfl (by rfl))
        | some s =>
          rw [← hqa]
          simp only [Option.map_some]
          obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ScanSim.ok (by rw [absPos_add_one hi4])
      · -- the plain path
        rename_i hescf
        rw [if_neg hescf]
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        have hqa := hu b i2 e q hq
        simp only [absPos_toNat]
        cases q with
        | none =>
          rw [← hqa]
          simp only [Option.map_none]
          rw [frontend.scan_fast.err] at h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ScanSim.err (ScanErrSim.mk rfl (by rfl))
        | some s =>
          rw [← hqa]
          simp only [Option.map_some]
          obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ScanSim.ok (by rw [absPos_add_one hi3])


/-! ## `scan_quoted_nat`, exact (`Scan/Fast.lean:649-655`)

Deviation 2 of `scan_types.rs`'s module note again: the port returns the
literal's decimal **bytes** where con-leche returns `readNatAt`'s `Nat`.  The
bridge is `Abs.lean`'s `natOfDigits`, and the content is that con-leche's
`readNat` walking the same run folds the same digits — `ScanKit.lean`'s
`readNatAt_eq_readNat` reduces `readNatAt` to `readNat` once the run is known
to be a `skipDigits` run, and `readNat_eq` is its one-step unfolding. -/

/-- **`readNat` over a digit run is the fold over its bytes.** -/
private theorem readNat_run (b : Slice Std.U8) (s e : Std.Usize)
    (hel : e.val ≤ b.val.length)
    (hdig : ∀ (m : Nat) (hm : m < b.val.length), s.val ≤ m → m < e.val →
      48 ≤ (b.val[m]).val ∧ (b.val[m]).val ≤ 57)
    (hstop : ¬ (isDigit (absByte (pByteAt b e.val)) = true)) :
    ∀ (d : Nat) (k : Std.Usize) (acc : Nat), e.val - k.val ≤ d → s.val ≤ k.val →
      k.val ≤ e.val →
      readNat (absBytes b) (absPos k) acc
        = ((b.val.drop k.val).take (e.val - k.val)).foldl
            (fun a c => a * 10 + (c.val - 48)) acc := by
  intro d
  induction d with
  | zero =>
    intro k acc hd hsk hke
    have hke' : k.val = e.val := by omega
    rw [readNat_eq, show e.val - k.val = 0 by omega]
    simp only [List.take_zero, List.foldl_nil]
    split
    · rw [if_neg (by rw [hke']; exact hstop)]
    · rfl
  | succ d ih =>
    intro k acc hd hsk hke
    rcases Nat.lt_or_ge k.val e.val with hlt | hge
    · have hkb : k.val < b.val.length := by omega
      obtain ⟨hlo, hhi⟩ := hdig k.val hkb hsk hlt
      have hpb : pByteAt b k.val = b.val[k.val] := by rw [pByteAt, dif_pos hkb]
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_ok (i := k) (by
        have := Slice.length_ineq b; omega)
      rw [readNat_eq, if_pos hkb,
        if_pos (show isDigit (absByte (pByteAt b k.val)) = true by
          rw [hpb, isDigit]
          simp only [Bool.and_eq_true, le_absByte_iff, absByte_le_iff, decide_eq_true_eq,
            UInt8.reduceToNat]
          omega),
        ← absPos_add_one hk1, ih k1 _ (by omega) (by omega) (by omega)]
      rw [List.drop_eq_getElem_cons hkb,
        show e.val - k.val = (e.val - k1.val) + 1 by omega,
        List.take_succ_cons, List.foldl_cons, hk1v, hpb, absByte_toNat]
    · have hke' : k.val = e.val := by omega
      rw [readNat_eq, show e.val - k.val = 0 by omega]
      simp only [List.take_zero, List.foldl_nil]
      split
      · rw [if_neg (by rw [hke']; exact hstop)]
      · rfl

/-- **`scan_fast::scan_quoted_nat` refines `scanQuotedNat`**
(`Scan/Fast.lean:649-655 scanQuotedNat`), the port's digit bytes against
con-leche's `Nat` through `natOfDigits`. -/
theorem scan_quoted_nat_refines {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec Std.U8) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_quoted_nat b i = ok o) :
    ScanSim natOfDigits o (scanQuotedNat (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_quoted_nat] at h
  rw [scanQuotedNat]
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [show byteAt (absBytes b) (absPos i) = absByte c from (byte_at_refines hc).symm]
  split at h
  · rename_i hne
    rw [if_pos (show (absByte c != 34) = true by
      simp only [bne_iff_ne, ne_eq, absByte_eq_iff, UInt8.reduceToNat]
      scalar_tac)]
    rw [frontend.scan_fast.err] at h
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err (ScanErrSim.mk rfl (by rw [absPos_toNat]))
  · rename_i heq
    rw [if_neg (show ¬ ((absByte c != 34) = true) by
      simp only [bne_iff_ne, ne_eq, absByte_eq_iff, UInt8.reduceToNat, not_not]
      scalar_tac)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = i.val + 1 := usize_add_one_inv hi2
    have hsd : skipDigits (absBytes b) (absPos i2) = absPos e := (skip_digits_refines he).symm
    have hle : i2.val ≤ e.val := skip_digits_ge he
    rw [← absPos_add_one hi2, ← skip_digits_refines he]
    simp only []
    split at h
    · -- an empty run
      rename_i hz
      rw [if_pos (show ((absPos e == absPos i2) ||
          (byteAt (absBytes b) (absPos e) != 34)) = true by
        simp only [Bool.or_eq_true, beq_iff_eq]
        exact Or.inl (by rw [hz]))]
      rw [frontend.scan_fast.err] at h
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact ScanSim.err (ScanErrSim.mk rfl (by rw [absPos_toNat]))
    · rename_i hnz
      obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
      rw [show byteAt (absBytes b) (absPos e) = absByte c1 from (byte_at_refines hc1).symm]
      split at h
      · -- the run does not end in a quote
        rename_i hq
        rw [if_pos (show ((absPos e == absPos i2) || (absByte c1 != 34)) = true by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, absByte_eq_iff, UInt8.reduceToNat]
          refine Or.inr ?_
          scalar_tac)]
        rw [frontend.scan_fast.err] at h
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact ScanSim.err (ScanErrSim.mk rfl (by rw [absPos_toNat]))
      · rename_i hq
        have hc1v : c1.val = 34 := by scalar_tac
        have hebv : pByteAt b e.val = c1 := by
          have := byte_at_eq b e
          rw [hc1] at this
          simpa using this.symm
        have hel : e.val < b.val.length := by
          by_contra hcon
          rw [pByteAt, dif_neg hcon] at hebv
          scalar_tac
        rw [if_neg (show ¬ (((absPos e == absPos i2) || (absByte c1 != 34)) = true) by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, absByte_eq_iff, UInt8.reduceToNat,
            beq_iff_eq, not_or, not_not]
          refine ⟨?_, hc1v⟩
          intro hcon
          exact hnz (by
            have hh := congrArg USize.toNat hcon
            rw [absPos_toNat, absPos_toNat] at hh
            scalar_tac))]
        obtain ⟨body, hbody, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ds, hds, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine ScanSim.ok ?_
        rw [absPos_add_one hi4]
        congr 1
        -- the value: `readNatAt` over the run is the fold over the port's bytes
        obtain ⟨-, hdig⟩ := skip_digits_digits he
        obtain ⟨-, h2, h3⟩ := range_index_val hbody
        have hdsv : ds.val = List.slice i2.val e.val b.val := by
          rw [to_vec_val hds, h3]
        rw [readNatAt_eq_readNat hsd hle,
          readNat_run b i2 e (by omega) hdig
            (by
              rw [hebv, isDigit]
              simp only [Bool.and_eq_true, le_absByte_iff, absByte_le_iff, decide_eq_true_eq,
                UInt8.reduceToNat, not_and]
              intro _
              omega)
            (e.val - i2.val) i2 0 (le_refl _) (le_refl _) hle]
        rw [natOfDigits, hdsv, List.slice]

/-! ## `utf8_decode` (`scan_fast.rs:924-985`), the decoder

`scan_fast::utf8_decode` has no con-leche counterpart: it stands for Lean's
own `String.fromUTF8?`, which `scanString` and `unescape` call on the bytes
they have collected.  So this is the one piece of the tier that is not a
recursion-for-recursion refinement but an agreement with a *primitive*.

The primitive's own definition is `ByteArray.IsValidUTF8 b`, i.e.
`∃ l : List Char, b = l.utf8Encode` (`Init/Prelude.lean`), and `utf8Encode`
is `List.flatMap String.utf8EncodeChar`, whose four branches are plain `Nat`
division and remainder.  That is the whole strategy: **never** reason about
the toolchain's `parseFirstByte`/`assemble` decoder, only about the
*encoder*, which is arithmetic `omega` can see.  The port's loop then owes,
at every position:

* an accept step: the bytes it consumed are `utf8EncodeChar` of the code
  point it pushed (`win_enc_*` below), so the window splits as
  `[c].utf8Encode ++ <the rest>`;
* a reject step: **no** character encodes to a prefix of the window
  (`enc_cases` below is the case analysis that rules them all out), so the
  window is not valid UTF-8.

`ByteArray.isValidUTF8_utf8Encode_singleton_append_iff` is what carries a
reject past the accepted prefix, and `List.utf8Encode_cons` what carries an
accept. -/

/-- The window `[k, n)` of the port's slice, as con-leche sees it. -/
private def win (b : Slice Std.U8) (k n : Nat) : List UInt8 :=
  ((b.val.map absByte).drop k).take (n - k)

/-- The window, as a `ByteArray` — the shape `IsValidUTF8` wants. -/
private def winB (b : Slice Std.U8) (k n : Nat) : ByteArray := (win b k n).toByteArray

/-- A `Vec<u32>` of code points, as the character list behind `absString`. -/
private def chars (o : alloc.vec.Vec Std.U32) : List Char :=
  o.val.map fun c => Char.ofNat c.val

private theorem absString_chars (o : alloc.vec.Vec Std.U32) :
    absString o = String.ofList (chars o) := rfl

/-- The window is empty once the cursor has reached the end. -/
private theorem win_nil {b : Slice Std.U8} {k n : Nat} (h : n ≤ k) : win b k n = [] := by
  simp [win, Nat.sub_eq_zero_of_le h]

/-- The port's total byte accessor, inside the slice. -/
private theorem pByteAt_val {b : Slice Std.U8} {m : Nat} (h : m < b.val.length) :
    pByteAt b m = b.val[m] := by rw [pByteAt, dif_pos h]

/-- One byte off the front of the window. -/
private theorem win_cons {b : Slice Std.U8} {k n : Nat} (hk : k < n) (hn : n ≤ b.val.length) :
    win b k n = absByte (pByteAt b k) :: win b (k + 1) n := by
  have hkl : k < (b.val.map absByte).length := by simpa using by omega
  rw [win, win, List.drop_eq_getElem_cons hkl,
    show n - k = (n - (k + 1)) + 1 by omega, List.take_succ_cons,
    pByteAt_val (show k < b.val.length by omega)]
  simp

/-- The window's length. -/
private theorem win_length {b : Slice Std.U8} {k n : Nat} (hn : n ≤ b.val.length) :
    (win b k n).length = n - k := by
  simp only [win, List.length_take, List.length_drop, List.length_map]
  omega

/-- `m`-th byte of the window, for the first four `m` the decoder looks at. -/
private theorem win_getElem {b : Slice Std.U8} {k n m : Nat} (hn : n ≤ b.val.length)
    (hm : k + m < n) :
    (win b k n)[m]'(by rw [win_length hn]; omega) = absByte (pByteAt b (k + m)) := by
  rw [pByteAt_val (show k + m < b.val.length by omega)]
  simp only [win, List.getElem_take, List.getElem_drop, List.getElem_map]

/-- The port clamps `e` to the slice's length; the window does not care. -/
private theorem win_clamp {b : Slice Std.U8} {j e n : Nat} (hn : n = min e b.val.length) :
    win b j e = win b j n := by
  rcases Nat.le_total e b.val.length with he | he
  · rw [hn, Nat.min_eq_left he]
  · rw [win, win, List.take_of_length_le, List.take_of_length_le] <;>
      simp only [List.length_drop, List.length_map] <;> omega

/-! ### The three facts about `String.fromUTF8?` this proof needs -/

/-- `List.utf8Encode`, at the level of the byte list. -/
private theorem utf8Encode_toByteArray (l : List Char) :
    l.utf8Encode = (l.flatMap String.utf8EncodeChar).toByteArray := rfl

/-- A window a character list encodes is decoded to that list. -/
private theorem fromUTF8_win {b : Slice Std.U8} {k n : Nat} {l : List Char}
    (h : l.flatMap String.utf8EncodeChar = win b k n) :
    String.fromUTF8? (winB b k n) = some (String.ofList l) := by
  have hb : winB b k n = l.utf8Encode := by rw [winB, utf8Encode_toByteArray, h]
  rw [String.fromUTF8?, dif_pos (hb ▸ ByteArray.isValidUTF8_utf8Encode)]
  apply congrArg
  rw [← String.toByteArray_inj]
  rw [String.toByteArray_ofList]
  exact hb

/-- A window nothing encodes is not valid UTF-8. -/
private theorem fromUTF8_win_none {b : Slice Std.U8} {k n : Nat}
    (h : ¬ (winB b k n).IsValidUTF8) : String.fromUTF8? (winB b k n) = none := by
  rw [String.fromUTF8?, dif_neg h]

/-- The window, as a `ByteArray`, is valid exactly when some list encodes it. -/
private theorem winB_valid_iff {b : Slice Std.U8} {k n : Nat} :
    (winB b k n).IsValidUTF8 ↔ ∃ l : List Char, l.flatMap String.utf8EncodeChar = win b k n := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    rw [winB, utf8Encode_toByteArray] at hl
    have := congrArg (fun a => a.data.toList) hl
    simpa [List.data_toByteArray] using this.symm
  · rintro ⟨l, hl⟩
    exact ⟨l, by rw [winB, utf8Encode_toByteArray, hl]⟩

/-! ### `String.utf8EncodeChar`, as arithmetic

The four branches of `Init/Prelude.lean`'s `String.utf8EncodeChar`, with the
`%` on each lead byte discharged from the branch's own bound — the form the
port's byte tests can be compared against by `omega` alone.  `enc_cases` is
the *reject* direction (no character encodes to a window starting like this),
`enc_mk1`..`enc_mk4` the *accept* one. -/

/-- Every character's value is a Unicode scalar value. -/
private theorem char_valid (c : Char) : Nat.isValidChar c.val.toNat := c.valid

/-- **The four shapes of a UTF-8 encoded character.**  Each carries the range
that forces it, so the lead byte's range follows by `omega`: `≤ 0x7f`,
`0xc2..0xdf`, `0xe0..0xef`, `0xf0..0xf4` — and nothing else is a lead byte. -/
private theorem enc_cases (c : Char) :
    (String.utf8EncodeChar c = [UInt8.ofNat c.val.toNat] ∧ c.val.toNat ≤ 0x7f) ∨
    (String.utf8EncodeChar c =
        [UInt8.ofNat (c.val.toNat / 64 + 0xc0), UInt8.ofNat (c.val.toNat % 64 + 0x80)] ∧
      0x80 ≤ c.val.toNat ∧ c.val.toNat ≤ 0x7ff) ∨
    (String.utf8EncodeChar c =
        [UInt8.ofNat (c.val.toNat / 4096 + 0xe0), UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80),
         UInt8.ofNat (c.val.toNat % 64 + 0x80)] ∧
      0x800 ≤ c.val.toNat ∧ c.val.toNat ≤ 0xffff ∧
      (c.val.toNat < 0xd800 ∨ 0xdfff < c.val.toNat)) ∨
    (String.utf8EncodeChar c =
        [UInt8.ofNat (c.val.toNat / 262144 + 0xf0), UInt8.ofNat (c.val.toNat / 4096 % 64 + 0x80),
         UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80), UInt8.ofNat (c.val.toNat % 64 + 0x80)] ∧
      0x10000 ≤ c.val.toNat ∧ c.val.toNat ≤ 0x10ffff) := by
  have hv := char_valid c
  simp only [String.utf8EncodeChar]
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨rfl, h1⟩
  · refine Or.inr (Or.inl ⟨?_, by omega, h2⟩)
    rw [Nat.mod_eq_of_lt (show c.val.toNat / 64 < 0x20 by omega)]
  · refine Or.inr (Or.inr (Or.inl ⟨?_, by omega, h3, by rcases hv with hv | hv <;> omega⟩))
    rw [Nat.mod_eq_of_lt (show c.val.toNat / 4096 < 0x10 by omega)]
  · refine Or.inr (Or.inr (Or.inr ⟨?_, by omega, by rcases hv with hv | hv <;> omega⟩))
    rw [Nat.mod_eq_of_lt (show c.val.toNat / 262144 < 0x08 by
      rcases hv with hv | hv <;> omega)]

/-- A one-byte code point's encoding. -/
private theorem enc_mk1 {v : Nat} (hv : Nat.isValidChar v) (h : v ≤ 0x7f) :
    String.utf8EncodeChar (Char.ofNat v) = [UInt8.ofNat v] := by
  simp only [String.utf8EncodeChar, char_ofNat_toNat hv]
  rw [if_pos h]

/-- A two-byte code point's encoding. -/
private theorem enc_mk2 {v : Nat} (hv : Nat.isValidChar v) (h1 : 0x80 ≤ v) (h2 : v ≤ 0x7ff) :
    String.utf8EncodeChar (Char.ofNat v) =
      [UInt8.ofNat (v / 64 + 0xc0), UInt8.ofNat (v % 64 + 0x80)] := by
  simp only [String.utf8EncodeChar, char_ofNat_toNat hv]
  rw [if_neg (by omega), if_pos h2, Nat.mod_eq_of_lt (show v / 64 < 0x20 by omega)]

/-- A three-byte code point's encoding. -/
private theorem enc_mk3 {v : Nat} (hv : Nat.isValidChar v) (h1 : 0x800 ≤ v) (h2 : v ≤ 0xffff) :
    String.utf8EncodeChar (Char.ofNat v) =
      [UInt8.ofNat (v / 4096 + 0xe0), UInt8.ofNat (v / 64 % 64 + 0x80),
       UInt8.ofNat (v % 64 + 0x80)] := by
  simp only [String.utf8EncodeChar, char_ofNat_toNat hv]
  rw [if_neg (by omega), if_neg (by omega), if_pos h2,
    Nat.mod_eq_of_lt (show v / 4096 < 0x10 by omega)]

/-- A four-byte code point's encoding. -/
private theorem enc_mk4 {v : Nat} (hv : Nat.isValidChar v) (h1 : 0x10000 ≤ v)
    (h2 : v ≤ 0x10ffff) :
    String.utf8EncodeChar (Char.ofNat v) =
      [UInt8.ofNat (v / 262144 + 0xf0), UInt8.ofNat (v / 4096 % 64 + 0x80),
       UInt8.ofNat (v / 64 % 64 + 0x80), UInt8.ofNat (v % 64 + 0x80)] := by
  simp only [String.utf8EncodeChar, char_ofNat_toNat hv]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    Nat.mod_eq_of_lt (show v / 262144 < 0x08 by omega)]

/-! ### The loop's claim, and the two ways of carrying it -/

/-- What one call of `utf8_decode_loop` owes: on `some`, the code points it
appended are a character list encoding the window; on `none`, the window is
not valid UTF-8 at all. -/
private def DecClaim (b : Slice Std.U8) (n : Nat) (out : alloc.vec.Vec Std.U32)
    (k : Nat) : Option (alloc.vec.Vec Std.U32) → Prop
  | some o => ∃ l : List Char, chars o = chars out ++ l ∧
      l.flatMap String.utf8EncodeChar = win b k n
  | none => ¬ (winB b k n).IsValidUTF8

/-- The loop stops at the end of the window. -/
private theorem claim_stop {b : Slice Std.U8} {n k : Nat} {out : alloc.vec.Vec Std.U32}
    (h : n ≤ k) : DecClaim b n out k (some out) :=
  ⟨[], by simp, by simp [win_nil h]⟩

/-- A byte list's `ByteArray`, on an append. -/
private theorem toByteArray_append (x y : List UInt8) :
    (x ++ y).toByteArray = x.toByteArray ++ y.toByteArray := by
  apply ByteArray.ext
  simp [List.data_toByteArray]

/-- **One accepted character carries the claim.**  The window splits as the
character's own encoding followed by the rest, so a `some` gets one more
character at the front and a `none` stays invalid
(`ByteArray.isValidUTF8_utf8Encode_singleton_append_iff`). -/
private theorem claim_step {b : Slice Std.U8} {n k k' : Nat} {v : Std.U32}
    {out out' : alloc.vec.Vec Std.U32} {r : Option (alloc.vec.Vec Std.U32)}
    (hw : win b k n = String.utf8EncodeChar (Char.ofNat v.val) ++ win b k' n)
    (hpush : out'.val = out.val ++ [v])
    (ih : DecClaim b n out' k' r) : DecClaim b n out k r := by
  have hbw : winB b k n = [Char.ofNat v.val].utf8Encode ++ winB b k' n := by
    rw [winB, winB, hw, toByteArray_append, List.utf8Encode_singleton]
  cases r with
  | none =>
    rw [DecClaim] at ih ⊢
    rw [hbw, ByteArray.isValidUTF8_utf8Encode_singleton_append_iff]
    exact ih
  | some o =>
    obtain ⟨l, hl, he⟩ := ih
    refine ⟨Char.ofNat v.val :: l, ?_, ?_⟩
    · rw [hl, chars, chars, hpush]
      simp
    · rw [List.flatMap_cons, he, hw]

/-- The loop gave up: nothing encodes the window. -/
private theorem claim_stuck {b : Slice Std.U8} {n k : Nat}
    {out : alloc.vec.Vec Std.U32}
    (h : ∀ l : List Char, l.flatMap String.utf8EncodeChar ≠ win b k n) :
    DecClaim b n out k none := fun hc => by
  obtain ⟨l, hl⟩ := winB_valid_iff.mp hc
  exact h l hl

/-! ### What a valid window must start with -/

/-- The window's `m`-th byte, as a `getElem?`. -/
private theorem win_getElem? {b : Slice Std.U8} {k n m : Nat} (hn : n ≤ b.val.length)
    (hm : k + m < n) :
    (win b k n)[m]? = some (absByte (pByteAt b (k + m))) := by
  rw [List.getElem?_eq_getElem (by rw [win_length hn]; omega), win_getElem hn hm]

/-- **Nothing but these four shapes starts a window that is valid UTF-8.**
This is the reject direction of the decoder: every `ok none` the port returns
has to contradict all four, which after `absByte_eq_iff` is `omega`'s job. -/
private theorem win_lead {b : Slice Std.U8} {k n : Nat} {l : List Char}
    (hn : n ≤ b.val.length) (hk : k < n)
    (h : l.flatMap String.utf8EncodeChar = win b k n) :
    (∃ v : Nat, v ≤ 0x7f ∧ (pByteAt b k).val = v) ∨
    (∃ v : Nat, 0x80 ≤ v ∧ v ≤ 0x7ff ∧ k + 1 < n ∧
        (pByteAt b k).val = v / 64 + 0xc0 ∧
        (pByteAt b (k + 1)).val = v % 64 + 0x80) ∨
    (∃ v : Nat, 0x800 ≤ v ∧ v ≤ 0xffff ∧ (v < 0xd800 ∨ 0xdfff < v) ∧ k + 2 < n ∧
        (pByteAt b k).val = v / 4096 + 0xe0 ∧
        (pByteAt b (k + 1)).val = v / 64 % 64 + 0x80 ∧
        (pByteAt b (k + 2)).val = v % 64 + 0x80) ∨
    (∃ v : Nat, 0x10000 ≤ v ∧ v ≤ 0x10ffff ∧ k + 3 < n ∧
        (pByteAt b k).val = v / 262144 + 0xf0 ∧
        (pByteAt b (k + 1)).val = v / 4096 % 64 + 0x80 ∧
        (pByteAt b (k + 2)).val = v / 64 % 64 + 0x80 ∧
        (pByteAt b (k + 3)).val = v % 64 + 0x80) := by
  have hlen : (win b k n).length = n - k := win_length hn
  have hne : l ≠ [] := by
    rintro rfl
    rw [List.flatMap_nil] at h
    have := congrArg List.length h
    rw [hlen] at this
    simp at this
    omega
  obtain ⟨c, l', rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.flatMap_cons] at h
  have hct : c.toNat = c.val.toNat := rfl
  have hpre : ∀ (e : List UInt8) (m : Nat), String.utf8EncodeChar c = e → m < e.length →
      (win b k n)[m]? = e[m]? := by
    rintro e m rfl hm
    rw [← h, List.getElem?_append_left hm]
  have hlong : ∀ (e : List UInt8), String.utf8EncodeChar c = e → e.length ≤ n - k := by
    rintro e rfl
    have := congrArg List.length h
    rw [hlen, List.length_append] at this
    omega
  have hbyte : ∀ (e : List UInt8) (m X : Nat), String.utf8EncodeChar c = e →
      e[m]? = some (UInt8.ofNat X) → X < 256 → m < e.length → k + m < n →
      (pByteAt b (k + m)).val = X := by
    intro e m X hce hem hX hm hkm
    have h1 : (win b k n)[m]? = some (UInt8.ofNat X) := by rw [hpre e m hce hm, hem]
    rw [win_getElem? hn hkm] at h1
    have h2 := absByte_eq_iff.mp (Option.some.inj h1)
    rw [h2]
    simp [Nat.mod_eq_of_lt hX]
  rcases enc_cases c with ⟨he, h1⟩ | ⟨he, h1, h2⟩ | ⟨he, h1, h2, h3⟩ | ⟨he, h1, h2⟩
  · exact Or.inl ⟨c.val.toNat, h1,
      by simpa using hbyte _ 0 _ he (by simp) (by omega) (by simp) (by omega)⟩
  · have hl2 := hlong _ he
    simp only [List.length_cons, List.length_nil] at hl2
    refine Or.inr (Or.inl ⟨c.val.toNat, h1, h2, by omega, ?_, ?_⟩)
    · simpa using hbyte _ 0 _ he (by simp) (by omega) (by simp) (by omega)
    · exact hbyte _ 1 _ he (by simp) (by omega) (by simp) (by omega)
  · have hl2 := hlong _ he
    simp only [List.length_cons, List.length_nil] at hl2
    refine Or.inr (Or.inr (Or.inl ⟨c.val.toNat, h1, h2, h3, by omega, ?_, ?_, ?_⟩))
    · simpa using hbyte _ 0 _ he (by simp) (by omega) (by simp) (by omega)
    · exact hbyte _ 1 _ he (by simp) (by omega) (by simp) (by omega)
    · exact hbyte _ 2 _ he (by simp) (by omega) (by simp) (by omega)
  · have hl2 := hlong _ he
    simp only [List.length_cons, List.length_nil] at hl2
    refine Or.inr (Or.inr (Or.inr ⟨c.val.toNat, h1, h2, by omega, ?_, ?_, ?_, ?_⟩))
    · simpa using hbyte _ 0 _ he (by simp) (by omega) (by simp) (by omega)
    · exact hbyte _ 1 _ he (by simp) (by omega) (by simp) (by omega)
    · exact hbyte _ 2 _ he (by simp) (by omega) (by simp) (by omega)
    · exact hbyte _ 3 _ he (by simp) (by omega) (by simp) (by omega)

/-! ### What an accepted character consumes

The mirror image of `win_lead`: the bytes the port consumed at `k` *are* the
encoding of the code point it pushed, so the window splits and `claim_step`
applies.  The hypotheses are exactly the port's own tests. -/

/-- One ASCII byte. -/
private theorem win_enc1 {b : Slice Std.U8} {k n V : Nat} (hn : n ≤ b.val.length) (hk : k < n)
    (hV : V ≤ 0x7f) (h0 : (pByteAt b k).val = V) :
    win b k n = String.utf8EncodeChar (Char.ofNat V) ++ win b (k + 1) n := by
  rw [enc_mk1 (Or.inl (by omega)) hV, win_cons hk hn]
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact byte_ofNat (by rw [h0]; omega)

/-- A two-byte sequence. -/
private theorem win_enc2 {b : Slice Std.U8} {k n V : Nat} (hn : n ≤ b.val.length)
    (hk : k + 1 < n) (hV1 : 0x80 ≤ V) (hV2 : V ≤ 0x7ff)
    (h0 : (pByteAt b k).val = V / 64 + 0xc0)
    (h1 : (pByteAt b (k + 1)).val = V % 64 + 0x80) :
    win b k n = String.utf8EncodeChar (Char.ofNat V) ++ win b (k + 2) n := by
  rw [enc_mk2 (Or.inl (by omega)) hV1 hV2, win_cons (by omega) hn, win_cons (by omega) hn,
    show k + 1 + 1 = k + 2 from rfl]
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨byte_ofNat (by rw [h0]; omega), byte_ofNat (by rw [h1]; omega)⟩

/-- A three-byte sequence. -/
private theorem win_enc3 {b : Slice Std.U8} {k n V : Nat} (hn : n ≤ b.val.length)
    (hk : k + 2 < n) (hv : Nat.isValidChar V) (hV1 : 0x800 ≤ V) (hV2 : V ≤ 0xffff)
    (h0 : (pByteAt b k).val = V / 4096 + 0xe0)
    (h1 : (pByteAt b (k + 1)).val = V / 64 % 64 + 0x80)
    (h2 : (pByteAt b (k + 2)).val = V % 64 + 0x80) :
    win b k n = String.utf8EncodeChar (Char.ofNat V) ++ win b (k + 3) n := by
  rw [enc_mk3 hv hV1 hV2, win_cons (by omega) hn, win_cons (by omega) hn,
    win_cons (by omega) hn, show k + 1 + 1 = k + 2 from rfl,
    show k + 2 + 1 = k + 3 from rfl]
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨byte_ofNat (by rw [h0]; omega), byte_ofNat (by rw [h1]; omega),
    byte_ofNat (by rw [h2]; omega)⟩

/-- A four-byte sequence. -/
private theorem win_enc4 {b : Slice Std.U8} {k n V : Nat} (hn : n ≤ b.val.length)
    (hk : k + 3 < n) (hV1 : 0x10000 ≤ V) (hV2 : V ≤ 0x10ffff)
    (h0 : (pByteAt b k).val = V / 262144 + 0xf0)
    (h1 : (pByteAt b (k + 1)).val = V / 4096 % 64 + 0x80)
    (h2 : (pByteAt b (k + 2)).val = V / 64 % 64 + 0x80)
    (h3 : (pByteAt b (k + 3)).val = V % 64 + 0x80) :
    win b k n = String.utf8EncodeChar (Char.ofNat V) ++ win b (k + 4) n := by
  rw [enc_mk4 (Or.inr ⟨by omega, by omega⟩) hV1 hV2, win_cons (by omega) hn,
    win_cons (by omega) hn, win_cons (by omega) hn, win_cons (by omega) hn,
    show k + 1 + 1 = k + 2 from rfl, show k + 2 + 1 = k + 3 from rfl,
    show k + 3 + 1 = k + 4 from rfl]
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨byte_ofNat (by rw [h0]; omega), byte_ofNat (by rw [h1]; omega),
    byte_ofNat (by rw [h2]; omega), byte_ofNat (by rw [h3]; omega)⟩

/-! ### The port's bit assembly, as arithmetic

The decoder's `(c0 as u32 & M) << S | …` chains, with the `|||` turned into
`+` by `or_add` wherever the right operand fits under the left's low zeros —
the same trick the encoder side (`utf8_of_bytes`) uses. -/

/-- `as u32` on a byte. -/
private theorem cast32_lift_val {x : Std.U8} {z : Std.U32}
    (h : lift (Std.UScalar.cast .U32 x) = ok z) : z.val = x.val := by
  rw [← lift_val h]; exact Std.U8.cast_U32_val_eq x

/-- Aeneas's `+` returned `ok`, so nothing wrapped. -/
private theorem uscalar_add_val {ty : Std.UScalarTy} {x y z : Std.UScalar ty}
    (h : x + y = ok z) : z.val = x.val + y.val := by
  have := Std.UScalar.add_equiv x y
  rw [h] at this; simp at this; omega

private theorem and31 (x : Nat) : x &&& 31 = x % 32 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x 5

private theorem and15 (x : Nat) : x &&& 15 = x % 16 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x 4

private theorem and7 (x : Nat) : x &&& 7 = x % 8 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x 3

private theorem or_add64 {A c : Nat} (hc : c < 64) (hA : A % 64 = 0) : A ||| c = A + c := by
  obtain ⟨a, rfl⟩ : (2 : Nat) ^ 6 ∣ A := by
    simpa using Nat.dvd_of_mod_eq_zero hA
  exact or_add 6 a (by simpa using hc)

private theorem or_add4096 {A c : Nat} (hc : c < 4096) (hA : A % 4096 = 0) :
    A ||| c = A + c := by
  obtain ⟨a, rfl⟩ : (2 : Nat) ^ 12 ∣ A := by
    simpa using Nat.dvd_of_mod_eq_zero hA
  exact or_add 12 a (by simpa using hc)

private theorem or_add262144 {A c : Nat} (hc : c < 262144) (hA : A % 262144 = 0) :
    A ||| c = A + c := by
  obtain ⟨a, rfl⟩ : (2 : Nat) ^ 18 ∣ A := by
    simpa using Nat.dvd_of_mod_eq_zero hA
  exact or_add 18 a (by simpa using hc)

/-- The three shift amounts the decoder uses, as `Nat`s. -/
private theorem sh6 : (6#i32).toNat = 6 := by rfl
private theorem sh12 : (12#i32).toNat = 12 := by rfl
private theorem sh18 : (18#i32).toNat = 18 := by rfl

/-- A `u32` shift left by six that did not wrap. -/
private theorem ushl32_6 {x z : Std.U32} (h : x <<< (6#i32) = ok z)
    (hb : x.val * 64 < 4294967296) : z.val = x.val * 64 := by
  rw [ushl_val h, sh6, show x.val <<< 6 = x.val * 64 from by rw [Nat.shiftLeft_eq]]
  exact Nat.mod_eq_of_lt hb

/-- A `u32` shift left by twelve that did not wrap. -/
private theorem ushl32_12 {x z : Std.U32} (h : x <<< (12#i32) = ok z)
    (hb : x.val * 4096 < 4294967296) : z.val = x.val * 4096 := by
  rw [ushl_val h, sh12, show x.val <<< 12 = x.val * 4096 from by rw [Nat.shiftLeft_eq]]
  exact Nat.mod_eq_of_lt hb

/-- A `u32` shift left by eighteen that did not wrap. -/
private theorem ushl32_18 {x z : Std.U32} (h : x <<< (18#i32) = ok z)
    (hb : x.val * 262144 < 4294967296) : z.val = x.val * 262144 := by
  rw [ushl_val h, sh18,
    show x.val <<< 18 = x.val * 262144 from by rw [Nat.shiftLeft_eq]]
  exact Nat.mod_eq_of_lt hb

/-! ### The loop -/

/-- **The reject step, as arithmetic.**  `win_lead`'s four shapes, packaged so
that each of the port's `return None` sites discharges them all with one
`omega` over the bytes it has read. -/
private theorem win_not_valid {b : Slice Std.U8} {n k : Nat}
    {out : alloc.vec.Vec Std.U32} (hn : n ≤ b.val.length) (hk : k < n)
    (H : ∀ v : Nat,
      ¬ ((v ≤ 0x7f ∧ (pByteAt b k).val = v) ∨
         (0x80 ≤ v ∧ v ≤ 0x7ff ∧ k + 1 < n ∧ (pByteAt b k).val = v / 64 + 0xc0 ∧
            (pByteAt b (k + 1)).val = v % 64 + 0x80) ∨
         (0x800 ≤ v ∧ v ≤ 0xffff ∧ (v < 0xd800 ∨ 0xdfff < v) ∧ k + 2 < n ∧
            (pByteAt b k).val = v / 4096 + 0xe0 ∧
            (pByteAt b (k + 1)).val = v / 64 % 64 + 0x80 ∧
            (pByteAt b (k + 2)).val = v % 64 + 0x80) ∨
         (0x10000 ≤ v ∧ v ≤ 0x10ffff ∧ k + 3 < n ∧
            (pByteAt b k).val = v / 262144 + 0xf0 ∧
            (pByteAt b (k + 1)).val = v / 4096 % 64 + 0x80 ∧
            (pByteAt b (k + 2)).val = v / 64 % 64 + 0x80 ∧
            (pByteAt b (k + 3)).val = v % 64 + 0x80))) :
    DecClaim b n out k none := by
  refine claim_stuck ?_
  intro l hl
  rcases win_lead hn hk hl with ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, hv⟩
  · exact H v (Or.inl hv)
  · exact H v (Or.inr (Or.inl hv))
  · exact H v (Or.inr (Or.inr (Or.inl hv)))
  · exact H v (Or.inr (Or.inr (Or.inr hv)))

set_option maxHeartbeats 2000000 in
/-- **`utf8_decode`'s loop carries `DecClaim`.**  Each of the port's five
lead-byte classes either accepts — and `win_enc1`..`win_enc4` split the window
into the character's own encoding and the rest — or rejects, and then
`win_not_valid` shows nothing could have encoded that window. -/
private theorem utf8_decode_loop_spec (b : Slice Std.U8) (n : Std.Usize)
    (hn : n.val ≤ b.val.length) (f : Nat) :
    ∀ (out : alloc.vec.Vec Std.U32) (k : Std.Usize)
      (r : Option (alloc.vec.Vec Std.U32)),
      n.val - k.val ≤ f →
      frontend.scan_fast.utf8_decode_loop b n out k = ok r →
      DecClaim b n.val out k.val r := by
  induction f with
  | zero =>
    intro out k r hf h
    rw [frontend.scan_fast.utf8_decode_loop.eq_def] at h
    rw [if_neg (show ¬ (k < n) by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact claim_stop (show n.val ≤ k.val by scalar_tac)
  | succ f ih =>
    intro out k r hf h
    rw [frontend.scan_fast.utf8_decode_loop.eq_def] at h
    by_cases hlt : k < n
    case neg =>
      rw [if_neg hlt] at h
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact claim_stop (show n.val ≤ k.val by scalar_tac)
    rw [if_pos hlt] at h
    have hk : k.val < n.val := by scalar_tac
    have hkb : k.val < b.val.length := by omega
    obtain ⟨c0, hc0, h⟩ := bind_eq_ok_iff.mp h
    have hp0 : pByteAt b k.val = c0 := by rw [pByteAt_val hkb, index_ok hkb hc0]
    -- one byte
    by_cases hlt128 : c0 < 128#u8
    case pos =>
      rw [if_pos hlt128] at h
      have hc0n : c0.val < 128 := by scalar_tac
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = c0.val := cast32_lift_val hi
      have hk1v : k1.val = k.val + 1 := by simpa using uscalar_add_val hk1
      refine claim_step (v := i) ?_ (vec_push_val hout1) (ih out1 k1 r (by omega) h)
      rw [hk1v]
      exact win_enc1 hn hk (by omega) (by rw [hp0, hiv])
    rw [if_neg hlt128] at h
    have hc0n : 128 ≤ c0.val := by scalar_tac
    -- a continuation byte, or an overlong two-byte lead: no character starts here
    by_cases hlt194 : c0 < 194#u8
    case pos =>
      rw [if_pos hlt194] at h
      have hc0n2 : c0.val < 194 := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0]; omega)
    rw [if_neg hlt194] at h
    have hc0n2 : 194 ≤ c0.val := by scalar_tac
    -- two bytes
    by_cases hlt224 : c0 < 224#u8
    case pos =>
      rw [if_pos hlt224] at h
      have hc0n3 : c0.val < 224 := by scalar_tac
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = k.val + 1 := by simpa using uscalar_add_val hi
      by_cases htr : n ≤ i
      case pos =>
        rw [if_pos htr] at h
        have htr' : n.val ≤ k.val + 1 := by rw [← hiv]; scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0]; omega)
      rw [if_neg htr] at h
      have hkn1 : k.val + 1 < n.val := by rw [← hiv]; scalar_tac
      obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
      have hp1 : pByteAt b (k.val + 1) = c1 := by
        rw [← hiv, pByteAt_val (by omega), index_ok (by omega) hc1]
      by_cases hb1 : c1 < 128#u8
      case pos =>
        rw [if_pos hb1] at h
        have hb1' : c1.val < 128 := by scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0, hp1]; omega)
      rw [if_neg hb1] at h
      by_cases hb2 : 192#u8 ≤ c1
      case pos =>
        rw [if_pos hb2] at h
        have hb2' : 192 ≤ c1.val := by scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0, hp1]; omega)
      rw [if_neg hb2] at h
      have hc1a : 128 ≤ c1.val := by scalar_tac
      have hc1b : c1.val < 192 := by scalar_tac
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i6, hi6, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
      have e2 : i2.val = c0.val % 32 := by
        rw [and_lift_val hi2, cast32_lift_val hi1]
        simpa using and31 c0.val
      have e3 : i3.val = c0.val % 32 * 64 := by
        rw [ushl32_6 hi3 (by rw [e2]; omega), e2]
      have e5 : i5.val = c1.val % 64 := by
        rw [and_lift_val hi5, cast32_lift_val hi4]
        simpa using and63 c1.val
      have e6 : i6.val = c0.val % 32 * 64 + c1.val % 64 := by
        rw [or_lift_val hi6, e3, e5]
        exact or_add64 (by omega) (by omega)
      have hk1v : k1.val = k.val + 2 := by simpa using uscalar_add_val hk1
      refine claim_step (v := i6) ?_ (vec_push_val hout1) (ih out1 k1 r (by omega) h)
      rw [hk1v]
      exact win_enc2 hn hkn1 (by omega) (by omega)
        (by rw [hp0, e6]; omega) (by rw [hp1, e6]; omega)
    rw [if_neg hlt224] at h
    have hc0n3 : 224 ≤ c0.val := by scalar_tac
    -- three bytes
    by_cases hlt240 : c0 < 240#u8
    case pos =>
      rw [if_pos hlt240] at h
      have hc0n4 : c0.val < 240 := by scalar_tac
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = k.val + 2 := by simpa using uscalar_add_val hi
      by_cases htr : n ≤ i
      case pos =>
        rw [if_pos htr] at h
        have htr' : n.val ≤ k.val + 2 := by rw [← hiv]; scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0]; omega)
      rw [if_neg htr] at h
      have hkn2 : k.val + 2 < n.val := by rw [← hiv]; scalar_tac
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = k.val + 1 := by simpa using uscalar_add_val hi1
      obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨c2, hc2, h⟩ := bind_eq_ok_iff.mp h
      have hp1 : pByteAt b (k.val + 1) = c1 := by
        rw [← hi1v, pByteAt_val (by omega), index_ok (by omega) hc1]
      have hp2 : pByteAt b (k.val + 2) = c2 := by
        rw [← hiv, pByteAt_val (by omega), index_ok (by omega) hc2]
      by_cases hb1 : c1 < 128#u8
      case pos =>
        rw [if_pos hb1] at h
        have hb1' : c1.val < 128 := by scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0, hp1]; omega)
      rw [if_neg hb1] at h
      by_cases hb2 : 192#u8 ≤ c1
      case pos =>
        rw [if_pos hb2] at h
        have hb2' : 192 ≤ c1.val := by scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0, hp1]; omega)
      rw [if_neg hb2] at h
      by_cases hb3 : c2 < 128#u8
      case pos =>
        rw [if_pos hb3] at h
        have hb3' : c2.val < 128 := by scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0, hp2]; omega)
      rw [if_neg hb3] at h
      by_cases hb4 : 192#u8 ≤ c2
      case pos =>
        rw [if_pos hb4] at h
        have hb4' : 192 ≤ c2.val := by scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0, hp2]; omega)
      rw [if_neg hb4] at h
      have hc1a : 128 ≤ c1.val := by scalar_tac
      have hc1b : c1.val < 192 := by scalar_tac
      have hc2a : 128 ≤ c2.val := by scalar_tac
      have hc2b : c2.val < 192 := by scalar_tac
      obtain ⟨j2, hj2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j3, hj3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j4, hj4, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j5, hj5, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j6, hj6, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j7, hj7, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j8, hj8, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j9, hj9, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j10, hj10, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
      have e3 : j3.val = c0.val % 16 := by
        rw [and_lift_val hj3, cast32_lift_val hj2]
        simpa using and15 c0.val
      have e4 : j4.val = c0.val % 16 * 4096 := by
        rw [ushl32_12 hj4 (by rw [e3]; omega), e3]
      have e6 : j6.val = c1.val % 64 := by
        rw [and_lift_val hj6, cast32_lift_val hj5]
        simpa using and63 c1.val
      have e7 : j7.val = c1.val % 64 * 64 := by
        rw [ushl32_6 hj7 (by rw [e6]; omega), e6]
      have e8 : j8.val = c0.val % 16 * 4096 + c1.val % 64 * 64 := by
        rw [or_lift_val hj8, e4, e7]
        exact or_add4096 (by omega) (by omega)
      have e10 : j10.val = c2.val % 64 := by
        rw [and_lift_val hj10, cast32_lift_val hj9]
        simpa using and63 c2.val
      have eV : V.val = c0.val % 16 * 4096 + c1.val % 64 * 64 + c2.val % 64 := by
        rw [or_lift_val hV, e8, e10]
        exact or_add64 (by omega) (by omega)
      by_cases hover : V < 2048#u32
      case pos =>
        rw [if_pos hover] at h
        have hover' : V.val < 2048 := by scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0, hp1, hp2]; omega)
      rw [if_neg hover] at h
      have hover' : 2048 ≤ V.val := by scalar_tac
      by_cases hsur : 55296#u32 ≤ V
      case neg =>
        rw [if_neg hsur] at h
        have hsur' : V.val < 55296 := by scalar_tac
        obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
        have hk1v : k1.val = k.val + 3 := by simpa using uscalar_add_val hk1
        refine claim_step (v := V) ?_ (vec_push_val hout1) (ih out1 k1 r (by omega) h)
        rw [hk1v]
        exact win_enc3 hn hkn2 (Or.inl (by omega)) (by omega) (by omega)
          (by rw [hp0, eV]; omega) (by rw [hp1, eV]; omega) (by rw [hp2, eV]; omega)
      rw [if_pos hsur] at h
      have hsur' : 55296 ≤ V.val := by scalar_tac
      by_cases hsur2 : V < 57344#u32
      case pos =>
        rw [if_pos hsur2] at h
        have hsur2' : V.val < 57344 := by scalar_tac
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact win_not_valid hn hk (by intro v; rw [hp0, hp1, hp2]; omega)
      rw [if_neg hsur2] at h
      have hsur2' : 57344 ≤ V.val := by scalar_tac
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
      have hk1v : k1.val = k.val + 3 := by simpa using uscalar_add_val hk1
      refine claim_step (v := V) ?_ (vec_push_val hout1) (ih out1 k1 r (by omega) h)
      rw [hk1v]
      exact win_enc3 hn hkn2 (Or.inr ⟨by omega, by omega⟩) (by omega) (by omega)
        (by rw [hp0, eV]; omega) (by rw [hp1, eV]; omega) (by rw [hp2, eV]; omega)
    rw [if_neg hlt240] at h
    have hc0n4 : 240 ≤ c0.val := by scalar_tac
    -- four bytes, or a lead byte no character can have
    by_cases hlt245 : c0 < 245#u8
    case neg =>
      rw [if_neg hlt245] at h
      have hc0n5 : 245 ≤ c0.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0]; omega)
    rw [if_pos hlt245] at h
    have hc0n5 : c0.val < 245 := by scalar_tac
    obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
    have hiv : i.val = k.val + 3 := by simpa using uscalar_add_val hi
    by_cases htr : n ≤ i
    case pos =>
      rw [if_pos htr] at h
      have htr' : n.val ≤ k.val + 3 := by rw [← hiv]; scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0]; omega)
    rw [if_neg htr] at h
    have hkn3 : k.val + 3 < n.val := by rw [← hiv]; scalar_tac
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    have hi1v : i1.val = k.val + 1 := by simpa using uscalar_add_val hi1
    obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = k.val + 2 := by simpa using uscalar_add_val hi2
    obtain ⟨c2, hc2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨c3, hc3, h⟩ := bind_eq_ok_iff.mp h
    have hp1 : pByteAt b (k.val + 1) = c1 := by
      rw [← hi1v, pByteAt_val (by omega), index_ok (by omega) hc1]
    have hp2 : pByteAt b (k.val + 2) = c2 := by
      rw [← hi2v, pByteAt_val (by omega), index_ok (by omega) hc2]
    have hp3 : pByteAt b (k.val + 3) = c3 := by
      rw [← hiv, pByteAt_val (by omega), index_ok (by omega) hc3]
    by_cases hb1 : c1 < 128#u8
    case pos =>
      rw [if_pos hb1] at h
      have hb1' : c1.val < 128 := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0, hp1]; omega)
    rw [if_neg hb1] at h
    by_cases hb2 : 192#u8 ≤ c1
    case pos =>
      rw [if_pos hb2] at h
      have hb2' : 192 ≤ c1.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0, hp1]; omega)
    rw [if_neg hb2] at h
    by_cases hb3 : c2 < 128#u8
    case pos =>
      rw [if_pos hb3] at h
      have hb3' : c2.val < 128 := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0, hp2]; omega)
    rw [if_neg hb3] at h
    by_cases hb4 : 192#u8 ≤ c2
    case pos =>
      rw [if_pos hb4] at h
      have hb4' : 192 ≤ c2.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0, hp2]; omega)
    rw [if_neg hb4] at h
    by_cases hb5 : c3 < 128#u8
    case pos =>
      rw [if_pos hb5] at h
      have hb5' : c3.val < 128 := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0, hp3]; omega)
    rw [if_neg hb5] at h
    by_cases hb6 : 192#u8 ≤ c3
    case pos =>
      rw [if_pos hb6] at h
      have hb6' : 192 ≤ c3.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0, hp3]; omega)
    rw [if_neg hb6] at h
    have hc1a : 128 ≤ c1.val := by scalar_tac
    have hc1b : c1.val < 192 := by scalar_tac
    have hc2a : 128 ≤ c2.val := by scalar_tac
    have hc2b : c2.val < 192 := by scalar_tac
    have hc3a : 128 ≤ c3.val := by scalar_tac
    have hc3b : c3.val < 192 := by scalar_tac
    obtain ⟨m3, hm3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m4, hm4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m5, hm5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m6, hm6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m7, hm7, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m8, hm8, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m9, hm9, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m10, hm10, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m11, hm11, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m12, hm12, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m13, hm13, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m14, hm14, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m15, hm15, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
    have e4 : m4.val = c0.val % 8 := by
      rw [and_lift_val hm4, cast32_lift_val hm3]
      simpa using and7 c0.val
    have e5 : m5.val = c0.val % 8 * 262144 := by
      rw [ushl32_18 hm5 (by rw [e4]; omega), e4]
    have e7 : m7.val = c1.val % 64 := by
      rw [and_lift_val hm7, cast32_lift_val hm6]
      simpa using and63 c1.val
    have e8 : m8.val = c1.val % 64 * 4096 := by
      rw [ushl32_12 hm8 (by rw [e7]; omega), e7]
    have e9 : m9.val = c0.val % 8 * 262144 + c1.val % 64 * 4096 := by
      rw [or_lift_val hm9, e5, e8]
      exact or_add262144 (by omega) (by omega)
    have e11 : m11.val = c2.val % 64 := by
      rw [and_lift_val hm11, cast32_lift_val hm10]
      simpa using and63 c2.val
    have e12 : m12.val = c2.val % 64 * 64 := by
      rw [ushl32_6 hm12 (by rw [e11]; omega), e11]
    have e13 : m13.val = c0.val % 8 * 262144 + c1.val % 64 * 4096 + c2.val % 64 * 64 := by
      rw [or_lift_val hm13, e9, e12]
      exact or_add4096 (by omega) (by omega)
    have e15 : m15.val = c3.val % 64 := by
      rw [and_lift_val hm15, cast32_lift_val hm14]
      simpa using and63 c3.val
    have eV : V.val =
        c0.val % 8 * 262144 + c1.val % 64 * 4096 + c2.val % 64 * 64 + c3.val % 64 := by
      rw [or_lift_val hV, e13, e15]
      exact or_add64 (by omega) (by omega)
    by_cases hover : V < 65536#u32
    case pos =>
      rw [if_pos hover] at h
      have hover' : V.val < 65536 := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0, hp1, hp2, hp3]; omega)
    rw [if_neg hover] at h
    have hover' : 65536 ≤ V.val := by scalar_tac
    by_cases hbig : 1114111#u32 < V
    case pos =>
      rw [if_pos hbig] at h
      have hbig' : 1114111 < V.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact win_not_valid hn hk (by intro v; rw [hp0, hp1, hp2, hp3]; omega)
    rw [if_neg hbig] at h
    have hbig' : V.val ≤ 1114111 := by scalar_tac
    obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
    have hk1v : k1.val = k.val + 4 := by simpa using uscalar_add_val hk1
    refine claim_step (v := V) ?_ (vec_push_val hout1) (ih out1 k1 r (by omega) h)
    rw [hk1v]
    exact win_enc4 hn hkn3 (by omega) (by omega)
      (by rw [hp0, eV]; omega) (by rw [hp1, eV]; omega)
      (by rw [hp2, eV]; omega) (by rw [hp3, eV]; omega)

/-! ### `utf8_decode`, exact -/

/-- The port's `[j, e)` window is the `ByteArray` `String.fromUTF8?` is given. -/
private theorem absBytes_extract_winB (b : Slice Std.U8) (j e : Nat) :
    (absBytes b).extract j e = winB b j e := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, winB, List.data_toByteArray]
  apply Array.ext'
  rw [Array.toList_extract]
  simp [absBytes, win]

/-- **`scan_fast::utf8_decode` is Lean's `String.fromUTF8?`** on the window
`[j, e)` -- the first of `scan_string_refines`' two residues, discharged. -/
theorem utf8_decode_spec : Utf8DecodeSpec := by
  intro b j e o h
  rw [frontend.scan_fast.utf8_decode] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  have hnv : n.val = min e.val b.val.length := by
    split at hn
    · rename_i hc
      have hc' : e.val < b.val.length := by scalar_tac
      simp only [Result.ok.injEq] at hn
      rw [← hn]
      omega
    · rename_i hc
      have hc' : ¬ (e.val < b.val.length) := by scalar_tac
      simp only [Result.ok.injEq] at hn
      rw [← hn]
      have : (Slice.len b).val = b.val.length := by scalar_tac
      omega
  have hnb : n.val ≤ b.val.length := by omega
  have hclaim := utf8_decode_loop_spec b n hnb (n.val - j.val)
    (alloc.vec.Vec.new Std.U32) j o (le_refl _) h
  have hwin : (absBytes b).extract j.val e.val = winB b j.val n.val := by
    rw [absBytes_extract_winB, winB, winB, win_clamp hnv]
  cases o with
  | none =>
    rw [hwin, Option.map_none]
    exact (fromUTF8_win_none hclaim).symm
  | some out =>
    obtain ⟨l, hl, he⟩ := hclaim
    rw [hwin, Option.map_some, absString_chars, hl, fromUTF8_win he]
    simp [chars]

end ConRon.Refine.Frontend
