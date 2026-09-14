/-
**The list and name-object scanners, exact against con-leche** (task #87,
phase 3).

`crates/con-ron-core/src/frontend/scan_fast.rs:1169-1608` against
`ConLeche/Frontend/Scan/Fast.lean:666-905`: the index-list loop, the two
variant-valued fields `pw` and `hints`, and the first two **slot loops** —
the two name-table records.

## What this file gives the record scanners

Agents E, I and L consume exactly these five, plus the object skeleton below:

    theorem scan_nat_list_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_nat_list b i = ok o) :
        ScanSim absU64s o (scanNatList (absBytes b) (absPos i))

    theorem scan_pw_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_pw b i = ok o) :
        ScanSim absPwRec o (scanPw (absBytes b) (absPos i))

    theorem scan_hints_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_hints b i = ok o) :
        ScanSim absHintsRec o (scanHints (absBytes b) (absPos i))

    theorem scan_str_name_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_str_name b i = ok o) :
        ScanSim absNameRec o (scanStrName (absBytes b) (absPos i))

    theorem scan_num_name_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_num_name b i = ok o) :
        ScanSim absNameRec o (scanNumName (absBytes b) (absPos i))

`scan_nat_list_loop_refines` is exported too: `scanPw` and every list-valued
slot of the tier enters the loop past the `[` rather than through
`scanNatList`.

## The two shapes, once

* **A list loop** (`scan_nat_list_loop`) accumulates into a `Vec` in the port
  and conses onto a `List` in con-leche, reversing at the close.  The
  invariant is therefore `(absU64s acc).reverse` — *the port's accumulator,
  abstracted and reversed, is con-leche's* — and the close is
  `List.reverse_reverse`.  Every other list loop of the tier (agent I's four,
  agent L's) is this proof with another element abstraction.

* **A slot loop** (`scan_str_name_loop`, `scan_num_name_loop`) is a `while`
  over JSON members.  con-leche writes the member step out inline in each of
  its twenty `scan*Loop`s; the port factors it once as
  `scan_fast::next_member` (`scan_types.rs`'s module note, deviation 3, the
  way `Scan/Naive.lean`'s `naiveObjLoop` factors it).  The bridge is
  `objStep` — con-leche's inlined skeleton read back with its three
  continuations abstracted — and `next_member_sim`, which runs the port's
  factored copy against it once and for all.  A loop then owes only its own
  `close` and `key` arms.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.ScanKit

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConRon.Refine
open ConLeche.Frontend

/-! ## Plumbing -/

/-- An Aeneas `err` arm, read forwards. -/
private theorem err_val {T : Type} {offset : Std.Usize}
    {what : frontend.scan_types.ErrTag} {x : core.result.Result (T × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.err T offset what = ok x) :
    x = .Err ⟨offset, what⟩ := by
  rw [frontend.scan_fast.err] at h
  exact (Result.ok_injective h).symm

/-- Two port positions are equal exactly when their values are. -/
theorem usize_ext {i j : Std.Usize} (h : i.val = j.val) : i = j :=
  Std.UScalar.eq_of_val_eq h

@[simp] theorem absPos_eq_iff {i j : Std.Usize} : absPos i = absPos j ↔ i = j := by
  constructor
  · intro h; exact usize_ext (absPos_inj h)
  · intro h; rw [h]

/-- `absPos` of the zero position is `0`, which is con-leche's "no such
position" sentinel. -/
@[simp] theorem absPos_zero : absPos 0#usize = 0 := by
  apply USize.toNat_inj.mp; simp

/-! ## Provisional kit: `num_end` and `read_nat_at`

`scan_fast::num_end` and `scan_fast::read_nat_at` belong to `ScanKit`; they
are proved here, `private`, only so that this file — the template the other
loop agents read — does not wait for them.  Delete them and use
`ScanKit`'s the moment it has them. -/

/-- `skip_digits` only ever skips forward. -/
private theorem skip_digits_ge {b : Slice Std.U8} (f : Nat) :
    ∀ (i j : Std.Usize), b.val.length - i.val ≤ f →
      frontend.scan_fast.skip_digits b i = ok j → i.val ≤ j.val := by
  induction f with
  | zero =>
    intro i j hf h
    rw [frontend.scan_fast.skip_digits, frontend.scan_fast.skip_digits_loop.eq_def] at h
    rw [if_neg (show ¬ (i < Slice.len b) by scalar_tac)] at h
    simp only [Result.ok.injEq] at h; subst h; omega
  | succ f ih =>
    intro i j hf h
    rw [frontend.scan_fast.skip_digits, frontend.scan_fast.skip_digits_loop.eq_def] at h
    by_cases hlt : i < Slice.len b
    · rw [if_pos hlt] at h
      have hi : i.val < b.val.length := by scalar_tac
      obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w, -, h⟩ := bind_eq_ok_iff.mp h
      by_cases hw : w = true
      · rw [if_pos hw] at h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hv := usize_add_one_inv hi3
        have := ih i3 j (by omega) h
        omega
      · rw [if_neg hw] at h
        simp only [Result.ok.injEq] at h; subst h; omega
    · rw [if_neg hlt] at h
      simp only [Result.ok.injEq] at h; subst h; omega

/-- The digit run `num_end` accepted really starts at `i` and moves forward. -/
private theorem kit_num_end_run {b : Slice Std.U8} {i e : Std.Usize}
    (h : frontend.scan_fast.num_end b i = ok e) (hne : e ≠ i) :
    frontend.scan_fast.skip_digits b i = ok e ∧ i.val < e.val := by
  rw [frontend.scan_fast.num_end] at h
  obtain ⟨d, hd, h⟩ := bind_eq_ok_iff.mp h
  have hge := skip_digits_ge (b.val.length - i.val) i d (le_refl _) hd
  by_cases h1 : d = i
  · rw [if_pos h1] at h
    exact absurd (by simpa using h.symm) hne
  · rw [if_neg h1] at h
    obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
    have hdi : i.val < d.val := by
      have : i.val ≠ d.val := fun hc => h1 (usize_ext hc.symm)
      omega
    by_cases h2 : c = 48#u8
    · rw [if_pos h2] at h
      obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
      by_cases h3 : (d != i2) = true
      · rw [if_pos h3] at h
        exact absurd (by simpa using h.symm) hne
      · rw [if_neg h3] at h
        have : d = e := by simpa using h
        subst this; exact ⟨hd, hdi⟩
    · rw [if_neg h2] at h
      have : d = e := by simpa using h
      subst this; exact ⟨hd, hdi⟩

/-- A checked `u64` multiplication that succeeded is the exact product. -/
private theorem checked_mul_val {x y z : Std.U64}
    (h : Std.U64.checked_mul x y = some z) : z.val = x.val * y.val := by
  have hs := Std.U64.checked_mul_bv_spec x y
  rw [h] at hs; exact hs.2.1

/-- A checked `u64` addition that succeeded is the exact sum. -/
private theorem checked_add_val {x y z : Std.U64}
    (h : Std.U64.checked_add x y = some z) : z.val = x.val + y.val := by
  have hs := Std.U64.checked_add_bv_spec x y
  rw [h] at hs; exact hs.2.1

/-- A `lift`ed pure step is an equation on its value. -/
private theorem lift_val {α : Type} {x y : α} (h : lift x = ok y) : x = y := by
  simpa only [lift, Result.ok.injEq] using h

/-- `UInt8` subtraction does not wrap on a decimal digit. -/
private theorem uint8_sub_48 {x : UInt8} (h : 48 ≤ x.toNat) :
    (x - 48).toNat = x.toNat - 48 := by
  have h2 : x.toNat < 256 := x.toNat_lt_size
  simp [UInt8.toNat_sub]
  omega

/-- Widening a byte keeps its value. -/
private theorem uint8_toUInt64_toNat (x : UInt8) : x.toUInt64.toNat = x.toNat := by simp

/-- A `Nat` below `2 ^ 64` survives the round trip. -/
private theorem ofNat_toNat_of_lt {n : Nat} (h : n < 2 ^ 64) :
    (UInt64.ofNat n).toNat = n := by
  have h' : n < 18446744073709551616 := by omega
  simp [Nat.mod_eq_of_lt h']

/-- The digit's contribution, on con-leche's side of the fence. -/
private theorem digit_sub {c : Std.U8} (h : 48 ≤ c.val) :
    (absByte c - 48).toUInt64 = UInt64.ofNat (c.val - 48) := by
  have hge : 48 ≤ (absByte c).toNat := by rw [absByte_toNat]; exact h
  have hc256 : c.val < 256 := by scalar_tac
  apply UInt64.toNat_inj.mp
  rw [uint8_toUInt64_toNat, uint8_sub_48 hge, absByte_toNat,
    ofNat_toNat_of_lt (by omega)]

/-- One accumulation step, as a machine word: `UInt64.ofNat` is a ring map, so
the port's exact `u64` and con-leche's wrapping one agree with no bound. -/
private theorem ofNat_step (A : UInt64) (d : Nat) :
    A * 10 + UInt64.ofNat d = UInt64.ofNat (A.toNat * 10 + d) := by
  apply UInt64.toNat_inj.mp
  simp [Nat.mod_add_mod]

/-- **The port's `u64` accumulation is con-leche's machine-word one**
(`Scan/Fast.lean:474-482 readNat64`).  The port's `checked_*` failures are
`ErrTag::IndexOverflow`, so an `Ok` is a run that did not overflow, and
`UInt64.ofNat` is a ring map: no side condition is needed. -/
private theorem kit_read_nat64 {b : Slice Std.U8} (f : Nat) :
    ∀ (i e k : Std.Usize) (acc x : Std.U64),
      b.val.length - k.val ≤ f →
      frontend.scan_fast.read_nat_at_loop b i e acc k = ok (.Ok x) →
      readNat64 (absBytes b) (absPos k) (absPos e) (UInt64.ofNat acc.val)
        = UInt64.ofNat x.val := by
  induction f with
  | zero =>
    intro i e k acc x hf h
    have hk : ¬ k.val < b.val.length := by omega
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    rw [readNat64, dif_neg (fun hc => hk (absPos_lt_usize.mp hc))]
    by_cases h1 : k < e
    · rw [if_pos h1, if_neg (show ¬ (k < Slice.len b) by scalar_tac)] at h
      rw [show acc = x from by simpa using h]
    · rw [if_neg h1] at h
      rw [show acc = x from by simpa using h]
  | succ f ih =>
    intro i e k acc x hf h
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    rw [readNat64]
    by_cases hk : k.val < b.val.length
    · rw [dif_pos (absPos_lt_usize.mpr hk)]
      by_cases h1 : k < e
      · rw [if_pos h1] at h
        rw [if_pos (by simpa using (show k.val < e.val by scalar_tac))]
        rw [if_pos (show k < Slice.len b by scalar_tac)] at h
        obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
        have ho' : Std.U64.checked_mul acc 10#u64 = o := lift_val ho
        cases hmul : Std.U64.checked_mul acc 10#u64 with
        | none => rw [hmul] at ho'; rw [← ho'] at h; simp at h
        | some y =>
          rw [hmul] at ho'; rw [← ho'] at h
          have hy' := checked_mul_val hmul
          obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
          have hc2 : c = b.val[k.val]'hk := by
            obtain ⟨y1, hy1, hy2⟩ := WP.spec_imp_exists (Slice.index_usize_spec b k hk)
            rw [hy1] at hc
            rw [← Result.ok_injective hc, hy2]
          obtain ⟨d, hd, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hd1, hd2⟩ := ConRon.Refine.Nat.usub_val hd
          obtain ⟨e4, he4, h⟩ := bind_eq_ok_iff.mp h
          have he4' : e4.val = d.val := by
            rw [← lift_val he4, Std.UScalar.cast_val_eq]
            scalar_tac
          obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
          have ho1' : Std.U64.checked_add y e4 = o1 := lift_val ho1
          cases hadd : Std.U64.checked_add y e4 with
          | none => rw [hadd] at ho1'; rw [← ho1'] at h; simp at h
          | some x1 =>
            rw [hadd] at ho1'; rw [← ho1'] at h
            have hx1' := checked_add_val hadd
            obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
            have hk1' := usize_add_one_inv hk1
            have hcb : (absBytes b).uget (absPos k)
                (by rw [absPos_toNat, absBytes_size]; exact hk) = absByte c := by
              rw [absBytes_uget b (absPos k) _ (by rw [absPos_toNat]; exact hk)]
              simp only [absPos_toNat]; rw [hc2]
            rw [hcb, ← absPos_add_one hk1, digit_sub (by scalar_tac), ofNat_step]
            rw [show (UInt64.ofNat acc.val).toNat * 10 + (c.val - 48) = x1.val from by
              have hacc : acc.val < 2 ^ 64 := by scalar_tac
              rw [ofNat_toNat_of_lt hacc]
              scalar_tac]
            exact ih i e k1 x1 x (by omega) h
      · rw [if_neg h1] at h
        rw [if_neg (by simpa using (show ¬ k.val < e.val by scalar_tac))]
        rw [show acc = x from by simpa using h]
    · rw [dif_neg (fun hc => hk (absPos_lt_usize.mp hc))]
      by_cases h1 : k < e
      · rw [if_pos h1, if_neg (show ¬ (k < Slice.len b) by scalar_tac)] at h
        rw [show acc = x from by simpa using h]
      · rw [if_neg h1] at h
        rw [show acc = x from by simpa using h]

/-- A byte read inside the array, at a port position. -/
private theorem uget_abs {b : Slice Std.U8} {i : Std.Usize}
    (h : (absPos i).toNat < (absBytes b).size) :
    (absBytes b).uget (absPos i) h = absByte (pByteAt b i.val) := by
  have hi : i.val < b.val.length := by
    rw [absBytes_size, absPos_toNat] at h; exact h
  rw [absBytes_uget b (absPos i) h (by rw [absPos_toNat]; exact hi), pByteAt, dif_pos hi]
  simp

/-- `readNat` at a port position, unfolded once. -/
private theorem readNat_eq (b : Slice Std.U8) (i : Std.Usize) (acc : Nat) :
    readNat (absBytes b) (absPos i) acc =
      if i.val < b.val.length then
        (if isDigit (absByte (pByteAt b i.val)) then
            readNat (absBytes b) (absPos i + 1)
              (acc * 10 + ((absByte (pByteAt b i.val)).toNat - 48))
         else acc)
      else acc := by
  rw [readNat]
  by_cases h : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_abs]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]

/-- **The port's `u64` accumulation is con-leche's `Nat` one** (`Scan/Fast.lean:
104-111 readNat`).  con-leche's `readNat` stops at the first non-digit rather
than at `e`, so the run has to be the one `skip_digits` found — which is
exactly what `num_end` and `scan_quoted_nat` hand `read_nat_at`. -/
private theorem kit_read_nat {b : Slice Std.U8} (f : Nat) :
    ∀ (i e k : Std.Usize) (acc x : Std.U64),
      b.val.length - k.val ≤ f →
      frontend.scan_fast.skip_digits b k = ok e →
      frontend.scan_fast.read_nat_at_loop b i e acc k = ok (.Ok x) →
      readNat (absBytes b) (absPos k) acc.val = x.val := by
  induction f with
  | zero =>
    intro i e k acc x hf hsd h
    have hk : ¬ k.val < b.val.length := by omega
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    rw [readNat_eq, if_neg hk]
    by_cases h1 : k < e
    · rw [if_pos h1, if_neg (show ¬ (k < Slice.len b) by scalar_tac)] at h
      rw [show acc = x from by simpa using h]
    · rw [if_neg h1] at h
      rw [show acc = x from by simpa using h]
  | succ f ih =>
    intro i e k acc x hf hsd h
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    rw [readNat_eq]
    by_cases hk : k.val < b.val.length
    · rw [if_pos hk]
      -- what `skip_digits` saw at `k` decides both loops
      rw [frontend.scan_fast.skip_digits, frontend.scan_fast.skip_digits_loop.eq_def,
        if_pos (show k < Slice.len b by scalar_tac)] at hsd
      obtain ⟨c, hc, hsd⟩ := bind_eq_ok_iff.mp hsd
      have hc2 : c = b.val[k.val]'hk := by
        obtain ⟨y1, hy1, hy2⟩ := WP.spec_imp_exists (Slice.index_usize_spec b k hk)
        rw [hy1] at hc
        rw [← Result.ok_injective hc, hy2]
      have hpb : pByteAt b k.val = c := by rw [pByteAt, dif_pos hk, hc2]
      obtain ⟨w, hw, hsd⟩ := bind_eq_ok_iff.mp hsd
      have hw' : w = isDigit (absByte c) := is_digit_refines hw
      rw [hpb, ← hw']
      by_cases hwt : w = true
      · -- a digit: both loops step
        rw [if_pos hwt] at hsd
        rw [if_pos hwt]
        obtain ⟨k1, hk1, hsd⟩ := bind_eq_ok_iff.mp hsd
        have hk1' := usize_add_one_inv hk1
        have hsd' : frontend.scan_fast.skip_digits b k1 = ok e := hsd
        have hge := skip_digits_ge (b.val.length - k1.val) k1 e (le_refl _) hsd'
        rw [if_pos (show k < e by scalar_tac)] at h
        rw [if_pos (show k < Slice.len b by scalar_tac)] at h
        obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
        have ho' : Std.U64.checked_mul acc 10#u64 = o := lift_val ho
        cases hmul : Std.U64.checked_mul acc 10#u64 with
        | none => rw [hmul] at ho'; rw [← ho'] at h; simp at h
        | some y =>
          rw [hmul] at ho'; rw [← ho'] at h
          have hy' := checked_mul_val hmul
          obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
          have hc1' : c1 = c := by
            obtain ⟨y1, hy1, hy2⟩ := WP.spec_imp_exists (Slice.index_usize_spec b k hk)
            rw [hy1] at hc1
            rw [← Result.ok_injective hc1, hy2, hc2]
          subst hc1'
          obtain ⟨d, hd, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hd1, hd2⟩ := ConRon.Refine.Nat.usub_val hd
          obtain ⟨e4, he4, h⟩ := bind_eq_ok_iff.mp h
          have he4' : e4.val = d.val := by
            rw [← lift_val he4, Std.UScalar.cast_val_eq]
            scalar_tac
          obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
          have ho1' : Std.U64.checked_add y e4 = o1 := lift_val ho1
          cases hadd : Std.U64.checked_add y e4 with
          | none => rw [hadd] at ho1'; rw [← ho1'] at h; simp at h
          | some x1 =>
            rw [hadd] at ho1'; rw [← ho1'] at h
            have hx1' := checked_add_val hadd
            obtain ⟨k2, hk2, h⟩ := bind_eq_ok_iff.mp h
            have hk2' := usize_add_one_inv hk2
            have hsame : k1 = k2 := usize_ext (by omega)
            subst hsame
            rw [← absPos_add_one hk2]
            rw [show acc.val * 10 + ((absByte c1).toNat - 48) = x1.val from by
              rw [absByte_toNat]; scalar_tac]
            exact ih i e k1 x1 x (by omega) hsd' h
      · -- not a digit: `skip_digits` stopped here, so `e = k` and both stop
        rw [if_neg hwt] at hsd
        rw [if_neg hwt]
        have hek : k = e := by simpa using hsd
        rw [if_neg (show ¬ (k < e) by rw [← hek]; scalar_tac)] at h
        rw [show acc = x from by simpa using h]
    · rw [if_neg hk]
      by_cases h1 : k < e
      · rw [if_pos h1, if_neg (show ¬ (k < Slice.len b) by scalar_tac)] at h
        rw [show acc = x from by simpa using h]
      · rw [if_neg h1] at h
        rw [show acc = x from by simpa using h]

/-- **`read_nat_at` refines `readNatAt`** (`Scan/Fast.lean:499-500`).  The two
branches of `readNatAt` are the two lemmas above; the port has no such split
because its accumulation is `checked`. -/
private theorem kit_read_nat_at {b : Slice Std.U8} {i e : Std.Usize} {x : Std.U64}
    (hrun : frontend.scan_fast.skip_digits b i = ok e)
    (h : frontend.scan_fast.read_nat_at b i e = ok (.Ok x)) :
    x.val = readNatAt (absBytes b) (absPos i) (absPos e) := by
  rw [frontend.scan_fast.read_nat_at] at h
  rw [readNatAt]
  have hz : ((0#u64 : Std.U64).val : Nat) = 0 := by scalar_tac
  by_cases hd : absPos e - absPos i ≤ 18
  · rw [if_pos hd]
    have hr := kit_read_nat64 (b.val.length - i.val) i e i 0#u64 x (le_refl _) h
    rw [hz] at hr
    rw [show (UInt64.ofNat 0) = 0 from by decide] at hr
    rw [hr, ofNat_toNat_of_lt (by scalar_tac)]
  · rw [if_neg hd]
    have hr := kit_read_nat (b.val.length - i.val) i e i 0#u64 x (le_refl _) hrun h
    rw [hz] at hr
    exact hr.symm

/-- The port's own failure: `read_nat_at` only ever reports
`ErrTag::IndexOverflow`, which `absErrTag` sends to `none`. -/
private theorem kit_read_nat_at_err_aux {b : Slice Std.U8} (f : Nat) :
    ∀ (i e k : Std.Usize) (acc : Std.U64) (er : frontend.scan_types.ScanErr),
      b.val.length - k.val ≤ f →
      frontend.scan_fast.read_nat_at_loop b i e acc k = ok (.Err er) →
      er.what = .IndexOverflow := by
  induction f with
  | zero =>
    intro i e k acc er hf h
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    by_cases h1 : k < e
    · rw [if_pos h1, if_neg (show ¬ (k < Slice.len b) by scalar_tac)] at h; simp at h
    · rw [if_neg h1] at h; simp at h
  | succ f ih =>
    intro i e k acc er hf h
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    by_cases hk : k.val < b.val.length
    · by_cases h1 : k < e
      · rw [if_pos h1, if_pos (show k < Slice.len b by scalar_tac)] at h
        obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
        have ho' : Std.U64.checked_mul acc 10#u64 = o := lift_val ho
        cases hmul : Std.U64.checked_mul acc 10#u64 with
        | none =>
          rw [hmul] at ho'; rw [← ho'] at h
          have : er = ⟨i, frontend.scan_types.ErrTag.IndexOverflow⟩ := by simpa using h.symm
          rw [this]
        | some y =>
          rw [hmul] at ho'; rw [← ho'] at h
          obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨d, -, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e4, -, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
          have ho1' : Std.U64.checked_add y e4 = o1 := lift_val ho1
          cases hadd : Std.U64.checked_add y e4 with
          | none =>
            rw [hadd] at ho1'; rw [← ho1'] at h
            have : er = ⟨i, frontend.scan_types.ErrTag.IndexOverflow⟩ := by simpa using h.symm
            rw [this]
          | some x1 =>
            rw [hadd] at ho1'; rw [← ho1'] at h
            obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
            have hk1' := usize_add_one_inv hk1
            exact ih i e k1 x1 er (by omega) h
      · rw [if_neg h1] at h; simp at h
    · by_cases h1 : k < e
      · rw [if_pos h1, if_neg (show ¬ (k < Slice.len b) by scalar_tac)] at h; simp at h
      · rw [if_neg h1] at h; simp at h

/-- `read_nat_at`'s error is always the port's own. -/
private theorem kit_read_nat_at_err {b : Slice Std.U8} {i e : Std.Usize}
    {er : frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.read_nat_at b i e = ok (.Err er)) :
    absErrTag er.what = none := by
  rw [frontend.scan_fast.read_nat_at] at h
  rw [kit_read_nat_at_err_aux (b.val.length - i.val) i e i 0#u64 er (le_refl _) h]
  rfl


/-! ## The shared object-member step

**Hosted here** (coordinator's ruling of task #87): `ScanObj` is the lowest
common ancestor of `ScanExpr`, `ScanInd` and `ScanLine`, so the one copy of
con-leche's inlined member skeleton and of the induction that runs the port's
factored `scan_fast::next_member` against it lives here.  The text is agent
E's, from `Refine/Frontend/ScanExpr.lean`, with two changes:

* `KitFacts` keeps only the three *key* facts.  `num_end` and `read_nat_at`
  were fields of it; they are proved above instead, and `natSlot_step` uses
  the proofs.
* `KitFacts.read_nat_at` could not have been proved as it stood: con-leche's
  `readNatAt` falls back to `readNat`, which runs to the end of the **digit
  run** rather than to `e`, so the claim needs `e` to be that end.  Every
  caller has it (`num_end`/`skip_digits` produced `e`), and `kit_read_nat_at`
  takes it as a hypothesis. -/

/-- The port's `u32` bitset as con-leche's.  Both are a `BitVec 32` under one
constructor, so every operation on it is `rfl`. -/
def absU32 (n : Std.U32) : UInt32 := UInt32.ofBitVec n.bv

theorem absU32_and (a b : Std.U32) : absU32 (a &&& b) = absU32 a &&& absU32 b := rfl

theorem absU32_or (a b : Std.U32) : absU32 (a ||| b) = absU32 a ||| absU32 b := rfl

theorem absU32_inj {a b : Std.U32} (h : absU32 a = absU32 b) : a = b := by
  cases a; cases b
  simp only [absU32, UInt32.ofBitVec.injEq] at h
  exact congrArg _ h

theorem absU32_beq (a b : Std.U32) : (absU32 a == absU32 b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have h2 : absU32 a ≠ absU32 b := fun he => h (absU32_inj he)
    simp [h, h2]

theorem absByte_inj {a b : Std.U8} (h : absByte a = absByte b) : a = b := by
  have := congrArg UInt8.toNat h
  simp only [absByte_toNat] at this
  scalar_tac

/-- Two port bytes compare as con-leche's. -/
theorem absByte_beq_u8 (a b : Std.U8) : (absByte a == absByte b) = (a == b) := by
  simp only [absByte_beq, absByte_toNat]
  by_cases h : a = b
  · subst h; simp
  · have h2 : ¬ (a.val = b.val) := fun hc => h (by scalar_tac)
    simp [h, h2]

/-- A slice read at an in-range index, forwards. -/
private theorem index_ok {t : Slice Std.U8} {i : Std.Usize} (hi : i.val < t.length) :
    Slice.index_usize t i = ok t.val[i.val] := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec t i hi)
  rw [hy, hyv]

/-- The byte con-leche's `uget` reads at an abstracted position. -/
private theorem uget_val (b : Slice Std.U8) (i : Std.Usize)
    (h : (absPos i) < (absBytes b).usize) (hi : i.val < b.val.length) :
    (absBytes b).uget (absPos i) (usizeInBounds _ _ h) = absByte (b.val[i.val]'hi) := by
  rw [absBytes_uget b (absPos i) (usizeInBounds _ _ h) (by simpa using hi)]
  simp

/-- The port's `usize` subtraction, abstracted: a difference the port returned
`ok` for did not underflow, so con-leche's machine word did not wrap. -/
theorem absPos_sub {x y z : Std.Usize} (h : x - y = ok z) :
    absPos z = absPos x - absPos y := by
  have h2 := UScalar.sub_equiv x y
  rw [h] at h2
  simp at h2
  have hy : y.val ≤ x.val := by scalar_tac
  have hz : z.val = x.val - y.val := by scalar_tac
  have hx : x.val < USize.size := usize_val_lt_size x
  have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
  apply USize.toNat_inj.mp
  rw [USize.toNat_sub]
  simp only [absPos_toNat, hz]
  have hstep : 2 ^ System.Platform.numBits - y.val + x.val
      = (x.val - y.val) + 2 ^ System.Platform.numBits := by omega
  rw [hstep, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- **con-leche's inlined member skeleton**, with the record-specific closing
arm `CL` and key dispatch `DI` abstracted.  Every `scan*Loop` of
`Scan/Fast.lean` is `memberBody` at its own `CL` and `DI`; the port calls
`scan_fast::next_member` in its place. -/
def memberBody {α : Type} (b : ByteArray)
    (L : USize → Bool → ScanRes α) (CL : USize → Bool → ScanRes α)
    (DI : Key → USize → USize → ScanRes α) (i : USize) (w : Bool) : ScanRes α :=
  if h : i < b.usize then
    if isWs (b.uget i (usizeInBounds b i h)) then L (i + 1) w
    else if b.uget i (usizeInBounds b i h) == 125 then CL i w
    else if b.uget i (usizeInBounds b i h) == 44 then
      (if w then .err ⟨i.toNat, .expectedKey⟩ else L (i + 1) true)
    else if b.uget i (usizeInBounds b i h) == 34 then
      (if !w then .err ⟨i.toNat, .expectedComma⟩
       else
        if keyEnd b (i + 1) == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if valueAt b i (keyEnd b (i + 1)) == i then
          .err ⟨i.toNat, .expectedColon⟩
        else DI (keyAt b i (keyEnd b (i + 1) - (i + 1))) i
          (valueAt b i (keyEnd b (i + 1))))
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩

/-- What one `scan_fast::next_member` step says about con-leche's skeleton:
the closing brace hands the loop to `CL` at the same position and
`wantMember`, a key hands it to `DI` at the same key and value positions, and
a failure is mirrored. -/
def MemberStep {α : Type} (L CL : USize → Bool → ScanRes α)
    (DI : Key → USize → USize → ScanRes α) (i : Std.Usize) (w : Bool)
    (o : core.result.Result (frontend.scan_fast.Member × Std.Usize × Bool)
           frontend.scan_types.ScanErr) : Prop :=
  match o with
  | .Ok (.Close, ni, nw) => L (absPos i) w = CL (absPos ni) nw
  | .Ok (.Key k ks v, _, _) => L (absPos i) w = DI (absKey k) (absPos ks) (absPos v)
  | .Err e => ScanErrSim e (L (absPos i) w)

/-- **The `ScanKit` facts the skeleton stands on**: the three key lemmas
`ScanKit` owes.  Bundling them keeps every consumer one `KitFacts b` away from
being hypothesis-free. -/
structure KitFacts (b : Slice Std.U8) : Prop where
  /-- `scan_fast::key_end` against `Scan/Fast.lean:133-146 keyEnd`. -/
  key_end : ∀ (j ke : Std.Usize),
    frontend.scan_fast.key_end b j = ok ke → keyEnd (absBytes b) (absPos j) = absPos ke
  /-- `scan_fast::value_at` against `Scan/Fast.lean:448-453 valueAt`. -/
  value_at : ∀ (i ke v : Std.Usize),
    frontend.scan_fast.value_at b i ke = ok v →
      valueAt (absBytes b) (absPos i) (absPos ke) = absPos v
  /-- `scan_fast::key_at` against `Scan/Fast.lean:224-446 keyAt`. -/
  key_at : ∀ (i kl : Std.Usize) (k : frontend.scan_types.Key),
    frontend.scan_fast.key_at b i kl = ok k →
      keyAt (absBytes b) (absPos i) (absPos kl) = absKey k

section Step
variable {b : Slice Std.U8}

/-- **The one induction every slot loop of the tier runs.**
`scan_fast::next_member` (`scan_fast.rs:1374-1435`) against the
whitespace/comma/key skeleton every `scan*Loop` of `Scan/Fast.lean` writes out
inline.  The measure is phase 1's, `b.len() - i`. -/
theorem nextMember_step {α : Type} (kf : KitFacts b) {L CL : USize → Bool → ScanRes α}
    {DI : Key → USize → USize → ScanRes α}
    (hbody : ∀ p w, L p w = memberBody (absBytes b) L CL DI p w) (f : Nat) :
    ∀ (i : Std.Usize) (w : Bool) (o), b.length - i.val ≤ f →
      frontend.scan_fast.next_member b i w = ok o → MemberStep L CL DI i w o := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro i w o hf h
    rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
    rw [MemberStep.eq_def, hbody, memberBody]
    by_cases hend : i ≥ Slice.len b
    · rw [if_pos hend] at h
      rw [← Result.ok_injective h]
      have hnot : ¬ (absPos i < (absBytes b).usize) := by
        rw [absPos_lt_usize]; scalar_tac
      rw [dif_neg hnot]
      exact ScanErrSim.mk (t := .expectedComma) rfl (by simp)
    · rw [if_neg hend] at h
      have hi : i.val < b.val.length := by scalar_tac
      have hi' : i.val < b.length := by scalar_tac
      have hlt : absPos i < (absBytes b).usize := absPos_lt_usize.mpr hi
      rw [dif_pos hlt, uget_val b i hlt hi]
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hcv : c = b.val[i.val]'hi :=
        Result.ok_injective (hc.symm.trans (index_ok hi))
      rw [← hcv]
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hws := is_ws_refines hb1
      subst hws
      by_cases hw : isWs (absByte c) = true
      · rw [if_pos hw] at h ⊢
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hstep : i2.val = i.val + 1 := usize_add_one_inv hi2
        rw [← absPos_add_one hi2]
        have hres := ih (b.length - i2.val) (by omega) i2 w o (le_refl _) h
        rwa [MemberStep.eq_def] at hres
      · rw [if_neg hw] at h ⊢
        rw [show ((125 : UInt8)) = absByte 125#u8 from rfl, absByte_beq_u8,
          show ((44 : UInt8)) = absByte 44#u8 from rfl, absByte_beq_u8,
          show ((34 : UInt8)) = absByte 34#u8 from rfl, absByte_beq_u8]
        by_cases h1 : c = 125#u8
        · rw [if_pos h1] at h
          rw [if_pos (beq_iff_eq.mpr h1), ← Result.ok_injective h]
        · rw [if_neg h1] at h
          rw [if_neg (by simp [h1])]
          by_cases h2 : c = 44#u8
          · rw [if_pos h2] at h
            rw [if_pos (beq_iff_eq.mpr h2)]
            by_cases h3 : w = true
            · rw [if_pos h3] at h
              rw [if_pos h3, ← Result.ok_injective h]
              exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
            · rw [if_neg h3] at h
              rw [if_neg h3]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hstep : i2.val = i.val + 1 := usize_add_one_inv hi2
              rw [← absPos_add_one hi2]
              have hres := ih (b.length - i2.val) (by omega) i2 true o (le_refl _) h
              rwa [MemberStep.eq_def] at hres
          · rw [if_neg h2] at h
            rw [if_neg (by simp [h2])]
            by_cases h4 : c = 34#u8
            · rw [if_pos h4] at h
              rw [if_pos (beq_iff_eq.mpr h4)]
              by_cases h5 : w = true
              · rw [if_pos h5] at h
                rw [if_neg (by simp [h5])]
                obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨ke, hke, h⟩ := bind_eq_ok_iff.mp h
                have hp2 : absPos i2 = absPos i + 1 := absPos_add_one hi2
                have hkeE : keyEnd (absBytes b) (absPos i + 1) = absPos ke := by
                  rw [← hp2]; exact kf.key_end i2 ke hke
                rw [hkeE]
                by_cases h6 : ke = 0#usize
                · rw [if_pos h6] at h
                  rw [if_pos (show (absPos ke == (0 : USize)) = true by simp; scalar_tac),
                    ← Result.ok_injective h]
                  exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
                · rw [if_neg h6] at h
                  rw [if_neg (show ¬ ((absPos ke == (0 : USize)) = true) by
                    simp; intro hx; exact h6 (usize_ext (by simpa using hx)))]
                  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                  rw [kf.value_at i ke v hv]
                  by_cases h7 : v = i
                  · rw [if_pos h7] at h
                    rw [if_pos (show (absPos v == absPos i) = true by simp; scalar_tac),
                      ← Result.ok_injective h]
                    exact ScanErrSim.mk (t := .expectedColon) rfl (by simp)
                  · rw [if_neg h7] at h
                    rw [if_neg (show ¬ ((absPos v == absPos i) = true) by
                      simp; intro hx; exact h7 (usize_ext hx))]
                    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
                    have h3E : absPos ke - (absPos i + 1) = absPos i3 := by
                      rw [← hp2, ← absPos_sub hi3]
                    rw [h3E, kf.key_at i i3 k hk, ← Result.ok_injective h]
              · rw [if_neg h5] at h
                rw [if_pos (by simp [h5]), ← Result.ok_injective h]
                exact ScanErrSim.mk (t := .expectedComma) rfl (by simp)
            · rw [if_neg h4] at h
              rw [if_neg (by simp [h4]), ← Result.ok_injective h]
              exact ScanErrSim.mk (t := .expectedComma) rfl (by simp)

/-! ### Reading a member step back -/

theorem MemberStep.close {α : Type} {L CL : USize → Bool → ScanRes α}
    {DI : Key → USize → USize → ScanRes α} {i ni : Std.Usize} {w nw : Bool}
    (h : MemberStep L CL DI i w (.Ok (.Close, ni, nw))) :
    L (absPos i) w = CL (absPos ni) nw := h

theorem MemberStep.key {α : Type} {L CL : USize → Bool → ScanRes α}
    {DI : Key → USize → USize → ScanRes α} {i ks v ni : Std.Usize} {w nw : Bool}
    {k : frontend.scan_types.Key}
    (h : MemberStep L CL DI i w (.Ok (.Key k ks v, ni, nw))) :
    L (absPos i) w = DI (absKey k) (absPos ks) (absPos v) := h

theorem MemberStep.err {α : Type} {L CL : USize → Bool → ScanRes α}
    {DI : Key → USize → USize → ScanRes α} {i : Std.Usize} {w : Bool}
    {e : frontend.scan_types.ScanErr} (h : MemberStep L CL DI i w (.Err e)) :
    ScanErrSim e (L (absPos i) w) := h

/-! ## A `Nat`-valued slot

`scan_fast::slot_nat` is the `numEnd`/`readNatAt`/`noProgress` chain every
`Nat`-valued slot of every `scan*Loop` writes out (module note, deviation 3).
`natSlot` is that chain with the slot's continuation abstracted. -/

/-- con-leche's `Nat`-valued slot, with the continuation abstracted. -/
def natSlot {α : Type} (b : ByteArray) (ks v : USize)
    (K : Nat → USize → ScanRes α) : ScanRes α :=
  if numEnd b v == v then .err ⟨v.toNat, .expectedNat⟩
  else if _hj : ks < numEnd b v then K (readNatAt b v (numEnd b v)) (numEnd b v)
  else .err ⟨ks.toNat, .noProgress⟩

/-- What one `scan_fast::slot_nat` says about that chain. -/
def NatSlotStep {α : Type} (b : Slice Std.U8) (ks v : Std.Usize)
    (K : Nat → USize → ScanRes α)
    (o : core.result.Result (Std.U64 × Std.Usize) frontend.scan_types.ScanErr) : Prop :=
  match o with
  | .Ok (x, e) => natSlot (absBytes b) (absPos ks) (absPos v) K = K (absU64 x) (absPos e)
  | .Err er => ScanErrSim er (natSlot (absBytes b) (absPos ks) (absPos v) K)

theorem NatSlotStep.ok {α : Type} {b : Slice Std.U8} {ks v e : Std.Usize}
    {K : Nat → USize → ScanRes α} {x : Std.U64}
    (h : NatSlotStep b ks v K (.Ok (x, e))) :
    natSlot (absBytes b) (absPos ks) (absPos v) K = K (absU64 x) (absPos e) := h

theorem NatSlotStep.err {α : Type} {b : Slice Std.U8} {ks v : Std.Usize}
    {K : Nat → USize → ScanRes α} {er : frontend.scan_types.ScanErr}
    (h : NatSlotStep b ks v K (.Err er)) :
    ScanErrSim er (natSlot (absBytes b) (absPos ks) (absPos v) K) := h

/-- **`scan_fast::slot_nat` against the chain con-leche writes out.**  Needs no
`KitFacts`: `num_end` and `read_nat_at` are proved above. -/
theorem natSlot_step {α : Type} {ks v : Std.Usize}
    {K : Nat → USize → ScanRes α} {o}
    (h : frontend.scan_fast.slot_nat b ks v = ok o) : NatSlotStep b ks v K o := by
  rw [frontend.scan_fast.slot_nat] at h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  have heA : absPos e = numEnd (absBytes b) (absPos v) := num_end_refines he
  rw [NatSlotStep.eq_def, natSlot, ← heA]
  by_cases h1 : e = v
  · rw [if_pos h1] at h
    rw [if_pos (show (absPos e == absPos v) = true by simp; scalar_tac), err_val h]
    exact ScanErrSim.mk (t := .expectedNat) rfl (by simp)
  · rw [if_neg h1] at h
    rw [if_neg (show ¬ ((absPos e == absPos v) = true) by
      simp; intro hx; exact h1 (usize_ext hx))]
    obtain ⟨hrun, -⟩ := kit_num_end_run he h1
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1' : b1 = decide (ks.val < e.val) := by
      rw [frontend.scan_fast.prog] at hb1
      have := Result.ok_injective hb1
      rw [← this]; exact decide_eq_decide.mpr (by constructor <;> (intro hx; scalar_tac))
    by_cases h2 : b1 = true
    · rw [if_pos h2] at h
      rw [dif_pos (absPos_lt.mpr (by rw [hb1'] at h2; simpa using h2))]
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Ok x =>
        rw [← Result.ok_injective h, ← kit_read_nat_at hrun hr]
      | Err er =>
        rw [← Result.ok_injective h]
        exact ScanErrSim.of_none (kit_read_nat_at_err hr)
    · rw [if_neg h2] at h
      rw [dif_neg (by rw [absPos_lt]; rw [hb1'] at h2; simpa using h2), err_val h]
      exact ScanErrSim.mk (t := .noProgress) rfl (by simp)

end Step

/-! ## Literals

Every string literal of the module is a `[u8; N]` constant (task #86, DESIGN.md
§3.8), read as a slice at the call site. -/

/-- A `const [u8; N]` literal read as a slice: the slice is the array. -/
private theorem slice_lit_val {k : Std.Usize} {S : Std.Array Std.U8 k} {s : Slice Std.U8}
    (h : lift (Std.Array.to_slice S) = ok s) : s.val = S.val := by
  simp only [lift_eq, Result.ok.injEq] at h
  subst h
  simp [Std.Array.val_to_slice]

/-- A port position advanced by a literal's width. -/
theorem absPos_add {i c j : Std.Usize} (h : i + c = ok j) :
    absPos j = absPos i + absPos c := by
  have hj : j.val = i.val + c.val := ConRon.Refine.Nat.uadd_val h
  have hb : i.val + c.val < USize.size := by have := usize_val_lt_size j; omega
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, absPos_toNat, hj]
  exact (Nat.mod_eq_of_lt hb).symm

/-! ## `scan_bool`

`scan_fast.rs:723-733` against `Scan/Fast.lean:466-469 scanBool`. -/

/-- **`scan_bool` refines `scanBool`** (`Scan/Fast.lean:466-469`). -/
theorem scan_bool_refines {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (Bool × Std.Usize) frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_bool b i = ok o) :
    ScanSim id o (scanBool (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_bool] at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  have hsv : s.val = [116#u8, 114#u8, 117#u8, 101#u8] := by
    rw [slice_lit_val hs]; simp [global_simps]
  have hsb : absBytes s = "true".toUTF8 := by rw [absBytes, hsv]; decide
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  have hb1' : b1 = matchLit (absBytes b) (absPos i) "true".toUTF8 0 := by
    rw [← hsb]; exact match_lit_refines (by rw [hsv]; decide) hb1
  rw [scanBool, ← hb1']
  by_cases hbt : b1 = true
  · rw [if_pos hbt] at h ⊢
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    refine ScanSim.ok ?_
    rw [absPos_add hi1, show absPos 4#usize = (4 : USize) from by
      apply USize.toNat_inj.mp; simp]
    rfl
  · rw [if_neg hbt] at h ⊢
    obtain ⟨s1, hs1, h⟩ := bind_eq_ok_iff.mp h
    have hs1v : s1.val = [102#u8, 97#u8, 108#u8, 115#u8, 101#u8] := by
      rw [slice_lit_val hs1]; simp [global_simps]
    have hs1b : absBytes s1 = "false".toUTF8 := by rw [absBytes, hs1v]; decide
    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
    have hb2' : b2 = matchLit (absBytes b) (absPos i) "false".toUTF8 0 := by
      rw [← hs1b]; exact match_lit_refines (by rw [hs1v]; decide) hb2
    rw [← hb2']
    by_cases hbf : b2 = true
    · rw [if_pos hbf] at h ⊢
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h]
      refine ScanSim.ok ?_
      rw [absPos_add hi1, show absPos 5#usize = (5 : USize) from by
        apply USize.toNat_inj.mp; simp]
      rfl
    · rw [if_neg hbf] at h ⊢
      rw [err_val h]
      exact ScanErrSim.mk (t := .expectedBool) rfl (by simp)

/-! ## The index list

`scan_fast.rs:1169-1221` against `Scan/Fast.lean:674-702` (`scanNatListLoop`,
`scanNatList`).  **This is the tier's list-loop template.**  The port pushes
onto a `Vec` where con-leche conses onto a `List` and reverses at the close, so
the invariant is `(absU64s acc).reverse` — the port's accumulator, abstracted
and reversed, is con-leche's — and the close is `List.reverse_reverse`. -/

/-- `scanNatListLoop` at a port position, unfolded once. -/
private theorem scanNatListLoop_eq (b : Slice Std.U8) (i : Std.Usize)
    (acc : List Nat) (w : Bool) :
    scanNatListLoop (absBytes b) (absPos i) acc w =
      if i.val < b.val.length then
        (if isWs (absByte (pByteAt b i.val)) then
            scanNatListLoop (absBytes b) (absPos i + 1) acc w
         else if absByte (pByteAt b i.val) == 93 then
            (if w && !acc.isEmpty then .err ⟨i.val, .expectedList⟩
             else .ok acc.reverse (absPos i + 1))
         else if absByte (pByteAt b i.val) == 44 then
            (if w then .err ⟨i.val, .expectedList⟩
             else scanNatListLoop (absBytes b) (absPos i + 1) acc true)
         else if isDigit (absByte (pByteAt b i.val)) then
            (if !w then .err ⟨i.val, .expectedList⟩
             else if numEnd (absBytes b) (absPos i) == absPos i then
               .err ⟨i.val, .expectedNat⟩
             else if _hj : absPos i < numEnd (absBytes b) (absPos i) then
               scanNatListLoop (absBytes b) (numEnd (absBytes b) (absPos i))
                 (readNatAt (absBytes b) (absPos i) (numEnd (absBytes b) (absPos i)) :: acc)
                 false
             else .err ⟨i.val, .noProgress⟩)
         else .err ⟨i.val, .expectedList⟩)
      else .err ⟨i.val, .expectedList⟩ := by
  rw [scanNatListLoop]
  by_cases h : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_pos]
    simp only [absPos_toNat]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]
    simp only [absPos_toNat]

/-- The loop of `scan_fast::scan_nat_list_loop` (con-leche:
`Scan/Fast.lean:674-698 scanNatListLoop`). -/
private theorem scan_nat_list_loop_aux {b : Slice Std.U8} (f : Nat) :
    ∀ (i : Std.Usize) (acc : alloc.vec.Vec Std.U64) (w : Bool)
      (o : core.result.Result (alloc.vec.Vec Std.U64 × Std.Usize)
             frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_nat_list_loop_loop b i acc w = ok o →
      ScanSim absU64s o
        (scanNatListLoop (absBytes b) (absPos i) (absU64s acc).reverse w) := by
  induction f with
  | zero =>
    intro i acc w o hf h
    have hi : ¬ i.val < b.val.length := by omega
    rw [frontend.scan_fast.scan_nat_list_loop_loop.eq_def,
      if_pos (show i ≥ Slice.len b by scalar_tac)] at h
    rw [err_val h, scanNatListLoop_eq, if_neg hi]
    exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
  | succ f ih =>
    intro i acc w o hf h
    rw [frontend.scan_fast.scan_nat_list_loop_loop.eq_def] at h
    by_cases hi : i.val < b.val.length
    · rw [if_neg (show ¬ (i ≥ Slice.len b) by scalar_tac)] at h
      rw [scanNatListLoop_eq, if_pos hi]
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hcp : c = pByteAt b i.val := by
        rw [pByteAt, dif_pos hi]
        obtain ⟨y1, hy1, hy2⟩ := WP.spec_imp_exists (Slice.index_usize_spec b i hi)
        rw [hy1] at hc
        rw [← Result.ok_injective hc, hy2]
      rw [← hcp]
      obtain ⟨w1, hw1, h⟩ := bind_eq_ok_iff.mp h
      have hw1' : w1 = isWs (absByte c) := is_ws_refines hw1
      by_cases hws : w1 = true
      · rw [if_pos hws] at h
        rw [if_pos (by rw [← hw1']; exact hws)]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v := usize_add_one_inv hi2
        rw [← absPos_add_one hi2]
        exact ih i2 acc w o (by omega) h
      · rw [if_neg hws] at h
        rw [if_neg (by rw [← hw1']; exact hws),
          show ((93 : UInt8)) = absByte 93#u8 from rfl, absByte_beq_u8]
        by_cases h93 : c = 93#u8
        · -- the closing bracket
          rw [if_pos h93] at h
          rw [if_pos (beq_iff_eq.mpr h93)]
          have hE : ((absU64s acc).reverse).isEmpty = decide (acc.val.length = 0) := by
            cases hv : acc.val with
            | nil => simp [absU64s, hv]
            | cons x xs => simp [absU64s, hv]
          have hlen : (alloc.vec.Vec.len acc).val = acc.val.length := by scalar_tac
          have hz0 : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
          by_cases hw : w = true
          · rw [if_pos hw] at h
            simp only at h
            by_cases hne : (alloc.vec.Vec.len acc != 0#usize) = true
            · rw [if_pos hne] at h
              have hnz : acc.val.length ≠ 0 := by
                intro hx
                have h0 : alloc.vec.Vec.len acc ≠ 0#usize := by simpa using hne
                exact h0 (usize_ext (by omega))
              rw [if_pos (show (w && !((absU64s acc).reverse).isEmpty) = true by
                rw [hE, hw]; simp [hnz]), err_val h]
              exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
            · rw [if_neg hne] at h
              have hzl : acc.val.length = 0 := by
                have h0 : acc.val = [] := by simpa using hne
                rw [h0, List.length_nil]
              rw [if_neg (show ¬ ((w && !((absU64s acc).reverse).isEmpty) = true) by
                rw [hE, hzl]; simp)]
              obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
              rw [← Result.ok_injective h]
              refine ScanSim.ok ?_
              rw [List.reverse_reverse, ← absPos_add_one hi3]
          · rw [if_neg hw] at h
            have hwf : w = false := by simpa using hw
            rw [if_neg (show ¬ ((w && !((absU64s acc).reverse).isEmpty) = true) by
              rw [hwf]; simp)]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            rw [← Result.ok_injective h]
            refine ScanSim.ok ?_
            rw [List.reverse_reverse, ← absPos_add_one hi2]
        · rw [if_neg h93] at h
          rw [if_neg (by simp [h93]),
            show ((44 : UInt8)) = absByte 44#u8 from rfl, absByte_beq_u8]
          by_cases h44 : c = 44#u8
          · -- the comma
            rw [if_pos h44] at h
            rw [if_pos (beq_iff_eq.mpr h44)]
            by_cases hw : w = true
            · rw [if_pos hw] at h
              rw [if_pos hw, err_val h]
              exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
            · rw [if_neg hw] at h
              rw [if_neg hw]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hi2v := usize_add_one_inv hi2
              rw [← absPos_add_one hi2]
              exact ih i2 acc true o (by omega) h
          · rw [if_neg h44] at h
            rw [if_neg (by simp [h44])]
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            have hb2' : b2 = isDigit (absByte c) := is_digit_refines hb2
            by_cases hdg : b2 = true
            · -- a list member
              rw [if_pos hdg] at h
              rw [if_pos (by rw [← hb2']; exact hdg)]
              by_cases hw : w = true
              · rw [if_pos hw] at h
                rw [if_neg (by simp [hw])]
                obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
                have heA : absPos e = numEnd (absBytes b) (absPos i) := num_end_refines he
                rw [← heA]
                by_cases hei : e = i
                · rw [if_pos hei] at h
                  rw [if_pos (show (absPos e == absPos i) = true by simp; scalar_tac),
                    err_val h]
                  exact ScanErrSim.mk (t := .expectedNat) rfl (by simp)
                · rw [if_neg hei] at h
                  rw [if_neg (show ¬ ((absPos e == absPos i) = true) by
                    simp; intro hx; exact hei (usize_ext hx))]
                  obtain ⟨hrun, hlt⟩ := kit_num_end_run he hei
                  rw [dif_pos (absPos_lt.mpr hlt)]
                  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
                  cases r with
                  | Ok p =>
                    obtain ⟨acc1, hpush, h⟩ := bind_eq_ok_iff.mp h
                    have hpv := ConRon.Refine.vec_push_val hpush
                    rw [show readNatAt (absBytes b) (absPos i) (absPos e) = absU64 p from
                      (kit_read_nat_at hrun hr).symm]
                    have hacc : (absU64s acc1).reverse
                        = absU64 p :: (absU64s acc).reverse := by
                      simp [absU64s, hpv]
                    rw [← hacc]
                    exact ih e acc1 false o (by omega) h
                  | Err er =>
                    rw [← Result.ok_injective h]
                    exact ScanErrSim.of_none (kit_read_nat_at_err hr)
              · rw [if_neg hw] at h
                rw [if_pos (by simp [hw]), err_val h]
                exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
            · rw [if_neg hdg] at h
              rw [if_neg (by rw [← hb2']; exact hdg), err_val h]
              exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
    · rw [if_pos (show i ≥ Slice.len b by scalar_tac)] at h
      rw [err_val h, scanNatListLoop_eq, if_neg hi]
      exact ScanErrSim.mk (t := .expectedList) rfl (by simp)

/-- **`scan_nat_list_loop` refines `scanNatListLoop`** at the empty
accumulator (`Scan/Fast.lean:674-698`).  `scanPw` and every list-valued slot
of the tier enter here, past the `[`. -/
theorem scan_nat_list_loop_refines {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (alloc.vec.Vec Std.U64 × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_nat_list_loop b i = ok o) :
    ScanSim absU64s o (scanNatListLoop (absBytes b) (absPos i) [] true) := by
  have hr := scan_nat_list_loop_aux (b.val.length - i.val) i
    (alloc.vec.Vec.new Std.U64) true o (le_refl _) h
  simpa [absU64s, alloc.vec.Vec.new] using hr

/-- **`scan_nat_list` refines `scanNatList`** (`Scan/Fast.lean:700-702`). -/
theorem scan_nat_list_refines {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (alloc.vec.Vec Std.U64 × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_nat_list b i = ok o) :
    ScanSim absU64s o (scanNatList (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_nat_list] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  have hcA : absByte c = byteAt (absBytes b) (absPos i) := byte_at_refines hc
  rw [scanNatList, ← hcA, show ((91 : UInt8)) = absByte 91#u8 from rfl, absByte_beq_u8]
  by_cases h91 : c = 91#u8
  · rw [if_pos h91] at h
    rw [if_pos (beq_iff_eq.mpr h91)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    exact scan_nat_list_loop_refines h
  · rw [if_neg h91] at h
    rw [if_neg (by simp [h91]), err_val h]
    exact ScanErrSim.mk (t := .expectedList) rfl (by simp)

/-! ## `pw`

`scan_fast.rs:1226-1249` against `Scan/Fast.lean:707-715 scanPw`. -/

/-- **`scan_pw` refines `scanPw`** (`Scan/Fast.lean:707-715`). -/
theorem scan_pw_refines {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.PwRec × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_pw b i = ok o) :
    ScanSim absPwRec o (scanPw (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_pw] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  have hcA : absByte c = byteAt (absBytes b) (absPos i) := byte_at_refines hc
  rw [scanPw, ← hcA, show ((91 : UInt8)) = absByte 91#u8 from rfl,
    show ((34 : UInt8)) = absByte 34#u8 from rfl, absByte_beq_u8, absByte_beq_u8]
  by_cases h91 : c = 91#u8
  · rw [if_pos h91] at h
    rw [if_pos (beq_iff_eq.mpr h91)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    have hrs := scan_nat_list_loop_refines hr
    rw [← absPos_add_one hi2]
    cases r with
    | Ok p =>
      obtain ⟨ns, j⟩ := p
      rw [← Result.ok_injective h]
      rw [ScanSim] at hrs
      rw [hrs]
      rfl
    | Err er =>
      rw [← Result.ok_injective h]
      intro le hle
      rw [hrs le hle]
  · rw [if_neg h91] at h
    rw [if_neg (by simp [h91])]
    by_cases h34 : c = 34#u8
    · rw [if_pos h34] at h
      rw [if_pos (beq_iff_eq.mpr h34)]
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
      have hsv : s.val = [110#u8, 101#u8, 118#u8, 101#u8, 114#u8, 34#u8] := by
        rw [slice_lit_val hs]; simp [global_simps]
      have hsb : absBytes s = "never\"".toUTF8 := by rw [absBytes, hsv]; decide
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1' : b1 = matchLit (absBytes b) (absPos i2) "never\"".toUTF8 0 := by
        rw [← hsb]; exact match_lit_refines (by rw [hsv]; decide) hb1
      rw [← absPos_add_one hi2, ← hb1']
      by_cases hbt : b1 = true
      · rw [if_pos hbt] at h ⊢
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        rw [← Result.ok_injective h]
        refine ScanSim.ok ?_
        rw [absPos_add hi3, show absPos 7#usize = (7 : USize) from by
          apply USize.toNat_inj.mp; simp]
        rfl
      · rw [if_neg hbt] at h ⊢
        rw [err_val h]
        exact ScanErrSim.mk (t := .badPw) rfl (by simp)
    · rw [if_neg h34] at h
      rw [if_neg (by simp [h34]), err_val h]
      exact ScanErrSim.mk (t := .badPw) rfl (by simp)

end ConRon.Refine.Frontend
