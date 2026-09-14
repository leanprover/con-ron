/-
**The bounds kit, exact against con-leche** (task #87, phase 3).

`crates/con-ron-core/src/frontend/scan_fast.rs`'s byte primitives against
`ConLeche/Frontend/Scan/Fast.lean:55-540` -- the "bounds kit", the key
classifier and the scalar readers.
-/
import ConRon.Refine.Frontend.Abs

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConLeche.Frontend

/-! ## `byte_at` -/

/-- The port's `byte_at` as a total function of a `Nat` index. -/
def pByteAt (b : Slice Std.U8) (n : Nat) : Std.U8 :=
  if h : n < b.val.length then b.val[n] else 0#u8

/-- A slice read at an in-range index, in the forward `= ok` form. -/
private theorem slice_index_ok {t : Slice Std.U8} {i : Std.Usize}
    (hi : i.val < t.val.length) : Slice.index_usize t i = ok t.val[i.val] := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec t i hi)
  rw [hy, hyv]

/-- `byte_at` is total: it is `pByteAt`. -/
theorem byte_at_eq (b : Slice Std.U8) (i : Std.Usize) :
    frontend.scan_fast.byte_at b i = ok (pByteAt b i.val) := by
  rw [frontend.scan_fast.byte_at, pByteAt]
  split
  · rename_i h
    have hi : i.val < b.val.length := by scalar_tac
    rw [dif_pos hi, slice_index_ok hi]
  · rename_i h
    have hi : ¬ i.val < b.val.length := by scalar_tac
    rw [dif_neg hi]

/-- **`pByteAt` is con-leche's `byteAt`** at any index a machine word names. -/
theorem byteAt_abs (b : Slice Std.U8) (n : Nat) (hn : n < USize.size) :
    byteAt (absBytes b) (USize.ofNat n) = absByte (pByteAt b n) := by
  have hn' : (USize.ofNat n).toNat = n := by
    simp [Nat.mod_eq_of_lt hn]
  rw [byteAt, pByteAt]
  split
  · rename_i h
    have h1 : n < b.val.length := by
      have := USize.lt_iff_toNat_lt.mp h
      rw [hn', absBytes_usize] at this; exact this
    rw [dif_pos h1, absBytes_uget b _ _ (by omega)]
    simp [hn']
  · rename_i h
    have h1 : ¬ n < b.val.length := by
      intro hc
      exact h (by rw [USize.lt_iff_toNat_lt, hn', absBytes_usize]; exact hc)
    rw [dif_neg h1]
    simp [absByte]

/-- **`byte_at` refines `byteAt`** (`Scan/Fast.lean:72-76`). -/
theorem byte_at_refines {b : Slice Std.U8} {i : Std.Usize} {c : Std.U8}
    (h : frontend.scan_fast.byte_at b i = ok c) :
    absByte c = byteAt (absBytes b) (absPos i) := by
  rw [byte_at_eq] at h
  have h : pByteAt b i.val = c := by simpa using h
  subst h
  rw [absPos, byteAt_abs b i.val (usize_val_lt_size i)]

/-- A byte read inside the array, through `absPos`. -/
private theorem uget_absPos {b : Slice Std.U8} {i : Std.Usize}
    (h : (absPos i).toNat < (absBytes b).size) :
    (absBytes b).uget (absPos i) h = absByte (pByteAt b i.val) := by
  have hi : i.val < b.val.length := by
    rw [absBytes_size] at h; rw [absPos_toNat] at h; exact h
  rw [absBytes_uget b (absPos i) h (by rw [absPos_toNat]; exact hi), pByteAt,
    dif_pos hi]
  simp

/-! ## `is_ws`, `is_digit`

`scan_fast.rs:96-98` / `101-103` against `Scan/Fast.lean:78-80` (`isWs`) and
`Scan/Fast.lean:82` (`isDigit`).  The three comparison bridges below are what
turns a `Std.U8` test into a `UInt8` one. -/

@[simp] theorem absByte_eq_iff {c : Std.U8} {d : UInt8} :
    absByte c = d ↔ c.val = d.toNat := by
  constructor
  · intro h; rw [← h, absByte_toNat]
  · intro h
    have : (absByte c).toNat = d.toNat := by rw [absByte_toNat, h]
    exact UInt8.toNat_inj.mp this

@[simp] theorem absByte_le_iff {c : Std.U8} {d : UInt8} :
    absByte c ≤ d ↔ c.val ≤ d.toNat := by
  rw [UInt8.le_iff_toNat_le, absByte_toNat]

@[simp] theorem le_absByte_iff {c : Std.U8} {d : UInt8} :
    d ≤ absByte c ↔ d.toNat ≤ c.val := by
  rw [UInt8.le_iff_toNat_le, absByte_toNat]

@[simp] theorem absByte_lt_iff {c : Std.U8} {d : UInt8} :
    absByte c < d ↔ c.val < d.toNat := by
  rw [UInt8.lt_iff_toNat_lt, absByte_toNat]

@[simp] theorem absByte_beq {c : Std.U8} {d : UInt8} :
    (absByte c == d) = decide (c.val = d.toNat) := by
  by_cases h : c.val = d.toNat
  · rw [absByte_eq_iff.mpr h]; simp [h]
  · have hne : absByte c ≠ d := fun hc => h (absByte_eq_iff.mp hc)
    simp [hne, h]

/-- **`is_ws` refines `isWs`** (`Scan/Fast.lean:78-80`). -/
theorem is_ws_refines {c : Std.U8} {r : Bool}
    (h : frontend.scan_fast.is_ws c = ok r) : r = isWs (absByte c) := by
  rw [frontend.scan_fast.is_ws] at h
  simp only [isWs]
  split at h
  · simp_all
  · split at h
    · simp_all
    · have h' : decide (c = 13#u8) = r := by simpa using h
      have t32 : (32 : UInt8).toNat = 32 := rfl
      have t9 : (9 : UInt8).toNat = 9 := rfl
      have t13 : (13 : UInt8).toNat = 13 := rfl
      have k32 : ¬ c.val = 32 := by scalar_tac
      have k9 : ¬ c.val = 9 := by scalar_tac
      rw [← h']
      simp only [absByte_beq, t32, t9, t13, k32, k9, decide_false, Bool.false_or]
      exact decide_eq_decide.mpr (by constructor <;> (intro hx; scalar_tac))

/-- **`is_digit` refines `isDigit`** (`Scan/Fast.lean:82`). -/
theorem is_digit_refines {c : Std.U8} {r : Bool}
    (h : frontend.scan_fast.is_digit c = ok r) : r = isDigit (absByte c) := by
  rw [frontend.scan_fast.is_digit] at h
  simp only [isDigit]
  split at h <;> simp_all

/-! ## `skip_ws`, `skip_digits`

`scan_fast.rs:107-124` against `Scan/Fast.lean:84-101`.  The port's `*_loop`
mirrors the Lean recursion one for one, so both are the same induction on the
`Nat` measure `b.len() - i` (`Refine/PinsBytes.lean` is the model). -/

/-- `skipWs` at a port position, unfolded once. -/
private theorem skipWs_eq (b : Slice Std.U8) (i : Std.Usize) :
    skipWs (absBytes b) (absPos i) =
      if i.val < b.val.length then
        (if isWs (absByte (pByteAt b i.val)) then skipWs (absBytes b) (absPos i + 1)
         else absPos i)
      else absPos i := by
  rw [skipWs]
  by_cases h : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_absPos]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]

/-- `skipDigits` at a port position, unfolded once. -/
private theorem skipDigits_eq (b : Slice Std.U8) (i : Std.Usize) :
    skipDigits (absBytes b) (absPos i) =
      if i.val < b.val.length then
        (if isDigit (absByte (pByteAt b i.val)) then skipDigits (absBytes b) (absPos i + 1)
         else absPos i)
      else absPos i := by
  rw [skipDigits]
  by_cases h : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_absPos]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]

private theorem skip_ws_loop_refines {b : Slice Std.U8} (f : Nat) :
    ∀ (i j : Std.Usize), b.val.length - i.val ≤ f →
      frontend.scan_fast.skip_ws_loop b i = ok j →
      absPos j = skipWs (absBytes b) (absPos i) := by
  induction f with
  | zero =>
    intro i j hf h
    rw [frontend.scan_fast.skip_ws_loop.eq_def] at h
    rw [if_neg (show ¬ (i < Slice.len b) by scalar_tac)] at h
    rw [skipWs_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
    have : i = j := by simpa using h
    rw [this]
  | succ f ih =>
    intro i j hf h
    rw [frontend.scan_fast.skip_ws_loop.eq_def] at h
    by_cases hlt : i < Slice.len b
    · rw [if_pos hlt] at h
      have hi : i.val < b.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
      have hc' : c = pByteAt b i.val := by
        rw [slice_index_ok hi] at hc; rw [pByteAt, dif_pos hi]; simpa using hc.symm
      have hw' : w = isWs (absByte (pByteAt b i.val)) := by
        rw [← hc']; exact is_ws_refines hw
      rw [skipWs_eq, if_pos hi, ← hw']
      by_cases hwt : w = true
      · rw [if_pos hwt] at h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hv := usize_add_one_inv hi3
        rw [if_pos hwt, ← absPos_add_one hi3]
        exact ih i3 j (by omega) h
      · rw [if_neg hwt] at h
        rw [if_neg hwt]
        have : i = j := by simpa using h
        rw [this]
    · rw [if_neg hlt] at h
      rw [skipWs_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
      have : i = j := by simpa using h
      rw [this]

/-- **`skip_ws` refines `skipWs`** (`Scan/Fast.lean:84-91`). -/
theorem skip_ws_refines {b : Slice Std.U8} {i j : Std.Usize}
    (h : frontend.scan_fast.skip_ws b i = ok j) :
    absPos j = skipWs (absBytes b) (absPos i) :=
  skip_ws_loop_refines (b.val.length - i.val) i j (le_refl _) h

private theorem skip_digits_loop_refines {b : Slice Std.U8} (f : Nat) :
    ∀ (i j : Std.Usize), b.val.length - i.val ≤ f →
      frontend.scan_fast.skip_digits_loop b i = ok j →
      absPos j = skipDigits (absBytes b) (absPos i) := by
  induction f with
  | zero =>
    intro i j hf h
    rw [frontend.scan_fast.skip_digits_loop.eq_def] at h
    rw [if_neg (show ¬ (i < Slice.len b) by scalar_tac)] at h
    rw [skipDigits_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
    have : i = j := by simpa using h
    rw [this]
  | succ f ih =>
    intro i j hf h
    rw [frontend.scan_fast.skip_digits_loop.eq_def] at h
    by_cases hlt : i < Slice.len b
    · rw [if_pos hlt] at h
      have hi : i.val < b.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
      have hc' : c = pByteAt b i.val := by
        rw [slice_index_ok hi] at hc; rw [pByteAt, dif_pos hi]; simpa using hc.symm
      have hw' : w = isDigit (absByte (pByteAt b i.val)) := by
        rw [← hc']; exact is_digit_refines hw
      rw [skipDigits_eq, if_pos hi, ← hw']
      by_cases hwt : w = true
      · rw [if_pos hwt] at h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hv := usize_add_one_inv hi3
        rw [if_pos hwt, ← absPos_add_one hi3]
        exact ih i3 j (by omega) h
      · rw [if_neg hwt] at h
        rw [if_neg hwt]
        have : i = j := by simpa using h
        rw [this]
    · rw [if_neg hlt] at h
      rw [skipDigits_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
      have : i = j := by simpa using h
      rw [this]

/-- **`skip_digits` refines `skipDigits`** (`Scan/Fast.lean:93-101`). -/
theorem skip_digits_refines {b : Slice Std.U8} {i j : Std.Usize}
    (h : frontend.scan_fast.skip_digits b i = ok j) :
    absPos j = skipDigits (absBytes b) (absPos i) :=
  skip_digits_loop_refines (b.val.length - i.val) i j (le_refl _) h

end ConRon.Refine.Frontend
