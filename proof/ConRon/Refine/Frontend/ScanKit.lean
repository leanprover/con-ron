/-
**The bounds kit, exact against con-leche** (task #87, phase 3).

`crates/con-ron-core/src/frontend/scan_fast.rs`'s byte primitives against
`ConLeche/Frontend/Scan/Fast.lean:55-540` -- the "bounds kit", the key
classifier and the scalar readers.  Everything above this file (the record
scanners, the object loops, the line dispatcher) reads bytes only through
these, so this is where the port's `Slice U8` + `Std.Usize` world is joined to
con-leche's `ByteArray` + `USize` one, once.

## What this file gives the object loops

Every lemma is stated **port on the left, con-leche on the right**; a caller
that wants the other orientation takes `.symm`.  Every one has `= ok …` as its
hypothesis, so nothing is claimed about an Aeneas `fail`/`div`.

    pByteAt (b : Slice Std.U8) (n : Nat) : Std.U8        -- `byte_at`, as a function
    byte_at_eq       : byte_at b i = ok (pByteAt b i.val)
    byteAt_pos       : byteAt (absBytes b) p = absByte (pByteAt b p.toNat)
    pos_lt_usize     : p < (absBytes b).usize ↔ p.toNat < b.val.length
    uget_pos         : (absBytes b).uget p h = absByte (pByteAt b p.toNat)

    byte_at_refines     : byte_at b i = ok c   → absByte c = byteAt (absBytes b) (absPos i)
    is_ws_refines       : is_ws c = ok r       → r = isWs (absByte c)
    is_digit_refines    : is_digit c = ok r    → r = isDigit (absByte c)
    skip_ws_refines     : skip_ws b i = ok j   → absPos j = skipWs (absBytes b) (absPos i)
    skip_digits_refines : skip_digits b i = ok j → absPos j = skipDigits (absBytes b) (absPos i)
    match_lit_refines   : (hnz) → match_lit b i lit = ok r →
                            r = matchLit (absBytes b) (absPos i) (absBytes lit) 0
    match_lit_litFrom   : (hnz) → match_lit b i lit = ok r →
                            r = litFrom (absBytes b) (absPos i) (lit.val.map absByte)
    key_end_refines     : key_end b j = ok e   → absPos e = keyEnd (absBytes b) (absPos j)
    key_at_refines      : key_at b i kl = ok k → absKey k = keyAt (absBytes b) (absPos i) (absPos kl)
    value_at_refines    : value_at b i ke = ok v → absPos v = valueAt (absBytes b) (absPos i) (absPos ke)
    num_end_refines     : num_end b i = ok e   → absPos e = numEnd (absBytes b) (absPos i)
    prog_eq             : prog ks e = ok r     → r = decide (absPos ks < absPos e)
    dup_eq              : dup seen bit = ok r  → r = ((absU32 seen &&& absU32 bit) != 0)
    newline_from_refines : newline_from b i = ok r → r = newlineFrom (absBytes b) (absPos i)
    has_escape_refines  : has_escape b j e = ok r → r = hasEscape (absBytes b) (absPos j) (absPos e)
    str_close_refines   : str_close b j = ok e → absPos e = strClose (absBytes b) (absPos j)
    skip_digits_ge      : skip_digits b i = ok e → i.val ≤ e.val
    num_end_run         : num_end b i = ok e → ¬ e = i → skip_digits b i = ok e
    readNat_eq          : `readNat` unfolded once at a port position
    readNatAt_eq_readNat : skipDigits (absBytes b) (absPos i) = absPos e → i.val ≤ e.val →
                            readNatAt (absBytes b) (absPos i) (absPos e) = readNat (absBytes b) (absPos i) 0
    read_nat_at_refines : skip_digits b i = ok e → read_nat_at b i e = ok (.Ok n) →
                            n.val = readNatAt (absBytes b) (absPos i) (absPos e)
    read_nat_at_err     : read_nat_at b i e = ok (.Err er) → ScanErrSim er x
    slot_nat_refines    : slot_nat b ks v = ok o → ScanSim absU64 o (slotNat (absBytes b) (absPos ks) (absPos v))
    skip_braced_refines : skip_braced b i depth = ok j →
                            absPos j = skipBraced (absBytes b) (absPos i) (absU64 depth)

where `hnz : ∀ m (hm : m < lit.val.length), lit.val[m] ≠ 0#u8` -- no literal of
the dialect holds a `0` byte, and that is exactly what makes the port's
`byte_at`-past-the-end agree with con-leche's out-of-bounds `false`.

**The `@[simp]` bridges this file owns.**  Four agents' `rw`s are written
against these normal forms, so they are listed here in full and nowhere else
declares one:

    absByte_eq_iff  : absByte c = d ↔ c.val = d.toNat
    absByte_le_iff  : absByte c ≤ d ↔ c.val ≤ d.toNat
    le_absByte_iff  : d ≤ absByte c ↔ d.toNat ≤ c.val
    absByte_lt_iff  : absByte c < d ↔ c.val < d.toNat
    absByte_beq     : (absByte c == d) = decide (c.val = d.toNat)
    absByte_inj_iff : absByte c = absByte d ↔ c = d
    absPos_beq      : (absPos i == u) = decide (i.val = u.toNat)
    absPos_lt       : absPos i < absPos j ↔ i.val < j.val
    absU32_toNat    : (absU32 x).toNat = x.val          -- `rfl`
    absU32_beq      : (absU32 a == absU32 b) = (a == b)

The idiom for a byte test is therefore `have : (absByte c == 34) = false := by
simp; scalar_tac` -- `simp` turns the `BEq` on `UInt8` into a `Nat` equation
and `scalar_tac` takes it back to the port's `c = 34#u8`.

## The two definitions this file adds

* **`litFrom B p cs`** -- `keyAt` does NOT call `matchLit`: it compares a key's
  tail with the unrolled `lit1`…`lit10` chains of `Scan/Fast.lean:160-222`
  (a `String` constant in that position is a heap object, `Fast.lean`'s own
  note, task #264), while the port spells the same compare as one `match_lit`
  against a `[u8; N]` constant (deviation 2 of `scan_fast.rs`'s module note).
  `litFrom` is that chain as a function of the literal's bytes, and
  `matchLit_eq_litFrom` is the equivalence to `matchLit`.  It is an
  intermediate definition in DESIGN.md's sense; `litFrom_1`…`litFrom_11` are
  what turn it back into `keyAt`'s own `litN` calls.
* **`slotNat B ks v`** -- `scan_fast::slot_nat` is the port's factoring of the
  `numEnd`/`readNatAt`/`noProgress` chain every `Nat`-valued slot of every
  `scan*Loop` of `Scan/Fast.lean` writes out inline (`Fast.lean:820-824` is
  one instance).  `slotNat` is that fragment as a con-leche function, written
  to be the Lean's own chain literally, so an object loop can unfold it and
  see exactly what its `scan*Loop` twin has.
* **`absU32`** -- the port's `u32` seen-mask as con-leche's `UInt32`, for
  `dup` and for every object loop's `seen` bits.  `Abs.lean` has no `u32`
  abstraction because no record field is one.  The body is `UInt32.ofBitVec
  n.bv` and NOT `UInt32.ofNat n.val`, because that is what makes `absU32_and`
  and `absU32_or` -- which every `seen |||`/`seen &&&` step rides on --
  definitional (`rfl`).  `absU32_inj`, `absU32_beq` go with them.

## `sorry` count in this file: 0
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
theorem slice_index_ok {t : Slice Std.U8} {i : Std.Usize}
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

/-- A machine-word position indexes con-leche's array exactly when it indexes
the port's slice. -/
theorem pos_lt_usize {b : Slice Std.U8} {p : USize} :
    p < (absBytes b).usize ↔ p.toNat < b.val.length := by
  rw [USize.lt_iff_toNat_lt, absBytes_usize]

/-- A byte read inside the array is `pByteAt`. -/
theorem uget_pos {b : Slice Std.U8} {p : USize} (h : p.toNat < (absBytes b).size) :
    (absBytes b).uget p h = absByte (pByteAt b p.toNat) := by
  have hi : p.toNat < b.val.length := by rw [absBytes_size] at h; exact h
  rw [absBytes_uget b p h hi, pByteAt, dif_pos hi]

/-- A byte read inside the array, through `absPos`. -/
theorem uget_absPos {b : Slice Std.U8} {i : Std.Usize}
    (h : (absPos i).toNat < (absBytes b).size) :
    (absBytes b).uget (absPos i) h = absByte (pByteAt b i.val) := by
  rw [uget_pos h, absPos_toNat]

/-- **`pByteAt` is con-leche's `byteAt`**, at any machine-word position. -/
theorem byteAt_pos (b : Slice Std.U8) (p : USize) :
    byteAt (absBytes b) p = absByte (pByteAt b p.toNat) := by
  rw [byteAt]
  split
  · rename_i h; rw [uget_pos]
  · rename_i h
    rw [pByteAt, dif_neg (fun hc => h (pos_lt_usize.mpr hc))]
    simp [absByte]

/-- **`byte_at` refines `byteAt`** (`Scan/Fast.lean:72-76`). -/
theorem byte_at_refines {b : Slice Std.U8} {i : Std.Usize} {c : Std.U8}
    (h : frontend.scan_fast.byte_at b i = ok c) :
    absByte c = byteAt (absBytes b) (absPos i) := by
  rw [byte_at_eq] at h
  have h : pByteAt b i.val = c := by simpa using h
  subst h
  rw [byteAt_pos, absPos_toNat]

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

/-! ## Positions, compared

The two bridges every `if p == q` / `if p < q` of a con-leche scanner needs on
the port's side of the fence. -/

@[simp] theorem absPos_beq {i : Std.Usize} {u : USize} :
    (absPos i == u) = decide (i.val = u.toNat) := by
  by_cases h : i.val = u.toNat
  · have he : absPos i = u := by apply USize.toNat_inj.mp; rw [absPos_toNat, h]
    simp [he, h]
  · have hne : absPos i ≠ u := by intro hc; exact h (by rw [← hc, absPos_toNat])
    simp [hne, h]

@[simp] theorem absPos_lt {i j : Std.Usize} : absPos i < absPos j ↔ i.val < j.val := by
  rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]

/-! ## `skip_ws`, `skip_digits`

`scan_fast.rs:107-124` against `Scan/Fast.lean:84-101`.  The port's `*_loop`
mirrors the Lean recursion one for one, so both are the same induction on the
`Nat` measure `b.len() - i` (`Refine/PinsBytes.lean` is the model). -/

/-- `skipWs` at a port position, unfolded once. -/
theorem skipWs_eq (b : Slice Std.U8) (i : Std.Usize) :
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
theorem skipDigits_eq (b : Slice Std.U8) (i : Std.Usize) :
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

/-! ## `match_lit`

`scan_fast.rs:132-142` against `Scan/Fast.lean:121-131` (`matchLit`).  The Lean
carries an explicit literal cursor `k`; the port starts it at `0`.  The two
sides agree *because no literal of the dialect holds a `0` byte*: con-leche's
`matchLit` declines outright once the line has run out, and the port's
`byte_at` reads `0` there, so the compare fails at the same step.  `hnz` is
that hypothesis, and it is what a `[u8; N]` key constant discharges by
`decide`. -/

/-- `absByte` is injective: a `Std.U8` is already a byte. -/
@[simp] theorem absByte_inj_iff {c d : Std.U8} : absByte c = absByte d ↔ c = d := by
  constructor
  · intro h
    have := congrArg UInt8.toNat h
    rw [absByte_toNat, absByte_toNat] at this
    scalar_tac
  · intro h; rw [h]

/-- `matchLit` over an abstracted literal, unfolded once. -/
private theorem matchLit_eq (b lit : Slice Std.U8) (p : USize) (k : Std.Usize) :
    matchLit (absBytes b) p (absBytes lit) (absPos k) =
      if k.val < lit.val.length then
        (if p.toNat < b.val.length then
           ((absByte (pByteAt b p.toNat) == absByte (pByteAt lit k.val)) &&
             matchLit (absBytes b) (p + 1) (absBytes lit) (absPos k + 1))
         else false)
      else true := by
  rw [matchLit]
  by_cases hk : k.val < lit.val.length
  · rw [dif_pos (absPos_lt_usize.mpr hk), if_pos hk]
    by_cases hp : p.toNat < b.val.length
    · rw [dif_pos (pos_lt_usize.mpr hp), if_pos hp, uget_pos, uget_absPos]
    · rw [dif_neg (fun hc => hp (pos_lt_usize.mp hc)), if_neg hp]
  · rw [dif_neg (fun hc => hk (absPos_lt_usize.mp hc)), if_neg hk]

private theorem match_lit_loop_refines {b lit : Slice Std.U8} (f : Nat)
    (hnz : ∀ (m : Nat) (hm : m < lit.val.length), lit.val[m] ≠ 0#u8) :
    ∀ (i k : Std.Usize) (p : USize) (r : Bool),
      lit.val.length - k.val ≤ f → p.toNat = i.val + k.val →
      frontend.scan_fast.match_lit_loop b i lit (Slice.len lit) k = ok r →
      r = matchLit (absBytes b) p (absBytes lit) (absPos k) := by
  induction f with
  | zero =>
    intro i k p r hf hp h
    rw [frontend.scan_fast.match_lit_loop.eq_def] at h
    rw [if_neg (show ¬ (k < Slice.len lit) by scalar_tac)] at h
    rw [matchLit_eq, if_neg (show ¬ k.val < lit.val.length by scalar_tac)]
    simpa using h.symm
  | succ f ih =>
    intro i k p r hf hp h
    rw [frontend.scan_fast.match_lit_loop.eq_def] at h
    by_cases hk : k < Slice.len lit
    · have hk' : k.val < lit.val.length := by scalar_tac
      rw [if_pos hk] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = p.toNat := by
        have := ConRon.Refine.Nat.uadd_val hi1; omega
      have hi2v : i2 = pByteAt b p.toNat := by
        rw [byte_at_eq, hi1v] at hi2; simpa using hi2.symm
      have hi3v : i3 = pByteAt lit k.val := by
        rw [slice_index_ok hk'] at hi3
        rw [pByteAt, dif_pos hk']; simpa using hi3.symm
      rw [matchLit_eq]
      rw [if_pos hk']
      by_cases hne : i2 = i3
      · -- the bytes agree: the port's cursor is inside the line
        rw [if_neg (show ¬ ((i2 != i3) = true) by simp [hne])] at h
        have hd : pByteAt b p.toNat = pByteAt lit k.val := by
          rw [← hi2v, ← hi3v]; exact hne
        have hpb : p.toNat < b.val.length := by
          by_contra hc
          have h0 : pByteAt b p.toNat = 0#u8 := by rw [pByteAt, dif_neg hc]
          have hlit : pByteAt lit k.val = lit.val[k.val] := by rw [pByteAt, dif_pos hk']
          exact hnz k.val hk' (by rw [← hlit, ← hd, h0])
        obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
        have hk1v := usize_add_one_inv hk1
        have hstep : (p + 1).toNat = p.toNat + 1 :=
          usizeStep (absBytes b) p (pos_lt_usize.mpr hpb)
        rw [if_pos hpb, ← absPos_add_one hk1]
        rw [ih i k1 (p + 1) r (by omega) (by omega) h]
        rw [hd]
        simp
      · -- the bytes differ, at the same step on both sides
        rw [if_pos (show (i2 != i3) = true by simp [hne])] at h
        have hr : r = false := by simpa using h.symm
        have hd : ¬ (pByteAt b p.toNat = pByteAt lit k.val) := by
          rw [← hi2v, ← hi3v]; exact hne
        rw [hr]
        by_cases hpb : p.toNat < b.val.length
        · rw [if_pos hpb]
          have hbe : (absByte (pByteAt b p.toNat) == absByte (pByteAt lit k.val)) = false := by
            rw [Bool.eq_false_iff]
            intro hc
            exact hd (absByte_inj_iff.mp (by simpa using hc))
          rw [hbe, Bool.false_and]
        · rw [if_neg hpb]
    · rw [if_neg hk] at h
      rw [matchLit_eq, if_neg (show ¬ k.val < lit.val.length by scalar_tac)]
      simpa using h.symm

/-- **`match_lit` refines `matchLit`** (`Scan/Fast.lean:121-131`), for a
literal with no `0` byte. -/
theorem match_lit_refines {b lit : Slice Std.U8} {i : Std.Usize} {r : Bool}
    (hnz : ∀ (m : Nat) (hm : m < lit.val.length), lit.val[m] ≠ 0#u8)
    (h : frontend.scan_fast.match_lit b i lit = ok r) :
    r = matchLit (absBytes b) (absPos i) (absBytes lit) 0 := by
  rw [frontend.scan_fast.match_lit] at h
  have hz : absPos (0#usize) = (0 : USize) := by simp [absPos]; rfl
  have := match_lit_loop_refines lit.val.length hnz i 0#usize (absPos i) r
    (by omega) (by simp) h
  rw [hz] at this
  exact this

/-! ### `matchLit` as the `litN` chain

`keyAt` does NOT call `matchLit`: it compares a key's tail with the unrolled
`lit1`…`lit10` chains of `Scan/Fast.lean:160-222`, because a `String` constant
in that position is a heap object (`Fast.lean`'s own note, task #264).  The
port spells the same compare as one `match_lit` against a `[u8; N]` constant
(deviation 2 of `scan_fast.rs`'s module note).  `litFrom` is that chain as a
function of the literal's bytes -- **an intermediate definition matching the
port's shape**, with `matchLit_eq_litFrom` the equivalence to `matchLit`; it
is what lets the 68 key literals be compared with `keyAt`'s `litN` calls by
`simp`. -/

/-- The unrolled `litN` compare of `Scan/Fast.lean:160-222`, as a function of
the literal's bytes: `litFrom B p [c₀, …, cₙ]` is `litN B p c₀ … cₙ`. -/
def litFrom (B : ByteArray) (p : USize) : List UInt8 → Bool
  | [] => true
  | c :: cs => (byteAt B p == c) && litFrom B (p + 1) cs

private theorem matchLit_litFrom_aux {b lit : Slice Std.U8} (f : Nat)
    (hnz : ∀ (m : Nat) (hm : m < lit.val.length), lit.val[m] ≠ 0#u8) :
    ∀ (p : USize) (k : Std.Usize), lit.val.length - k.val ≤ f →
      matchLit (absBytes b) p (absBytes lit) (absPos k) =
        litFrom (absBytes b) p ((lit.val.map absByte).drop k.val) := by
  induction f with
  | zero =>
    intro p k hf
    rw [matchLit_eq, if_neg (show ¬ k.val < lit.val.length by omega)]
    rw [List.drop_eq_nil_of_le (by simp; omega), litFrom]
  | succ f ih =>
    intro p k hf
    by_cases hk : k.val < lit.val.length
    · have hkm : k.val < (lit.val.map absByte).length := by simpa using hk
      have hdrop : (lit.val.map absByte).drop k.val
          = (lit.val.map absByte)[k.val] :: (lit.val.map absByte).drop (k.val + 1) :=
        List.drop_eq_getElem_cons hkm
      have hel : (lit.val.map absByte)[k.val] = absByte (pByteAt lit k.val) := by
        rw [pByteAt, dif_pos hk]; simp
      have hk1 : ∃ w : Std.Usize, k + 1#usize = ok w ∧ w.val = k.val + 1 := by
        refine usize_add_ok ?_
        have := Slice.length_ineq lit; omega
      obtain ⟨k1, hk1e, hk1v⟩ := hk1
      rw [matchLit_eq, if_pos hk, hdrop, hel, litFrom, byteAt_pos]
      by_cases hpb : p.toNat < b.val.length
      · rw [if_pos hpb, ← absPos_add_one hk1e, ih (p + 1) k1 (by omega), hk1v]
      · rw [if_neg hpb]
        have h0 : pByteAt b p.toNat = 0#u8 := by rw [pByteAt, dif_neg hpb]
        have hne : ¬ (absByte (pByteAt b p.toNat) = absByte (pByteAt lit k.val)) := by
          rw [h0]
          intro hc
          exact hnz k.val hk (by
            have := absByte_inj_iff.mp hc
            rw [pByteAt, dif_pos hk] at this
            exact this.symm)
        rw [show (absByte (pByteAt b p.toNat) == absByte (pByteAt lit k.val)) = false from by
          rw [Bool.eq_false_iff]; intro hc; exact hne (by simpa using hc)]
        rw [Bool.false_and]
    · rw [matchLit_eq, if_neg hk, List.drop_eq_nil_of_le (by simp; omega), litFrom]

/-- **`matchLit` is the `litN` chain** of the literal's bytes, for a literal
with no `0` byte. -/
theorem matchLit_eq_litFrom {b lit : Slice Std.U8} (p : USize)
    (hnz : ∀ (m : Nat) (hm : m < lit.val.length), lit.val[m] ≠ 0#u8) :
    matchLit (absBytes b) p (absBytes lit) 0 = litFrom (absBytes b) p (lit.val.map absByte) := by
  have hz : absPos (0#usize) = (0 : USize) := by simp [absPos]; rfl
  have := matchLit_litFrom_aux (b := b) (lit := lit) lit.val.length hnz p 0#usize (by simp)
  rw [hz] at this
  simpa using this

/-- **`match_lit` against a literal with no `0` byte is the `litN` chain.**
This is the form `key_at` and `scan_bool` use. -/
theorem match_lit_litFrom {b lit : Slice Std.U8} {i : Std.Usize} {r : Bool}
    (hnz : ∀ (m : Nat) (hm : m < lit.val.length), lit.val[m] ≠ 0#u8)
    (h : frontend.scan_fast.match_lit b i lit = ok r) :
    r = litFrom (absBytes b) (absPos i) (lit.val.map absByte) := by
  rw [match_lit_refines hnz h, matchLit_eq_litFrom (absPos i) hnz]

/-! ### `litFrom` against con-leche's `litN`

`keyAt` reads a key's tail with `lit1`…`lit10` (`Scan/Fast.lean:160-222`),
whose arguments are `j`, `j + 1`, …, `j + 9`; `litFrom` walks the same bytes
one `+ 1` at a time.  The `litFrom_N` bridges below are what makes a port
literal of `N` bytes -- whose first byte is the one `keyAt` switched on --
into `keyAt`'s own `lit(N-1)` call at the same position, and they are the only
place the `+ 1 + 1` / `+ 2` spelling of a position has to be reconciled. -/

/-- A small `Nat` is a `USize`: the word is 32 or 64 bits wide either way. -/
private theorem usize_small (n : Nat) (h : n ≤ 16) : n < USize.size := by
  have h2 : (16:Nat) < USize.size := by
    rw [USize.size]
    rcases System.Platform.numBits_eq with hb | hb <;> rw [hb] <;> norm_num
  omega

private theorem uT1 : ((1 : USize)).toNat = 1 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 1 (by norm_num))]
private theorem uT2 : ((2 : USize)).toNat = 2 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 2 (by norm_num))]
private theorem uT3 : ((3 : USize)).toNat = 3 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 3 (by norm_num))]
private theorem uT4 : ((4 : USize)).toNat = 4 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 4 (by norm_num))]
private theorem uT5 : ((5 : USize)).toNat = 5 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 5 (by norm_num))]
private theorem uT6 : ((6 : USize)).toNat = 6 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 6 (by norm_num))]
private theorem uT7 : ((7 : USize)).toNat = 7 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 7 (by norm_num))]
private theorem uT8 : ((8 : USize)).toNat = 8 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 8 (by norm_num))]
private theorem uT9 : ((9 : USize)).toNat = 9 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 9 (by norm_num))]
private theorem uT10 : ((10 : USize)).toNat = 10 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 10 (by norm_num))]
private theorem uT11 : ((11 : USize)).toNat = 11 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 11 (by norm_num))]
private theorem uT12 : ((12 : USize)).toNat = 12 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small 12 (by norm_num))]

private theorem uA1 (x : USize) : x + 1 + 1 = x + 2 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT1, uT2,
    Nat.mod_eq_of_lt (usize_small 2 (by norm_num))]
private theorem uA2 (x : USize) : x + 2 + 1 = x + 3 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT2, uT3,
    Nat.mod_eq_of_lt (usize_small 3 (by norm_num))]
private theorem uA3 (x : USize) : x + 3 + 1 = x + 4 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT3, uT4,
    Nat.mod_eq_of_lt (usize_small 4 (by norm_num))]
private theorem uA4 (x : USize) : x + 4 + 1 = x + 5 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT4, uT5,
    Nat.mod_eq_of_lt (usize_small 5 (by norm_num))]
private theorem uA5 (x : USize) : x + 5 + 1 = x + 6 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT5, uT6,
    Nat.mod_eq_of_lt (usize_small 6 (by norm_num))]
private theorem uA6 (x : USize) : x + 6 + 1 = x + 7 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT6, uT7,
    Nat.mod_eq_of_lt (usize_small 7 (by norm_num))]
private theorem uA7 (x : USize) : x + 7 + 1 = x + 8 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT7, uT8,
    Nat.mod_eq_of_lt (usize_small 8 (by norm_num))]
private theorem uA8 (x : USize) : x + 8 + 1 = x + 9 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT8, uT9,
    Nat.mod_eq_of_lt (usize_small 9 (by norm_num))]
private theorem uA9 (x : USize) : x + 9 + 1 = x + 10 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT9, uT10,
    Nat.mod_eq_of_lt (usize_small 10 (by norm_num))]
private theorem uA10 (x : USize) : x + 10 + 1 = x + 11 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT10, uT11,
    Nat.mod_eq_of_lt (usize_small 11 (by norm_num))]
private theorem uA11 (x : USize) : x + 11 + 1 = x + 12 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT11, uT12,
    Nat.mod_eq_of_lt (usize_small 12 (by norm_num))]
private theorem uB2 (x : USize) : x + 1 + 2 = x + 3 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT2, uT3,
    Nat.mod_eq_of_lt (usize_small 3 (by norm_num))]
private theorem uB3 (x : USize) : x + 1 + 3 = x + 4 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT3, uT4,
    Nat.mod_eq_of_lt (usize_small 4 (by norm_num))]
private theorem uB4 (x : USize) : x + 1 + 4 = x + 5 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT4, uT5,
    Nat.mod_eq_of_lt (usize_small 5 (by norm_num))]
private theorem uB5 (x : USize) : x + 1 + 5 = x + 6 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT5, uT6,
    Nat.mod_eq_of_lt (usize_small 6 (by norm_num))]
private theorem uB6 (x : USize) : x + 1 + 6 = x + 7 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT6, uT7,
    Nat.mod_eq_of_lt (usize_small 7 (by norm_num))]
private theorem uB7 (x : USize) : x + 1 + 7 = x + 8 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT7, uT8,
    Nat.mod_eq_of_lt (usize_small 8 (by norm_num))]
private theorem uB8 (x : USize) : x + 1 + 8 = x + 9 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT8, uT9,
    Nat.mod_eq_of_lt (usize_small 9 (by norm_num))]
private theorem uB9 (x : USize) : x + 1 + 9 = x + 10 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT9, uT10,
    Nat.mod_eq_of_lt (usize_small 10 (by norm_num))]
private theorem uB10 (x : USize) : x + 1 + 10 = x + 11 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT10, uT11,
    Nat.mod_eq_of_lt (usize_small 11 (by norm_num))]
private theorem uB11 (x : USize) : x + 1 + 11 = x + 12 := by
  rw [USize.add_assoc]
  congr 1
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, uT1, uT11, uT12,
    Nat.mod_eq_of_lt (usize_small 12 (by norm_num))]

private theorem litFrom_1 (B : ByteArray) (q : USize) (c0 : UInt8) :
    litFrom B q [c0] = (byteAt B q == c0) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_2 (B : ByteArray) (q : USize) (c0 c1 : UInt8) :
    litFrom B q [c0, c1] =
      ((byteAt B q == c0) && lit1 B (q + 1) c1) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_3 (B : ByteArray) (q : USize) (c0 c1 c2 : UInt8) :
    litFrom B q [c0, c1, c2] =
      ((byteAt B q == c0) && lit2 B (q + 1) c1 c2) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_4 (B : ByteArray) (q : USize) (c0 c1 c2 c3 : UInt8) :
    litFrom B q [c0, c1, c2, c3] =
      ((byteAt B q == c0) && lit3 B (q + 1) c1 c2 c3) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_5 (B : ByteArray) (q : USize) (c0 c1 c2 c3 c4 : UInt8) :
    litFrom B q [c0, c1, c2, c3, c4] =
      ((byteAt B q == c0) && lit4 B (q + 1) c1 c2 c3 c4) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_6 (B : ByteArray) (q : USize) (c0 c1 c2 c3 c4 c5 : UInt8) :
    litFrom B q [c0, c1, c2, c3, c4, c5] =
      ((byteAt B q == c0) && lit5 B (q + 1) c1 c2 c3 c4 c5) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_7 (B : ByteArray) (q : USize) (c0 c1 c2 c3 c4 c5 c6 : UInt8) :
    litFrom B q [c0, c1, c2, c3, c4, c5, c6] =
      ((byteAt B q == c0) && lit6 B (q + 1) c1 c2 c3 c4 c5 c6) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_8 (B : ByteArray) (q : USize) (c0 c1 c2 c3 c4 c5 c6 c7 : UInt8) :
    litFrom B q [c0, c1, c2, c3, c4, c5, c6, c7] =
      ((byteAt B q == c0) && lit7 B (q + 1) c1 c2 c3 c4 c5 c6 c7) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_9 (B : ByteArray) (q : USize) (c0 c1 c2 c3 c4 c5 c6 c7 c8 : UInt8) :
    litFrom B q [c0, c1, c2, c3, c4, c5, c6, c7, c8] =
      ((byteAt B q == c0) && lit8 B (q + 1) c1 c2 c3 c4 c5 c6 c7 c8) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_10 (B : ByteArray) (q : USize) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : UInt8) :
    litFrom B q [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] =
      ((byteAt B q == c0) && lit9 B (q + 1) c1 c2 c3 c4 c5 c6 c7 c8 c9) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]
private theorem litFrom_11 (B : ByteArray) (q : USize) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : UInt8) :
    litFrom B q [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10] =
      ((byteAt B q == c0) && lit10 B (q + 1) c1 c2 c3 c4 c5 c6 c7 c8 c9 c10) := by
  simp only [litFrom, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10,
    Bool.and_true, Bool.and_assoc, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11, uB2, uB3, uB4, uB5, uB6, uB7, uB8, uB9, uB10, uB11]

/-! ## `key_end`

`scan_fast.rs:149-162` against `Scan/Fast.lean:133-146` (`keyEnd`).  The port
tests `c < 32` and `c == 92` in two `if`s where the Lean writes one `||`. -/

/-- `keyEnd` at a port position, unfolded once. -/
private theorem keyEnd_eq (b : Slice Std.U8) (j : Std.Usize) :
    keyEnd (absBytes b) (absPos j) =
      (if j.val < b.val.length then
        (if absByte (pByteAt b j.val) == 34 then absPos j
         else if absByte (pByteAt b j.val) < 32 || absByte (pByteAt b j.val) == 92 then 0
         else keyEnd (absBytes b) (absPos j + 1))
      else 0) := by
  rw [keyEnd]
  by_cases h : j.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_absPos]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]

private theorem key_end_loop_refines {b : Slice Std.U8} (f : Nat) :
    ∀ (j e : Std.Usize), b.val.length - j.val ≤ f →
      frontend.scan_fast.key_end_loop b j = ok e →
      absPos e = keyEnd (absBytes b) (absPos j) := by
  have hz : absPos (0#usize) = (0 : USize) := by simp [absPos]; rfl
  induction f with
  | zero =>
    intro j e hf h
    rw [frontend.scan_fast.key_end_loop.eq_def] at h
    rw [if_neg (show ¬ (j < Slice.len b) by scalar_tac)] at h
    rw [keyEnd_eq, if_neg (show ¬ j.val < b.val.length by scalar_tac)]
    have : 0#usize = e := by simpa using h
    rw [← this, hz]
  | succ f ih =>
    intro j e hf h
    rw [frontend.scan_fast.key_end_loop.eq_def] at h
    by_cases hlt : j < Slice.len b
    · rw [if_pos hlt] at h
      have hj : j.val < b.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hc' : c = pByteAt b j.val := by
        rw [slice_index_ok hj] at hc; rw [pByteAt, dif_pos hj]; simpa using hc.symm
      rw [keyEnd_eq, if_pos hj, ← hc']
      by_cases h34 : c = 34#u8
      · rw [if_pos h34] at h
        have hb : (absByte c == 34) = true := by simp; scalar_tac
        have he : j = e := by simpa using h
        rw [hb, he]; simp
      · rw [if_neg h34] at h
        have hb : (absByte c == 34) = false := by simp; scalar_tac
        rw [hb]
        by_cases h32 : c < 32#u8
        · rw [if_pos h32] at h
          have hb2 : (decide (absByte c < 32) || absByte c == 92) = true := by
            simp; left; scalar_tac
          rw [hb2]
          have : 0#usize = e := by simpa using h
          rw [← this, hz]; simp
        · rw [if_neg h32] at h
          by_cases h92 : c = 92#u8
          · rw [if_pos h92] at h
            have hb2 : (decide (absByte c < 32) || absByte c == 92) = true := by
              simp; right; scalar_tac
            rw [hb2]
            have : 0#usize = e := by simpa using h
            rw [← this, hz]; simp
          · rw [if_neg h92] at h
            have hb2 : (decide (absByte c < 32) || absByte c == 92) = false := by
              simp; constructor <;> scalar_tac
            rw [hb2]
            simp only [Bool.false_eq_true, if_false]
            obtain ⟨j1, hj1, h⟩ := bind_eq_ok_iff.mp h
            have hj1v := usize_add_one_inv hj1
            rw [← absPos_add_one hj1]
            exact ih j1 e (by omega) h
    · rw [if_neg hlt] at h
      rw [keyEnd_eq, if_neg (show ¬ j.val < b.val.length by scalar_tac)]
      have : 0#usize = e := by simpa using h
      rw [← this, hz]

/-- **`key_end` refines `keyEnd`** (`Scan/Fast.lean:133-146`). -/
theorem key_end_refines {b : Slice Std.U8} {j e : Std.Usize}
    (h : frontend.scan_fast.key_end b j = ok e) :
    absPos e = keyEnd (absBytes b) (absPos j) :=
  key_end_loop_refines (b.val.length - j.val) j e (le_refl _) h

/-! ## `key_at`

`scan_fast.rs:183-704` against `Scan/Fast.lean:224-446` (`keyAt`) and its
ten `litN` helpers (`Scan/Fast.lean:160-222`). -/

/-- One `[u8; N]` key constant of `key_at`, compared: the port's `match_lit`
against it is `keyAt`'s own unrolled chain over the same bytes. -/
private theorem key_lit {b : Slice Std.U8} {i j : Std.Usize} {n : Std.Usize}
    {S : Array Std.U8 n} {s : Slice Std.U8} {r : Bool} {cs : List UInt8}
    (hj : i + 1#usize = ok j)
    (hs : lift (Array.to_slice S) = ok s)
    (hcs : S.val.map absByte = cs)
    (hnz0 : ∀ c ∈ cs, c ≠ 0)
    (h : frontend.scan_fast.match_lit b j s = ok r) :
    r = litFrom (absBytes b) (absPos i + 1) cs := by
  have hsv : s = Array.to_slice S := by simpa using hs.symm
  have hval : s.val = S.val := by rw [hsv]; simp
  have hnz : ∀ (m : Nat) (hm : m < S.val.length), S.val[m] ≠ 0#u8 := by
    intro m hm hc
    have hmem : absByte (S.val[m]) ∈ cs := by
      rw [← hcs]; exact List.mem_map_of_mem (List.getElem_mem hm)
    exact hnz0 _ hmem (by rw [hc]; rfl)
  rw [match_lit_litFrom (by rw [hval]; exact hnz) h, hval, hcs, absPos_add_one hj]

/-- The leaf of every branch of `key_at_refines`: put each candidate's
`litFrom` into `keyAt`'s `litN` spelling, use the first byte the arm switched
on, and let the byte atoms -- which are the same terms on both sides -- decide
the if-chains. -/
local macro "key_close" : tactic => `(tactic|
  (simp only [litFrom_1, litFrom_2, litFrom_3, litFrom_4, litFrom_5, litFrom_6,
      litFrom_7, litFrom_8, litFrom_9, litFrom_10, litFrom_11] at *
   try simp_all [absKey]
   all_goals ((try split_ifs) <;>
     simp_all [absKey, lit1, lit2, lit3, lit4, lit5, lit6, lit7, lit8, lit9, lit10])))

set_option maxHeartbeats 2000000 in
/-- **`key_at` refines `keyAt`** (`Scan/Fast.lean:224-446`, and the ten `litN`
helpers of `Scan/Fast.lean:160-222`).  One bullet per first byte, then one per
key length, then one per candidate literal: the port's `match_lit` against a
`[u8; N]` constant is `litFrom` of that constant's bytes (`key_lit`), which is
exactly the `litN` chain con-leche compares with.  The two sides order the
candidates of a length differently -- the port alphabetically, the Lean by
expected frequency -- and that is sound because two distinct literals of the
same length differ in some byte, which is what `key_close` sees.

The proof is mechanical and long because the switch is: 19 first bytes, 44
lengths, 66 literals.  Nothing in it is interesting; `key_lit` and `key_close`
are the two moving parts. -/
theorem key_at_refines {b : Slice Std.U8} {i kl : Std.Usize} {k : frontend.scan_types.Key}
    (h : frontend.scan_fast.key_at b i kl = ok k) :
    absKey k = keyAt (absBytes b) (absPos i) (absPos kl) := by
  rw [frontend.scan_fast.key_at] at h
  obtain ⟨j, hj, w0⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c, hc, w00⟩ := bind_eq_ok_iff.mp w0
  have hcb : byteAt (absBytes b) (absPos i + 1) = absByte c := by
    rw [← absPos_add_one hj]; exact (byte_at_refines hc).symm
  clear h w0 hc
  rw [keyAt]
  split at w00
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 97 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s1, hs1, w1⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v1, hv1, w2⟩ := bind_eq_ok_iff.mp w1
      have q1 := key_lit (cs := [97, 108, 108]) hj hs1
        (by simp [frontend.scan_fast.key_at.S_ALL]) (by decide) hv1
      split at w2
      · have hk : k = frontend.scan_types.Key.KAll := by simpa using w2.symm
        subst hk
        key_close
      · obtain ⟨s2, hs2, w3⟩ := bind_eq_ok_iff.mp w2
        obtain ⟨v2, hv2, w4⟩ := bind_eq_ok_iff.mp w3
        have q2 := key_lit (cs := [97, 112, 112]) hj hs2
          (by simp [frontend.scan_fast.key_at.S_APP]) (by decide) hv2
        split at w4
        · have hk : k = frontend.scan_types.Key.KApp := by simpa using w4.symm
          subst hk
          key_close
        · obtain ⟨s3, hs3, w5⟩ := bind_eq_ok_iff.mp w4
          obtain ⟨v3, hv3, w6⟩ := bind_eq_ok_iff.mp w5
          have q3 := key_lit (cs := [97, 114, 103]) hj hs3
            (by simp [frontend.scan_fast.key_at.S_ARG]) (by decide) hv3
          split at w6
          · have hk : k = frontend.scan_types.Key.KArg := by simpa using w6.symm
            subst hk
            key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w6.symm
            subst hk
            key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s4, hs4, w7⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v4, hv4, w8⟩ := bind_eq_ok_iff.mp w7
        have q4 := key_lit (cs := [97, 120, 105, 111, 109]) hj hs4
          (by simp [frontend.scan_fast.key_at.S_AXIOM]) (by decide) hv4
        split at w8
        · have hk : k = frontend.scan_types.Key.KAxiom := by simpa using w8.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w8.symm
          subst hk
          key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
        subst hk
        have gk3 : ¬ kl.val = 3 := by scalar_tac
        have gk5 : ¬ kl.val = 5 := by scalar_tac
        key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 98 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s5, hs5, w9⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v5, hv5, w10⟩ := bind_eq_ok_iff.mp w9
      have q5 := key_lit (cs := [98, 111, 100, 121]) hj hs5
        (by simp [frontend.scan_fast.key_at.S_BODY]) (by decide) hv5
      split at w10
      · have hk : k = frontend.scan_types.Key.KBody := by simpa using w10.symm
        subst hk
        key_close
      · obtain ⟨s6, hs6, w11⟩ := bind_eq_ok_iff.mp w10
        obtain ⟨v6, hv6, w12⟩ := bind_eq_ok_iff.mp w11
        have q6 := key_lit (cs := [98, 118, 97, 114]) hj hs6
          (by simp [frontend.scan_fast.key_at.S_BVAR]) (by decide) hv6
        split at w12
        · have hk : k = frontend.scan_types.Key.KBvar := by simpa using w12.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w12.symm
          subst hk
          key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s7, hs7, w13⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v7, hv7, w14⟩ := bind_eq_ok_iff.mp w13
        have q7 := key_lit (cs := [98, 105, 110, 100, 101, 114, 73, 110, 102, 111]) hj hs7
          (by simp [frontend.scan_fast.key_at.S_BINDERINFO]) (by decide) hv7
        split at w14
        · have hk : k = frontend.scan_types.Key.KBinderInfo := by simpa using w14.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w14.symm
          subst hk
          key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
        subst hk
        have gk4 : ¬ kl.val = 4 := by scalar_tac
        have gk10 : ¬ kl.val = 10 := by scalar_tac
        key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 99 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s8, hs8, w15⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v8, hv8, w16⟩ := bind_eq_ok_iff.mp w15
      have q8 := key_lit (cs := [99, 105, 100, 120]) hj hs8
        (by simp [frontend.scan_fast.key_at.S_CIDX]) (by decide) hv8
      split at w16
      · have hk : k = frontend.scan_types.Key.KCidx := by simpa using w16.symm
        subst hk
        key_close
      · obtain ⟨s9, hs9, w17⟩ := bind_eq_ok_iff.mp w16
        obtain ⟨v9, hv9, w18⟩ := bind_eq_ok_iff.mp w17
        have q9 := key_lit (cs := [99, 116, 111, 114]) hj hs9
          (by simp [frontend.scan_fast.key_at.S_CTOR]) (by decide) hv9
        split at w18
        · have hk : k = frontend.scan_types.Key.KCtor := by simpa using w18.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w18.symm
          subst hk
          key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s10, hs10, w19⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v10, hv10, w20⟩ := bind_eq_ok_iff.mp w19
        have q10 := key_lit (cs := [99, 111, 110, 115, 116]) hj hs10
          (by simp [frontend.scan_fast.key_at.S_CONST]) (by decide) hv10
        split at w20
        · have hk : k = frontend.scan_types.Key.KConst := by simpa using w20.symm
          subst hk
          key_close
        · obtain ⟨s11, hs11, w21⟩ := bind_eq_ok_iff.mp w20
          obtain ⟨v11, hv11, w22⟩ := bind_eq_ok_iff.mp w21
          have q11 := key_lit (cs := [99, 116, 111, 114, 115]) hj hs11
            (by simp [frontend.scan_fast.key_at.S_CTORS]) (by decide) hv11
          split at w22
          · have hk : k = frontend.scan_types.Key.KCtors := by simpa using w22.symm
            subst hk
            key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w22.symm
            subst hk
            key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
        subst hk
        have gk4 : ¬ kl.val = 4 := by scalar_tac
        have gk5 : ¬ kl.val = 5 := by scalar_tac
        key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 100 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s12, hs12, w23⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v12, hv12, w24⟩ := bind_eq_ok_iff.mp w23
      have q12 := key_lit (cs := [100, 101, 102]) hj hs12
        (by simp [frontend.scan_fast.key_at.S_DEF]) (by decide) hv12
      split at w24
      · have hk : k = frontend.scan_types.Key.KDef := by simpa using w24.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w24.symm
        subst hk
        key_close
    · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
      subst hk
      have gk3 : ¬ kl.val = 3 := by scalar_tac
      key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 102 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s13, hs13, w25⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v13, hv13, w26⟩ := bind_eq_ok_iff.mp w25
      have q13 := key_lit (cs := [102, 110]) hj hs13
        (by simp [frontend.scan_fast.key_at.S_FN]) (by decide) hv13
      split at w26
      · have hk : k = frontend.scan_types.Key.KFn := by simpa using w26.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w26.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s14, hs14, w27⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v14, hv14, w28⟩ := bind_eq_ok_iff.mp w27
        have q14 := key_lit (cs := [102, 111, 114, 97, 108, 108, 69]) hj hs14
          (by simp [frontend.scan_fast.key_at.S_FORALLE]) (by decide) hv14
        split at w28
        · have hk : k = frontend.scan_types.Key.KForallE := by simpa using w28.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w28.symm
          subst hk
          key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
        subst hk
        have gk2 : ¬ kl.val = 2 := by scalar_tac
        have gk7 : ¬ kl.val = 7 := by scalar_tac
        key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 104 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s15, hs15, w29⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v15, hv15, w30⟩ := bind_eq_ok_iff.mp w29
      have q15 := key_lit (cs := [104, 105, 110, 116, 115]) hj hs15
        (by simp [frontend.scan_fast.key_at.S_HINTS]) (by decide) hv15
      split at w30
      · have hk : k = frontend.scan_types.Key.KHints := by simpa using w30.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w30.symm
        subst hk
        key_close
    · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
      subst hk
      have gk5 : ¬ kl.val = 5 := by scalar_tac
      key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 105 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s16, hs16, w31⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v16, hv16, w32⟩ := bind_eq_ok_iff.mp w31
      have q16 := key_lit (cs := [105]) hj hs16
        (by simp [frontend.scan_fast.key_at.S_I]) (by decide) hv16
      split at w32
      · have hk : k = frontend.scan_types.Key.KI := by simpa using w32.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w32.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s17, hs17, w33⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v17, hv17, w34⟩ := bind_eq_ok_iff.mp w33
        have q17 := key_lit (cs := [105, 101]) hj hs17
          (by simp [frontend.scan_fast.key_at.S_IE]) (by decide) hv17
        split at w34
        · have hk : k = frontend.scan_types.Key.KIe := by simpa using w34.symm
          subst hk
          key_close
        · obtain ⟨s18, hs18, w35⟩ := bind_eq_ok_iff.mp w34
          obtain ⟨v18, hv18, w36⟩ := bind_eq_ok_iff.mp w35
          have q18 := key_lit (cs := [105, 108]) hj hs18
            (by simp [frontend.scan_fast.key_at.S_IL]) (by decide) hv18
          split at w36
          · have hk : k = frontend.scan_types.Key.KIl := by simpa using w36.symm
            subst hk
            key_close
          · obtain ⟨s19, hs19, w37⟩ := bind_eq_ok_iff.mp w36
            obtain ⟨v19, hv19, w38⟩ := bind_eq_ok_iff.mp w37
            have q19 := key_lit (cs := [105, 110]) hj hs19
              (by simp [frontend.scan_fast.key_at.S_IN]) (by decide) hv19
            split at w38
            · have hk : k = frontend.scan_types.Key.KIn := by simpa using w38.symm
              subst hk
              key_close
            · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w38.symm
              subst hk
              key_close
      · split at w00
        · rename_i hkl
          subst hkl
          obtain ⟨s20, hs20, w39⟩ := bind_eq_ok_iff.mp w00
          obtain ⟨v20, hv20, w40⟩ := bind_eq_ok_iff.mp w39
          have q20 := key_lit (cs := [105, 100, 120]) hj hs20
            (by simp [frontend.scan_fast.key_at.S_IDX]) (by decide) hv20
          split at w40
          · have hk : k = frontend.scan_types.Key.KIdx := by simpa using w40.symm
            subst hk
            key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w40.symm
            subst hk
            key_close
        · split at w00
          · rename_i hkl
            subst hkl
            obtain ⟨s21, hs21, w41⟩ := bind_eq_ok_iff.mp w00
            obtain ⟨v21, hv21, w42⟩ := bind_eq_ok_iff.mp w41
            have q21 := key_lit (cs := [105, 109, 97, 120]) hj hs21
              (by simp [frontend.scan_fast.key_at.S_IMAX]) (by decide) hv21
            split at w42
            · have hk : k = frontend.scan_types.Key.KImax := by simpa using w42.symm
              subst hk
              key_close
            · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w42.symm
              subst hk
              key_close
          · split at w00
            · rename_i hkl
              subst hkl
              obtain ⟨s22, hs22, w43⟩ := bind_eq_ok_iff.mp w00
              obtain ⟨v22, hv22, w44⟩ := bind_eq_ok_iff.mp w43
              have q22 := key_lit (cs := [105, 115, 82, 101, 99]) hj hs22
                (by simp [frontend.scan_fast.key_at.S_ISREC]) (by decide) hv22
              split at w44
              · have hk : k = frontend.scan_types.Key.KIsRec := by simpa using w44.symm
                subst hk
                key_close
              · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w44.symm
                subst hk
                key_close
            · split at w00
              · rename_i hkl
                subst hkl
                obtain ⟨s23, hs23, w45⟩ := bind_eq_ok_iff.mp w00
                obtain ⟨v23, hv23, w46⟩ := bind_eq_ok_iff.mp w45
                have q23 := key_lit (cs := [105, 110, 100, 117, 99, 116]) hj hs23
                  (by simp [frontend.scan_fast.key_at.S_INDUCT]) (by decide) hv23
                split at w46
                · have hk : k = frontend.scan_types.Key.KInduct := by simpa using w46.symm
                  subst hk
                  key_close
                · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w46.symm
                  subst hk
                  key_close
              · split at w00
                · rename_i hkl
                  subst hkl
                  obtain ⟨s24, hs24, w47⟩ := bind_eq_ok_iff.mp w00
                  obtain ⟨v24, hv24, w48⟩ := bind_eq_ok_iff.mp w47
                  have q24 := key_lit (cs := [105, 115, 85, 110, 115, 97, 102, 101]) hj hs24
                    (by simp [frontend.scan_fast.key_at.S_ISUNSAFE]) (by decide) hv24
                  split at w48
                  · have hk : k = frontend.scan_types.Key.KIsUnsafe := by simpa using w48.symm
                    subst hk
                    key_close
                  · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w48.symm
                    subst hk
                    key_close
                · split at w00
                  · rename_i hkl
                    subst hkl
                    obtain ⟨s25, hs25, w49⟩ := bind_eq_ok_iff.mp w00
                    obtain ⟨v25, hv25, w50⟩ := bind_eq_ok_iff.mp w49
                    have q25 := key_lit (cs := [105, 110, 100, 117, 99, 116, 105, 118, 101]) hj hs25
                      (by simp [frontend.scan_fast.key_at.S_INDUCTIVE]) (by decide) hv25
                    split at w50
                    · have hk : k = frontend.scan_types.Key.KInductive := by simpa using w50.symm
                      subst hk
                      key_close
                    · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w50.symm
                      subst hk
                      key_close
                  · split at w00
                    · rename_i hkl
                      subst hkl
                      obtain ⟨s26, hs26, w51⟩ := bind_eq_ok_iff.mp w00
                      obtain ⟨v26, hv26, w52⟩ := bind_eq_ok_iff.mp w51
                      have q26 := key_lit (cs := [105, 115, 82, 101, 102, 108, 101, 120, 105, 118, 101]) hj hs26
                        (by simp [frontend.scan_fast.key_at.S_ISREFLEXIVE]) (by decide) hv26
                      split at w52
                      · have hk : k = frontend.scan_types.Key.KIsReflexive := by simpa using w52.symm
                        subst hk
                        key_close
                      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w52.symm
                        subst hk
                        key_close
                    · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
                      subst hk
                      have gk1 : ¬ kl.val = 1 := by scalar_tac
                      have gk2 : ¬ kl.val = 2 := by scalar_tac
                      have gk3 : ¬ kl.val = 3 := by scalar_tac
                      have gk4 : ¬ kl.val = 4 := by scalar_tac
                      have gk5 : ¬ kl.val = 5 := by scalar_tac
                      have gk6 : ¬ kl.val = 6 := by scalar_tac
                      have gk8 : ¬ kl.val = 8 := by scalar_tac
                      have gk9 : ¬ kl.val = 9 := by scalar_tac
                      have gk11 : ¬ kl.val = 11 := by scalar_tac
                      key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 107 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s27, hs27, w53⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v27, hv27, w54⟩ := bind_eq_ok_iff.mp w53
      have q27 := key_lit (cs := [107]) hj hs27
        (by simp [frontend.scan_fast.key_at.S_K]) (by decide) hv27
      split at w54
      · have hk : k = frontend.scan_types.Key.KK := by simpa using w54.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w54.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s28, hs28, w55⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v28, hv28, w56⟩ := bind_eq_ok_iff.mp w55
        have q28 := key_lit (cs := [107, 105, 110, 100]) hj hs28
          (by simp [frontend.scan_fast.key_at.S_KIND]) (by decide) hv28
        split at w56
        · have hk : k = frontend.scan_types.Key.KKind := by simpa using w56.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w56.symm
          subst hk
          key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
        subst hk
        have gk1 : ¬ kl.val = 1 := by scalar_tac
        have gk4 : ¬ kl.val = 4 := by scalar_tac
        key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 108 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s29, hs29, w57⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v29, hv29, w58⟩ := bind_eq_ok_iff.mp w57
      have q29 := key_lit (cs := [108, 97, 109]) hj hs29
        (by simp [frontend.scan_fast.key_at.S_LAM]) (by decide) hv29
      split at w58
      · have hk : k = frontend.scan_types.Key.KLam := by simpa using w58.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w58.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s30, hs30, w59⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v30, hv30, w60⟩ := bind_eq_ok_iff.mp w59
        have q30 := key_lit (cs := [108, 101, 116, 69]) hj hs30
          (by simp [frontend.scan_fast.key_at.S_LETE]) (by decide) hv30
        split at w60
        · have hk : k = frontend.scan_types.Key.KLetE := by simpa using w60.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w60.symm
          subst hk
          key_close
      · split at w00
        · rename_i hkl
          subst hkl
          obtain ⟨s31, hs31, w61⟩ := bind_eq_ok_iff.mp w00
          obtain ⟨v31, hv31, w62⟩ := bind_eq_ok_iff.mp w61
          have q31 := key_lit (cs := [108, 101, 118, 101, 108, 80, 97, 114, 97, 109, 115]) hj hs31
            (by simp [frontend.scan_fast.key_at.S_LEVELPARAMS]) (by decide) hv31
          split at w62
          · have hk : k = frontend.scan_types.Key.KLevelParams := by simpa using w62.symm
            subst hk
            key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w62.symm
            subst hk
            key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
          subst hk
          have gk3 : ¬ kl.val = 3 := by scalar_tac
          have gk4 : ¬ kl.val = 4 := by scalar_tac
          have gk11 : ¬ kl.val = 11 := by scalar_tac
          key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 109 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s32, hs32, w63⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v32, hv32, w64⟩ := bind_eq_ok_iff.mp w63
      have q32 := key_lit (cs := [109, 97, 120]) hj hs32
        (by simp [frontend.scan_fast.key_at.S_MAX]) (by decide) hv32
      split at w64
      · have hk : k = frontend.scan_types.Key.KMax := by simpa using w64.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w64.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s33, hs33, w65⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v33, hv33, w66⟩ := bind_eq_ok_iff.mp w65
        have q33 := key_lit (cs := [109, 101, 116, 97]) hj hs33
          (by simp [frontend.scan_fast.key_at.S_META]) (by decide) hv33
        split at w66
        · have hk : k = frontend.scan_types.Key.KMeta := by simpa using w66.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w66.symm
          subst hk
          key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
        subst hk
        have gk3 : ¬ kl.val = 3 := by scalar_tac
        have gk4 : ¬ kl.val = 4 := by scalar_tac
        key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 110 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s34, hs34, w67⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v34, hv34, w68⟩ := bind_eq_ok_iff.mp w67
      have q34 := key_lit (cs := [110, 117, 109]) hj hs34
        (by simp [frontend.scan_fast.key_at.S_NUM]) (by decide) hv34
      split at w68
      · have hk : k = frontend.scan_types.Key.KNum := by simpa using w68.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w68.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s35, hs35, w69⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v35, hv35, w70⟩ := bind_eq_ok_iff.mp w69
        have q35 := key_lit (cs := [110, 97, 109, 101]) hj hs35
          (by simp [frontend.scan_fast.key_at.S_NAME]) (by decide) hv35
        split at w70
        · have hk : k = frontend.scan_types.Key.KName := by simpa using w70.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w70.symm
          subst hk
          key_close
      · split at w00
        · rename_i hkl
          subst hkl
          obtain ⟨s36, hs36, w71⟩ := bind_eq_ok_iff.mp w00
          obtain ⟨v36, hv36, w72⟩ := bind_eq_ok_iff.mp w71
          have q36 := key_lit (cs := [110, 97, 116, 86, 97, 108]) hj hs36
            (by simp [frontend.scan_fast.key_at.S_NATVAL]) (by decide) hv36
          split at w72
          · have hk : k = frontend.scan_types.Key.KNatVal := by simpa using w72.symm
            subst hk
            key_close
          · obtain ⟨s37, hs37, w73⟩ := bind_eq_ok_iff.mp w72
            obtain ⟨v37, hv37, w74⟩ := bind_eq_ok_iff.mp w73
            have q37 := key_lit (cs := [110, 111, 110, 100, 101, 112]) hj hs37
              (by simp [frontend.scan_fast.key_at.S_NONDEP]) (by decide) hv37
            split at w74
            · have hk : k = frontend.scan_types.Key.KNondep := by simpa using w74.symm
              subst hk
              key_close
            · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w74.symm
              subst hk
              key_close
        · split at w00
          · rename_i hkl
            subst hkl
            obtain ⟨s38, hs38, w75⟩ := bind_eq_ok_iff.mp w00
            obtain ⟨v38, hv38, w76⟩ := bind_eq_ok_iff.mp w75
            have q38 := key_lit (cs := [110, 102, 105, 101, 108, 100, 115]) hj hs38
              (by simp [frontend.scan_fast.key_at.S_NFIELDS]) (by decide) hv38
            split at w76
            · have hk : k = frontend.scan_types.Key.KNfields := by simpa using w76.symm
              subst hk
              key_close
            · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w76.symm
              subst hk
              key_close
          · split at w00
            · rename_i hkl
              subst hkl
              obtain ⟨s39, hs39, w77⟩ := bind_eq_ok_iff.mp w00
              obtain ⟨v39, hv39, w78⟩ := bind_eq_ok_iff.mp w77
              have q39 := key_lit (cs := [110, 117, 109, 70, 105, 101, 108, 100, 115]) hj hs39
                (by simp [frontend.scan_fast.key_at.S_NUMFIELDS]) (by decide) hv39
              split at w78
              · have hk : k = frontend.scan_types.Key.KNumFields := by simpa using w78.symm
                subst hk
                key_close
              · obtain ⟨s40, hs40, w79⟩ := bind_eq_ok_iff.mp w78
                obtain ⟨v40, hv40, w80⟩ := bind_eq_ok_iff.mp w79
                have q40 := key_lit (cs := [110, 117, 109, 77, 105, 110, 111, 114, 115]) hj hs40
                  (by simp [frontend.scan_fast.key_at.S_NUMMINORS]) (by decide) hv40
                split at w80
                · have hk : k = frontend.scan_types.Key.KNumMinors := by simpa using w80.symm
                  subst hk
                  key_close
                · obtain ⟨s41, hs41, w81⟩ := bind_eq_ok_iff.mp w80
                  obtain ⟨v41, hv41, w82⟩ := bind_eq_ok_iff.mp w81
                  have q41 := key_lit (cs := [110, 117, 109, 78, 101, 115, 116, 101, 100]) hj hs41
                    (by simp [frontend.scan_fast.key_at.S_NUMNESTED]) (by decide) hv41
                  split at w82
                  · have hk : k = frontend.scan_types.Key.KNumNested := by simpa using w82.symm
                    subst hk
                    key_close
                  · obtain ⟨s42, hs42, w83⟩ := bind_eq_ok_iff.mp w82
                    obtain ⟨v42, hv42, w84⟩ := bind_eq_ok_iff.mp w83
                    have q42 := key_lit (cs := [110, 117, 109, 80, 97, 114, 97, 109, 115]) hj hs42
                      (by simp [frontend.scan_fast.key_at.S_NUMPARAMS]) (by decide) hv42
                    split at w84
                    · have hk : k = frontend.scan_types.Key.KNumParams := by simpa using w84.symm
                      subst hk
                      key_close
                    · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w84.symm
                      subst hk
                      key_close
            · split at w00
              · rename_i hkl
                subst hkl
                obtain ⟨s43, hs43, w85⟩ := bind_eq_ok_iff.mp w00
                obtain ⟨v43, hv43, w86⟩ := bind_eq_ok_iff.mp w85
                have q43 := key_lit (cs := [110, 117, 109, 73, 110, 100, 105, 99, 101, 115]) hj hs43
                  (by simp [frontend.scan_fast.key_at.S_NUMINDICES]) (by decide) hv43
                split at w86
                · have hk : k = frontend.scan_types.Key.KNumIndices := by simpa using w86.symm
                  subst hk
                  key_close
                · obtain ⟨s44, hs44, w87⟩ := bind_eq_ok_iff.mp w86
                  obtain ⟨v44, hv44, w88⟩ := bind_eq_ok_iff.mp w87
                  have q44 := key_lit (cs := [110, 117, 109, 77, 111, 116, 105, 118, 101, 115]) hj hs44
                    (by simp [frontend.scan_fast.key_at.S_NUMMOTIVES]) (by decide) hv44
                  split at w88
                  · have hk : k = frontend.scan_types.Key.KNumMotives := by simpa using w88.symm
                    subst hk
                    key_close
                  · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w88.symm
                    subst hk
                    key_close
              · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
                subst hk
                have gk3 : ¬ kl.val = 3 := by scalar_tac
                have gk4 : ¬ kl.val = 4 := by scalar_tac
                have gk6 : ¬ kl.val = 6 := by scalar_tac
                have gk7 : ¬ kl.val = 7 := by scalar_tac
                have gk9 : ¬ kl.val = 9 := by scalar_tac
                have gk10 : ¬ kl.val = 10 := by scalar_tac
                key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 111 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s45, hs45, w89⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v45, hv45, w90⟩ := bind_eq_ok_iff.mp w89
      have q45 := key_lit (cs := [111, 112, 97, 113, 117, 101]) hj hs45
        (by simp [frontend.scan_fast.key_at.S_OPAQUE]) (by decide) hv45
      split at w90
      · have hk : k = frontend.scan_types.Key.KOpaque := by simpa using w90.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w90.symm
        subst hk
        key_close
    · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
      subst hk
      have gk6 : ¬ kl.val = 6 := by scalar_tac
      key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 112 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s46, hs46, w91⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v46, hv46, w92⟩ := bind_eq_ok_iff.mp w91
      have q46 := key_lit (cs := [112, 119]) hj hs46
        (by simp [frontend.scan_fast.key_at.S_PW]) (by decide) hv46
      split at w92
      · have hk : k = frontend.scan_types.Key.KPw := by simpa using w92.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w92.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s47, hs47, w93⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v47, hv47, w94⟩ := bind_eq_ok_iff.mp w93
        have q47 := key_lit (cs := [112, 114, 101]) hj hs47
          (by simp [frontend.scan_fast.key_at.S_PRE]) (by decide) hv47
        split at w94
        · have hk : k = frontend.scan_types.Key.KPre := by simpa using w94.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w94.symm
          subst hk
          key_close
      · split at w00
        · rename_i hkl
          subst hkl
          obtain ⟨s48, hs48, w95⟩ := bind_eq_ok_iff.mp w00
          obtain ⟨v48, hv48, w96⟩ := bind_eq_ok_iff.mp w95
          have q48 := key_lit (cs := [112, 114, 111, 106]) hj hs48
            (by simp [frontend.scan_fast.key_at.S_PROJ]) (by decide) hv48
          split at w96
          · have hk : k = frontend.scan_types.Key.KProj := by simpa using w96.symm
            subst hk
            key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w96.symm
            subst hk
            key_close
        · split at w00
          · rename_i hkl
            subst hkl
            obtain ⟨s49, hs49, w97⟩ := bind_eq_ok_iff.mp w00
            obtain ⟨v49, hv49, w98⟩ := bind_eq_ok_iff.mp w97
            have q49 := key_lit (cs := [112, 97, 114, 97, 109]) hj hs49
              (by simp [frontend.scan_fast.key_at.S_PARAM]) (by decide) hv49
            split at w98
            · have hk : k = frontend.scan_types.Key.KParam := by simpa using w98.symm
              subst hk
              key_close
            · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w98.symm
              subst hk
              key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
            subst hk
            have gk2 : ¬ kl.val = 2 := by scalar_tac
            have gk3 : ¬ kl.val = 3 := by scalar_tac
            have gk4 : ¬ kl.val = 4 := by scalar_tac
            have gk5 : ¬ kl.val = 5 := by scalar_tac
            key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 113 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s50, hs50, w99⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v50, hv50, w100⟩ := bind_eq_ok_iff.mp w99
      have q50 := key_lit (cs := [113, 117, 111, 116]) hj hs50
        (by simp [frontend.scan_fast.key_at.S_QUOT]) (by decide) hv50
      split at w100
      · have hk : k = frontend.scan_types.Key.KQuot := by simpa using w100.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w100.symm
        subst hk
        key_close
    · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
      subst hk
      have gk4 : ¬ kl.val = 4 := by scalar_tac
      key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 114 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s51, hs51, w101⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v51, hv51, w102⟩ := bind_eq_ok_iff.mp w101
      have q51 := key_lit (cs := [114, 104, 115]) hj hs51
        (by simp [frontend.scan_fast.key_at.S_RHS]) (by decide) hv51
      split at w102
      · have hk : k = frontend.scan_types.Key.KRhs := by simpa using w102.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w102.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s52, hs52, w103⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v52, hv52, w104⟩ := bind_eq_ok_iff.mp w103
        have q52 := key_lit (cs := [114, 101, 99, 115]) hj hs52
          (by simp [frontend.scan_fast.key_at.S_RECS]) (by decide) hv52
        split at w104
        · have hk : k = frontend.scan_types.Key.KRecs := by simpa using w104.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w104.symm
          subst hk
          key_close
      · split at w00
        · rename_i hkl
          subst hkl
          obtain ⟨s53, hs53, w105⟩ := bind_eq_ok_iff.mp w00
          obtain ⟨v53, hv53, w106⟩ := bind_eq_ok_iff.mp w105
          have q53 := key_lit (cs := [114, 117, 108, 101, 115]) hj hs53
            (by simp [frontend.scan_fast.key_at.S_RULES]) (by decide) hv53
          split at w106
          · have hk : k = frontend.scan_types.Key.KRules := by simpa using w106.symm
            subst hk
            key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w106.symm
            subst hk
            key_close
        · split at w00
          · rename_i hkl
            subst hkl
            obtain ⟨s54, hs54, w107⟩ := bind_eq_ok_iff.mp w00
            obtain ⟨v54, hv54, w108⟩ := bind_eq_ok_iff.mp w107
            have q54 := key_lit (cs := [114, 101, 103, 117, 108, 97, 114]) hj hs54
              (by simp [frontend.scan_fast.key_at.S_REGULAR]) (by decide) hv54
            split at w108
            · have hk : k = frontend.scan_types.Key.KRegular := by simpa using w108.symm
              subst hk
              key_close
            · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w108.symm
              subst hk
              key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
            subst hk
            have gk3 : ¬ kl.val = 3 := by scalar_tac
            have gk4 : ¬ kl.val = 4 := by scalar_tac
            have gk5 : ¬ kl.val = 5 := by scalar_tac
            have gk7 : ¬ kl.val = 7 := by scalar_tac
            key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 115 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s55, hs55, w109⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v55, hv55, w110⟩ := bind_eq_ok_iff.mp w109
      have q55 := key_lit (cs := [115, 116, 114]) hj hs55
        (by simp [frontend.scan_fast.key_at.S_STR]) (by decide) hv55
      split at w110
      · have hk : k = frontend.scan_types.Key.KStr := by simpa using w110.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w110.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s56, hs56, w111⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v56, hv56, w112⟩ := bind_eq_ok_iff.mp w111
        have q56 := key_lit (cs := [115, 111, 114, 116]) hj hs56
          (by simp [frontend.scan_fast.key_at.S_SORT]) (by decide) hv56
        split at w112
        · have hk : k = frontend.scan_types.Key.KSort := by simpa using w112.symm
          subst hk
          key_close
        · obtain ⟨s57, hs57, w113⟩ := bind_eq_ok_iff.mp w112
          obtain ⟨v57, hv57, w114⟩ := bind_eq_ok_iff.mp w113
          have q57 := key_lit (cs := [115, 117, 99, 99]) hj hs57
            (by simp [frontend.scan_fast.key_at.S_SUCC]) (by decide) hv57
          split at w114
          · have hk : k = frontend.scan_types.Key.KSucc := by simpa using w114.symm
            subst hk
            key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w114.symm
            subst hk
            key_close
      · split at w00
        · rename_i hkl
          subst hkl
          obtain ⟨s58, hs58, w115⟩ := bind_eq_ok_iff.mp w00
          obtain ⟨v58, hv58, w116⟩ := bind_eq_ok_iff.mp w115
          have q58 := key_lit (cs := [115, 97, 102, 101, 116, 121]) hj hs58
            (by simp [frontend.scan_fast.key_at.S_SAFETY]) (by decide) hv58
          split at w116
          · have hk : k = frontend.scan_types.Key.KSafety := by simpa using w116.symm
            subst hk
            key_close
          · obtain ⟨s59, hs59, w117⟩ := bind_eq_ok_iff.mp w116
            obtain ⟨v59, hv59, w118⟩ := bind_eq_ok_iff.mp w117
            have q59 := key_lit (cs := [115, 116, 114, 86, 97, 108]) hj hs59
              (by simp [frontend.scan_fast.key_at.S_STRVAL]) (by decide) hv59
            split at w118
            · have hk : k = frontend.scan_types.Key.KStrVal := by simpa using w118.symm
              subst hk
              key_close
            · obtain ⟨s60, hs60, w119⟩ := bind_eq_ok_iff.mp w118
              obtain ⟨v60, hv60, w120⟩ := bind_eq_ok_iff.mp w119
              have q60 := key_lit (cs := [115, 116, 114, 117, 99, 116]) hj hs60
                (by simp [frontend.scan_fast.key_at.S_STRUCT]) (by decide) hv60
              split at w120
              · have hk : k = frontend.scan_types.Key.KStruct := by simpa using w120.symm
                subst hk
                key_close
              · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w120.symm
                subst hk
                key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
          subst hk
          have gk3 : ¬ kl.val = 3 := by scalar_tac
          have gk4 : ¬ kl.val = 4 := by scalar_tac
          have gk6 : ¬ kl.val = 6 := by scalar_tac
          key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 116 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s61, hs61, w121⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v61, hv61, w122⟩ := bind_eq_ok_iff.mp w121
      have q61 := key_lit (cs := [116, 104, 109]) hj hs61
        (by simp [frontend.scan_fast.key_at.S_THM]) (by decide) hv61
      split at w122
      · have hk : k = frontend.scan_types.Key.KThm := by simpa using w122.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w122.symm
        subst hk
        key_close
    · split at w00
      · rename_i hkl
        subst hkl
        obtain ⟨s62, hs62, w123⟩ := bind_eq_ok_iff.mp w00
        obtain ⟨v62, hv62, w124⟩ := bind_eq_ok_iff.mp w123
        have q62 := key_lit (cs := [116, 121, 112, 101]) hj hs62
          (by simp [frontend.scan_fast.key_at.S_TYPE]) (by decide) hv62
        split at w124
        · have hk : k = frontend.scan_types.Key.KType := by simpa using w124.symm
          subst hk
          key_close
        · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w124.symm
          subst hk
          key_close
      · split at w00
        · rename_i hkl
          subst hkl
          obtain ⟨s63, hs63, w125⟩ := bind_eq_ok_iff.mp w00
          obtain ⟨v63, hv63, w126⟩ := bind_eq_ok_iff.mp w125
          have q63 := key_lit (cs := [116, 121, 112, 101, 115]) hj hs63
            (by simp [frontend.scan_fast.key_at.S_TYPES]) (by decide) hv63
          split at w126
          · have hk : k = frontend.scan_types.Key.KTypes := by simpa using w126.symm
            subst hk
            key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w126.symm
            subst hk
            key_close
        · split at w00
          · rename_i hkl
            subst hkl
            obtain ⟨s64, hs64, w127⟩ := bind_eq_ok_iff.mp w00
            obtain ⟨v64, hv64, w128⟩ := bind_eq_ok_iff.mp w127
            have q64 := key_lit (cs := [116, 121, 112, 101, 78, 97, 109, 101]) hj hs64
              (by simp [frontend.scan_fast.key_at.S_TYPENAME]) (by decide) hv64
            split at w128
            · have hk : k = frontend.scan_types.Key.KTypeName := by simpa using w128.symm
              subst hk
              key_close
            · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w128.symm
              subst hk
              key_close
          · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
            subst hk
            have gk3 : ¬ kl.val = 3 := by scalar_tac
            have gk4 : ¬ kl.val = 4 := by scalar_tac
            have gk5 : ¬ kl.val = 5 := by scalar_tac
            have gk8 : ¬ kl.val = 8 := by scalar_tac
            key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 117 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s65, hs65, w129⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v65, hv65, w130⟩ := bind_eq_ok_iff.mp w129
      have q65 := key_lit (cs := [117, 115]) hj hs65
        (by simp [frontend.scan_fast.key_at.S_US]) (by decide) hv65
      split at w130
      · have hk : k = frontend.scan_types.Key.KUs := by simpa using w130.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w130.symm
        subst hk
        key_close
    · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
      subst hk
      have gk2 : ¬ kl.val = 2 := by scalar_tac
      key_close
  · have hcb' : byteAt (absBytes b) (absPos i + 1) = 118 := by rw [hcb]; rfl
    rw [hcb']
    simp only []
    split at w00
    · rename_i hkl
      subst hkl
      obtain ⟨s66, hs66, w131⟩ := bind_eq_ok_iff.mp w00
      obtain ⟨v66, hv66, w132⟩ := bind_eq_ok_iff.mp w131
      have q66 := key_lit (cs := [118, 97, 108, 117, 101]) hj hs66
        (by simp [frontend.scan_fast.key_at.S_VALUE]) (by decide) hv66
      split at w132
      · have hk : k = frontend.scan_types.Key.KValue := by simpa using w132.symm
        subst hk
        key_close
      · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w132.symm
        subst hk
        key_close
    · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
      subst hk
      have gk5 : ¬ kl.val = 5 := by scalar_tac
      key_close
  · have hk : k = frontend.scan_types.Key.KUnknown := by simpa using w00.symm
    subst hk
    have d97 : ¬ c.val = 97 := by
      have d : ¬ c = 97#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d98 : ¬ c.val = 98 := by
      have d : ¬ c = 98#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d99 : ¬ c.val = 99 := by
      have d : ¬ c = 99#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d100 : ¬ c.val = 100 := by
      have d : ¬ c = 100#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d102 : ¬ c.val = 102 := by
      have d : ¬ c = 102#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d104 : ¬ c.val = 104 := by
      have d : ¬ c = 104#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d105 : ¬ c.val = 105 := by
      have d : ¬ c = 105#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d107 : ¬ c.val = 107 := by
      have d : ¬ c = 107#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d108 : ¬ c.val = 108 := by
      have d : ¬ c = 108#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d109 : ¬ c.val = 109 := by
      have d : ¬ c = 109#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d110 : ¬ c.val = 110 := by
      have d : ¬ c = 110#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d111 : ¬ c.val = 111 := by
      have d : ¬ c = 111#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d112 : ¬ c.val = 112 := by
      have d : ¬ c = 112#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d113 : ¬ c.val = 113 := by
      have d : ¬ c = 113#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d114 : ¬ c.val = 114 := by
      have d : ¬ c = 114#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d115 : ¬ c.val = 115 := by
      have d : ¬ c = 115#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d116 : ¬ c.val = 116 := by
      have d : ¬ c = 116#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d117 : ¬ c.val = 117 := by
      have d : ¬ c = 117#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    have d118 : ¬ c.val = 118 := by
      have d : ¬ c = 118#u8 := by assumption
      intro hz; exact d (by scalar_tac)
    split
    all_goals first
      | rfl
      | (exfalso; rename_i hx; rw [hcb] at hx
         simp only [absByte_eq_iff] at hx; simp at hx; omega)


/-! ## `value_at`

`scan_fast.rs:711-718` against `Scan/Fast.lean:448-453` (`valueAt`). -/

/-- **`value_at` refines `valueAt`** (`Scan/Fast.lean:448-453`). -/
theorem value_at_refines {b : Slice Std.U8} {i ke v : Std.Usize}
    (h : frontend.scan_fast.value_at b i ke = ok v) :
    absPos v = valueAt (absBytes b) (absPos i) (absPos ke) := by
  rw [frontend.scan_fast.value_at] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  simp only [valueAt]
  rw [← absPos_add_one hi1, ← skip_ws_refines hp, ← byte_at_refines hc]
  by_cases h58 : c = 58#u8
  · rw [if_pos h58] at h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
    have hb : (absByte c == 58) = true := by simp; scalar_tac
    rw [hb, if_pos rfl, ← absPos_add_one hi3]
    exact skip_ws_refines h
  · rw [if_neg h58] at h
    have hb : (absByte c == 58) = false := by simp; scalar_tac
    rw [hb]
    have : i = v := by simpa using h
    rw [this]; simp

/-! ## `num_end`

`scan_fast.rs:740-749` against `Scan/Fast.lean:483-494` (`numEnd`): a digit
run with JSON's leading-zero rule.  The port spells `byte_at b i == 48 && e !=
i + 1` as two nested `if`s, and computes `i + 1` only inside the `48` arm --
so a run that would overflow the cursor there is a port failure, which claims
nothing. -/

/-- **`num_end` refines `numEnd`** (`Scan/Fast.lean:483-494`). -/
theorem num_end_refines {b : Slice Std.U8} {i e : Std.Usize}
    (h : frontend.scan_fast.num_end b i = ok e) :
    absPos e = numEnd (absBytes b) (absPos i) := by
  rw [frontend.scan_fast.num_end] at h
  obtain ⟨d, hd, h⟩ := bind_eq_ok_iff.mp h
  simp only [numEnd, ← skip_digits_refines hd]
  by_cases hdi : d = i
  · rw [if_pos hdi] at h
    have hb : (absPos d == absPos i) = true := by simp; scalar_tac
    rw [hb, if_pos rfl]
    have : i = e := by simpa using h
    rw [this]
  · rw [if_neg hdi] at h
    have hb : (absPos d == absPos i) = false := by simp; scalar_tac
    rw [hb, if_neg (by simp)]
    obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
    rw [← byte_at_refines hc]
    by_cases h48 : c = 48#u8
    · rw [if_pos h48] at h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hb48 : (absByte c == 48) = true := by simp; scalar_tac
      rw [hb48, Bool.true_and, ← absPos_add_one hi2]
      by_cases hne : (d != i2) = true
      · rw [if_pos hne] at h
        have : (absPos d != absPos i2) = true := by
          simp_all only [bne_iff_ne, ne_eq]
          intro hc2; exact hne (by have := absPos_inj hc2; scalar_tac)
        rw [this, if_pos rfl]
        have : i = e := by simpa using h
        rw [this]
      · rw [if_neg hne] at h
        have hdi2 : d.val = i2.val := by simpa using hne
        have : (absPos d != absPos i2) = false := by
          simp; rw [absPos, absPos, hdi2]
        rw [this, if_neg (by simp)]
        have : d = e := by simpa using h
        rw [this]
    · rw [if_neg h48] at h
      have hb48 : (absByte c == 48) = false := by simp; scalar_tac
      rw [hb48, Bool.false_and, if_neg (by simp)]
      have : d = e := by simpa using h
      rw [this]

/-! ## The port's own two guards

`prog` and `dup` are con-ron's factoring of the `noProgress` and
`duplicateKey` tests every slot of every `scan*Loop` of `Scan/Fast.lean`
writes inline (`scan_fast.rs:1440-1450`, "con-leche: none"). -/

/-- **`prog` is con-leche's `i < e` guard.** -/
theorem prog_eq {ks e : Std.Usize} {r : Bool}
    (h : frontend.scan_fast.prog ks e = ok r) : r = decide (absPos ks < absPos e) := by
  rw [frontend.scan_fast.prog] at h
  have hr : decide (ks < e) = r := by simpa using h
  rw [← hr]
  simp [absPos_lt]

/-- A port `u32` seen-mask as con-leche's. -/
def absU32 (x : Std.U32) : UInt32 := UInt32.ofBitVec x.bv

@[simp] theorem absU32_toNat (x : Std.U32) : (absU32 x).toNat = x.val := rfl

/-- The bit operations commute with the abstraction definitionally -- which is
what every `seen`-bitset step of every object loop rides on. -/
theorem absU32_and (a b : Std.U32) : absU32 (a &&& b) = absU32 a &&& absU32 b := rfl

theorem absU32_or (a b : Std.U32) : absU32 (a ||| b) = absU32 a ||| absU32 b := rfl

theorem absU32_inj {a b : Std.U32} (h : absU32 a = absU32 b) : a = b := by
  have hv : a.val = b.val := by
    have := congrArg UInt32.toNat h
    rwa [absU32_toNat, absU32_toNat] at this
  scalar_tac

@[simp] theorem absU32_beq (a b : Std.U32) : (absU32 a == absU32 b) = (a == b) := by
  by_cases h : a = b
  · simp [h]
  · have h1 : absU32 a ≠ absU32 b := fun hc => h (absU32_inj hc)
    simp [h, h1]

/-- **`dup` is con-leche's `(seen &&& bit) != 0`.** -/
theorem dup_eq {seen bit : Std.U32} {r : Bool}
    (h : frontend.scan_fast.dup seen bit = ok r) :
    r = ((absU32 seen &&& absU32 bit) != 0) := by
  rw [frontend.scan_fast.dup] at h
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  have hxv : x.val = seen.val &&& bit.val := by
    have hxe : seen &&& bit = x := by simpa using hx
    rw [← hxe, Std.UScalar.val_and]
  have hr : (x != 0#u32) = r := by simpa using h
  have hand : (absU32 seen &&& absU32 bit).toNat = x.val := by
    rw [UInt32.toNat_and, absU32_toNat, absU32_toNat, hxv]
  rw [← hr]
  by_cases hc : x = 0#u32
  · have h0 : (absU32 seen &&& absU32 bit) = 0 := by
      apply UInt32.toNat_inj.mp; rw [hand, hc]; rfl
    rw [hc, h0]; simp
  · have h0 : (absU32 seen &&& absU32 bit) ≠ 0 := by
      intro he
      apply hc
      have hz : (0:UInt32).toNat = 0 := rfl
      rw [he, hz] at hand
      scalar_tac
    have e1 : (x != 0#u32) = true := by simp [hc]
    have e2 : ((absU32 seen &&& absU32 bit) != 0) = true := by simp [h0]
    rw [e1, e2]

/-! ## `newline_from`

`scan_fast.rs:4125-4134` against `Scan/Fast.lean:2639-2642` (`newlineFrom`). -/

private theorem newlineFrom_eq (b : Slice Std.U8) (i : Std.Usize) :
    newlineFrom (absBytes b) (absPos i) =
      (if i.val < b.val.length then
        (absByte (pByteAt b i.val) == 10 || newlineFrom (absBytes b) (absPos i + 1))
       else false) := by
  rw [newlineFrom]
  by_cases h : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_absPos]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]

private theorem newline_from_loop_refines {b : Slice Std.U8} (f : Nat) :
    ∀ (i : Std.Usize) (r : Bool), b.val.length - i.val ≤ f →
      frontend.scan_fast.newline_from_loop b i = ok r →
      r = newlineFrom (absBytes b) (absPos i) := by
  induction f with
  | zero =>
    intro i r hf h
    rw [frontend.scan_fast.newline_from_loop.eq_def] at h
    rw [if_neg (show ¬ (i < Slice.len b) by scalar_tac)] at h
    rw [newlineFrom_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
    simpa using h.symm
  | succ f ih =>
    intro i r hf h
    rw [frontend.scan_fast.newline_from_loop.eq_def] at h
    by_cases hlt : i < Slice.len b
    · rw [if_pos hlt] at h
      have hi : i.val < b.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hc' : c = pByteAt b i.val := by
        rw [slice_index_ok hi] at hc; rw [pByteAt, dif_pos hi]; simpa using hc.symm
      rw [newlineFrom_eq, if_pos hi, ← hc']
      by_cases h10 : c = 10#u8
      · rw [if_pos h10] at h
        have hb : (absByte c == 10) = true := by simp; scalar_tac
        rw [hb, Bool.true_or]
        simpa using h.symm
      · rw [if_neg h10] at h
        have hb : (absByte c == 10) = false := by simp; scalar_tac
        rw [hb, Bool.false_or]
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        have := usize_add_one_inv hi1
        rw [← absPos_add_one hi1]
        exact ih i1 r (by omega) h
    · rw [if_neg hlt] at h
      rw [newlineFrom_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
      simpa using h.symm

/-- **`newline_from` refines `newlineFrom`** (`Scan/Fast.lean:2639-2642`). -/
theorem newline_from_refines {b : Slice Std.U8} {i : Std.Usize} {r : Bool}
    (h : frontend.scan_fast.newline_from b i = ok r) :
    r = newlineFrom (absBytes b) (absPos i) :=
  newline_from_loop_refines (b.val.length - i.val) i r (le_refl _) h

/-! ## `has_escape`

`scan_fast.rs:825-834` against `Scan/Fast.lean:525-534` (`hasEscape`). -/

private theorem hasEscape_eq (b : Slice Std.U8) (j e : Std.Usize) :
    hasEscape (absBytes b) (absPos j) (absPos e) =
      (if j.val < b.val.length then
        (if j.val < e.val then
          (if absByte (pByteAt b j.val) == 92 then true
           else hasEscape (absBytes b) (absPos j + 1) (absPos e))
         else false)
       else false) := by
  rw [hasEscape]
  by_cases h : j.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_absPos]
    by_cases h2 : j.val < e.val
    · rw [if_pos (absPos_lt.mpr h2), if_pos h2]
    · rw [if_neg (fun hc => h2 (absPos_lt.mp hc)), if_neg h2]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]

private theorem has_escape_loop_refines {b : Slice Std.U8} (f : Nat) :
    ∀ (j e : Std.Usize) (r : Bool), b.val.length - j.val ≤ f →
      frontend.scan_fast.has_escape_loop b e j = ok r →
      r = hasEscape (absBytes b) (absPos j) (absPos e) := by
  induction f with
  | zero =>
    intro j e r hf h
    rw [frontend.scan_fast.has_escape_loop.eq_def] at h
    rw [if_neg (show ¬ (j < Slice.len b) by scalar_tac)] at h
    rw [hasEscape_eq, if_neg (show ¬ j.val < b.val.length by scalar_tac)]
    simpa using h.symm
  | succ f ih =>
    intro j e r hf h
    rw [frontend.scan_fast.has_escape_loop.eq_def] at h
    by_cases hlt : j < Slice.len b
    · rw [if_pos hlt] at h
      have hj : j.val < b.val.length := by scalar_tac
      rw [hasEscape_eq, if_pos hj]
      by_cases hje : j < e
      · rw [if_pos hje] at h
        rw [if_pos (show j.val < e.val by scalar_tac)]
        obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
        have hc' : c = pByteAt b j.val := by
          rw [slice_index_ok hj] at hc; rw [pByteAt, dif_pos hj]; simpa using hc.symm
        rw [← hc']
        by_cases h92 : c = 92#u8
        · rw [if_pos h92] at h
          have hb : (absByte c == 92) = true := by simp; scalar_tac
          rw [if_pos (by simpa using hb)]
          simpa using h.symm
        · rw [if_neg h92] at h
          have hb : (absByte c == 92) = false := by simp; scalar_tac
          rw [if_neg (by simp [hb])]
          obtain ⟨j1, hj1, h⟩ := bind_eq_ok_iff.mp h
          have := usize_add_one_inv hj1
          rw [← absPos_add_one hj1]
          exact ih j1 e r (by omega) h
      · rw [if_neg hje] at h
        rw [if_neg (show ¬ j.val < e.val by scalar_tac)]
        simpa using h.symm
    · rw [if_neg hlt] at h
      rw [hasEscape_eq, if_neg (show ¬ j.val < b.val.length by scalar_tac)]
      simpa using h.symm

/-- **`has_escape` refines `hasEscape`** (`Scan/Fast.lean:525-534`). -/
theorem has_escape_refines {b : Slice Std.U8} {j e : Std.Usize} {r : Bool}
    (h : frontend.scan_fast.has_escape b j e = ok r) :
    r = hasEscape (absBytes b) (absPos j) (absPos e) :=
  has_escape_loop_refines (b.val.length - j.val) j e r (le_refl _) h

/-! ## `str_close`

`scan_fast.rs:799-821` against `Scan/Fast.lean:502-523` (`strClose`).  The port
steps `j + 2` over an escape where the Lean writes `j + 1 + 1`. -/

/-- The port's two-byte step over an escape, as con-leche's. -/
private theorem absPos_add_two {i j : Std.Usize} (h : i + 2#usize = ok j) :
    absPos j = absPos i + 1 + 1 := by
  have hv : j.val = i.val + 2 := by
    have h2 := Std.UScalar.add_equiv i (2#usize)
    rw [h] at h2; simp at h2; scalar_tac
  have hb : i.val + 2 < USize.size := by have := usize_val_lt_size j; omega
  rw [uA1]
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, absPos_toNat, uT2, hv]
  exact (Nat.mod_eq_of_lt hb).symm

private theorem strClose_eq (b : Slice Std.U8) (j : Std.Usize) :
    strClose (absBytes b) (absPos j) =
      (if j.val < b.val.length then
        (if absByte (pByteAt b j.val) == 34 then absPos j
         else if absByte (pByteAt b j.val) == 92 then
           (if j.val + 1 < b.val.length then
             (if absByte (pByteAt b (j.val + 1)) < 32 then 0
              else strClose (absBytes b) (absPos j + 1 + 1))
            else 0)
         else if absByte (pByteAt b j.val) < 32 then 0
         else strClose (absBytes b) (absPos j + 1))
       else 0) := by
  rw [strClose]
  by_cases h : j.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_absPos]
    by_cases h34 : absByte (pByteAt b j.val) == 34
    · rw [if_pos h34, if_pos h34]
    · rw [if_neg h34, if_neg h34]
      by_cases h92 : absByte (pByteAt b j.val) == 92
      · rw [if_pos h92, if_pos h92]
        have hstep : (absPos j + 1).toNat = j.val + 1 := by
          rw [usizeStep (absBytes b) (absPos j) (absPos_lt_usize.mpr h), absPos_toNat]
        by_cases h2 : j.val + 1 < b.val.length
        · rw [dif_pos (by rw [pos_lt_usize, hstep]; exact h2), if_pos h2]
          rw [uget_pos, hstep]
        · rw [dif_neg (by rw [pos_lt_usize, hstep]; exact h2), if_neg h2]
      · rw [if_neg h92, if_neg h92]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]

private theorem str_close_loop_refines {b : Slice Std.U8} (f : Nat) :
    ∀ (j e : Std.Usize), b.val.length - j.val ≤ f →
      frontend.scan_fast.str_close_loop b j = ok e →
      absPos e = strClose (absBytes b) (absPos j) := by
  have hz : absPos (0#usize) = (0 : USize) := by simp [absPos]; rfl
  induction f with
  | zero =>
    intro j e hf h
    rw [frontend.scan_fast.str_close_loop.eq_def] at h
    rw [if_neg (show ¬ (j < Slice.len b) by scalar_tac)] at h
    rw [strClose_eq, if_neg (show ¬ j.val < b.val.length by scalar_tac)]
    have : 0#usize = e := by simpa using h
    rw [← this, hz]
  | succ f ih =>
    intro j e hf h
    rw [frontend.scan_fast.str_close_loop.eq_def] at h
    by_cases hlt : j < Slice.len b
    · rw [if_pos hlt] at h
      have hj : j.val < b.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hc' : c = pByteAt b j.val := by
        rw [slice_index_ok hj] at hc; rw [pByteAt, dif_pos hj]; simpa using hc.symm
      rw [strClose_eq, if_pos hj, ← hc']
      by_cases h34 : c = 34#u8
      · rw [if_pos h34] at h
        have hb : (absByte c == 34) = true := by simp; scalar_tac
        rw [hb, if_pos rfl]
        have : j = e := by simpa using h
        rw [this]
      · rw [if_neg h34] at h
        have hb : (absByte c == 34) = false := by simp; scalar_tac
        rw [hb, if_neg (by simp)]
        by_cases h92 : c = 92#u8
        · rw [if_pos h92] at h
          have hb2 : (absByte c == 92) = true := by simp; scalar_tac
          rw [hb2, if_pos rfl]
          obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
          have hi1v := usize_add_one_inv hi1
          by_cases hlt2 : i1 < Slice.len b
          · rw [if_pos hlt2] at h
            have hj2 : j.val + 1 < b.val.length := by scalar_tac
            rw [if_pos hj2]
            obtain ⟨c2, hc2, h⟩ := bind_eq_ok_iff.mp h
            have hc2' : c2 = pByteAt b (j.val + 1) := by
              rw [slice_index_ok (show i1.val < b.val.length by scalar_tac)] at hc2
              rw [pByteAt, dif_pos hj2]
              have : i1.val = j.val + 1 := hi1v
              simp only [this] at hc2
              simpa using hc2.symm
            rw [← hc2']
            by_cases h32 : c2 < 32#u8
            · rw [if_pos h32] at h
              rw [if_pos (by simp; scalar_tac)]
              have : 0#usize = e := by simpa using h
              rw [← this, hz]
            · rw [if_neg h32] at h
              rw [if_neg (by simp; scalar_tac)]
              obtain ⟨j1, hj1, h⟩ := bind_eq_ok_iff.mp h
              have hj1v : j1.val = j.val + 2 := by
                have h2 := Std.UScalar.add_equiv j (2#usize)
                rw [hj1] at h2; simp at h2; scalar_tac
              rw [← absPos_add_two hj1]
              exact ih j1 e (by omega) h
          · rw [if_neg hlt2] at h
            rw [if_neg (show ¬ j.val + 1 < b.val.length by scalar_tac)]
            have : 0#usize = e := by simpa using h
            rw [← this, hz]
        · rw [if_neg h92] at h
          have hb2 : (absByte c == 92) = false := by simp; scalar_tac
          rw [hb2, if_neg (by simp)]
          by_cases h32 : c < 32#u8
          · rw [if_pos h32] at h
            rw [if_pos (by simp; scalar_tac)]
            have : 0#usize = e := by simpa using h
            rw [← this, hz]
          · rw [if_neg h32] at h
            rw [if_neg (by simp; scalar_tac)]
            obtain ⟨j1, hj1, h⟩ := bind_eq_ok_iff.mp h
            have hj1v := usize_add_one_inv hj1
            rw [← absPos_add_one hj1]
            exact ih j1 e (by omega) h
    · rw [if_neg hlt] at h
      rw [strClose_eq, if_neg (show ¬ j.val < b.val.length by scalar_tac)]
      have : 0#usize = e := by simpa using h
      rw [← this, hz]

/-- **`str_close` refines `strClose`** (`Scan/Fast.lean:502-523`). -/
theorem str_close_refines {b : Slice Std.U8} {j e : Std.Usize}
    (h : frontend.scan_fast.str_close b j = ok e) :
    absPos e = strClose (absBytes b) (absPos j) :=
  str_close_loop_refines (b.val.length - j.val) j e (le_refl _) h


private theorem usize_small64 (n : Nat) (h : n ≤ 64) : n < USize.size := by
  have h2 : (64:Nat) < USize.size := by
    rw [USize.size]
    rcases System.Platform.numBits_eq with hb | hb <;> rw [hb] <;> norm_num
  omega

private theorem uT18 : ((18 : USize)).toNat = 18 := by
  simp [USize.toNat_ofNat, Nat.mod_eq_of_lt (usize_small64 18 (by norm_num))]

/-! ## `read_nat_at` -/

/-- `skipDigits` never goes backwards. -/
private theorem skipDigits_ge (b : Slice Std.U8) (f : Nat) :
    ∀ (k : Std.Usize), b.val.length - k.val ≤ f →
      k.val ≤ (skipDigits (absBytes b) (absPos k)).toNat := by
  induction f with
  | zero =>
    intro k hf
    rw [skipDigits_eq, if_neg (show ¬ k.val < b.val.length by omega), absPos_toNat]
  | succ f ih =>
    intro k hf
    by_cases hk : k.val < b.val.length
    · rw [skipDigits_eq, if_pos hk]
      by_cases hd : isDigit (absByte (pByteAt b k.val)) = true
      · rw [if_pos hd]
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_ok (i := k)
          (by have := Slice.length_ineq b; omega)
        rw [← absPos_add_one hk1]
        have := ih k1 (by omega)
        omega
      · rw [if_neg hd, absPos_toNat]
    · rw [skipDigits_eq, if_neg hk, absPos_toNat]

private theorem skipDigits_step {b : Slice Std.U8} {k k1 e : Std.Usize}
    (hk : k.val < b.val.length) (hlt : k.val < e.val) (hk1 : k1.val = k.val + 1)
    (h : skipDigits (absBytes b) (absPos k) = absPos e) :
    isDigit (absByte (pByteAt b k.val)) = true ∧
      skipDigits (absBytes b) (absPos k1) = absPos e := by
  rw [skipDigits_eq, if_pos hk] at h
  by_cases hd : isDigit (absByte (pByteAt b k.val)) = true
  · rw [if_pos hd] at h
    refine ⟨hd, ?_⟩
    have hb : (absPos k + 1).toNat = k.val + 1 := by
      rw [usizeStep (absBytes b) (absPos k) (absPos_lt_usize.mpr hk), absPos_toNat]
    have he : absPos k1 = absPos k + 1 := by
      apply USize.toNat_inj.mp; rw [absPos_toNat, hb, hk1]
    rw [he]; exact h
  · rw [if_neg hd] at h
    have := absPos_inj h
    omega

private theorem skipDigits_stop {b : Slice Std.U8} {k e : Std.Usize}
    (hk : k.val < b.val.length) (hge : e.val ≤ k.val)
    (h : skipDigits (absBytes b) (absPos k) = absPos e) :
    ¬ (isDigit (absByte (pByteAt b k.val)) = true) := by
  have hle : k.val ≤ e.val := by
    have := skipDigits_ge b (b.val.length - k.val) k (le_refl _)
    rw [h, absPos_toNat] at this; exact this
  intro hd
  rw [skipDigits_eq, if_pos hk, if_pos hd] at h
  obtain ⟨k1, hk1, hk1v⟩ := usize_add_ok (i := k) (by have := Slice.length_ineq b; omega)
  rw [← absPos_add_one hk1] at h
  have h2 := skipDigits_ge b (b.val.length - k1.val) k1 (le_refl _)
  rw [h, absPos_toNat] at h2
  omega

/-! ### The two accumulations, unfolded once -/

private theorem readNat64_eq (b : Slice Std.U8) (k e : Std.Usize) (accL : UInt64) :
    readNat64 (absBytes b) (absPos k) (absPos e) accL =
      (if k.val < b.val.length then
        (if k.val < e.val then
          readNat64 (absBytes b) (absPos k + 1) (absPos e)
            (accL * 10 + (absByte (pByteAt b k.val) - 48).toUInt64)
         else accL)
       else accL) := by
  rw [readNat64]
  by_cases h : k.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_absPos]
    by_cases h2 : k.val < e.val
    · rw [if_pos (absPos_lt.mpr h2), if_pos h2]
    · rw [if_neg (fun hc => h2 (absPos_lt.mp hc)), if_neg h2]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]

/-- **`readNat`, unfolded once at a port position** (`Scan/Fast.lean:103-112`). -/
theorem readNat_eq (b : Slice Std.U8) (k : Std.Usize) (acc : Nat) :
    readNat (absBytes b) (absPos k) acc =
      (if k.val < b.val.length then
        (if isDigit (absByte (pByteAt b k.val)) then
          readNat (absBytes b) (absPos k + 1)
            (acc * 10 + ((absByte (pByteAt b k.val)).toNat - 48))
         else acc)
       else acc) := by
  rw [readNat]
  by_cases h : k.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_absPos]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]

/-- **The machine-word accumulation is the `Nat` one while the run fits.**
`readNat64` wraps; it does not, on a run short enough that the value stays
below `2 ^ 64`, and the bound travels as `acc * 10 ^ d + 10 ^ d ≤ 2 ^ 64`. -/
private theorem readNat64_eq_readNat (b : Slice Std.U8) (f : Nat) :
    ∀ (k e : Std.Usize) (accL : UInt64) (accN : Nat),
      e.val - k.val ≤ f →
      skipDigits (absBytes b) (absPos k) = absPos e →
      k.val ≤ e.val →
      accL.toNat = accN →
      accN * 10 ^ (e.val - k.val) + 10 ^ (e.val - k.val) ≤ 2 ^ 64 →
      (readNat64 (absBytes b) (absPos k) (absPos e) accL).toNat
        = readNat (absBytes b) (absPos k) accN := by
  induction f with
  | zero =>
    intro k e accL accN hf hrun hle hacc hbd
    have hke : k.val = e.val := by omega
    rw [readNat64_eq, readNat_eq]
    by_cases hk : k.val < b.val.length
    · rw [if_pos hk, if_pos hk, if_neg (show ¬ k.val < e.val by omega),
        if_neg (skipDigits_stop hk (by omega) hrun), hacc]
    · rw [if_neg hk, if_neg hk, hacc]
  | succ f ih =>
    intro k e accL accN hf hrun hle hacc hbd
    by_cases hlt : k.val < e.val
    · have hk : k.val < b.val.length := by
        by_contra hc
        rw [skipDigits_eq, if_neg hc] at hrun
        have := absPos_inj hrun; omega
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_ok (i := k)
        (by have := Slice.length_ineq b; omega)
      obtain ⟨hd, hrun1⟩ := skipDigits_step hk hlt hk1v hrun
      have hdig : 48 ≤ (absByte (pByteAt b k.val)).toNat ∧
          (absByte (pByteAt b k.val)).toNat ≤ 57 := by
        rw [isDigit] at hd
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
        constructor
        · exact (UInt8.le_iff_toNat_le.mp hd.1)
        · exact (UInt8.le_iff_toNat_le.mp hd.2)
      -- the run has at least one digit, so `10 ^ d = 10 * 10 ^ (d - 1)`
      have hpow : (10:Nat) ^ (e.val - k.val) = 10 * 10 ^ (e.val - k1.val) := by
        have : e.val - k.val = (e.val - k1.val) + 1 := by omega
        rw [this, Nat.pow_succ]; ring
      have hb10 : accN * 10 + 10 ≤ 2 ^ 64 := by
        have hp : (1:Nat) ≤ 10 ^ (e.val - k1.val) := Nat.one_le_pow _ _ (by norm_num)
        rw [hpow] at hbd
        have h2 : (10:Nat) ≤ 10 * 10 ^ (e.val - k1.val) := by nlinarith
        have h1 : accN * 10 ≤ accN * (10 * 10 ^ (e.val - k1.val)) :=
          Nat.mul_le_mul_left _ h2
        omega
      have haccL : (accL * 10 + (absByte (pByteAt b k.val) - 48).toUInt64).toNat
          = accN * 10 + ((absByte (pByteAt b k.val)).toNat - 48) := by
        have hsub : ((absByte (pByteAt b k.val) - 48).toUInt64).toNat
            = (absByte (pByteAt b k.val)).toNat - 48 := by
          rw [UInt8.toNat_toUInt64, UInt8.toNat_sub]
          have : ((48:UInt8)).toNat = 48 := rfl
          rw [this]
          omega
        rw [UInt64.toNat_add, UInt64.toNat_mul, hacc, hsub]
        have h10 : ((10:UInt64)).toNat = 10 := rfl
        rw [h10]
        omega
      rw [readNat64_eq, if_pos hk, if_pos hlt, readNat_eq, if_pos hk, if_pos hd,
        ← absPos_add_one hk1]
      refine ih k1 e _ _ (by omega) hrun1 (by omega) haccL ?_
      rw [hpow] at hbd
      refine le_trans ?_ hbd
      have hc : (absByte (pByteAt b k.val)).toNat - 48 ≤ 9 := by omega
      have hq : ((absByte (pByteAt b k.val)).toNat - 48) * 10 ^ (e.val - k1.val)
          ≤ 9 * 10 ^ (e.val - k1.val) := Nat.mul_le_mul_right _ hc
      nlinarith [hq]
    · have hke : k.val = e.val := by omega
      rw [readNat64_eq, readNat_eq]
      by_cases hk : k.val < b.val.length
      · rw [if_pos hk, if_pos hk, if_neg (show ¬ k.val < e.val by omega),
          if_neg (skipDigits_stop hk (by omega) hrun), hacc]
      · rw [if_neg hk, if_neg hk, hacc]

/-- **`readNatAt` is `readNat` on a digit run** (`Scan/Fast.lean:496-500`):
the two branches agree, because a run of at most 18 digits cannot leave the
machine word.  This is the characterisation `scan_quoted_nat` needs. -/
theorem readNatAt_eq_readNat {b : Slice Std.U8} {i e : Std.Usize}
    (hrun : skipDigits (absBytes b) (absPos i) = absPos e) (hle : i.val ≤ e.val) :
    readNatAt (absBytes b) (absPos i) (absPos e) = readNat (absBytes b) (absPos i) 0 := by
  rw [readNatAt]
  split
  · rename_i h18
    have hsub : (absPos e - absPos i).toNat = e.val - i.val := by
      rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, absPos_toNat, absPos_toNat]; omega)]
      rw [absPos_toNat, absPos_toNat]
    have hd : e.val - i.val ≤ 18 := by
      have := USize.le_iff_toNat_le.mp h18
      rw [hsub, uT18] at this; exact this
    have hbd : 0 * 10 ^ (e.val - i.val) + 10 ^ (e.val - i.val) ≤ 2 ^ 64 := by
      have : (10:Nat) ^ (e.val - i.val) ≤ 10 ^ 18 := Nat.pow_le_pow_right (by norm_num) hd
      omega
    exact readNat64_eq_readNat b (e.val - i.val) i e 0 0 (le_refl _) hrun hle rfl hbd
  · rfl


/-- `skip_digits` never goes backwards, on the port's side of the fence. -/
theorem skip_digits_ge {b : Slice Std.U8} {i e : Std.Usize}
    (h : frontend.scan_fast.skip_digits b i = ok e) : i.val ≤ e.val := by
  have hr := skip_digits_refines h
  have := skipDigits_ge b (b.val.length - i.val) i (le_refl _)
  rw [← hr, absPos_toNat] at this
  exact this

/-- **A `num_end` that moved is the digit run.**  `numEnd` returns either `i`
(no digits, or JSON's leading-zero rule) or `skipDigits`'s answer, so a caller
that has ruled `e = i` out has the run. -/
theorem num_end_run {b : Slice Std.U8} {i e : Std.Usize}
    (h : frontend.scan_fast.num_end b i = ok e) (hne : ¬ e = i) :
    frontend.scan_fast.skip_digits b i = ok e := by
  rw [frontend.scan_fast.num_end] at h
  obtain ⟨d, hd, h⟩ := bind_eq_ok_iff.mp h
  by_cases hdi : d = i
  · rw [if_pos hdi] at h
    exact absurd (by simpa using h.symm) hne
  · rw [if_neg hdi] at h
    obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
    by_cases h48 : c = 48#u8
    · rw [if_pos h48] at h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      by_cases hne2 : (d != i2) = true
      · rw [if_pos hne2] at h
        exact absurd (by simpa using h.symm) hne
      · rw [if_neg hne2] at h
        have : d = e := by simpa using h
        rw [← this]; exact hd
    · rw [if_neg h48] at h
      have : d = e := by simpa using h
      rw [← this]; exact hd

/-! ### The port's `u64` loop against con-leche's `Nat` one -/

private theorem read_nat_at_loop_nat {b : Slice Std.U8} {i e : Std.Usize} (f : Nat) :
    ∀ (k : Std.Usize) (acc n : Std.U64),
      b.val.length - k.val ≤ f →
      skipDigits (absBytes b) (absPos k) = absPos e →
      k.val ≤ e.val →
      frontend.scan_fast.read_nat_at_loop b i e acc k = ok (.Ok n) →
      readNat (absBytes b) (absPos k) acc.val = n.val := by
  induction f with
  | zero =>
    intro k acc n hf hrun hle h
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    rw [readNat_eq, if_neg (show ¬ k.val < b.val.length by omega)]
    by_cases hke : k < e
    · rw [if_pos hke, if_neg (show ¬ k < Slice.len b by scalar_tac)] at h
      have : acc = n := by simpa using h
      rw [this]
    · rw [if_neg hke] at h
      have : acc = n := by simpa using h
      rw [this]
  | succ f ih =>
    intro k acc n hf hrun hle h
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    by_cases hke : k < e
    · rw [if_pos hke] at h
      by_cases hkl : k < Slice.len b
      · rw [if_pos hkl] at h
        have hk : k.val < b.val.length := by scalar_tac
        have hlt : k.val < e.val := by scalar_tac
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_ok (i := k)
          (by have := Slice.length_ineq b; omega)
        obtain ⟨hd, hrun1⟩ := skipDigits_step hk hlt hk1v hrun
        rw [readNat_eq, if_pos hk, if_pos hd, ← absPos_add_one hk1]
        obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
        have hoe : Std.U64.checked_mul acc 10#u64 = o := by simpa using ho
        cases o with
        | none => simp at h
        | some x =>
          have hspec := Std.U64.checked_mul_bv_spec acc 10#u64
          rw [hoe] at hspec
          obtain ⟨-, hxv, -⟩ := hspec
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
          have ho1e : Std.U64.checked_add x i4 = o1 := by simpa using ho1
          have hi2v : i2 = pByteAt b k.val := by
            rw [slice_index_ok hk] at hi2; rw [pByteAt, dif_pos hk]; simpa using hi2.symm
          have hsub := Std.UScalar.sub_equiv i2 (48#u8)
          rw [hi3] at hsub
          simp at hsub
          have hi4v : i4.val = i3.val := by
            have hc := Std.U8.cast_U64_val_eq i3
            have he : UScalar.cast .U64 i3 = i4 := by simpa using hi4
            rw [← he, hc]
          cases o1 with
          | none => simp at h
          | some x1 =>
            have hadd := Std.U64.checked_add_bv_spec x i4
            rw [ho1e] at hadd
            obtain ⟨-, hx1v, -⟩ := hadd
            obtain ⟨k2, hk2, h⟩ := bind_eq_ok_iff.mp h
            have hk2v := usize_add_one_inv hk2
            have hkk : k2 = k1 := by
              have : k1.val = k2.val := by omega
              scalar_tac
            rw [hkk] at h
            have hx1 : x1.val = acc.val * 10 + ((absByte (pByteAt b k.val)).toNat - 48) := by
              rw [← hi2v, absByte_toNat]
              have h10 : (10#u64).val = 10 := by scalar_tac
              rw [h10] at hxv
              scalar_tac
            rw [← hx1]
            exact ih k1 x1 n (by omega) hrun1 (by omega) h
      · rw [if_neg hkl] at h
        rw [readNat_eq, if_neg (show ¬ k.val < b.val.length by scalar_tac)]
        have : acc = n := by simpa using h
        rw [this]
    · rw [if_neg hke] at h
      have hke' : e.val ≤ k.val := by scalar_tac
      rw [readNat_eq]
      by_cases hk : k.val < b.val.length
      · rw [if_pos hk, if_neg (skipDigits_stop hk hke' hrun)]
        have : acc = n := by simpa using h
        rw [this]
      · rw [if_neg hk]
        have : acc = n := by simpa using h
        rw [this]


/-- **`read_nat_at`'s value is `readNatAt`** (`Scan/Fast.lean:496-500`), on a
digit run.  The side condition is `e` being the end of the run -- what
`num_end_run` and `scan_quoted_nat`'s own `skip_digits` call both supply. -/
theorem read_nat_at_refines {b : Slice Std.U8} {i e : Std.Usize} {n : Std.U64}
    (hrun : frontend.scan_fast.skip_digits b i = ok e)
    (h : frontend.scan_fast.read_nat_at b i e = ok (.Ok n)) :
    n.val = readNatAt (absBytes b) (absPos i) (absPos e) := by
  have hsd : skipDigits (absBytes b) (absPos i) = absPos e := (skip_digits_refines hrun).symm
  have hle : i.val ≤ e.val := skip_digits_ge hrun
  rw [readNatAt_eq_readNat hsd hle]
  rw [frontend.scan_fast.read_nat_at] at h
  have hz := read_nat_at_loop_nat (b.val.length - i.val) i 0#u64 n (le_refl _) hsd hle h
  rw [← hz]
  norm_num

private theorem read_nat_at_loop_err {b : Slice Std.U8} {i e : Std.Usize} (f : Nat) :
    ∀ (k : Std.Usize) (acc : Std.U64) (er : frontend.scan_types.ScanErr),
      b.val.length - k.val ≤ f →
      frontend.scan_fast.read_nat_at_loop b i e acc k = ok (.Err er) →
      er.what = frontend.scan_types.ErrTag.IndexOverflow := by
  induction f with
  | zero =>
    intro k acc er hf h
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    by_cases hke : k < e
    · rw [if_pos hke, if_neg (show ¬ k < Slice.len b by scalar_tac)] at h; simp at h
    · rw [if_neg hke] at h; simp at h
  | succ f ih =>
    intro k acc er hf h
    rw [frontend.scan_fast.read_nat_at_loop.eq_def] at h
    by_cases hke : k < e
    · rw [if_pos hke] at h
      by_cases hkl : k < Slice.len b
      · rw [if_pos hkl] at h
        have hk : k.val < b.val.length := by scalar_tac
        obtain ⟨o, -, h⟩ := bind_eq_ok_iff.mp h
        cases o with
        | none => simp only [Result.ok.injEq, core.result.Result.Err.injEq] at h; rw [← h]
        | some x =>
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
          cases o1 with
          | none => simp only [Result.ok.injEq, core.result.Result.Err.injEq] at h; rw [← h]
          | some x1 =>
            obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
            have := usize_add_one_inv hk1
            exact ih k1 x1 er (by omega) h
      · rw [if_neg hkl] at h; simp at h
    · rw [if_neg hke] at h; simp at h

/-- **The port's own overflow claims nothing.**  `ErrTag::IndexOverflow` is
con-ron's (deviation 4 of the module note); `absErrTag` sends it to `none`. -/
theorem read_nat_at_err {α : Type} {b : Slice Std.U8} {i e : Std.Usize}
    {er : frontend.scan_types.ScanErr} {x : ConLeche.Frontend.ScanRes α}
    (h : frontend.scan_fast.read_nat_at b i e = ok (.Err er)) : ScanErrSim er x := by
  rw [frontend.scan_fast.read_nat_at] at h
  exact ScanErrSim.overflow (read_nat_at_loop_err (b.val.length - i.val) i 0#u64 er (le_refl _) h)

/-! ## `slot_nat`

`scan_fast.rs:1454-1466` is the port's factoring of the `numEnd`/`readNatAt`/
`noProgress` chain every `Nat`-valued slot of every `scan*Loop` writes out
(`Scan/Fast.lean:820-824` is one instance).  `slotNat` is that fragment as a
con-leche function -- an intermediate definition in DESIGN.md's sense, written
to be the Lean's own inline chain, so an object loop can unfold it and see
exactly what its `scan*Loop` twin has. -/

/-- con-leche's inline `numEnd`/`readNatAt`/`noProgress` chain. -/
def slotNat (B : ByteArray) (ks v : USize) : ConLeche.Frontend.ScanRes Nat :=
  let e := numEnd B v
  if e == v then .err ⟨v.toNat, .expectedNat⟩
  else if ks < e then .ok (readNatAt B v e) e
  else .err ⟨ks.toNat, .noProgress⟩

/-- **`slot_nat` refines `slotNat`**, in full outcome. -/
theorem slot_nat_refines {b : Slice Std.U8} {ks v : Std.Usize}
    {o : core.result.Result (Std.U64 × Std.Usize) frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.slot_nat b ks v = ok o) :
    ScanSim absU64 o (slotNat (absBytes b) (absPos ks) (absPos v)) := by
  rw [frontend.scan_fast.slot_nat] at h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  have hnum : absPos e = numEnd (absBytes b) (absPos v) := num_end_refines he
  simp only [slotNat, ← hnum]
  by_cases hev : e = v
  · rw [if_pos hev] at h
    rw [frontend.scan_fast.err] at h
    have ho : (core.result.Result.Err
        ({ offset := v, what := frontend.scan_types.ErrTag.ExpectedNat } :
          frontend.scan_types.ScanErr)) = o := by simpa using h
    rw [← ho]
    refine ScanSim.err (ScanErrSim.mk (t := .expectedNat) rfl ?_)
    rw [if_pos (show (absPos e == absPos v) = true by simp; scalar_tac)]
    simp
  · rw [if_neg hev] at h
    rw [if_neg (show ¬ (absPos e == absPos v) = true by simp; scalar_tac)]
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = decide (absPos ks < absPos e) := prog_eq hb1
    by_cases hp : b1 = true
    · rw [if_pos hp] at h
      rw [if_pos (by rw [hb1v] at hp; simpa using hp)]
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Ok x =>
        have ho : core.result.Result.Ok (x, e) = o := by simpa using h
        rw [← ho]
        refine ScanSim.ok ?_
        have hrun : frontend.scan_fast.skip_digits b v = ok e := num_end_run he hev
        rw [show absU64 x = x.val from rfl, read_nat_at_refines hrun hr]
      | Err er =>
        have ho : core.result.Result.Err er = o := by simpa using h
        rw [← ho]
        exact ScanSim.err (read_nat_at_err hr)
    · rw [if_neg hp] at h
      rw [if_neg (by rw [hb1v] at hp; simpa using hp)]
      rw [frontend.scan_fast.err] at h
      have ho : (core.result.Result.Err
          ({ offset := ks, what := frontend.scan_types.ErrTag.NoProgress } :
            frontend.scan_types.ScanErr)) = o := by simpa using h
      rw [← ho]
      refine ScanSim.err (ScanErrSim.mk (t := .noProgress) rfl ?_)
      simp



/-- `strClose` is `0` or at least where it started: what discharges
con-leche's `_hj : i < e + 1` guard, which the port does not have. -/
private theorem strClose_ge (b : Slice Std.U8) (f : Nat) :
    ∀ (j : Std.Usize), b.val.length - j.val ≤ f →
      (strClose (absBytes b) (absPos j)).toNat = 0 ∨
        j.val ≤ (strClose (absBytes b) (absPos j)).toNat := by
  induction f with
  | zero =>
    intro j hf
    rw [strClose_eq, if_neg (show ¬ j.val < b.val.length by omega)]
    left; rfl
  | succ f ih =>
    intro j hf
    by_cases hj : j.val < b.val.length
    · rw [strClose_eq, if_pos hj]
      by_cases h34 : (absByte (pByteAt b j.val) == 34) = true
      · rw [if_pos h34]; right; rw [absPos_toNat]
      · rw [if_neg h34]
        by_cases h92 : (absByte (pByteAt b j.val) == 92) = true
        · rw [if_pos h92]
          by_cases h2 : j.val + 1 < b.val.length
          · rw [if_pos h2]
            by_cases hc : absByte (pByteAt b (j.val + 1)) < 32
            · rw [if_pos hc]; left; rfl
            · rw [if_neg hc]
              obtain ⟨j1, hj1, hj1v⟩ := usize_add_ok (i := j)
                (by have := Slice.length_ineq b; omega)
              obtain ⟨j2, hj2, hj2v⟩ := usize_add_ok (i := j1)
                (by have := Slice.length_ineq b; omega)
              have he : absPos j2 = absPos j + 1 + 1 := by
                rw [absPos_add_one hj2, absPos_add_one hj1]
              rw [← he]
              rcases ih j2 (by omega) with h | h
              · left; exact h
              · right; omega
          · rw [if_neg h2]; left; rfl
        · rw [if_neg h92]
          by_cases hc : absByte (pByteAt b j.val) < 32
          · rw [if_pos hc]; left; rfl
          · rw [if_neg hc]
            obtain ⟨j1, hj1, hj1v⟩ := usize_add_ok (i := j)
              (by have := Slice.length_ineq b; omega)
            rw [← absPos_add_one hj1]
            rcases ih j1 (by omega) with h | h
            · left; exact h
            · right; omega
    · rw [strClose_eq, if_neg hj]; left; rfl

/-! ## `skip_braced` -/

private theorem skipBraced_eq (b : Slice Std.U8) (i : Std.Usize) (depth : Nat) :
    skipBraced (absBytes b) (absPos i) depth =
      (if i.val < b.val.length then
        (if absByte (pByteAt b i.val) == 34 then
          (if strClose (absBytes b) (absPos i + 1) == 0 then 0
           else if absPos i < strClose (absBytes b) (absPos i + 1) + 1 then
             skipBraced (absBytes b) (strClose (absBytes b) (absPos i + 1) + 1) depth
           else 0)
         else if absByte (pByteAt b i.val) == 10 then 0
         else if absByte (pByteAt b i.val) == 123 || absByte (pByteAt b i.val) == 91 then
           skipBraced (absBytes b) (absPos i + 1) (depth + 1)
         else if absByte (pByteAt b i.val) == 125 || absByte (pByteAt b i.val) == 93 then
           (match depth with
            | 0 => absPos i + 1
            | d + 1 => skipBraced (absBytes b) (absPos i + 1) d)
         else skipBraced (absBytes b) (absPos i + 1) depth)
       else 0) := by
  conv_lhs => rw [skipBraced.eq_def]
  by_cases h : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_absPos]
    simp only [dite_eq_ite]
    rfl
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]


/-- **`skip_braced` refines `skipBraced`** (`Scan/Fast.lean:755-769`).

This is the one place in the module where the two shapes genuinely differ:
con-leche's `skipBraced` carries a `_hj : i < e + 1` guard after a quoted
string -- it is what its `termination_by b.size - i.toNat` needs, since a
string can be any length -- and the port has no such test, because in Rust the
loop's own `e + 1 > i` is enough.  The guard is discharged, not assumed:
`strClose_ge` says `strClose` returns `0` or a position at or after the one it
started at, and the port has already ruled `0` out. -/
private theorem skip_braced_loop_refines {b : Slice Std.U8} (f : Nat) :
    ∀ (i : Std.Usize) (depth : Std.U64) (j : Std.Usize),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.skip_braced_loop b i depth = ok j →
      absPos j = skipBraced (absBytes b) (absPos i) (absU64 depth) := by
  have hz : absPos (0#usize) = (0 : USize) := by simp [absPos]; rfl
  induction f with
  | zero =>
    intro i depth j hf h
    rw [frontend.scan_fast.skip_braced_loop.eq_def] at h
    rw [if_neg (show ¬ (i < Slice.len b) by scalar_tac)] at h
    rw [skipBraced_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
    have : 0#usize = j := by simpa using h
    rw [← this, hz]
  | succ f ih =>
    intro i depth j hf h
    rw [frontend.scan_fast.skip_braced_loop.eq_def] at h
    by_cases hlt : i < Slice.len b
    · rw [if_pos hlt] at h
      have hi : i.val < b.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hc' : c = pByteAt b i.val := by
        rw [slice_index_ok hi] at hc; rw [pByteAt, dif_pos hi]; simpa using hc.symm
      rw [skipBraced_eq, if_pos hi, ← hc']
      by_cases h34 : c = 34#u8
      · -- a quoted string: the one arm where the shapes differ
        rw [if_pos h34] at h
        rw [if_pos (show (absByte c == 34) = true by simp; scalar_tac)]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
        have hi2v := usize_add_one_inv hi2
        have hev : absPos e = strClose (absBytes b) (absPos i + 1) := by
          rw [← absPos_add_one hi2]; exact str_close_refines he
        rw [← hev]
        by_cases he0 : e = 0#usize
        · rw [if_pos he0] at h
          rw [if_pos (show (absPos e == (0:USize)) = true by simp; scalar_tac)]
          have : 0#usize = j := by simpa using h
          rw [← this, hz]
        · rw [if_neg he0] at h
          rw [if_neg (show ¬ (absPos e == (0:USize)) = true by simp; scalar_tac)]
          obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
          have hi3v := usize_add_one_inv hi3
          -- `strClose` is `0` or at least `i + 1`, and `0` is out
          have hge : i2.val ≤ e.val := by
            rcases strClose_ge b (b.val.length - i2.val) i2 (le_refl _) with hg | hg
            · exfalso
              rw [absPos_add_one hi2, ← hev, absPos_toNat] at hg
              exact he0 (by scalar_tac)
            · rw [absPos_add_one hi2, ← hev, absPos_toNat] at hg; exact hg
          rw [if_pos (show absPos i < absPos e + 1 by
            rw [← absPos_add_one hi3, absPos_lt]; omega), ← absPos_add_one hi3]
          exact ih i3 depth j (by omega) h
      · rw [if_neg h34] at h
        rw [if_neg (show ¬ (absByte c == 34) = true by simp; scalar_tac)]
        by_cases h10 : c = 10#u8
        · rw [if_pos h10] at h
          rw [if_pos (show (absByte c == 10) = true by simp; scalar_tac)]
          have : 0#usize = j := by simpa using h
          rw [← this, hz]
        · rw [if_neg h10] at h
          rw [if_neg (show ¬ (absByte c == 10) = true by simp; scalar_tac)]
          by_cases h123 : c = 123#u8
          · rw [if_pos h123] at h
            rw [if_pos (show (absByte c == 123 || absByte c == 91) = true by
              simp; left; scalar_tac)]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨d1, hd1, h⟩ := bind_eq_ok_iff.mp h
            have hi2v := usize_add_one_inv hi2
            have hd1v : d1.val = depth.val + 1 := by
              have h2 := Std.UScalar.add_equiv depth (1#u64)
              rw [hd1] at h2; simp at h2; scalar_tac
            rw [← absPos_add_one hi2, show absU64 depth + 1 = absU64 d1 from by
              rw [absU64, absU64, hd1v]]
            exact ih i2 d1 j (by omega) h
          · rw [if_neg h123] at h
            by_cases h91 : c = 91#u8
            · rw [if_pos h91] at h
              rw [if_pos (show (absByte c == 123 || absByte c == 91) = true by
                simp; right; scalar_tac)]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨d1, hd1, h⟩ := bind_eq_ok_iff.mp h
              have hi2v := usize_add_one_inv hi2
              have hd1v : d1.val = depth.val + 1 := by
                have h2 := Std.UScalar.add_equiv depth (1#u64)
                rw [hd1] at h2; simp at h2; scalar_tac
              rw [← absPos_add_one hi2, show absU64 depth + 1 = absU64 d1 from by
                rw [absU64, absU64, hd1v]]
              exact ih i2 d1 j (by omega) h
            · rw [if_neg h91] at h
              rw [if_neg (show ¬ (absByte c == 123 || absByte c == 91) = true by
                simp; constructor <;> scalar_tac)]
              by_cases h125 : c = 125#u8
              · rw [if_pos h125] at h
                rw [if_pos (show (absByte c == 125 || absByte c == 93) = true by
                  simp; left; scalar_tac)]
                by_cases hd0 : depth = 0#u64
                · rw [if_pos hd0] at h
                  rw [show absU64 depth = 0 from by rw [hd0]; rfl]
                  exact absPos_add_one h
                · rw [if_neg hd0] at h
                  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨d1, hd1, h⟩ := bind_eq_ok_iff.mp h
                  have hi2v := usize_add_one_inv hi2
                  have hd1v : depth.val = d1.val + 1 := by
                    have h2 := Std.UScalar.sub_equiv depth (1#u64)
                    rw [hd1] at h2; simp at h2; scalar_tac
                  rw [show absU64 depth = absU64 d1 + 1 from by
                    rw [absU64, absU64, hd1v]]
                  rw [← absPos_add_one hi2]
                  exact ih i2 d1 j (by omega) h
              · rw [if_neg h125] at h
                by_cases h93 : c = 93#u8
                · rw [if_pos h93] at h
                  rw [if_pos (show (absByte c == 125 || absByte c == 93) = true by
                    simp; right; scalar_tac)]
                  by_cases hd0 : depth = 0#u64
                  · rw [if_pos hd0] at h
                    rw [show absU64 depth = 0 from by rw [hd0]; rfl]
                    exact absPos_add_one h
                  · rw [if_neg hd0] at h
                    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨d1, hd1, h⟩ := bind_eq_ok_iff.mp h
                    have hi2v := usize_add_one_inv hi2
                    have hd1v : depth.val = d1.val + 1 := by
                      have h2 := Std.UScalar.sub_equiv depth (1#u64)
                      rw [hd1] at h2; simp at h2; scalar_tac
                    rw [show absU64 depth = absU64 d1 + 1 from by
                      rw [absU64, absU64, hd1v]]
                    rw [← absPos_add_one hi2]
                    exact ih i2 d1 j (by omega) h
                · rw [if_neg h93] at h
                  rw [if_neg (show ¬ (absByte c == 125 || absByte c == 93) = true by
                    simp; constructor <;> scalar_tac)]
                  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
                  have hi2v := usize_add_one_inv hi2
                  rw [← absPos_add_one hi2]
                  exact ih i2 depth j (by omega) h
    · rw [if_neg hlt] at h
      rw [skipBraced_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
      have : 0#usize = j := by simpa using h
      rw [← this, hz]

/-- **`skip_braced` refines `skipBraced`** (`Scan/Fast.lean:755-769`). -/
theorem skip_braced_refines {b : Slice Std.U8} {i : Std.Usize} {depth : Std.U64}
    {j : Std.Usize} (h : frontend.scan_fast.skip_braced b i depth = ok j) :
    absPos j = skipBraced (absBytes b) (absPos i) (absU64 depth) :=
  skip_braced_loop_refines (b.val.length - i.val) i depth j (le_refl _) h


end ConRon.Refine.Frontend
