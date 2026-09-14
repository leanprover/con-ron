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
private theorem uget_absPos {b : Slice Std.U8} {i : Std.Usize}
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

end ConRon.Refine.Frontend
