/-
# `ConRon.Refine2.Frontend.Olean.Region` — `olean/region.rs` against upstream's `Region.lean`

**Task #142, Theorem 2.**  Byte reads over `Slice U8` against `ByteArray`, words
against `UInt64`, the saturating sums against `Nat`.  The twin imports upstream's
`Olean/Region.lean` whole, so these are the leaves of the reader's tier: each
function equals upstream's on the abstraction.  They are pure: a statement is
`f … = ok x → A x = g …`.

`absRegion bs r` is upstream's `Region` of a Rust `Region` with its bytes beside it
(the Rust keeps them apart).  `RegionFits bs r` is what the saturating comparisons
need of it: every file ends inside the bytes and below `u64::MAX`, so that a sum
stopped at `u64::MAX` answers a comparison with a file's end as `Nat`'s does.  It
is a fact about the Rust value that `part_of_bytes` and `region_of_parts*` establish
(`part_max`), and it is carried by the region's relation, `RegionRel`, not by any
twin.
-/
import ConRon.Refine2.Frontend.Scan.Str
import ConRon.Refine2.Frontend.PreludeText
import ConRon.Refine.CoreKNames
import ConRon.Arena.Frontend.Olean.Spec

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConLeche.Frontend.Olean (rdU8 rdU32 rdU64 isScalar)
open ConRon.Refine.HashMap (uscalar_add_eq uscalar_sub_eq uscalar_mul_eq uscalar_div_eq)
open ConRon.Refine.Nat (ushiftLeftI_val toNat NatWF)

/-- `let x ← f; k` in a hypothesis, peeled. -/
macro "peel " h:ident " as " x:rcasesPat ", " hx:rcasesPat : tactic =>
  `(tactic| (have h_ := ConRon.Refine.bind_eq_ok_iff.mp $h:ident; clear $h:ident;
             obtain ⟨$x:rcasesPat, $hx:rcasesPat, $h:ident⟩ := h_))

/-! ## Words -/

/-- A word of the file, as upstream's `UInt64`. -/
def absWord (x : Std.U64) : UInt64 := UInt64.ofNat x.val

@[simp] theorem absWord_toNat (x : Std.U64) : (absWord x).toNat = x.val := by
  simp [absWord]

theorem absWord_inj {a b : Std.U64} (h : absWord a = absWord b) : a = b := by
  have := congrArg UInt64.toNat h
  simp only [absWord_toNat] at this
  exact UScalar.eq_of_val_eq this

@[simp] theorem absWord_eq_iff {a b : Std.U64} : absWord a = absWord b ↔ a = b :=
  ⟨absWord_inj, fun h => by rw [h]⟩

@[simp] theorem absWord_le {a b : Std.U64} : absWord a ≤ absWord b ↔ a.val ≤ b.val := by
  simp [UInt64.le_iff_toNat_le]

theorem absWord_sub {a b : Std.U64} (h : b.val ≤ a.val) :
    (absWord a - absWord b).toNat = a.val - b.val := by
  rw [UInt64.toNat_sub_of_le _ _ (absWord_le.mpr h)]
  simp

/-- `absByte` as a word. -/
@[simp] theorem absByte_toUInt64_toNat (c : Std.U8) : (absByte c).toUInt64.toNat = c.val := by
  simp

@[simp] theorem u64_max_val : core.num.U64.MAX.val = 2 ^ 64 - 1 := by decide

@[simp] theorem u64_val_lit8 : (8#u64 : Std.U64).val = 8 := by decide

theorem u64_lt (x : Std.U64) : x.val < 2 ^ 64 := by scalar_tac

/-- A `usize` as a `u64`. -/
theorem cast_u64_usize (x : Std.Usize) : (UScalar.cast UScalarTy.U64 x).val = x.val :=
  ConRon.Refine.ExprOps.usize_cast_u64_val x

theorem cast_u64_u8 (x : Std.U8) : (UScalar.cast UScalarTy.U64 x).val = x.val :=
  U8.cast_U64_val_eq x

theorem cast_u64_u32 (x : Std.U32) : (UScalar.cast UScalarTy.U64 x).val = x.val :=
  U32.cast_U64_val_eq x

/-! ## The saturating sums -/

/-- **`sat_add` is `Nat`'s `+`, stopped at `u64::MAX`.** -/
theorem sat_add_spec {a b c : Std.U64} (h : sat_add a b = ok c) :
    c.val = min (a.val + b.val) (2 ^ 64 - 1) := by
  rw [sat_add] at h
  peel h as i, hi
  have hiv := uscalar_sub_eq hi
  rw [u64_max_val] at hiv
  have hb := u64_lt b
  split at h
  · cases Result.ok_injective h
    rename_i hgt
    have : a.val > i.val := by scalar_tac
    rw [u64_max_val]; omega
  · rename_i hle
    have : a.val ≤ i.val := by scalar_tac
    have := uscalar_add_eq h
    omega

/-- **`sat_mul8` is `Nat`'s `8 * n`, stopped at `u64::MAX`.** -/
theorem sat_mul8_spec {n c : Std.U64} (h : sat_mul8 n = ok c) :
    c.val = min (8 * n.val) (2 ^ 64 - 1) := by
  rw [sat_mul8] at h
  peel h as i, hi
  have hiv := uscalar_div_eq hi
  rw [u64_max_val, u64_val_lit8] at hiv
  have hb := u64_lt n
  split at h
  · cases Result.ok_injective h
    rename_i hgt
    have : n.val > i.val := by scalar_tac
    rw [u64_max_val]; omega
  · rename_i hle
    have : n.val ≤ i.val := by scalar_tac
    have := uscalar_mul_eq h
    rw [u64_val_lit8] at this
    omega

/-- A saturated sum compared with something below `u64::MAX` answers as `Nat`'s. -/
theorem sat_le_iff {x : Nat} {f : Nat} (hf : f < 2 ^ 64 - 1) :
    min x (2 ^ 64 - 1) ≤ f ↔ x ≤ f := by
  omega

/-! ## Byte reads -/

theorem absBytes_getElem (b : Slice Std.U8) (i : Nat) (h : i < (absBytes b).size)
    (h' : i < b.val.length) : (absBytes b)[i] = absByte b.val[i] := by
  show (absBytes b).data[i] = _
  simp [absBytes]

/-- The total value of a byte read: `rdU8` on the abstraction. -/
theorem rdU8_absBytes (b : Slice Std.U8) (i : Nat) :
    (rdU8 (absBytes b) i).toNat = (if h : i < b.val.length then b.val[i].val else 0) := by
  simp only [rdU8]
  by_cases hi : i < b.val.length
  · rw [dite_eq_left (by simpa using hi), dite_eq_left hi, absBytes_getElem _ _ _ hi, absByte_toNat]
  · rw [dite_eq_right (by simpa using hi), dite_eq_right hi]; rfl

theorem usize_of_lt_len {b : Slice Std.U8} {i : Std.U64} (hi : i.val < b.val.length) :
    (UScalar.cast UScalarTy.Usize i).val = i.val :=
  ConRon.Refine.ExprOps.u64_cast_usize_val (by scalar_tac)

/-- **`rd_u8` is `rdU8`.** -/
theorem rd_u8_eq {b : Slice Std.U8} {i : Std.U64} {x : Std.U8} (h : rd_u8 b i = ok x) :
    absByte x = rdU8 (absBytes b) i.val := by
  rw [rd_u8] at h
  simp only [rdU8]
  simp only [lift, bind_ok] at h
  have hlen := cast_u64_usize (Slice.len b)
  split at h
  · rename_i hlt
    have hi : i.val < b.val.length := by scalar_tac
    have hc := usize_of_lt_len hi
    have hix : (UScalar.cast UScalarTy.Usize i).val < b.val.length := by omega
    rw [slice_index_ok hix] at h
    cases Result.ok_injective h
    rw [dite_eq_left (by simpa using hi), absBytes_getElem _ _ _ hi]
    simp only [hc]
  · rename_i hge
    have hi : ¬ i.val < b.val.length := by scalar_tac
    cases Result.ok_injective h
    rw [dite_eq_right (by simpa using hi)]
    rfl

@[simp] theorem absByte_toUInt32_toNat (c : Std.U8) : (absByte c).toUInt32.toNat = c.val := by
  simp

theorem cast_u32_u8 (x : Std.U8) : (UScalar.cast UScalarTy.U32 x).val = x.val :=
  U8.cast_U32_val_eq x

theorem i32_lit_toNat8 : (8#i32 : Std.I32).toNat = 8 := by decide
theorem i32_lit_toNat16 : (16#i32 : Std.I32).toNat = 16 := by decide
theorem i32_lit_toNat24 : (24#i32 : Std.I32).toNat = 24 := by decide
theorem i32_lit_toNat32 : (32#i32 : Std.I32).toNat = 32 := by decide
theorem i32_lit_toNat40 : (40#i32 : Std.I32).toNat = 40 := by decide
theorem i32_lit_toNat48 : (48#i32 : Std.I32).toNat = 48 := by decide
theorem i32_lit_toNat56 : (56#i32 : Std.I32).toNat = 56 := by decide

/-- **`rd_u32` is `rdU32`.** -/
theorem rd_u32_eq {b : Slice Std.U8} {i : Std.U64} {x : Std.U32} (h : rd_u32 b i = ok x) :
    ConRon.Refine2.absU32 x = rdU32 (absBytes b) i.val := by
  rw [rd_u32] at h
  simp only [lift, bind_ok] at h
  peel h as c0, h0
  peel h as i1, hi1
  peel h as c1, h1
  peel h as s1, hs1
  peel h as i2, hi2
  peel h as c2, h2
  peel h as s2, hs2
  peel h as i3, hi3
  peel h as c3, h3
  peel h as s3, hs3
  cases Result.ok_injective h
  have e0 := rd_u8_eq h0
  have e1 := rd_u8_eq h1
  have e2 := rd_u8_eq h2
  have e3 := rd_u8_eq h3
  have l1 : (1#u64 : Std.U64).val = 1 := by decide
  have l2 : (2#u64 : Std.U64).val = 2 := by decide
  have l3 : (3#u64 : Std.U64).val = 3 := by decide
  rw [uscalar_add_eq hi1, l1] at e1
  rw [uscalar_add_eq hi2, l2] at e2
  rw [uscalar_add_eq hi3, l3] at e3
  have v1 := (ushiftLeftI_val hs1).2
  have v2 := (ushiftLeftI_val hs2).2
  have v3 := (ushiftLeftI_val hs3).2
  simp only [i32_lit_toNat8, i32_lit_toNat16, i32_lit_toNat24, cast_u32_u8] at v1 v2 v3
  apply UInt32.toNat_inj.mp
  simp only [rdU32, ← e0, ← e1, ← e2, ← e3]
  simp only [ConRon.Refine2.absU32_toNat, UInt32.toNat_or, UInt32.toNat_shiftLeft,
    UScalar.val_or, v1, v2, v3, cast_u32_u8, absByte_toUInt32_toNat]
  simp [Nat.shiftLeft_eq]

/-- One byte of `rd_u64`: its read, as the abstraction's. -/
theorem rd_u64_byte {b : Slice Std.U8} {k kj j : Std.Usize} {i n : Nat} {c : Std.U8}
    (hk : k.val = i) (hj : j.val = n) (hlt : i + n < b.val.length)
    (h1 : k + j = ok kj) (h2 : Slice.index_usize b kj = ok c) :
    absByte c = (absBytes b)[i + n]'(by simpa using hlt) := by
  have hv : kj.val = i + n := by rw [uscalar_add_eq h1, hk, hj]
  rw [slice_index_ok (by omega)] at h2
  cases Result.ok_injective h2
  rw [absBytes_getElem _ _ _ hlt]
  simp only [hv]

/-- **`rd_u64` is `rdU64`.** -/
theorem rd_u64_eq {b : Slice Std.U8} {i : Std.U64} {x : Std.U64} (h : rd_u64 b i = ok x) :
    absWord x = rdU64 (absBytes b) i.val := by
  rw [rd_u64] at h
  simp only [rdU64]
  simp only [lift, bind_ok] at h
  have hlen := cast_u64_usize (Slice.len b)
  split at h
  · rename_i h8
    peel h as n8, hn8
    have hn8v := uscalar_sub_eq hn8
    split at h
    · rename_i hle
      have hi : i.val + 8 ≤ b.val.length := by scalar_tac
      have hc := usize_of_lt_len (b := b) (i := i) (by omega)
      have hi' : i.val + 8 ≤ (absBytes b).size := by simpa using hi
      rw [dite_eq_left hi']
      peel h as c0, h0
      rw [slice_index_ok (by omega)] at h0
      cases Result.ok_injective h0
      have e0 : absByte (b.val[(UScalar.cast UScalarTy.Usize i).val]'(by omega)) = (absBytes b)[i.val] := by
        rw [absBytes_getElem _ _ _ (by omega)]
        simp only [hc]
      peel h as k1, hk1
      peel h as c1, h1
      peel h as s1, hs1
      peel h as k2, hk2
      peel h as c2, h2
      peel h as s2, hs2
      peel h as k3, hk3
      peel h as c3, h3
      peel h as s3, hs3
      peel h as k4, hk4
      peel h as c4, h4
      peel h as s4, hs4
      peel h as k5, hk5
      peel h as c5, h5
      peel h as s5, hs5
      peel h as k6, hk6
      peel h as c6, h6
      peel h as s6, hs6
      peel h as k7, hk7
      peel h as c7, h7
      peel h as s7, hs7
      cases Result.ok_injective h
      have e1 := rd_u64_byte (n := 1) hc (by decide) (by omega) hk1 h1
      have e2 := rd_u64_byte (n := 2) hc (by decide) (by omega) hk2 h2
      have e3 := rd_u64_byte (n := 3) hc (by decide) (by omega) hk3 h3
      have e4 := rd_u64_byte (n := 4) hc (by decide) (by omega) hk4 h4
      have e5 := rd_u64_byte (n := 5) hc (by decide) (by omega) hk5 h5
      have e6 := rd_u64_byte (n := 6) hc (by decide) (by omega) hk6 h6
      have e7 := rd_u64_byte (n := 7) hc (by decide) (by omega) hk7 h7
      have v1 := (ushiftLeftI_val hs1).2
      have v2 := (ushiftLeftI_val hs2).2
      have v3 := (ushiftLeftI_val hs3).2
      have v4 := (ushiftLeftI_val hs4).2
      have v5 := (ushiftLeftI_val hs5).2
      have v6 := (ushiftLeftI_val hs6).2
      have v7 := (ushiftLeftI_val hs7).2
      simp only [i32_lit_toNat8, i32_lit_toNat16, i32_lit_toNat24, i32_lit_toNat32, i32_lit_toNat40,
        i32_lit_toNat48, i32_lit_toNat56, cast_u64_u8] at v1 v2 v3 v4 v5 v6 v7
      apply UInt64.toNat_inj.mp
      simp only [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7]
      simp only [absWord_toNat, UInt64.toNat_or, UInt64.toNat_shiftLeft,
        UScalar.val_or, v1, v2, v3, v4, v5, v6, v7, cast_u64_u8, absByte_toUInt64_toNat]
      simp [Nat.shiftLeft_eq]
    · rename_i hgt
      have hi : ¬ i.val + 8 ≤ b.val.length := by scalar_tac
      cases Result.ok_injective h
      rw [dite_eq_right (by simpa using hi)]
      rfl
  · rename_i h8
    have hi : ¬ i.val + 8 ≤ b.val.length := by scalar_tac
    cases Result.ok_injective h
    rw [dite_eq_right (by simpa using hi)]
    rfl

/-! ## The region -/

theorem data_start_val : DATA_START.val = 96 := by unfold DATA_START; decide
theorem tag_array_val : TAG_ARRAY.val = 246 := by unfold TAG_ARRAY; decide
theorem tag_string_val : TAG_STRING.val = 249 := by unfold TAG_STRING; decide
theorem tag_mpz_val : TAG_MPZ.val = 250 := by unfold TAG_MPZ; decide

/-- A `Seg`, as upstream's. -/
def absSeg (s : frontend.olean.region.Seg) : ConLeche.Frontend.Olean.Seg := ⟨absWord s.base, s.off.val, s.size.val⟩

/-- **A Rust `Region` with its bytes beside it, as upstream's `Region`.** -/
def absRegion (bs : Slice Std.U8) (r : frontend.olean.region.Region) :
    ConLeche.Frontend.Olean.Region :=
  ⟨absBytes bs, (r.segs.val.map absSeg).toArray⟩

/-- What a saturating comparison and a `usize` cast need of a region: every file
ends inside the bytes and below `u64::MAX`. -/
def RegionFits (bs : Slice Std.U8) (r : frontend.olean.region.Region) : Prop :=
  ∀ s ∈ r.segs.val, s.off.val + s.size.val ≤ bs.val.length ∧ s.off.val + s.size.val < 2 ^ 64 - 1

theorem absRegion_size (bs : Slice Std.U8) (r : frontend.olean.region.Region) :
    (absRegion bs r).segs.size = r.segs.val.length := by
  simp [absRegion]

theorem absRegion_get (bs : Slice Std.U8) (r : frontend.olean.region.Region) {i : Nat}
    (h : i < r.segs.val.length) :
    (absRegion bs r).segs[i]'(by rw [absRegion_size]; exact h) = absSeg r.segs.val[i] := by
  simp [absRegion]

theorem vec_index_eq {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    ∃ hi : i.val < v.val.length, x = v.val[i.val] := by
  have := ConRon.Refine.ExprOps.vec_index_getElem? h
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp this
  exact ⟨hi, he.symm⟩

/-- **`is_scalar` is `isScalar`.** -/
theorem is_scalar_eq {v : Std.U64} {b : Bool} (h : is_scalar v = ok b) :
    b = isScalar (absWord v) := by
  rw [is_scalar] at h
  simp only [lift, bind_ok] at h
  cases Result.ok_injective h
  have l1 : (1#u64 : Std.U64).val = 1 := by decide
  have hv : (v &&& 1#u64).val = v.val % 2 := by
    rw [UScalar.val_and, l1, Nat.and_one_is_mod]
  simp only [isScalar]
  by_cases hm : v.val % 2 = 1
  · have e1 : v &&& 1#u64 = 1#u64 := UScalar.eq_of_val_eq (by rw [hv, l1, hm])
    have e2 : absWord v &&& 1 = 1 := by
      apply UInt64.toNat_inj.mp
      simp [UInt64.toNat_and, Nat.and_one_is_mod, hm]
    simp [e1, e2]
  · have e1 : ¬ v &&& 1#u64 = 1#u64 := fun he => hm (by have := congrArg UScalar.val he; rw [hv, l1] at this; exact this)
    have e2 : ¬ absWord v &&& 1 = 1 := fun he => hm (by
      have := congrArg UInt64.toNat he
      simpa [UInt64.toNat_and, Nat.and_one_is_mod] using this)
    simp [e1, e2]

/-- **`unbox` is `unbox`.** -/
theorem unbox_eq {v x : Std.U64} (h : frontend.olean.region.unbox v = ok x) :
    x.val = ConLeche.Frontend.Olean.unbox (absWord v) := by
  rw [frontend.olean.region.unbox] at h
  have := (ConRon.Refine.Nat.ushiftRightI_val h).2
  have l1 : (1#i32 : Std.I32).toNat = 1 := by decide
  rw [l1] at this
  rw [this, ConLeche.Frontend.Olean.unbox]
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- The test of `Region.locGo`, on words. -/
theorem seg_test (s : frontend.olean.region.Seg) (a : Std.U64) :
    ((absSeg s).base ≤ absWord a && decide ((absWord a - (absSeg s).base).toNat < (absSeg s).size))
      = decide (s.base.val ≤ a.val ∧ a.val - s.base.val < s.size.val) := by
  simp only [absSeg]
  by_cases hb : s.base.val ≤ a.val
  · simp [absWord_sub hb, hb]
  · simp [hb]

/-- **`region_loc_go` is `Region.locGo`**, the search from the file `i`. -/
theorem region_loc_go_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {a : Std.U64} :
    ∀ (n : Nat) {i : Std.Usize} {g : Std.U64}, i.val = n → region_loc_go r a i = ok g →
      g.val = (absRegion bs r).locGo (absWord a) n := by
  intro n
  induction n with
  | zero =>
    intro i g hi h
    rw [region_loc_go, region_loc_go_loop] at h
    rw [ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    simp [ConLeche.Frontend.Olean.Region.locGo]
  | succ n ih =>
    intro i g hi h
    rw [region_loc_go, region_loc_go_loop] at h
    rw [ite_eq_left (by scalar_tac)] at h
    peel h as i1, hi1
    have hi1v : i1.val = n := by have := uscalar_sub_eq hi1; have l : (1#usize : Std.Usize).val = 1 := by decide
                                 omega
    peel h as s, hs
    obtain ⟨hlt, hse⟩ := vec_index_eq hs
    have hn : n < r.segs.val.length := by omega
    have hse' : r.segs.val[n] = s := by rw [hse]; simp only [hi1v]
    rw [ConLeche.Frontend.Olean.Region.locGo, dite_eq_left (by rw [absRegion_size]; exact hn),
      absRegion_get bs r hn, hse']
    simp only [seg_test]
    split at h
    · rename_i hb
      have hb' : s.base.val ≤ a.val := hb
      peel h as o, ho
      have hov := uscalar_sub_eq ho
      split at h
      · rename_i hlt2
        have hlt' : a.val - s.base.val < s.size.val := by have : o.val < s.size.val := hlt2; omega
        rw [ite_eq_left (decide_eq_true ⟨hb', hlt'⟩)]
        simp only [absSeg, absWord_sub hb']
        peel h as g1, hg1
        have hg1v := uscalar_add_eq hg1
        peel h as m, hm
        have hmv : m.val = g1.val % 8 := ConRon.Refine.CoreK.uscalar_rem_eq (by decide) hm
        have d : (ConLeche.Frontend.Olean.dataStart) = 96 := rfl
        have d2 := data_start_val
        split at h
        · rename_i hm0
          have hm0' : g1.val % 8 = 0 := by have := congrArg UScalar.val hm0; rw [hmv] at this; rw [this]; rfl
          split at h
          · rename_i hd
            have hd' : 96 ≤ o.val := by have : DATA_START.val ≤ o.val := hd; omega
            peel h as e, he
            have hev := uscalar_add_eq he
            rw [u64_val_lit8] at hev
            split at h
            · rename_i hle
              have hle' : e.val ≤ s.size.val := hle
              cases Result.ok_injective h
              rw [ite_eq_left (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, d]; omega)]
              omega
            · rename_i hle
              have hle' : ¬ e.val ≤ s.size.val := hle
              cases Result.ok_injective h
              rw [ite_eq_right (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, d]; omega)]
              rfl
          · rename_i hd
            have hd' : ¬ 96 ≤ o.val := by have : ¬ DATA_START.val ≤ o.val := hd; omega
            cases Result.ok_injective h
            rw [ite_eq_right (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, d]; omega)]
            rfl
        · rename_i hm0
          have hm0' : g1.val % 8 ≠ 0 := by
            intro he; apply hm0; apply UScalar.eq_of_val_eq; rw [hmv, he]; rfl
          cases Result.ok_injective h
          rw [ite_eq_right (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; omega)]
          rfl
      · rename_i hge
        have hge' : ¬ a.val - s.base.val < s.size.val := by have : ¬ o.val < s.size.val := hge; omega
        rw [ite_eq_right (by rw [decide_eq_true_eq]; omega)]
        exact ih hi1v h
    · rename_i hb
      have hb' : ¬ s.base.val ≤ a.val := hb
      rw [ite_eq_right (by rw [decide_eq_true_eq]; omega)]
      exact ih hi1v h

/-- A location, as upstream's. -/
abbrev locOf (o : Option Std.U64) : Option Nat := o.map (·.val)

theorem usize_len_val (r : frontend.olean.region.Region) :
    (alloc.vec.Vec.len r.segs).val = r.segs.val.length := by simp

/-- **`region_loc` is `Region.loc`.** -/
theorem region_loc_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {a : Std.U64}
    {o : Option Std.U64} (h : region_loc r a = ok o) :
    locOf o = (absRegion bs r).loc (absWord a) := by
  rw [region_loc] at h
  peel h as b, hb
  have hb' := is_scalar_eq hb
  simp only [ConLeche.Frontend.Olean.Region.loc, ← hb']
  split at h
  · rename_i hb1
    cases Result.ok_injective h
    simp [hb1]
  · rename_i hb1
    peel h as g, hg
    have hgv := region_loc_go_eq bs r.segs.val.length (by rw [usize_len_val]) hg
    rw [← absRegion_size bs r] at hgv
    simp only [hb1, Bool.false_eq_true, ↓reduceIte, ← hgv]
    split at h
    · rename_i hg0
      cases Result.ok_injective h
      simp [hg0]
    · rename_i hg0
      cases Result.ok_injective h
      have : g.val ≠ 0 := fun he => hg0 (UScalar.eq_of_val_eq (by rw [he]; rfl))
      simp [this]

/-- **`region_end_go` is `Region.endGo`.** -/
theorem region_end_go_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g : Std.U64} :
    ∀ (n : Nat) {i : Std.Usize} {e : Std.U64}, i.val = n → region_end_go r g i = ok e →
      e.val = (absRegion bs r).endGo g.val n := by
  intro n
  induction n with
  | zero =>
    intro i e hi h
    rw [region_end_go, region_end_go_loop] at h
    rw [ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    simp [ConLeche.Frontend.Olean.Region.endGo]
  | succ n ih =>
    intro i e hi h
    rw [region_end_go, region_end_go_loop] at h
    rw [ite_eq_left (by scalar_tac)] at h
    peel h as i1, hi1
    have hi1v : i1.val = n := by
      have := uscalar_sub_eq hi1
      have l : (1#usize : Std.Usize).val = 1 := by decide
      omega
    peel h as s, hs
    obtain ⟨hlt, hse⟩ := vec_index_eq hs
    have hn : n < r.segs.val.length := by omega
    have hse' : r.segs.val[n] = s := by rw [hse]; simp only [hi1v]
    rw [ConLeche.Frontend.Olean.Region.endGo, dite_eq_left (by rw [absRegion_size]; exact hn),
      absRegion_get bs r hn, hse']
    simp only [absSeg]
    peel h as s2, hs2
    have hs2v := uscalar_add_eq hs2
    split at h
    · rename_i hb
      have hb' : s.off.val ≤ g.val := hb
      split at h
      · rename_i hlt2
        have hlt' : g.val < s2.val := hlt2
        cases Result.ok_injective h
        rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
        exact hs2v
      · rename_i hge
        have hge' : ¬ g.val < s2.val := hge
        rw [ite_eq_right (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
        exact ih hi1v h
    · rename_i hb
      have hb' : ¬ s.off.val ≤ g.val := hb
      rw [ite_eq_right (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
      exact ih hi1v h

/-- **`region_file_end` is `Region.fileEnd`.** -/
theorem region_file_end_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g e : Std.U64}
    (h : region_file_end r g = ok e) : e.val = (absRegion bs r).fileEnd g.val := by
  rw [region_file_end] at h
  have := region_end_go_eq bs r.segs.val.length (by rw [usize_len_val]) h
  rw [← absRegion_size bs r] at this
  exact this

/-- **`region_down` is `Region.down`.** -/
theorem region_down_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g v : Std.U64}
    {o : Option Std.U64} (h : region_down r g v = ok o) :
    locOf o = (absRegion bs r).down g.val (absWord v) := by
  rw [region_down] at h
  peel h as o1, h1
  have e := region_loc_eq bs h1
  simp only [ConLeche.Frontend.Olean.Region.down, ← e]
  cases o1 with
  | none => cases Result.ok_injective h; rfl
  | some c =>
    simp only [Option.map_some]
    dsimp only at h
    split at h
    · rename_i hlt
      have hlt' : c.val < g.val := hlt
      cases Result.ok_injective h
      rw [ite_eq_left hlt']; rfl
    · rename_i hge
      have hge' : ¬ c.val < g.val := hge
      cases Result.ok_injective h
      rw [ite_eq_right hge']; rfl

/-- **`region_ok_ptr` is `Region.okPtr`.** -/
theorem region_ok_ptr_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g v : Std.U64}
    {b : Bool} (h : region_ok_ptr r g v = ok b) :
    b = (absRegion bs r).okPtr g.val (absWord v) := by
  rw [region_ok_ptr] at h
  peel h as b1, h1
  have e1 := is_scalar_eq h1
  simp only [ConLeche.Frontend.Olean.Region.okPtr, ← e1]
  split at h
  · rename_i hb
    cases Result.ok_injective h
    simp [hb]
  · rename_i hb
    peel h as o, ho
    have e2 := region_down_eq bs ho
    rw [← e2]
    cases o <;> cases Result.ok_injective h <;> simp [hb]

@[simp] theorem rdU8_toNat_abs (bs : Slice Std.U8) (r : frontend.olean.region.Region) :
    (absRegion bs r).bytes = absBytes bs := rfl

/-- **`region_tag` is `Region.tag`.** -/
theorem region_tag_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : region_tag bs g = ok x) : x.val = (absRegion bs r).tag g.val := by
  rw [region_tag] at h
  peel h as i, hi
  peel h as c, hc
  cases Result.ok_injective h
  have e := rd_u8_eq hc
  rw [uscalar_add_eq hi] at e
  have l : (7#u64 : Std.U64).val = 7 := by decide
  rw [l] at e
  simp only [ConLeche.Frontend.Olean.Region.tag, rdU8_toNat_abs, ← e, absByte_toNat, cast_u64_u8]

/-- **`region_nobjs` is `Region.nobjs`.** -/
theorem region_nobjs_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : region_nobjs bs g = ok x) : x.val = (absRegion bs r).nobjs g.val := by
  rw [region_nobjs] at h
  peel h as i, hi
  peel h as c, hc
  cases Result.ok_injective h
  have e := rd_u8_eq hc
  rw [uscalar_add_eq hi] at e
  have l : (6#u64 : Std.U64).val = 6 := by decide
  rw [l] at e
  simp only [ConLeche.Frontend.Olean.Region.nobjs, rdU8_toNat_abs, ← e, absByte_toNat, cast_u64_u8]

/-- **`region_fits` is `Region.fits`.** -/
theorem region_fits_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g : Std.U64}
    {b : Bool} (h : region_fits bs r g = ok b) : b = (absRegion bs r).fits g.val := by
  rw [region_fits] at h
  peel h as i, hi
  peel h as i1, hi1
  peel h as i2, hi2
  peel h as i3, hi3
  peel h as i4, hi4
  cases Result.ok_injective h
  have e1 := region_nobjs_eq bs (r := r) hi1
  have e2 := region_file_end_eq bs hi4
  have v1 := uscalar_add_eq hi
  have v2 := uscalar_mul_eq hi2
  have v3 := uscalar_add_eq hi3
  rw [u64_val_lit8] at v1 v2
  simp only [ConLeche.Frontend.Olean.Region.fits, ← e1, ← e2, ← v1, ← v2, ← v3]
  by_cases hc : i3.val ≤ i4.val
  · have : i3 ≤ i4 := hc
    simp [this, hc]
  · have : ¬ i3 ≤ i4 := hc
    simp [this, hc]

/-- **`region_fld` is `Region.fld`.** -/
theorem region_fld_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g i x : Std.U64}
    (h : region_fld bs g i = ok x) : absWord x = (absRegion bs r).fld g.val i.val := by
  rw [region_fld] at h
  peel h as i1, hi1
  peel h as i2, hi2
  peel h as i3, hi3
  have v1 := uscalar_add_eq hi1
  have v2 := uscalar_mul_eq hi2
  have v3 := uscalar_add_eq hi3
  rw [u64_val_lit8] at v1 v2
  have := rd_u64_eq h
  rw [v3, v1, v2] at this
  exact this

/-- **`region_ptr_fld` is `Region.ptrFld`.** -/
theorem region_ptr_fld_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g i : Std.U64}
    {o : Option Std.U64} (h : region_ptr_fld bs r g i = ok o) :
    o.map absWord = (absRegion bs r).ptrFld g.val i.val := by
  rw [region_ptr_fld] at h
  peel h as v, hv
  peel h as b, hb
  have e1 := region_fld_eq bs (r := r) hv
  have e2 := region_ok_ptr_eq bs hb
  simp only [ConLeche.Frontend.Olean.Region.ptrFld, ← e1, ← e2]
  split at h <;> rename_i hc <;> cases Result.ok_injective h <;> simp [hc]

/-- The scalar area's location, in `region_u8` and `region_u32`. -/
theorem scalar_at (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g k i i1 i2 i3 i4 : Std.U64}
    (hi : g + 8#u64 = ok i) (hi1 : region_nobjs bs g = ok i1) (hi2 : 8#u64 * i1 = ok i2)
    (hi3 : i + i2 = ok i3) (hi4 : i3 + k = ok i4) :
    i4.val = g.val + 8 + 8 * (absRegion bs r).nobjs g.val + k.val := by
  have e1 := region_nobjs_eq bs (r := r) hi1
  have v1 := uscalar_add_eq hi
  have v2 := uscalar_mul_eq hi2
  have v3 := uscalar_add_eq hi3
  have v4 := uscalar_add_eq hi4
  rw [u64_val_lit8] at v1 v2
  omega

/-- **`region_u8` is `Region.u8`.** -/
theorem region_u8_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g k : Std.U64}
    {o : Option Std.U8} (h : region_u8 bs r g k = ok o) :
    o.map absByte = (absRegion bs r).u8 g.val k.val := by
  rw [region_u8] at h
  peel h as i, hi
  peel h as i1, hi1
  peel h as i2, hi2
  peel h as i3, hi3
  peel h as i4, hi4
  peel h as i5, hi5
  have ei := scalar_at bs (r := r) hi hi1 hi2 hi3 hi4
  have ef := region_file_end_eq bs hi5
  simp only [ConLeche.Frontend.Olean.Region.u8, ← ei, ← ef]
  split at h
  · rename_i hc
    have hc' : i4.val < i5.val := hc
    peel h as c, hcc
    cases Result.ok_injective h
    rw [ite_eq_left hc']
    simp only [Option.map_some, rd_u8_eq hcc]; rfl
  · rename_i hc
    have hc' : ¬ i4.val < i5.val := hc
    cases Result.ok_injective h
    rw [ite_eq_right hc']; rfl

/-- **`region_u32` is `Region.u32`.** -/
theorem region_u32_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g k : Std.U64}
    {o : Option Std.U32} (h : region_u32 bs r g k = ok o) :
    o.map ConRon.Refine2.absU32 = (absRegion bs r).u32 g.val k.val := by
  rw [region_u32] at h
  peel h as i, hi
  peel h as i1, hi1
  peel h as i2, hi2
  peel h as i3, hi3
  peel h as i4, hi4
  peel h as i5, hi5
  peel h as i6, hi6
  have ei := scalar_at bs (r := r) hi hi1 hi2 hi3 hi4
  have ef := region_file_end_eq bs hi6
  have v5 := uscalar_add_eq hi5
  have l : (4#u64 : Std.U64).val = 4 := by decide
  rw [l] at v5
  simp only [ConLeche.Frontend.Olean.Region.u32, ← ei, ← ef]
  split at h
  · rename_i hc
    have hc' : i5.val ≤ i6.val := hc
    peel h as c, hcc
    cases Result.ok_injective h
    rw [ite_eq_left (by omega)]
    simp only [Option.map_some, rd_u32_eq hcc]; rfl
  · rename_i hc
    have hc' : ¬ i5.val ≤ i6.val := hc
    cases Result.ok_injective h
    rw [ite_eq_right (by omega)]; rfl

/-- **`region_bool` is `Region.bool`.** -/
theorem region_bool_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g k : Std.U64}
    {o : Option Bool} (h : region_bool bs r g k = ok o) :
    o = (absRegion bs r).bool g.val k.val := by
  rw [region_bool] at h
  peel h as o1, h1
  have e := region_u8_eq bs h1
  simp only [ConLeche.Frontend.Olean.Region.bool, ← e]
  cases o1 with
  | none => cases Result.ok_injective h; rfl
  | some c =>
    simp only [Option.map_some]
    dsimp only at h
    split at h
    · cases Result.ok_injective h; rfl
    · cases Result.ok_injective h; rfl
    · rename_i h0 h1'
      cases Result.ok_injective h
      have n0 : absByte c ≠ 0 := by
        intro he
        apply h0
        have := congrArg UInt8.toNat he
        rw [absByte_toNat] at this
        exact UScalar.eq_of_val_eq (by rw [this]; rfl)
      have n1 : absByte c ≠ 1 := by
        intro he
        apply h1'
        have := congrArg UInt8.toNat he
        rw [absByte_toNat] at this
        exact UScalar.eq_of_val_eq (by rw [this]; rfl)
      split
      · rename_i he; exact absurd (Option.some.inj he) n0
      · rename_i he; exact absurd (Option.some.inj he) n1
      · rfl

/-- **`region_is_ctor` is `Region.isCtor`.** -/
theorem region_is_ctor_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {g t n : Std.U64}
    {b : Bool} (h : region_is_ctor bs r g t n = ok b) :
    b = (absRegion bs r).isCtor g.val t.val n.val := by
  rw [region_is_ctor] at h
  peel h as i, hi
  have e1 := region_tag_eq bs (r := r) hi
  simp only [ConLeche.Frontend.Olean.Region.isCtor, ← e1]
  split at h
  · rename_i hc
    peel h as i1, hi1
    have e2 := region_nobjs_eq bs (r := r) hi1
    simp only [← e2, hc, BEq.rfl, Bool.true_and]
    split at h
    · rename_i hc2
      subst hc2
      simp only [BEq.rfl, Bool.true_and]
      exact region_fits_eq bs h
    · rename_i hc2
      cases Result.ok_injective h
      have : i1.val ≠ n.val := fun he => hc2 (UScalar.eq_of_val_eq he)
      simp [this]
  · rename_i hc
    cases Result.ok_injective h
    have : i.val ≠ t.val := fun he => hc (UScalar.eq_of_val_eq he)
    simp [this]


/-! ## The runtime's own object kinds -/

/-- **`limbs_fold` is `limbsFold`**, a well-formed number. -/
theorem limbs_fold_eq {b : Slice Std.U8} {lo : Std.U64} :
    ∀ (n : Nat) {i : Std.U64} {acc x : ron.nat.Nat}, i.val = n → NatWF acc →
      limbs_fold b lo i acc = ok x →
      toNat x = ConLeche.Frontend.Olean.limbsFold (absBytes b) lo.val n (toNat acc) ∧ NatWF x := by
  intro n
  induction n with
  | zero =>
    intro i acc x hi ha h
    rw [limbs_fold, limbs_fold_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    exact ⟨rfl, ha⟩
  | succ n ih =>
    intro i acc x hi ha h
    rw [limbs_fold, limbs_fold_loop, ite_eq_left (by scalar_tac)] at h
    peel h as i1, hi1
    peel h as top, htop
    peel h as i2, hi2
    peel h as i3, hi3
    peel h as w, hw
    peel h as m, hm
    peel h as acc1, hacc1
    have l : (1#u64 : Std.U64).val = 1 := by decide
    have l64 : (64#u64 : Std.U64).val = 64 := by decide
    have v1 : i1.val = n := by have := uscalar_sub_eq hi1; omega
    have v2 := uscalar_mul_eq hi2
    have v3 := uscalar_add_eq hi3
    rw [u64_val_lit8] at v2
    have e := rd_u64_eq hw
    obtain ⟨t1, -⟩ := ConRon.Refine.Nat.shift_left_refines htop
    obtain ⟨m1, -⟩ := ConRon.Refine.Nat.from_u64_refines hm
    obtain ⟨a1, a2⟩ := ConRon.Refine.Nat.add_refines hacc1
    rw [ConLeche.Frontend.Olean.limbsFold]
    have goal := ih v1 a2 h
    rw [goal.1, a1, t1, m1, l64, ConRon.Refine.Nat.nat_shiftLeft_eq]
    refine ⟨?_, goal.2⟩
    congr 2
    rw [← absWord_toNat w, e, v3, v2, v1]

/-- **`limbs` is `limbs`**, a well-formed number. -/
theorem limbs_eq {b : Slice Std.U8} :
    ∀ (N : Nat) {lo n : Std.U64} {x : ron.nat.Nat}, n.val = N →
      frontend.olean.region.limbs b lo n = ok x →
      toNat x = ConLeche.Frontend.Olean.limbs (absBytes b) lo.val N ∧ NatWF x := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro lo n x hn h
    rw [frontend.olean.region.limbs] at h
    rw [ConLeche.Frontend.Olean.limbs]
    split at h
    · rename_i hc
      have hc' : N ≤ 16 := by
        have : n.val ≤ (16#u64 : Std.U64).val := hc
        have l : (16#u64 : Std.U64).val = 16 := by decide
        omega
      rw [ite_eq_left hc']
      peel h as z, hz
      obtain ⟨z1, z2⟩ := ConRon.Refine.Nat.zero_refines hz
      have := limbs_fold_eq N hn z2 h
      rwa [z1] at this
    · rename_i hc
      have hc' : ¬ N ≤ 16 := by
        have : ¬ n.val ≤ (16#u64 : Std.U64).val := hc
        have l : (16#u64 : Std.U64).val = 16 := by decide
        omega
      rw [ite_eq_right hc']
      peel h as k, hk
      peel h as low, hlow
      peel h as i, hi
      peel h as i1, hi1
      peel h as i2, hi2
      peel h as high, hhigh
      peel h as i3, hi3
      peel h as n1, hn1
      have l2 : (2#u64 : Std.U64).val = 2 := by decide
      have l64 : (64#u64 : Std.U64).val = 64 := by decide
      have vk : k.val = N / 2 := by have := uscalar_div_eq hk; rw [l2] at this; omega
      have v := uscalar_mul_eq hi
      have v1 := uscalar_add_eq hi1
      have v2 := uscalar_sub_eq hi2
      have v3 := uscalar_mul_eq hi3
      rw [u64_val_lit8] at v
      rw [l64] at v3
      obtain ⟨e1, -⟩ := ih (N / 2) (by omega) vk hlow
      obtain ⟨e2, -⟩ := ih (N - N / 2) (by omega) (by omega) hhigh
      obtain ⟨s1, -⟩ := ConRon.Refine.Nat.shift_left_refines hn1
      obtain ⟨a1, a2⟩ := ConRon.Refine.Nat.add_refines h
      refine ⟨?_, a2⟩
      rw [a1, s1, e1, e2, v3, vk, v1, v, vk]
      simp [Nat.shiftLeft_eq]

/-- A location's arithmetic reads: the words of the object at `c`. -/
theorem i32_31 : (31#i32 : Std.I32).toNat = 31 := by decide

/-- `wrapping_add` is `UInt64`'s `+`. -/
theorem wrapping_add_24 (v : Std.U64) :
    absWord (core.num.U64.wrapping_add v 24#u64) = absWord v + 24 := by
  apply UInt64.toNat_inj.mp
  simp only [absWord_toNat, UInt64.toNat_add]
  have : (core.num.U64.wrapping_add v 24#u64).val = (v.val + 24) % 2 ^ 64 := by
    rw [UScalar.val, core.num.U64.wrapping_add, UScalar.wrapping_add_bv_eq, BitVec.toNat_add]; rfl
  rw [this]; rfl

/-- A number, as upstream's. -/
abbrev absNat (n : ron.nat.Nat) : Nat := toNat n

/-- **`region_mpz_at` is `Region.mpzAt`**, a well-formed number. -/
theorem region_mpz_at_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {c v : Std.U64}
    {o : Option ron.nat.Nat} (h : region_mpz_at bs r c v = ok o) :
    o.map absNat = (absRegion bs r).mpzAt c.val (absWord v) ∧ ∀ n, o = some n → NatWF n := by
  rw [region_mpz_at] at h
  peel h as t, ht
  have et := region_tag_eq bs (r := r) ht
  rw [ConLeche.Frontend.Olean.Region.mpzAt]
  have tv : ConLeche.Frontend.Olean.tagMPZ = 250 := rfl
  have tv2 := tag_mpz_val
  split at h
  · rename_i hc
    have hc' : (absRegion bs r).tag c.val = 250 := by rw [← et, hc, tv2]
    simp only [hc', tv, beq_self_eq_true, ↓reduceIte]
    peel h as i1, hi1
    peel h as size, hsize
    simp only [lift, bind_ok] at h
    peel h as i2, hi2
    have e1 := rd_u32_eq hsize
    have v1 := uscalar_add_eq hi1
    have l12 : (12#u64 : Std.U64).val = 12 := by decide
    rw [v1, l12] at e1
    have v2 := (ushiftLeftI_val hi2).2
    rw [i32_31] at v2
    have l1 : (1#u32 : Std.U32).val = 1 := by decide
    rw [l1] at v2
    have v2' : i2.val = 2 ^ 31 := by rw [v2]; decide
    have hsz : (rdU32 (absRegion bs r).bytes (c.val + 12)) = ConRon.Refine2.absU32 size := e1.symm
    rw [hsz]
    have hsv : (ConRon.Refine2.absU32 size).toNat = size.val := ConRon.Refine2.absU32_toNat size
    simp only [hsv]
    split at h
    · rename_i hlt
      have hlt' : size.val < 2 ^ 31 := by have : size.val < i2.val := hlt; omega
      have hlt2 : (ConRon.Refine2.absU32 size < 2 ^ 31) := by
        rw [UInt32.lt_iff_toNat_lt, hsv]; show size.val < 2147483648; omega
      peel h as i3, hi3
      peel h as i4, hi4
      have e3 := rd_u64_eq hi4
      have v3 := uscalar_add_eq hi3
      have l16 : (16#u64 : Std.U64).val = 16 := by decide
      rw [v3, l16] at e3
      have hw : absWord (core.num.U64.wrapping_add v 24#u64) = absWord v + 24 := wrapping_add_24 v
      rw [show rdU64 (absRegion bs r).bytes (c.val + 16) = absWord i4 from e3.symm]
      simp only [hlt2, decide_true, Bool.true_and]
      split at h
      · rename_i heq
        rw [← hw, heq]
        simp only [BEq.rfl, Bool.true_and]
        peel h as i6, hi6
        peel h as i7, hi7
        peel h as i8, hi8
        peel h as i9, hi9
        have v6 := uscalar_add_eq hi6
        have v7 := uscalar_mul_eq hi7
        have v8 := uscalar_add_eq hi8
        have e9 := region_file_end_eq bs hi9
        have l24 : (24#u64 : Std.U64).val = 24 := by decide
        rw [l24] at v6
        rw [u64_val_lit8, cast_u64_u32] at v7
        rw [← e9]
        split at h
        · rename_i hle
          have hle' : c.val + 24 + 8 * size.val ≤ i9.val := by
            have : i8.val ≤ i9.val := hle
            omega
          peel h as n1, hn1
          cases Result.ok_injective h
          obtain ⟨l1, l2⟩ := limbs_eq _ (cast_u64_u32 size) hn1
          rw [v6] at l1
          simp only [hle', decide_true, ↓reduceIte, Option.map_some]
          exact ⟨congrArg some l1, fun n hn => by cases hn; exact l2⟩
        · rename_i hle
          have hle' : ¬ c.val + 24 + 8 * size.val ≤ i9.val := by
            have : ¬ i8.val ≤ i9.val := hle
            omega
          cases Result.ok_injective h
          simp [hle']
      · rename_i hne
        cases Result.ok_injective h
        have : absWord i4 ≠ absWord v + 24 := by
          rw [← hw]; intro he; exact hne (absWord_inj he)
        simp [this]
    · rename_i hge
      have hge' : ¬ size.val < 2 ^ 31 := by have : ¬ size.val < i2.val := hge; omega
      have hge2 : ¬ (ConRon.Refine2.absU32 size < 2 ^ 31) := by
        rw [UInt32.lt_iff_toNat_lt, hsv]; show ¬ size.val < 2147483648; omega
      cases Result.ok_injective h
      simp [hge2]
  · rename_i hc
    cases Result.ok_injective h
    have hc' : (absRegion bs r).tag c.val ≠ 250 := by
      intro he; apply hc; apply UScalar.eq_of_val_eq; rw [et, he, tv2]
    simp [tv, hc']


/-- **`region_nat_p` is `Region.natP`**, a well-formed number. -/
theorem region_nat_p_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g v : Std.U64}
    {o : Option ron.nat.Nat} (h : region_nat_p bs r g v = ok o) :
    o.map absNat = (absRegion bs r).natP g.val (absWord v) ∧ ∀ n, o = some n → NatWF n := by
  rw [region_nat_p] at h
  peel h as b, hb
  have e := is_scalar_eq hb
  simp only [ConLeche.Frontend.Olean.Region.natP, ← e]
  split at h
  · rename_i hb1
    peel h as i, hi
    peel h as n, hn
    cases Result.ok_injective h
    obtain ⟨n1, n2⟩ := ConRon.Refine.Nat.from_u64_refines hn
    simp only [hb1, ↓reduceIte, Option.map_some]
    refine ⟨congrArg some (by rw [absNat, n1, unbox_eq hi]), fun _ hn => by cases hn; exact n2⟩
  · rename_i hb1
    peel h as o1, ho1
    have e1 := region_down_eq bs ho1
    simp only [hb1, Bool.false_eq_true, ↓reduceIte, ← e1]
    cases o1 with
    | none => cases Result.ok_injective h; exact ⟨rfl, fun _ hn => by cases hn⟩
    | some c => exact region_mpz_at_eq h

/-- A `Nat` as a saturating word. -/
theorem nat_saturate_eq {n : ron.nat.Nat} {k : Std.U64} (hn : NatWF n) (h : nat_saturate n = ok k) :
    k.val = min (absNat n) (2 ^ 64 - 1) := by
  rw [nat_saturate] at h
  peel h as o, ho
  rcases ConRon.Refine.Nat.to_u64_refines hn ho with ⟨x, rfl, hx⟩ | ⟨rfl, hx⟩
  · cases Result.ok_injective h
    have := u64_lt k
    simp only [absNat]
    omega
  · cases Result.ok_injective h
    simp only [absNat, u64_max_val]
    omega

/-- **What a word in a skeleton holds: `Nat`'s value, stopped at `u64::MAX`.** -/
def SatRel (k : Std.U64) (n : Nat) : Prop := k.val = min n (2 ^ 64 - 1)

/-- A word whose `Nat` is below the saturation point is that `Nat`. -/
theorem SatRel.val_of_ne {k : Std.U64} {n : Nat} (h : SatRel k n) (hk : k ≠ core.num.U64.MAX) :
    k.val = n := by
  have : k.val ≠ 2 ^ 64 - 1 := fun he => hk (UScalar.eq_of_val_eq (by rw [he, u64_max_val]))
  unfold SatRel at h
  omega

/-- The test `skel_fits` and `nat_word` make. -/
theorem SatRel.max_iff {k : Std.U64} {n : Nat} (h : SatRel k n) :
    k = core.num.U64.MAX ↔ 2 ^ 64 - 1 ≤ n := by
  unfold SatRel at h
  constructor
  · intro he
    rw [he, u64_max_val] at h
    omega
  · intro he
    exact UScalar.eq_of_val_eq (by rw [h, u64_max_val]; omega)

/-- **`region_nat_sat` is `Region.natP`, saturated.** -/
theorem region_nat_sat_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g v : Std.U64}
    {o : Option Std.U64} (h : region_nat_sat bs r g v = ok o) :
    Option.Rel SatRel o ((absRegion bs r).natP g.val (absWord v)) := by
  rw [region_nat_sat] at h
  peel h as b, hb
  have e := is_scalar_eq hb
  simp only [ConLeche.Frontend.Olean.Region.natP, ← e]
  split at h
  · rename_i hb1
    peel h as i, hi
    cases Result.ok_injective h
    simp only [hb1, ↓reduceIte]
    refine Option.Rel.some ?_
    have := unbox_eq hi
    have hlt := u64_lt i
    unfold SatRel
    omega
  · rename_i hb1
    peel h as o1, ho1
    have e1 := region_down_eq bs ho1
    simp only [hb1, Bool.false_eq_true, ↓reduceIte, ← e1]
    cases o1 with
    | none => cases Result.ok_injective h; exact Option.Rel.none
    | some c =>
      dsimp only at h
      peel h as o2, ho2
      obtain ⟨e2, e3⟩ := region_mpz_at_eq ho2
      simp only [Option.map_some, ← e2]
      cases o2 with
      | none => cases Result.ok_injective h; exact Option.Rel.none
      | some n =>
        dsimp only at h
        peel h as k, hk
        cases Result.ok_injective h
        exact Option.Rel.some (nat_saturate_eq (e3 n rfl) hk)

/-- A string, as upstream's. -/
abbrev absStr := ConRon.Refine.absString

/-- A location within the bytes casts to `usize` as itself. -/
theorem usize_of_le_len {bs : Slice Std.U8} {i : Std.U64} (hi : i.val ≤ bs.val.length) :
    (UScalar.cast UScalarTy.Usize i).val = i.val :=
  ConRon.Refine.ExprOps.u64_cast_usize_val (by scalar_tac)

/-- The file end a search answers is a file's end, or `0`. -/
theorem end_go_fits {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g : Std.U64}
    (hr : RegionFits bs r) :
    ∀ (n : Nat), (absRegion bs r).endGo g.val n ≤ bs.val.length ∧
      (absRegion bs r).endGo g.val n < 2 ^ 64 - 1 := by
  intro n
  induction n with
  | zero => simp [ConLeche.Frontend.Olean.Region.endGo]
  | succ n ih =>
    rw [ConLeche.Frontend.Olean.Region.endGo]
    split
    · rename_i hn
      rw [absRegion_size] at hn
      rw [absRegion_get bs r hn]
      dsimp only
      split
      · have := hr _ (List.getElem_mem hn)
        simpa [absSeg] using this
      · exact ih
    · simp

theorem file_end_fits {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g e : Std.U64}
    (hr : RegionFits bs r) (h : region_file_end r g = ok e) :
    e.val ≤ bs.val.length ∧ e.val < 2 ^ 64 - 1 := by
  rw [region_file_end_eq bs h]
  exact end_go_fits hr _

/-- **`region_str_at` is `Region.strAt`.** -/
theorem region_str_at_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {c : Std.U64}
    {o : Option (alloc.vec.Vec Std.U32)} (hr : RegionFits bs r) (h : region_str_at bs r c = ok o) :
    o.map absStr = (absRegion bs r).strAt c.val := by
  rw [region_str_at] at h
  peel h as t, ht
  have et := region_tag_eq bs (r := r) ht
  rw [ConLeche.Frontend.Olean.Region.strAt]
  have tv : ConLeche.Frontend.Olean.tagString = 249 := rfl
  have tv2 := tag_string_val
  split at h
  · rename_i hc
    have hc' : (absRegion bs r).tag c.val = 249 := by rw [← et, hc, tv2]
    simp only [hc', tv, beq_self_eq_true, ↓reduceIte]
    peel h as i1, hi1
    peel h as sz, hsz
    peel h as fe, hfe
    have v1 := uscalar_add_eq hi1
    have es := rd_u64_eq hsz
    have l8 := u64_val_lit8
    rw [v1, l8] at es
    rw [show rdU64 (absRegion bs r).bytes (c.val + 8) = absWord sz from es.symm, absWord_toNat,
      ← region_file_end_eq bs hfe]
    obtain ⟨ff1, ff2⟩ := file_end_fits hr hfe
    split at h
    · rename_i hsz1
      have hsz1' : 1 ≤ sz.val := hsz1
      peel h as i2, hi2
      peel h as i3, hi3
      have v2 := uscalar_add_eq hi2
      have l32 : (32#u64 : Std.U64).val = 32 := by decide
      rw [l32] at v2
      have v3 := sat_add_spec hi3
      split at h
      · rename_i hle
        have hle' : c.val + 32 + sz.val ≤ fe.val := by
          have : i3.val ≤ fe.val := hle
          omega
        peel h as i4, hi4
        peel h as i5, hi5
        peel h as i6, hi6
        have v4 := uscalar_add_eq hi4
        have v5 := uscalar_sub_eq hi5
        have l1 : (1#u64 : Std.U64).val = 1 := by decide
        rw [l1] at v5
        have e6 := rd_u8_eq hi6
        rw [v5, v4, v2] at e6
        rw [show rdU8 (absRegion bs r).bytes (c.val + 32 + sz.val - 1) = absByte i6 from e6.symm]
        simp only [hsz1', hle', decide_true, Bool.true_and]
        split at h
        · rename_i h0
          simp only [lift, bind_ok] at h
          peel h as i8, hi8
          peel h as i9, hi9
          have v8 := uscalar_add_eq hi8
          have v9 := uscalar_sub_eq hi9
          rw [l1] at v9
          have := utf8_decode_spec _ _ _ _ h
          rw [usize_of_le_len (bs := bs) (by omega), usize_of_le_len (bs := bs) (by omega), v9, v8, v2] at this
          rw [ite_eq_left (by rw [h0]; rfl)]
          exact this
        · rename_i h0
          cases Result.ok_injective h
          have : absByte i6 ≠ 0 := by
            intro he
            apply h0
            have := congrArg UInt8.toNat he
            rw [absByte_toNat] at this
            exact UScalar.eq_of_val_eq (by rw [this]; rfl)
          rw [ite_eq_right (fun hh => this (beq_iff_eq.mp hh))]
          rfl
      · rename_i hle
        have hle' : ¬ c.val + 32 + sz.val ≤ fe.val := by
          have : ¬ i3.val ≤ fe.val := hle
          omega
        cases Result.ok_injective h
        simp [hle']
    · rename_i hsz1
      have hsz1' : ¬ 1 ≤ sz.val := hsz1
      cases Result.ok_injective h
      simp [hsz1']
  · rename_i hc
    cases Result.ok_injective h
    have hc' : (absRegion bs r).tag c.val ≠ 249 := by
      intro he; apply hc; apply UScalar.eq_of_val_eq; rw [et, he, tv2]
    simp [tv, hc']

/-- **`region_str_p` is `Region.strP`.** -/
theorem region_str_p_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g v : Std.U64}
    {o : Option (alloc.vec.Vec Std.U32)} (hr : RegionFits bs r) (h : region_str_p bs r g v = ok o) :
    o.map absStr = (absRegion bs r).strP g.val (absWord v) := by
  rw [region_str_p] at h
  peel h as o1, ho1
  have e := region_down_eq bs ho1
  simp only [ConLeche.Frontend.Olean.Region.strP, ← e]
  cases o1 with
  | none => cases Result.ok_injective h; rfl
  | some c => exact region_str_at_eq hr h

/-- A list of locations, as upstream's. -/
def absLocs (v : alloc.vec.Vec Std.U64) : Array Nat := (v.val.map (·.val)).toArray

/-- A list of words, as upstream's. -/
def absWords (v : alloc.vec.Vec Std.U64) : Array UInt64 := (v.val.map absWord).toArray

/-- **`region_obj_array_go` is `Region.objArrayGo`.** -/
theorem region_obj_array_go_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {c lo n : Std.U64} :
    ∀ (m : Nat) {acc : alloc.vec.Vec Std.U64} {i : Std.U64} {o}, n.val - i.val = m →
      region_obj_array_go_loop bs r c lo n acc i = ok o →
      o.map absLocs = (absRegion bs r).objArrayGo c.val lo.val n.val i.val (absLocs acc) := by
  intro m
  induction m with
  | zero =>
    intro acc i o hm h
    rw [region_obj_array_go_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [ConLeche.Frontend.Olean.Region.objArrayGo, ite_eq_right (by omega)]
    rfl
  | succ m ih =>
    intro acc i o hm h
    have hlt : i.val < n.val := by omega
    rw [region_obj_array_go_loop, ite_eq_left (show i < n from hlt)] at h
    rw [ConLeche.Frontend.Olean.Region.objArrayGo, ite_eq_left hlt]
    peel h as i1, hi1
    peel h as i2, hi2
    peel h as i3, hi3
    peel h as o1, ho1
    have v1 := uscalar_mul_eq hi1
    have v2 := uscalar_add_eq hi2
    rw [u64_val_lit8] at v1
    have e3 := rd_u64_eq hi3
    rw [v2, v1] at e3
    rw [show rdU64 (absRegion bs r).bytes (lo.val + 8 * i.val) = absWord i3 from e3.symm,
      ← region_down_eq bs ho1]
    cases o1 with
    | none => cases Result.ok_injective h; rfl
    | some e =>
      dsimp only at h
      peel h as acc1, hacc1
      peel h as i4, hi4
      have l1 : (1#u64 : Std.U64).val = 1 := by decide
      have v4 := uscalar_add_eq hi4
      rw [l1] at v4
      have := ih (i := i4) (by omega) h
      rw [v4] at this
      have ea : absLocs acc1 = (absLocs acc).push e.val := by
        simp [absLocs, ConRon.Refine.vec_push_val hacc1]
      simp only [locOf, Option.map_some, ← ea]
      exact this

/-- **`region_obj_array` is `Region.objArray`.** -/
theorem region_obj_array_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g v : Std.U64}
    {o} (hr : RegionFits bs r) (h : region_obj_array bs r g v = ok o) :
    o.map absLocs = (absRegion bs r).objArray g.val (absWord v) := by
  rw [region_obj_array] at h
  peel h as o1, ho1
  rw [ConLeche.Frontend.Olean.Region.objArray, ← region_down_eq bs ho1]
  cases o1 with
  | none => cases Result.ok_injective h; rfl
  | some c =>
    dsimp only at h
    peel h as t, ht
    have et := region_tag_eq bs (r := r) ht
    have tv : ConLeche.Frontend.Olean.tagArray = 246 := rfl
    have tv2 := tag_array_val
    simp only [Option.map_some]
    split at h
    · rename_i hc
      have hc' : (absRegion bs r).tag c.val = 246 := by rw [← et, hc, tv2]
      simp only [hc', tv, beq_self_eq_true, ↓reduceIte]
      peel h as i1, hi1
      peel h as n, hn
      peel h as i2, hi2
      peel h as i3, hi3
      peel h as i4, hi4
      peel h as i5, hi5
      have v1 := uscalar_add_eq hi1
      have en := rd_u64_eq hn
      rw [v1, u64_val_lit8] at en
      have v2 := uscalar_add_eq hi2
      have l24 : (24#u64 : Std.U64).val = 24 := by decide
      rw [l24] at v2
      have v3 := sat_mul8_spec hi3
      have v4 := sat_add_spec hi4
      obtain ⟨ff1, ff2⟩ := file_end_fits hr hi5
      rw [show rdU64 (absRegion bs r).bytes (c.val + 8) = absWord n from en.symm, absWord_toNat,
        ← region_file_end_eq bs hi5]
      split at h
      · rename_i hle
        have hle' : c.val + 24 + 8 * n.val ≤ i5.val := by
          have : i4.val ≤ i5.val := hle
          omega
        rw [ite_eq_left hle']
        simp only [lift, bind_ok] at h
        have := region_obj_array_go_eq (n.val - (0#u64 : Std.U64).val) rfl h
        rw [v2] at this
        exact this
      · rename_i hle
        have hle' : ¬ c.val + 24 + 8 * n.val ≤ i5.val := by
          have : ¬ i4.val ≤ i5.val := hle
          omega
        cases Result.ok_injective h
        rw [ite_eq_right hle']; rfl
    · rename_i hc
      cases Result.ok_injective h
      have hc' : (absRegion bs r).tag c.val ≠ 246 := by
        intro he; apply hc; apply UScalar.eq_of_val_eq; rw [et, he, tv2]
      simp [tv, hc']

/-- **`region_list_go` is `Region.listGo`.**  By the location, as upstream's. -/
theorem region_list_go_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} :
    ∀ (m : Nat) {c : Std.U64} {acc o}, c.val = m → region_list_go_loop bs r c acc = ok o →
      o.map absWords = (absRegion bs r).listGo c.val (absWords acc) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c acc o hm h
    rw [region_list_go_loop] at h
    rw [ConLeche.Frontend.Olean.Region.listGo]
    peel h as b, hb
    have l1 : (1#u64 : Std.U64).val = 1 := by decide
    have l2 : (2#u64 : Std.U64).val = 2 := by decide
    have e := region_is_ctor_eq bs hb
    rw [l1, l2] at e
    rw [← e]
    split at h
    · rename_i hb1
      rw [ite_eq_left hb1]
      peel h as o1, ho1
      have e1 := region_ptr_fld_eq bs ho1
      have l0 : (0#u64 : Std.U64).val = 0 := by decide
      rw [l0] at e1
      rw [← e1]
      cases o1 with
      | none => cases Result.ok_injective h; rfl
      | some hd =>
        dsimp only at h
        peel h as acc1, hacc1
        peel h as tl, htl
        have e2 := region_fld_eq bs (r := r) htl
        rw [l1] at e2
        have ea : absWords acc1 = (absWords acc).push (absWord hd) := by
          simp [absWords, ConRon.Refine.vec_push_val hacc1]
        simp only [Option.map_some, ← e2, ← ea]
        split at h
        · rename_i ht
          cases Result.ok_injective h
          have : absWord tl = 1 := by rw [ht]; rfl
          simp [this]
        · rename_i ht
          have hn : (absWord tl == 1) = false := by
            rw [beq_eq_false_iff_ne]
            intro he
            apply ht
            have := congrArg UInt64.toNat he
            rw [absWord_toNat] at this
            exact UScalar.eq_of_val_eq (by rw [this]; rfl)
          simp only [hn, Bool.false_eq_true, ↓reduceIte]
          peel h as o2, ho2
          have e3 := region_down_eq bs ho2
          split
          · rename_i c2 hc2
            rw [← e2] at hc2
            have hlt : c2 < c.val := ConLeche.Frontend.Olean.Region.down_lt hc2
            rw [← e3] at hc2
            cases o2 with
            | none => cases hc2
            | some c3 =>
              have hc3 : c3.val = c2 := Option.some.inj hc2
              dsimp only at h
              have := ih c2 (by omega) hc3 h
              rw [hc3] at this
              exact this
          · rename_i hc2
            rw [← e2, ← e3] at hc2
            cases o2 with
            | none => cases Result.ok_injective h; rfl
            | some c3 => cases hc2
    · rename_i hb1
      rw [ite_eq_right hb1]
      cases Result.ok_injective h
      rfl

/-- **`region_list` is `Region.list`.** -/
theorem region_list_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g v : Std.U64} {o}
    (h : region_list bs r g v = ok o) :
    o.map absWords = (absRegion bs r).list g.val (absWord v) := by
  rw [region_list] at h
  rw [ConLeche.Frontend.Olean.Region.list]
  split at h
  · rename_i hv
    cases Result.ok_injective h
    have : absWord v = 1 := by rw [hv]; rfl
    simp only [this, BEq.rfl, ↓reduceIte]
    rfl
  · rename_i hv
    have hn : (absWord v == 1) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      apply hv
      have := congrArg UInt64.toNat he
      rw [absWord_toNat] at this
      exact UScalar.eq_of_val_eq (by rw [this]; rfl)
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    peel h as o1, ho1
    rw [← region_down_eq bs ho1]
    cases o1 with
    | none => cases Result.ok_injective h; rfl
    | some c => exact region_list_go_eq _ rfl h

end ConRon.Refine2.Frontend.Olean
