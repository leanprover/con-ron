/-
# `ConRon.Refine2.Frontend.Olean.Fast` — the mark pass of `olean/fast.rs`

**Task #142, Theorem 2.**  The twin's mark pass is upstream's own, so these are pure:
the marks are a `Vec U8` against `ByteArray` by `absM`, and each function is upstream's
on the abstraction (`MS`).  A location of a region lies inside its bytes (`region_loc_fits`),
which is what makes the Rust's `s as usize` the identity.
-/
import ConRon.Refine2.Frontend.Olean.Spec
import ConRon.Refine2.Frontend.Olean.Parts

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_fld region_down region_tag region_nobjs region_fits
  region_loc region_loc_go)
open frontend.olean.spec (name_shape)
open frontend.olean.fast (marks_at marked fail_m failed_m mark_ptr mark_two mark_name mark_level
  mark_levels mark_expr mark_slot mark_pass mark_pass_loop mark_root mark_roots mark_roots_loop
  max_loc max_loc_loop K_NAME K_LEVEL K_LEVELS K_EXPR)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConLeche.Frontend.Olean (marksAt failM failedM markPtr markName markLevel markLevels markExpr
  markKind markSlot markPass markRoot maxLoc kName kLevel kLevels kExpr rdU8)
open ConRon.Refine.HashMap (uscalar_add_eq uscalar_sub_eq uscalar_mul_eq uscalar_div_eq)

/-! ## A location lies inside the bytes -/

theorem locGo_fits {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    (a : UInt64) : ∀ n, (absRegion bs r).locGo a n = 0 ∨ (absRegion bs r).locGo a n + 8 ≤ bs.val.length := by
  intro n
  induction n with
  | zero => left; simp [ConLeche.Frontend.Olean.Region.locGo]
  | succ n ih =>
    rw [ConLeche.Frontend.Olean.Region.locGo]
    by_cases hn : n < (absRegion bs r).segs.size
    · rw [dite_eq_left hn]
      have hn' : n < r.segs.val.length := by rw [← absRegion_size bs r]; exact hn
      rw [absRegion_get bs r hn']
      have hs := (hr _ (List.getElem_mem hn')).1
      dsimp only
      split
      · split
        · rename_i h1
          right
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
          simp only [absSeg] at h1 ⊢
          omega
        · left; rfl
      · exact ih
    · rw [dite_eq_right hn]; left; rfl

/-- **A location of a region lies inside its bytes.** -/
theorem region_loc_fits {bs : Slice Std.U8} {r : frontend.olean.region.Region} {a c : Std.U64}
    (hr : RegionFits bs r) (h : region_loc r a = ok (some c)) : c.val + 8 ≤ bs.val.length := by
  have e := region_loc_eq bs h
  simp only [locOf, Option.map_some, ConLeche.Frontend.Olean.Region.loc] at e
  split at e
  · cases e
  · split at e
    · cases e
    · rename_i hg
      rw [Option.some.inj e]
      have hne : (absRegion bs r).locGo (absWord a) (absRegion bs r).segs.size ≠ 0 := by simpa using hg
      rcases locGo_fits hr (absWord a) (absRegion bs r).segs.size with h0 | h1
      · exact absurd h0 hne
      · exact h1

/-- A followed pointer's location lies inside the bytes. -/
theorem region_down_fits {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g v c : Std.U64}
    (hr : RegionFits bs r) (h : region_down r g v = ok (some c)) : c.val + 8 ≤ bs.val.length := by
  rw [region_down] at h
  peel h as o, ho
  cases o with
  | none => cases Result.ok_injective h
  | some c1 =>
    dsimp only at h
    split at h
    · cases Result.ok_injective h; exact region_loc_fits hr ho
    · cases Result.ok_injective h

/-- A slot of a location is a `usize`. -/
theorem slot_fits {bs : Slice Std.U8} {c s : Std.U64} (hc : c.val + 8 ≤ bs.val.length)
    (hs : (c / 8#u64) = ok s) : s.val ≤ Std.Usize.max := by
  have hv := uscalar_div_eq hs
  rw [u64_val_lit8] at hv
  have hl : bs.val.length ≤ Std.Usize.max := by scalar_tac
  omega

/-! ## The bytes -/

/-- The marks, as upstream's. -/
abbrev absM (m : alloc.vec.Vec Std.U8) : ByteArray := absBytes (alloc.vec.Vec.deref m)

theorem absM_data (m : alloc.vec.Vec Std.U8) : (absM m).data = (m.val.map absByte).toArray := by
  simp [absBytes, deref_val]

theorem absM_ext {m : alloc.vec.Vec Std.U8} {M : ByteArray} (h : m.val.map absByte = M.data.toList) :
    absM m = M := by
  apply ByteArray.ext
  rw [absM_data, h]

theorem absByte_and (a b : Std.U8) : absByte (a &&& b) = absByte a &&& absByte b := by
  apply UInt8.toNat_inj.mp
  rw [absByte_toNat, UInt8.toNat_and, absByte_toNat, absByte_toNat, UScalar.val_and]

theorem absByte_or (a b : Std.U8) : absByte (a ||| b) = absByte a ||| absByte b := by
  apply UInt8.toNat_inj.mp
  rw [absByte_toNat, UInt8.toNat_or, absByte_toNat, absByte_toNat, UScalar.val_or]

theorem absByte_bne_zero (a : Std.U8) : (a != 0#u8) = (absByte a != 0) := by
  by_cases h : a = 0#u8
  · subst h; rfl
  · have h2 : absByte a ≠ 0 := by
      intro he
      apply h
      have := congrArg UInt8.toNat he
      rw [absByte_toNat] at this
      exact UScalar.eq_of_val_eq this
    rw [bne_iff_ne.mpr h, bne_iff_ne.mpr h2]

@[simp] theorem absByte_k_name : absByte K_NAME = kName := by unfold K_NAME; rfl
@[simp] theorem absByte_k_level : absByte K_LEVEL = kLevel := by unfold K_LEVEL; rfl
@[simp] theorem absByte_k_levels : absByte K_LEVELS = kLevels := by unfold K_LEVELS; rfl
@[simp] theorem absByte_k_expr : absByte K_EXPR = kExpr := by unfold K_EXPR; rfl

/-- A write of the marks, in range. -/
theorem absM_set {m : alloc.vec.Vec Std.U8} {i : Std.Usize} {x : Std.U8} :
    absM (alloc.vec.Vec.set m i x) = (absM m).set! i.val (absByte x) := by
  apply absM_ext
  show _ = ((absM m).data.set! i.val (absByte x)).toList
  rw [absM_data]
  simp [alloc.vec.Vec.set_val_eq, List.map_set]

theorem u8_index_mut {v : alloc.vec.Vec Std.U8} {i : Std.Usize} {x : Std.U8} {f : Std.U8 → alloc.vec.Vec Std.U8}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Std.U8) v i = ok (x, f)) :
    i.val < v.val.length ∧ f = alloc.vec.Vec.set v i := by
  obtain ⟨h1, -, h3⟩ := ConRon.Refine.HashMap.vec_index_mut_eq h
  exact ⟨h1, h3⟩

/-- **`marks_at` is `marksAt`.** -/
theorem marks_at_eq {m : alloc.vec.Vec Std.U8} {s : Std.U64} {x : Std.U8} (h : marks_at m s = ok x) :
    absByte x = marksAt (absM m) s.val :=
  rd_u8_eq h

/-- **`marked` is `marked`.** -/
theorem marked_eq {m : alloc.vec.Vec Std.U8} {k : Std.U8} {s : Std.U64} {b : Bool}
    (h : marked m k s = ok b) :
    b = ConLeche.Frontend.Olean.marked (absM m) (absByte k) s.val := by
  rw [marked] at h
  peel h as x, hx
  simp only [lift, bind_ok] at h
  cases Result.ok_injective h
  simp only [ConLeche.Frontend.Olean.marked, ← marks_at_eq hx]
  rw [absByte_bne_zero, absByte_and]

/-- **`mark` is `mark`.** -/
theorem mark_eq {m : alloc.vec.Vec Std.U8} {k : Std.U8} {s : Std.U64} {m' : alloc.vec.Vec Std.U8}
    (hs : s.val ≤ Std.Usize.max) (h : frontend.olean.fast.mark m k s = ok m') :
    absM m' = ConLeche.Frontend.Olean.mark (absM m) (absByte k) s.val := by
  rw [frontend.olean.fast.mark] at h
  simp only [lift, bind_ok] at h
  have hc := ConRon.Refine.ExprOps.u64_cast_usize_val hs
  simp only [ConLeche.Frontend.Olean.mark]
  split at h
  · rename_i hlt
    have hlt' : s.val < m.val.length := by
      have : (UScalar.cast UScalarTy.Usize s).val < (alloc.vec.Vec.len m).val := hlt
      rw [hc] at this; simpa using this
    peel h as x, hx
    peel h as p, hp
    obtain ⟨y, f⟩ := p
    obtain ⟨-, rfl⟩ := u8_index_mut hp
    cases Result.ok_injective h
    obtain ⟨_, he⟩ := vec_index_eq hx
    have hxx : absByte x = marksAt (absM m) s.val := by
      apply UInt8.toNat_inj.mp
      show _ = (rdU8 (absM m) s.val).toNat
      rw [rdU8_absBytes, absByte_toNat, dite_eq_left (by rw [deref_val]; exact hlt')]
      simp only [he, deref_val, hc]
    rw [absM_set, absByte_or, hc, hxx]
  · rename_i hge
    have hge' : ¬ s.val < m.val.length := by
      have : ¬ (UScalar.cast UScalarTy.Usize s).val < (alloc.vec.Vec.len m).val := hge
      rw [hc] at this; simpa using this
    cases Result.ok_injective h
    apply ByteArray.ext
    show _ = ((absM m).data.set! s.val _)
    rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le]
    rw [absM_data]; simp; omega

/-! ## `MS`: a step of the marks -/

/-- A marks function of the Rust against upstream's value. -/
def MS (x : Result (alloc.vec.Vec Std.U8)) (y : ByteArray) : Prop := ∀ m', x = ok m' → absM m' = y

theorem MS.pure_step {γ : Type} {f : Result γ} {k : γ → Result (alloc.vec.Vec Std.U8)} {y : ByteArray}
    (h : ∀ a, f = ok a → MS (k a) y) : MS (Std.bind f k) y := by
  intro m' hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 _ h2

theorem MS.ok {m : alloc.vec.Vec Std.U8} : MS (ok m) (absM m) := by
  intro m' h; cases Result.ok_injective h; rfl

/-- **`fail_m` is `failM`.** -/
theorem fail_m_ms {m : alloc.vec.Vec Std.U8} : MS (fail_m m) (failM (absM m)) := by
  intro m' h
  rw [fail_m] at h
  peel h as p, hp
  obtain ⟨y, f⟩ := p
  obtain ⟨-, rfl⟩ := u8_index_mut hp
  cases Result.ok_injective h
  rw [absM_set]
  rfl

/-- **`failed_m` is `failedM`.** -/
theorem failed_m_eq {m : alloc.vec.Vec Std.U8} {b : Bool} (h : failed_m m = ok b) :
    b = failedM (absM m) := by
  rw [failed_m] at h
  peel h as x, hx
  simp only [lift, bind_ok] at h
  cases Result.ok_injective h
  simp only [failedM]
  have := marks_at_eq hx
  rw [show (0#u64 : Std.U64).val = 0 by decide] at this
  rw [← this, absByte_bne_zero, absByte_and]
  rfl

/-- **`mark_ptr` is `markPtr`.** -/
theorem mark_ptr_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g v : Std.U64}
    {k : Std.U8} {nil : Bool} {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (mark_ptr r m g k nil v) (markPtr (absRegion bs r) (absM m) g.val (absByte k) nil (absWord v)) := by
  have tail : MS (do
        let o ← region_down r g v
        match o with
        | none => fail_m m
        | some c => do
          let i ← c / 8#u64
          frontend.olean.fast.mark m k i)
      (match (absRegion bs r).down g.val (absWord v) with
       | some c => ConLeche.Frontend.Olean.mark (absM m) (absByte k) (c / 8)
       | none => failM (absM m)) := by
    refine MS.pure_step fun o ho => ?_
    rw [← region_down_eq bs ho]
    cases o with
    | none => exact fail_m_ms
    | some c =>
      refine MS.pure_step fun s hs => ?_
      intro m' hm
      have hv := uscalar_div_eq hs
      rw [u64_val_lit8] at hv
      simp only [locOf, Option.map_some, ← hv]
      exact mark_eq (slot_fits (region_down_fits hr ho) hs) hm
  rw [mark_ptr]
  simp only [markPtr]
  cases nil with
  | false => exact tail
  | true =>
    by_cases hv : v = 1#u64
    · subst hv
      have : (absWord 1#u64 == 1) = true := rfl
      simp only [Bool.true_and, this, ↓reduceIte]
      exact MS.ok
    · simp only [hv, ↓reduceIte, Bool.true_and]
      rw [ite_eq_right (fun he => hv (word_eq_one.mp he))]
      exact tail

/-- The bind of a marks function with a function of the marks. -/
theorem MS.bind_of {x : Result (alloc.vec.Vec Std.U8)} {y : ByteArray}
    {k : alloc.vec.Vec Std.U8 → Result (alloc.vec.Vec Std.U8)} {z : ByteArray → ByteArray}
    (hx : MS x y) (hk : ∀ m1, MS (k m1) (z (absM m1))) : MS (Std.bind x k) (z y) := by
  intro m' hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  rw [← hx a h1]
  exact hk a _ h2

/-- **`mark_two` is the arms of two followed fields.** -/
theorem mark_two_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g n want f1 f2 : Std.U64}
    {k1 k2 : Std.U8} {nil1 nil2 : Bool} {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (mark_two bs r g m n want k1 nil1 f1 k2 nil2 f2)
      (if n.val = want.val then
        markPtr (absRegion bs r) (markPtr (absRegion bs r) (absM m) g.val (absByte k1) nil1
          ((absRegion bs r).fld g.val f1.val)) g.val (absByte k2) nil2 ((absRegion bs r).fld g.val f2.val)
       else failM (absM m)) := by
  rw [mark_two]
  by_cases hn : n = want
  · subst hn
    rw [ite_eq_left rfl, ite_eq_left rfl]
    refine MS.pure_step fun i hi => ?_
    rw [← region_fld_eq bs hi]
    refine MS.bind_of (z := fun M => markPtr (absRegion bs r) M g.val (absByte k2) nil2 ((absRegion bs r).fld g.val f2.val))
      (mark_ptr_ms hr) (fun m1 => MS.pure_step fun i1 hi1 => ?_)
    rw [← region_fld_eq bs hi1]
    exact mark_ptr_ms hr
  · rw [ite_eq_right hn, ite_eq_right (u64_lit_ne hn)]
    exact fail_m_ms

/-- The arms of one followed field. -/
theorem mark_one_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g n want f : Std.U64}
    {k : Std.U8} {nil : Bool} {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (if n = want then do
          let i ← region_fld bs g f
          mark_ptr r m g k nil i
        else fail_m m)
      (if n.val = want.val then
        markPtr (absRegion bs r) (absM m) g.val (absByte k) nil ((absRegion bs r).fld g.val f.val)
       else failM (absM m)) := by
  by_cases hn : n = want
  · subst hn
    rw [ite_eq_left rfl, ite_eq_left rfl]
    refine MS.pure_step fun i hi => ?_
    rw [← region_fld_eq bs hi]
    exact mark_ptr_ms hr
  · rw [ite_eq_right hn, ite_eq_right (u64_lit_ne hn)]
    exact fail_m_ms

/-- The arms that follow nothing. -/
theorem mark_none_ms {n want : Std.U64} {m : alloc.vec.Vec Std.U8} :
    MS (if n != want then fail_m m else ok m)
      (if n.val = want.val then absM m else failM (absM m)) := by
  by_cases hn : n = want
  · subst hn
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact MS.ok
  · rw [ite_eq_left (by simpa using hn), ite_eq_right (u64_lit_ne hn)]
    exact fail_m_ms

/-- A shape's arm of `markExpr` with three followed fields. -/
theorem mark_three_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g n : Std.U64}
    {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (if n = 4#u64 then do
          let i1 ← region_fld bs g 1#u64
          let m1 ← mark_ptr r m g K_EXPR false i1
          let i2 ← region_fld bs g 2#u64
          let m2 ← mark_ptr r m1 g K_EXPR false i2
          let i3 ← region_fld bs g 3#u64
          mark_ptr r m2 g K_EXPR false i3
        else fail_m m)
      (if n.val = (4#u64 : Std.U64).val then
        markPtr (absRegion bs r) (markPtr (absRegion bs r) (markPtr (absRegion bs r) (absM m) g.val
          (absByte K_EXPR) false ((absRegion bs r).fld g.val 1)) g.val (absByte K_EXPR) false
          ((absRegion bs r).fld g.val 2)) g.val (absByte K_EXPR) false ((absRegion bs r).fld g.val 3)
       else failM (absM m)) := by
  by_cases hn : n = 4#u64
  · subst hn
    rw [ite_eq_left rfl, ite_eq_left rfl]
    refine MS.pure_step fun i hi => ?_
    rw [fld_1 hi]
    refine MS.bind_of (z := fun M => markPtr (absRegion bs r) (markPtr (absRegion bs r) M g.val
      (absByte K_EXPR) false ((absRegion bs r).fld g.val 2)) g.val (absByte K_EXPR) false
      ((absRegion bs r).fld g.val 3)) (mark_ptr_ms hr) (fun m1 => MS.pure_step fun i1 hi1 => ?_)
    rw [fld_2 hi1]
    refine MS.bind_of (z := fun M => markPtr (absRegion bs r) M g.val (absByte K_EXPR) false
      ((absRegion bs r).fld g.val 3)) (mark_ptr_ms hr) (fun m2 => MS.pure_step fun i2 hi2 => ?_)
    rw [fld_3 hi2]
    exact mark_ptr_ms hr
  · rw [ite_eq_right hn, ite_eq_right (u64_lit_ne hn)]
    exact fail_m_ms

/-- An arm of upstream's match on `(tag, nobjs)`: at the arm's number of fields the fact
`h` holds, at any other the match's last arm. -/
macro "mark_arm " n:ident want:term:max h:term : tactic =>
  `(tactic| (have h_ := $h:term
             by_cases hN : $n:ident = $want:term
             · subst hN
               rw [ite_eq_left (show UScalar.val ($want : Std.U64) = UScalar.val ($want : Std.U64) from rfl)] at h_
               try simp only [absByte_k_name, absByte_k_level, absByte_k_levels, absByte_k_expr] at h_
               exact h_
             · rw [ite_eq_right (u64_lit_ne hN)] at h_
               have hv := u64_lit_ne hN
               twin_arm $n:ident hv h_))

/-- **`mark_name` is `markName`.** -/
theorem mark_name_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g : Std.U64}
    {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (mark_name bs r g m) (markName (absRegion bs r) g.val (absM m)) := by
  rw [mark_name]
  simp only [markName]
  refine MS.pure_step fun b hb => ?_
  rw [← region_fits_eq bs hb]
  split
  · refine MS.pure_step fun t ht => MS.pure_step fun n hn => MS.pure_step fun b1 hb1 => ?_
    rw [← region_tag_eq bs ht, ← region_nobjs_eq bs hn]
    have hs := name_shape_eq hb1
    split
    · rename_i hb2
      rw [hb2] at hs
      have hs' : (t.val = 1 ∨ t.val = 2) ∧ n.val = 2 := by simpa using hs.symm
      refine MS.pure_step fun i hi => ?_
      rw [← absByte_k_name]
      obtain ⟨h1 | h1, h2⟩ := hs' <;> rw [h1, h2]
      · show MS _ (markPtr _ _ _ _ _ ((absRegion bs r).fld g.val 0))
        rw [fld_0 hi]
        exact mark_ptr_ms hr
      · show MS _ (markPtr _ _ _ _ _ ((absRegion bs r).fld g.val 0))
        rw [fld_0 hi]
        exact mark_ptr_ms hr
    · rename_i hb2
      have hs' : ¬ ((t.val = 1 ∨ t.val = 2) ∧ n.val = 2) := by
        intro hc
        apply hb2
        rw [hs]
        simp [hc.1, hc.2]
      split
      · exact absurd ⟨Or.inl (by assumption), by assumption⟩ hs'
      · exact absurd ⟨Or.inr (by assumption), by assumption⟩ hs'
      · exact fail_m_ms
  · exact fail_m_ms

/-- **`mark_level` is `markLevel`.** -/
theorem mark_level_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g : Std.U64}
    {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (mark_level bs r g m) (markLevel (absRegion bs r) g.val (absM m)) := by
  rw [mark_level]
  simp only [markLevel]
  refine MS.pure_step fun b hb => ?_
  rw [← region_fits_eq bs hb]
  split
  · refine MS.pure_step fun n hn => MS.pure_step fun t ht => ?_
    rw [← region_tag_eq bs ht, ← region_nobjs_eq bs hn]
    split
    · mark_arm n 0#u64 (mark_none_ms (n := n) (want := 0#u64) (m := m))
    · mark_arm n 1#u64 (mark_one_ms (bs := bs) (g := g) (n := n) (want := 1#u64) (f := 0#u64)
        (k := K_LEVEL) (nil := true) (m := m) hr)
    · mark_arm n 2#u64 (mark_two_ms (bs := bs) (g := g) (n := n) (want := 2#u64) (f1 := 0#u64)
        (f2 := 1#u64) (k1 := K_LEVEL) (k2 := K_LEVEL) (nil1 := true) (nil2 := true) (m := m) hr)
    · mark_arm n 2#u64 (mark_two_ms (bs := bs) (g := g) (n := n) (want := 2#u64) (f1 := 0#u64)
        (f2 := 1#u64) (k1 := K_LEVEL) (k2 := K_LEVEL) (nil1 := true) (nil2 := true) (m := m) hr)
    · mark_arm n 1#u64 (mark_one_ms (bs := bs) (g := g) (n := n) (want := 1#u64) (f := 0#u64)
        (k := K_NAME) (nil := true) (m := m) hr)
    · rename_i h0 h1 h2 h3 h4
      have e0 : t.val ≠ 0 := fun he => h0 (UScalar.eq_of_val_eq he)
      have e1 : t.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq he)
      have e2 : t.val ≠ 2 := fun he => h2 (UScalar.eq_of_val_eq he)
      have e3 : t.val ≠ 3 := fun he => h3 (UScalar.eq_of_val_eq he)
      have e4 : t.val ≠ 4 := fun he => h4 (UScalar.eq_of_val_eq he)
      generalize UScalar.val t = T at e0 e1 e2 e3 e4 ⊢
      rcases T with _ | _ | _ | _ | _ | T
      · exact absurd rfl e0
      · exact absurd rfl e1
      · exact absurd rfl e2
      · exact absurd rfl e3
      · exact absurd rfl e4
      · exact fail_m_ms
  · exact fail_m_ms

/-- **`mark_levels` is `markLevels`.** -/
theorem mark_levels_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g : Std.U64}
    {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (mark_levels bs r g m) (markLevels (absRegion bs r) g.val (absM m)) := by
  rw [mark_levels]
  simp only [markLevels]
  refine MS.pure_step fun b hb => ?_
  rw [← region_fits_eq bs hb]
  split
  · refine MS.pure_step fun t ht => ?_
    rw [← region_tag_eq bs ht]
    by_cases h1 : t = 1#u64
    · subst h1
      rw [ite_eq_left rfl]
      refine MS.pure_step fun n hn => ?_
      rw [← region_nobjs_eq bs hn]
      mark_arm n 2#u64 (mark_two_ms (bs := bs) (g := g) (n := n) (want := 2#u64) (f1 := 0#u64)
        (f2 := 1#u64) (k1 := K_LEVEL) (k2 := K_LEVELS) (nil1 := true) (nil2 := true) (m := m) hr)
    · rw [ite_eq_right h1]
      have e1 : t.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq he)
      split
      · exact absurd (by assumption) e1
      · exact fail_m_ms
  · exact fail_m_ms

/-- **`mark_expr` is `markExpr`.** -/
theorem mark_expr_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g : Std.U64}
    {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (mark_expr bs r g m) (markExpr (absRegion bs r) g.val (absM m)) := by
  rw [mark_expr]
  simp only [markExpr]
  refine MS.pure_step fun b hb => ?_
  rw [← region_fits_eq bs hb]
  split
  · refine MS.pure_step fun n hn => MS.pure_step fun t ht => ?_
    rw [← region_tag_eq bs ht, ← region_nobjs_eq bs hn]
    split
    · mark_arm n 2#u64 (mark_two_ms (bs := bs) (g := g) (n := n) (want := 2#u64) (f1 := 0#u64)
        (f2 := 1#u64) (k1 := K_EXPR) (k2 := K_EXPR) (nil1 := false) (nil2 := false) (m := m) hr)
    · mark_arm n 1#u64 (mark_none_ms (n := n) (want := 1#u64) (m := m))
    · mark_arm n 1#u64 (mark_one_ms (bs := bs) (g := g) (n := n) (want := 1#u64) (f := 0#u64)
        (k := K_LEVEL) (nil := true) (m := m) hr)
    · mark_arm n 2#u64 (mark_two_ms (bs := bs) (g := g) (n := n) (want := 2#u64) (f1 := 0#u64)
        (f2 := 1#u64) (k1 := K_NAME) (k2 := K_LEVELS) (nil1 := true) (nil2 := true) (m := m) hr)
    · mark_arm n 3#u64 (mark_two_ms (bs := bs) (g := g) (n := n) (want := 3#u64) (f1 := 1#u64)
        (f2 := 2#u64) (k1 := K_EXPR) (k2 := K_EXPR) (nil1 := false) (nil2 := false) (m := m) hr)
    · mark_arm n 3#u64 (mark_two_ms (bs := bs) (g := g) (n := n) (want := 3#u64) (f1 := 1#u64)
        (f2 := 2#u64) (k1 := K_EXPR) (k2 := K_EXPR) (nil1 := false) (nil2 := false) (m := m) hr)
    · mark_arm n 4#u64 (mark_three_ms (bs := bs) (g := g) (n := n) (m := m) hr)
    · mark_arm n 1#u64 (mark_none_ms (n := n) (want := 1#u64) (m := m))
    · mark_arm n 2#u64 (mark_one_ms (bs := bs) (g := g) (n := n) (want := 2#u64) (f := 1#u64)
        (k := K_EXPR) (nil := false) (m := m) hr)
    · mark_arm n 3#u64 (mark_two_ms (bs := bs) (g := g) (n := n) (want := 3#u64) (f1 := 0#u64)
        (f2 := 2#u64) (k1 := K_NAME) (k2 := K_EXPR) (nil1 := true) (nil2 := false) (m := m) hr)
    · rename_i h5 h0 h3 h4 h6 h7 h8 h9 h10 h11
      have e0 : t.val ≠ 0 := fun he => h0 (UScalar.eq_of_val_eq he)
      have e3 : t.val ≠ 3 := fun he => h3 (UScalar.eq_of_val_eq he)
      have e4 : t.val ≠ 4 := fun he => h4 (UScalar.eq_of_val_eq he)
      have e5 : t.val ≠ 5 := fun he => h5 (UScalar.eq_of_val_eq he)
      have e6 : t.val ≠ 6 := fun he => h6 (UScalar.eq_of_val_eq he)
      have e7 : t.val ≠ 7 := fun he => h7 (UScalar.eq_of_val_eq he)
      have e8 : t.val ≠ 8 := fun he => h8 (UScalar.eq_of_val_eq he)
      have e9 : t.val ≠ 9 := fun he => h9 (UScalar.eq_of_val_eq he)
      have e10 : t.val ≠ 10 := fun he => h10 (UScalar.eq_of_val_eq he)
      have e11 : t.val ≠ 11 := fun he => h11 (UScalar.eq_of_val_eq he)
      generalize UScalar.val t = T at e0 e3 e4 e5 e6 e7 e8 e9 e10 e11 ⊢
      rcases T with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | T
      · exact absurd rfl e0
      · exact fail_m_ms
      · exact fail_m_ms
      · exact absurd rfl e3
      · exact absurd rfl e4
      · exact absurd rfl e5
      · exact absurd rfl e6
      · exact absurd rfl e7
      · exact absurd rfl e8
      · exact absurd rfl e9
      · exact absurd rfl e10
      · exact absurd rfl e11
      · exact fail_m_ms
  · exact fail_m_ms

/-! ## The sweep -/

theorem mul8_val {p i : Std.U64} (h : 8#u64 * p = ok i) : i.val = 8 * p.val := by
  have := uscalar_mul_eq h
  rwa [u64_val_lit8] at this

/-- The last kind of `mark_slot`. -/
theorem kind_last {bs : Slice Std.U8} {r : frontend.olean.region.Region} {p : Std.U64} {k : Std.U8}
    {m : alloc.vec.Vec Std.U8} {fr : Std.U64 → alloc.vec.Vec Std.U8 → Result (alloc.vec.Vec Std.U8)}
    {fu : ConLeche.Frontend.Olean.Region → Nat → ByteArray → ByteArray}
    (hf : ∀ g m, MS (fr g m) (fu (absRegion bs r) g.val (absM m))) :
    MS (do
        let b ← marked m k p
        if b then do
            let i ← 8#u64 * p
            fr i m
          else Result.ok m)
      (markKind (absRegion bs r) (absByte k) fu p.val (absM m)) := by
  refine MS.pure_step fun b hb => ?_
  simp only [markKind]
  rw [← marked_eq hb]
  split
  · refine MS.pure_step fun i hi => ?_
    rw [← mul8_val hi]
    exact hf _ _
  · exact MS.ok

/-- A kind of `mark_slot`, with what follows it. -/
theorem kind_step {bs : Slice Std.U8} {r : frontend.olean.region.Region} {p : Std.U64} {k : Std.U8}
    {m : alloc.vec.Vec Std.U8} {fr : Std.U64 → alloc.vec.Vec Std.U8 → Result (alloc.vec.Vec Std.U8)}
    {fu : ConLeche.Frontend.Olean.Region → Nat → ByteArray → ByteArray}
    {K : alloc.vec.Vec Std.U8 → Result (alloc.vec.Vec Std.U8)} {z : ByteArray → ByteArray}
    (hf : ∀ g m, MS (fr g m) (fu (absRegion bs r) g.val (absM m)))
    (hk : ∀ m1, MS (K m1) (z (absM m1))) :
    MS (do
        let b ← marked m k p
        let m1 ← if b then do
            let i ← 8#u64 * p
            fr i m
          else Result.ok m
        K m1)
      (z (markKind (absRegion bs r) (absByte k) fu p.val (absM m))) := by
  refine MS.pure_step fun b hb => ?_
  simp only [markKind]
  rw [← marked_eq hb]
  refine MS.bind_of ?_ hk
  split
  · refine MS.pure_step fun i hi => ?_
    rw [← mul8_val hi]
    exact hf _ _
  · exact MS.ok

/-- **`mark_slot` is `markSlot`.** -/
theorem mark_slot_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {p : Std.U64}
    {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (mark_slot bs r p m) (markSlot (absRegion bs r) p.val (absM m)) := by
  rw [mark_slot]
  simp only [markSlot, ← absByte_k_name, ← absByte_k_level, ← absByte_k_levels, ← absByte_k_expr]
  refine kind_step (z := fun M => markKind (absRegion bs r) (absByte K_EXPR) markExpr p.val
      (markKind (absRegion bs r) (absByte K_LEVELS) markLevels p.val
        (markKind (absRegion bs r) (absByte K_LEVEL) markLevel p.val M)))
    (fr := mark_name bs r) (fun _ _ => mark_name_ms hr) fun m1 => ?_
  refine kind_step (z := fun M => markKind (absRegion bs r) (absByte K_EXPR) markExpr p.val
      (markKind (absRegion bs r) (absByte K_LEVELS) markLevels p.val M))
    (fr := mark_level bs r) (fun _ _ => mark_level_ms hr) fun m2 => ?_
  refine kind_step (z := fun M => markKind (absRegion bs r) (absByte K_EXPR) markExpr p.val M)
    (fr := mark_levels bs r) (fun _ _ => mark_levels_ms hr) fun m3 => ?_
  exact kind_last (fr := mark_expr bs r) (fun _ _ => mark_expr_ms hr)

/-- **`mark_pass` is `markPass`.** -/
theorem mark_pass_loop_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r) :
    ∀ (n : Nat) {m : alloc.vec.Vec Std.U8} {p : Std.U64}, p.val = n →
      MS (mark_pass_loop bs r m p) (markPass (absRegion bs r) (absM m) n) := by
  intro n
  induction n with
  | zero =>
    intro m p hp
    rw [mark_pass_loop, ite_eq_right (by scalar_tac)]
    exact MS.ok
  | succ n ih =>
    intro m p hp
    rw [mark_pass_loop, ite_eq_left (by scalar_tac)]
    refine MS.pure_step fun p1 hp1 => MS.pure_step fun i hi => ?_
    have hv : p1.val = n := by
      have := uscalar_sub_eq hp1
      have l : (1#u64 : Std.U64).val = 1 := by decide
      omega
    rw [markPass, ← hv, ← marks_at_eq hi, ← absByte_bne_zero, hv]
    by_cases hb : (i != 0#u8) = true
    · rw [ite_eq_left hb, ite_eq_left hb]
      rw [← hv]
      refine MS.bind_of (z := fun M => if failedM M = true then M else markPass (absRegion bs r) M p1.val)
        (mark_slot_ms hr) (fun m1 => MS.pure_step fun b hb1 => ?_)
      rw [← failed_m_eq hb1]
      split
      · exact MS.ok
      · exact ih (by rw [hv]) |> fun h => by rw [hv]; exact h
    · rw [ite_eq_right hb, ite_eq_right hb]
      exact ih hv

theorem mark_pass_ms {bs : Slice Std.U8} {r : frontend.olean.region.Region} {p : Std.U64}
    {m : alloc.vec.Vec Std.U8} (hr : RegionFits bs r) :
    MS (mark_pass bs r m p) (markPass (absRegion bs r) (absM m) p.val) := by
  rw [mark_pass]
  exact mark_pass_loop_ms hr _ rfl

/-! ## The roots -/

/-- What `mark_root` and `mark_roots` answer, as upstream's `Option`. -/
def rootAbs (o : Bool × alloc.vec.Vec Std.U8) : Option ByteArray :=
  if o.1 then some (absM o.2) else none

/-- **`mark_root` is `markRoot`.** -/
theorem mark_root_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {k : Std.U8} {nil : Bool}
    {m : alloc.vec.Vec Std.U8} {v : Std.U64} {o} (hr : RegionFits bs r)
    (h : mark_root r k nil m v = ok o) :
    markRoot (absRegion bs r) (absByte k) nil (absM m) (absWord v) = rootAbs o := by
  have tail : ∀ {o}, (do
        let o1 ← region_loc r v
        match o1 with
        | none => Result.ok (false, m)
        | some c => do
          let i ← c / 8#u64
          let m1 ← frontend.olean.fast.mark m k i
          Result.ok (true, m1)) = ok o →
      (match (absRegion bs r).loc (absWord v) with
       | some c => some (ConLeche.Frontend.Olean.mark (absM m) (absByte k) (c / 8))
       | none => none) = rootAbs o := by
    intro o h
    peel h as o1, ho1
    rw [← region_loc_eq bs ho1]
    cases o1 with
    | none => cases Result.ok_injective h; rfl
    | some c =>
      dsimp only at h
      peel h as s, hs
      peel h as m1, hm1
      cases Result.ok_injective h
      have hv := uscalar_div_eq hs
      rw [u64_val_lit8] at hv
      simp only [locOf, Option.map_some, ← hv, rootAbs, ↓reduceIte]
      rw [mark_eq (slot_fits (region_loc_fits hr ho1) hs) hm1]
  rw [mark_root] at h
  simp only [markRoot]
  cases nil with
  | false => exact tail h
  | true =>
    by_cases hv : v = 1#u64
    · subst hv
      rw [ite_eq_left rfl] at h
      cases Result.ok_injective h
      rfl
    · rw [ite_eq_right hv] at h
      rw [ite_eq_right (by simpa using fun he => hv (word_eq_one.mp he))]
      exact tail h

/-- `mark_roots`' loop is upstream's `foldlM`. -/
theorem mark_roots_loop_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {k : Std.U8} {nil : Bool}
    {vs : alloc.vec.Vec Std.U64} (hr : RegionFits bs r) :
    ∀ (f : Nat) {i : Std.Usize} {m : alloc.vec.Vec Std.U8} {o}, vs.val.length - i.val ≤ f →
      mark_roots_loop r k nil m vs i = ok o →
      ((vs.val.drop i.val).map absWord).foldlM (markRoot (absRegion bs r) (absByte k) nil) (absM m)
        = rootAbs o := by
  intro f
  induction f with
  | zero =>
    intro i m o hf h
    rw [mark_roots_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ f ih =>
    intro i m o hf h
    rw [mark_roots_loop] at h
    by_cases hi : i < alloc.vec.Vec.len vs
    · rw [ite_eq_left hi] at h
      have hlt : i.val < vs.val.length := by scalar_tac
      peel h as x, hx
      peel h as p, hp
      obtain ⟨b, m1⟩ := p
      obtain ⟨_, hxe⟩ := vec_index_eq hx
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.foldlM_cons, ← hxe, mark_root_eq hr hp]
      cases b with
      | false =>
        cases Result.ok_injective h
        rfl
      | true =>
        peel h as i3, hi3
        have hv := uscalar_add_eq hi3
        have l : (1#usize : Std.Usize).val = 1 := by decide
        show ((vs.val.drop (i.val + 1)).map absWord).foldlM _ (absM m1) = _
        rw [show i.val + 1 = i3.val by omega]
        exact ih (by omega) h
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      rfl

/-- **`mark_roots` is `foldlM (markRoot …)`.** -/
theorem mark_roots_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {k : Std.U8} {nil : Bool}
    {vs : alloc.vec.Vec Std.U64} {m : alloc.vec.Vec Std.U8} {o} (hr : RegionFits bs r)
    (h : mark_roots r k nil m vs = ok o) :
    (vs.val.map absWord).foldlM (markRoot (absRegion bs r) (absByte k) nil) (absM m) = rootAbs o := by
  rw [mark_roots] at h
  have := mark_roots_loop_eq (bs := bs) hr _ (Nat.le_refl _) h
  simpa using this

/-! ## The highest location -/

/-- `max_loc`'s loop is upstream's `maxLoc`. -/
theorem max_loc_loop_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {vs : alloc.vec.Vec Std.U64} :
    ∀ (f : Nat) {i : Std.Usize} {m o : Std.U64}, vs.val.length - i.val ≤ f →
      max_loc_loop r vs m i = ok o →
      o.val = maxLoc (absRegion bs r) ((vs.val.drop i.val).map absWord) m.val := by
  intro f
  induction f with
  | zero =>
    intro i m o hf h
    rw [max_loc_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ f ih =>
    intro i m o hf h
    rw [max_loc_loop] at h
    by_cases hi : i < alloc.vec.Vec.len vs
    · rw [ite_eq_left hi] at h
      have hlt : i.val < vs.val.length := by scalar_tac
      peel h as x, hx
      peel h as g, hg
      peel h as m1, hm1
      peel h as i3, hi3
      obtain ⟨_, hxe⟩ := vec_index_eq hx
      have hgv := region_loc_go_eq bs r.segs.val.length (by rw [usize_len_val]) hg
      rw [← absRegion_size bs r] at hgv
      have hm : m1.val = max m.val g.val := by
        split at hm1
        · rename_i hc
          have hc' : g.val > m.val := hc
          cases Result.ok_injective hm1
          omega
        · rename_i hc
          have hc' : ¬ g.val > m.val := hc
          cases Result.ok_injective hm1
          omega
      have hv := uscalar_add_eq hi3
      have l : (1#usize : Std.Usize).val = 1 := by decide
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, ← hxe]
      simp only [maxLoc, List.foldl_cons]
      rw [← hgv, ← hm]
      have := ih (i := i3) (by omega) h
      rw [this]
      simp only [maxLoc]
      rw [show i.val + 1 = i3.val by omega]
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      rfl

/-- **`max_loc` is `maxLoc`.** -/
theorem max_loc_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {vs : alloc.vec.Vec Std.U64} {m o : Std.U64} (h : max_loc r vs m = ok o) :
    o.val = maxLoc (absRegion bs r) (vs.val.map absWord) m.val := by
  rw [max_loc] at h
  have := max_loc_loop_eq (bs := bs) _ (Nat.le_refl _) h
  simpa using this

/-- The highest location of some roots lies inside the bytes. -/
theorem maxLoc_le {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r) :
    ∀ (l : List UInt64) {m : Nat}, m ≤ bs.val.length → maxLoc (absRegion bs r) l m ≤ bs.val.length := by
  intro l
  induction l with
  | nil => intro m hm; exact hm
  | cons a t ih =>
    intro m hm
    simp only [maxLoc, List.foldl_cons]
    refine ih ?_
    rcases locGo_fits hr a (absRegion bs r).segs.size with h0 | h1 <;> omega

/-! ## The zeros -/

theorem zeros_data (n : Nat) : (ConLeche.Frontend.Olean.zeros n).data.toList = List.replicate n 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [ConLeche.Frontend.Olean.zeros]
    by_cases h0 : n = 0
    · subst h0; rfl
    · rw [ite_eq_right h0]
      have hh := ih (n / 2) (by omega)
      have hd : (ConLeche.Frontend.Olean.zeros (n / 2) ++ ConLeche.Frontend.Olean.zeros (n / 2)).data.toList
          = List.replicate (n / 2 + n / 2) 0 := by
        rw [ByteArray.data_append, Array.toList_append, hh, List.replicate_append_replicate]
      dsimp only
      split
      · rename_i ho
        show (ByteArray.push _ 0).data.toList = _
        rw [ByteArray.data_push, Array.toList_push, hd, ← List.replicate_succ']
        congr 1; omega
      · rename_i ho
        rw [hd]
        congr 1; omega

/-- **`zeros` is `zeros`.** -/
theorem zeros_eq {n : Std.Usize} {m : alloc.vec.Vec Std.U8} (h : frontend.olean.fast.zeros n = ok m) :
    absM m = ConLeche.Frontend.Olean.zeros n.val := by
  rw [frontend.olean.fast.zeros, alloc.vec.Vec.resize] at h
  have hv : m.val = List.replicate n.val 0#u8 := by
    split at h
    · rename_i hlt
      simp at hlt
    · peel h as x, hx
      have hx0 : 0#u8 = x := Result.ok_injective hx
      subst hx0
      cases Result.ok_injective h
      have e0 : ∀ (l : List Std.U8) (hl), (alloc.vec.Vec.from l hl).val = l := fun l hl => Slice.from_val _ _
      have e1 : (alloc.vec.Vec.new Std.U8).val = [] := Slice.from_val _ _
      rw [e0, e1]
      simp [List.resize]
  apply absM_ext
  rw [zeros_data, hv, List.map_replicate]
  rfl

end ConRon.Refine2.Frontend.Olean
