/-
`kernel::pins_decode`'s byte readers against `ConRon.Refine.PinsDec` — half (A)
of task #64's decoder refinement, the part below the records.

Every lemma here is stated over the model's **whole** outcome (task #67): *if
the model's reader accepts the slice `t` at index `i` and stops at index `j`,
then `PinsDec`'s reader accepts the byte suffix `bytesFrom t i` and stops at
`bytesFrom t j`, with the same value; and if the model declines, it declines
with a `Native` error* — `absErrKind ce = none`, which claims nothing and is
what `ErrSim.of_none` turns into an `ErrSim` at a caller.  The two index facts
`i ≤ j` and `j ≤ t.length` travel with the accept branch because the pass
above needs them for its fuel.

**Why the failure branch claims nothing.**  `kernel::pins_decode` is the one
module of the crate whose errors are *wholly* the port's own: con-leche has no
decoder at all — its `natOpPinSets` is elaboration-time data
(`#load_natop_pins`, `ConLeche/Kernel/NatOpPins.lean:61-64`, over an
`include_str` JSON) — so not one of the module's twenty-eight throws mirrors a
`throw`, and every one of them goes through the single constructor
`bad_text` (`pins_decode.rs:100`), which builds a `CheckError::Native`.  This
is what DESIGN.md's task-#67 error-site census records for the file, and
`bad_text_native` below is the one lemma the whole group's failure branch
rests on.

`Refine/PinsRecords.lean` is the next layer (the `N`/`L`/`W`/`E` records),
`Refine/PinsRun.lean` the pass; `Refine/PinsDec.lean`'s module note has the
map of the whole proof.
-/
import ConRon.Refine.PinsAbs
import ConRon.Refine.Nat
import ConRon.Refine.Name
import ConRon.Refine.Level
import ConRon.Refine.PropWhen

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.PinsBytes

open ConRon.Refine ConRon.Refine.PinsDec

/-! ## The byte suffix an index names -/

/-- The byte suffix of `t` from index `i`, which is what `PinsDec`'s readers
take where the model's take a slice and an index. -/
def bytesFrom (t : Slice Std.U8) (i : Std.Usize) : PinsDec.Bytes :=
  (bytesOf t).drop i.val

theorem bytesFrom_length {t : Slice Std.U8} {i : Std.Usize} :
    (bytesFrom t i).length = t.length - i.val := by
  simp [bytesFrom, bytesOf, Slice.length]

theorem bytesFrom_eq_nil {t : Slice Std.U8} {i : Std.Usize} (h : t.length ≤ i.val) :
    bytesFrom t i = [] := by
  have := bytesFrom_length (t := t) (i := i)
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- Two in-range indices name the same suffix only if they are equal: the
lengths decide it.  This is what turns a `PinsDec`-side equation back into an
index fact. -/
theorem bytesFrom_inj {t : Slice Std.U8} {i j : Std.Usize}
    (hi : i.val ≤ t.length) (hj : j.val ≤ t.length)
    (h : bytesFrom t i = bytesFrom t j) : i.val = j.val := by
  have h1 := bytesFrom_length (t := t) (i := i)
  have h2 := bytesFrom_length (t := t) (i := j)
  rw [h, h2] at h1; omega

/-! ### The three moves every reader below makes -/

/-- A slice read at an in-range index, in the forward `= ok` form. -/
private theorem slice_index_ok {t : Slice Std.U8} {i : Std.Usize}
    (hi : i.val < t.length) : Slice.index_usize t i = ok t.val[i.val] := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec t i hi)
  rw [hy, hyv]

/-- A `Vec` read at an in-range index, in the forward `= ok` form. -/
private theorem vec_index_ok {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hi : i.val < v.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i
      = ok v.val[i.val] := by
  simp only [alloc.vec.Vec.index_slice_index]
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hi)
  rw [hy, hyv]

/-- Stepping an in-range index never overflows: the slice is short enough. -/
private theorem step_ok {t : Slice Std.U8} {i : Std.Usize} (hi : i.val < t.length) :
    ∃ w : Std.Usize, i + 1#usize = ok w ∧ w.val = i.val + 1 := by
  refine usize_add_ok ?_
  have := Slice.length_ineq t
  scalar_tac

/-- `u64` subtraction in the forward `= ok` form. -/
private theorem u64_sub_ok {x y : Std.U64} (h : y.val ≤ x.val) :
    ∃ w : Std.U64, x - y = ok w ∧ w.val = x.val - y.val := by
  obtain ⟨w, h1, h2⟩ := WP.spec_imp_exists (Std.U64.sub_spec (x := x) (y := y) h)
  exact ⟨w, h1, h2.1⟩

/-- `u64` addition in the forward `= ok` form. -/
private theorem u64_add_ok {x y : Std.U64} (h : x.val + y.val ≤ Std.U64.max) :
    ∃ w : Std.U64, x + y = ok w ∧ w.val = x.val + y.val := by
  obtain ⟨w, h1, h2⟩ := WP.spec_imp_exists (Std.U64.add_spec (x := x) (y := y) h)
  exact ⟨w, h1, h2⟩

/-- `u64` multiplication in the forward `= ok` form. -/
private theorem u64_mul_ok {x y : Std.U64} (h : x.val * y.val ≤ Std.U64.max) :
    ∃ w : Std.U64, x * y = ok w ∧ w.val = x.val * y.val := by
  obtain ⟨w, h1, h2⟩ := WP.spec_imp_exists (Std.U64.mul_spec (x := x) (y := y) h)
  exact ⟨w, h1, h2⟩

/-- The suffix at an in-range index is that byte, then the rest. -/
private theorem bytesFrom_cons {t : Slice Std.U8} {i : Std.Usize}
    (hi : i.val < t.length) :
    bytesFrom t i = t.val[i.val].val :: (bytesOf t).drop (i.val + 1) := by
  have hlen : i.val < (bytesOf t).length := by simpa [bytesOf] using hi
  simp only [bytesFrom]
  rw [List.drop_eq_getElem_cons hlen]
  simp [bytesOf]

/-- `bytesFrom` only looks at the index's value, so the stepped index names
exactly the tail `bytesFrom_cons` exposes. -/
private theorem bytesFrom_step {t : Slice Std.U8} {i j : Std.Usize}
    (h : j.val = i.val + 1) : bytesFrom t j = (bytesOf t).drop (i.val + 1) := by
  simp [bytesFrom, h]

/-! ### The module's one error

`bad_text` is the decoder's only error constructor, and it is `Native`: the
port's own decline, which a refinement lemma claims nothing about.  So every
`.Err` branch below reads `absErrKind ce = none`, and every proof of one is
either `err_native` (the throw itself) or the callee's own `.Err` branch. -/

/-- **The module's one error is `Native`.**  `kernel::pins_decode::bad_text`
(`pins_decode.rs:94-101`) builds `core_types::native`, so `absErrKind` sends it
to `none` and `ErrSim.of_none` discharges any `ErrSim` about it. -/
theorem bad_text_native {ce : core_types.CheckError}
    (h : pins_decode.bad_text = ok ce) : absErrKind ce = none := by
  rw [pins_decode.bad_text] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨s, hs, v, hv, h⟩ := h
  rw [core_types.native, Result.ok.injEq] at h
  subst h
  rfl

/-- Every error arm of the decoder is that one constructor, in the shape the
generated model gives it: `bad_text >>= fun ce => ok (.Err ce)`. -/
theorem err_native {T : Type} {o : core.result.Result T core_types.CheckError}
    (h : (pins_decode.bad_text >>= fun ce =>
            ok (core.result.Result.Err ce : core.result.Result T core_types.CheckError))
        = ok o) : ∃ ce, o = .Err ce ∧ absErrKind ce = none := by
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ce, hce, h⟩ := h
  simp only [Result.ok.injEq] at h
  exact ⟨ce, h.symm, bad_text_native hce⟩

/-! ## Bytes -/

theorem byte_at_refines {t : Slice Std.U8} {i : Std.Usize} {b : Std.U64}
    (h : pins_decode.byte_at t i = ok b) : b.val = PinsDec.byteAt (bytesFrom t i) := by
  rw [pins_decode.byte_at] at h
  split at h
  · rename_i hlt
    have hi : i.val < t.length := by scalar_tac
    rw [slice_index_ok hi] at h
    simp only [bind_tc_ok, Result.ok.injEq] at h
    subst h
    rw [bytesFrom_cons hi]
    simp [PinsDec.byteAt]
  · rename_i hge
    have hi : t.length ≤ i.val := by scalar_tac
    simp only [Result.ok.injEq] at h
    subst h
    rw [bytesFrom_eq_nil hi]
    simp [PinsDec.byteAt]

/-- A byte that is not the past-the-end sentinel comes from a real index. -/
private theorem byte_at_lt {t : Slice Std.U8} {i : Std.Usize} {b : Std.U64}
    (h : pins_decode.byte_at t i = ok b) (hb : b.val ≠ 256) : i.val < t.length := by
  rw [pins_decode.byte_at] at h
  split at h
  · rename_i hlt; scalar_tac
  · exfalso
    simp only [Result.ok.injEq] at h
    subst h
    exact hb (by scalar_tac)

/-- The byte the model read, as a fact about the suffix `PinsDec` reads. -/
private theorem byte_at_head {t : Slice Std.U8} {i : Std.Usize} {b : Std.U64}
    (h : pins_decode.byte_at t i = ok b) (hi : i.val < t.length) :
    t.val[i.val].val = b.val := by
  have hb := byte_at_refines h
  rw [bytesFrom_cons hi] at hb
  simpa [PinsDec.byteAt] using hb.symm

/-- Every byte string starts with the empty pattern. -/
private theorem startsWith_nil (bs : PinsDec.Bytes) :
    PinsDec.startsWith bs [] = true := by
  cases bs <;> rfl

/-- The fuel induction behind `starts_with_from_refines`: the recursion is
bounded by the *pattern*, so the measure is `p.length - i`. -/
private theorem starts_with_from_aux {t p : Slice Std.U8} :
    ∀ k (i : Std.Usize), p.length - i.val ≤ k →
      pins_decode.starts_with_from t p i = ok true →
      PinsDec.startsWith (bytesFrom t i) (bytesFrom p i) = true := by
  intro k
  induction k with
  | zero =>
    intro i hk h
    rw [bytesFrom_eq_nil (show p.length ≤ i.val by omega)]
    exact startsWith_nil _
  | succ k ih =>
    intro i hk h
    by_cases hlt : i.val < p.length
    · rw [pins_decode.starts_with_from.eq_def] at h
      simp only [] at h
      split at h
      · exfalso; scalar_tac
      · simp only [bind_eq_ok_iff] at h
        obtain ⟨b, hb, c0, hc0, c1, hc1, h⟩ := h
        rw [slice_index_ok hlt, Result.ok.injEq] at hc0
        subst hc0
        simp only [Std.lift, Result.ok.injEq] at hc1
        subst hc1
        split at h
        · simp at h
        · rename_i hne
          have hbv : b.val = p.val[i.val].val := by simpa using hne
          have hti : i.val < t.length := by
            refine byte_at_lt hb ?_
            have : p.val[i.val].val ≤ 255 := by scalar_tac
            omega
          simp only [bind_eq_ok_iff] at h
          obtain ⟨w, hw, h⟩ := h
          obtain ⟨w', hw', hw'v⟩ := step_ok hti
          rw [hw', Result.ok.injEq] at hw
          subst hw
          have hrec := ih w' (by omega) h
          rw [bytesFrom_step hw'v, bytesFrom_step (t := p) hw'v] at hrec
          rw [bytesFrom_cons hti, bytesFrom_cons hlt, byte_at_head hb hti, hbv]
          simpa [PinsDec.startsWith] using hrec
    · rw [bytesFrom_eq_nil (show p.length ≤ i.val by omega)]
      exact startsWith_nil _

theorem starts_with_from_refines {t p : Slice Std.U8} {i : Std.Usize}
    (h : pins_decode.starts_with_from t p i = ok true) (hi : i.val ≤ p.length) :
    PinsDec.startsWith (bytesFrom t i) (bytesFrom p i) = true := by
  -- `hi` is not needed below: the measure `p.length - i` is `0` exactly where
  -- the pattern is already exhausted, which is the base case.
  have _ := hi
  exact starts_with_from_aux (p.length - i.val) i (le_refl _) h

/-- `bytes_from` copies the rest of its slice onto the accumulator. -/
private theorem bytes_from_aux {bs : Slice Std.U8} :
    ∀ k (i : Std.Usize) (out : alloc.vec.Vec Std.U8), bs.length - i.val ≤ k →
      ∀ v, pins_decode.bytes_from bs i out = ok v →
        v.val = out.val ++ bs.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out hk v h
    rw [pins_decode.bytes_from.eq_def] at h
    simp only [] at h
    split at h
    · simp only [Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · exfalso; scalar_tac
  | succ k ih =>
    intro i out hk v h
    rw [pins_decode.bytes_from.eq_def] at h
    simp only [] at h
    split at h
    · simp only [Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rename_i hlt
      have hi : i.val < bs.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hx, out1, hpush, w, hw, h⟩ := h
      rw [slice_index_ok hi, Result.ok.injEq] at hx
      subst hx
      obtain ⟨w', hw', hw'v⟩ := step_ok hi
      rw [hw', Result.ok.injEq] at hw
      subst hw
      have hrec := ih w' out1 (by omega) v h
      rw [hrec, vec_push_val hpush, hw'v, List.drop_eq_getElem_cons hi]
      simp

/-- `pins_header` builds `PinsDec.headerBytes`. -/
theorem pins_header_refines {v : alloc.vec.Vec Std.U8}
    (h : pins_decode.pins_header = ok v) :
    v.val.map (fun b => b.val) = PinsDec.headerBytes := by
  rw [pins_decode.pins_header] at h
  simp only [Std.lift, bind_tc_ok] at h
  have hv := bytes_from_aux (bs := Array.to_slice pins_decode.pins_header.H)
    (Array.to_slice pins_decode.pins_header.H).length 0#usize
    (alloc.vec.Vec.new Std.U8) (by scalar_tac) v h
  rw [hv]
  simp [alloc.vec.Vec.new, Array.val_to_slice, pins_decode.pins_header.H,
    Array.make, PinsDec.headerBytes]

/-- The full outcome (task #67): on `.Err` the decoder declined with its own
`Native` error, which claims nothing about con-leche — see the module note. -/
theorem after_space_refines {t : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result Std.Usize core_types.CheckError}
    (h : pins_decode.after_space t i = ok o) :
    match o with
    | .Ok j => PinsDec.afterSpace (bytesFrom t i) = some (bytesFrom t j)
        ∧ i.val < j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.after_space] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  split at h
  · rename_i h32
    have hi : i.val < t.length := byte_at_lt hb (by scalar_tac)
    obtain ⟨w, hw, hwv⟩ := step_ok hi
    rw [hw] at h
    simp only [bind_tc_ok, Result.ok.injEq] at h
    subst h
    have hx : t.val[i.val].val = 32 := by rw [byte_at_head hb hi]; scalar_tac
    refine ⟨?_, by omega, by omega⟩
    rw [bytesFrom_cons hi, hx, bytesFrom_step hwv]
    rfl
  · obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce

/-- The full outcome; see `after_space_refines`. -/
theorem after_newline_refines {t : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result Std.Usize core_types.CheckError}
    (h : pins_decode.after_newline t i = ok o) :
    match o with
    | .Ok j => PinsDec.afterNewline (bytesFrom t i) = some (bytesFrom t j)
        ∧ i.val < j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.after_newline] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  split at h
  · rename_i h10
    have hi : i.val < t.length := byte_at_lt hb (by scalar_tac)
    obtain ⟨w, hw, hwv⟩ := step_ok hi
    rw [hw] at h
    simp only [bind_tc_ok, Result.ok.injEq] at h
    subst h
    have hx : t.val[i.val].val = 10 := by rw [byte_at_head hb hi]; scalar_tac
    refine ⟨?_, by omega, by omega⟩
    rw [bytesFrom_cons hi, hx, bytesFrom_step hwv]
    rfl
  · obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce

/-! ## Scalars -/

/-- Past the end `byte_at` is the sentinel, which matches no arm of any
reader: this is how every "the slice ran out" case becomes a contradiction. -/
private theorem byte_at_end {t : Slice Std.U8} {i : Std.Usize} {b : Std.U64}
    (h : pins_decode.byte_at t i = ok b) (hi : t.length ≤ i.val) : b.val = 256 := by
  have hr := byte_at_refines h
  rw [bytesFrom_eq_nil hi] at hr
  simpa [PinsDec.byteAt] using hr

/-- A non-digit that ends a `<nat>` field stops `readNatFrom` where it stands. -/
private theorem readNatFrom_stop {r : PinsDec.Bytes} {c acc : Nat}
    (h : c = 32 ∨ c = 10) : PinsDec.readNatFrom (c :: r) acc = some (acc, c :: r) := by
  rcases h with rfl | rfl <;> simp [PinsDec.readNatFrom, PinsDec.isDigit]

/-- The same, for the bignum loop. -/
private theorem readBigNatFrom_stop {r : PinsDec.Bytes} {c acc : Nat}
    (h : c = 32 ∨ c = 10) :
    PinsDec.readBigNatFrom (c :: r) acc = some (acc, c :: r) := by
  rcases h with rfl | rfl <;> simp [PinsDec.readBigNatFrom, PinsDec.isDigit]

/-- The fuel induction behind `read_nat_from_refines`: `read_nat_from` advances
the index by a byte per digit, so `t.length - i` is a measure. -/
private theorem read_nat_from_aux {t : Slice Std.U8} :
    ∀ k (i : Std.Usize) (acc : Std.U64), t.length - i.val ≤ k →
      ∀ (o : core.result.Result (Std.U64 × Std.Usize) core_types.CheckError),
        pins_decode.read_nat_from t i acc = ok o →
        match o with
        | .Ok (n, j) =>
            PinsDec.readNatFrom (bytesFrom t i) acc.val = some (n.val, bytesFrom t j)
              ∧ i.val ≤ j.val ∧ j.val ≤ t.length
        | .Err ce => absErrKind ce = none := by
  intro k
  induction k with
  | zero =>
    intro i acc hk o h
    rw [pins_decode.read_nat_from.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbv := byte_at_end hb (by omega)
    rw [if_neg (show ¬ (b < 48#u64) by scalar_tac), if_pos (show b > 57#u64 by scalar_tac),
        if_neg (show ¬ (b = 32#u64) by scalar_tac),
        if_neg (show ¬ (b = 10#u64) by scalar_tac)] at h
    obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce
  | succ k ih =>
    intro i acc hk o h
    rw [pins_decode.read_nat_from.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    by_cases hend : t.length ≤ i.val
    · have hbv := byte_at_end hb hend
      rw [if_neg (show ¬ (b < 48#u64) by scalar_tac), if_pos (show b > 57#u64 by scalar_tac),
          if_neg (show ¬ (b = 32#u64) by scalar_tac),
          if_neg (show ¬ (b = 10#u64) by scalar_tac)] at h
      obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce
    · have hi : i.val < t.length := by omega
      have hcons : bytesFrom t i = b.val :: (bytesOf t).drop (i.val + 1) := by
        rw [bytesFrom_cons hi, byte_at_head hb hi]
      split at h
      · split at h
        · rename_i h32
          simp only [Result.ok.injEq] at h
          subst h
          exact ⟨by rw [hcons]; exact readNatFrom_stop (Or.inl (by scalar_tac)),
            le_refl _, by omega⟩
        · split at h
          · rename_i h10
            simp only [Result.ok.injEq] at h
            subst h
            exact ⟨by rw [hcons]; exact readNatFrom_stop (Or.inr (by scalar_tac)),
              le_refl _, by omega⟩
          · obtain ⟨ce, rfl, hce⟩ := err_native h
            exact hce
      · split at h
        · split at h
          · rename_i h32
            simp only [Result.ok.injEq] at h
            subst h
            exact ⟨by rw [hcons]; exact readNatFrom_stop (Or.inl (by scalar_tac)),
              le_refl _, by omega⟩
          · split at h
            · rename_i h10
              simp only [Result.ok.injEq] at h
              subst h
              exact ⟨by rw [hcons]; exact readNatFrom_stop (Or.inr (by scalar_tac)),
                le_refl _, by omega⟩
            · obtain ⟨ce, rfl, hce⟩ := err_native h
              exact hce
        · rename_i hge48 hle57
          split at h
          · obtain ⟨ce, rfl, hce⟩ := err_native h
            exact hce
          · rename_i hacc
            have hd1 : 48 ≤ b.val := by scalar_tac
            have hd2 : b.val ≤ 57 := by scalar_tac
            have hab : acc.val ≤ 1000000000000000000 := by scalar_tac
            obtain ⟨w1, hw1, hw1v⟩ := step_ok hi
            obtain ⟨w2, hw2, hw2v⟩ := u64_mul_ok (x := acc) (y := 10#u64) (by scalar_tac)
            obtain ⟨w3, hw3, hw3v⟩ := u64_sub_ok (x := b) (y := 48#u64) (by scalar_tac)
            obtain ⟨w4, hw4, hw4v⟩ := u64_add_ok (x := w2) (y := w3) (by scalar_tac)
            rw [show (10#u64 : Std.U64).val = 10 from by scalar_tac] at hw2v
            rw [show (48#u64 : Std.U64).val = 48 from by scalar_tac] at hw3v
            simp only [hw1, hw2, hw3, hw4, bind_tc_ok] at h
            cases o with
            | Err ce => exact ih w1 w4 (by omega) _ h
            | Ok pr =>
            obtain ⟨n, j⟩ := pr
            obtain ⟨hrec, hij, hjt⟩ := ih w1 w4 (by omega) _ h
            rw [bytesFrom_step hw1v] at hrec
            refine ⟨?_, by omega, hjt⟩
            rw [hcons]
            simp only [PinsDec.readNatFrom]
            rw [if_pos (show PinsDec.isDigit b.val = true by
              simp only [PinsDec.isDigit, Bool.and_eq_true, decide_eq_true_eq]; omega)]
            rw [if_neg (show ¬ (acc.val > 1000000000000000000) by omega)]
            rw [show acc.val * 10 + (b.val - 48) = w4.val by omega]
            exact hrec

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem read_nat_from_refines {t : Slice Std.U8} {i : Std.Usize} {acc : Std.U64}
    {o : core.result.Result (Std.U64 × Std.Usize) core_types.CheckError}
    (h : pins_decode.read_nat_from t i acc = ok o) :
    match o with
    | .Ok (n, j) =>
        PinsDec.readNatFrom (bytesFrom t i) acc.val = some (n.val, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  cases o <;> exact read_nat_from_aux (t.length - i.val) i acc (le_refl _) _ h

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem read_nat_refines {t : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (Std.U64 × Std.Usize) core_types.CheckError}
    (h : pins_decode.read_nat t i = ok o) :
    match o with
    | .Ok (n, j) => PinsDec.readNat (bytesFrom t i) = some (n.val, bytesFrom t j)
        ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.read_nat] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  split at h
  · obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce
  · split at h
    · obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce
    · rename_i hge48 hle57
      cases o with
      | Err ce => exact read_nat_from_refines h
      | Ok pr =>
      obtain ⟨n, j⟩ := pr
      have hd1 : 48 ≤ b.val := by scalar_tac
      have hd2 : b.val ≤ 57 := by scalar_tac
      obtain ⟨hrec, hij, hjt⟩ := read_nat_from_refines h
      have h0 : (0#u64 : Std.U64).val = 0 := by scalar_tac
      rw [h0] at hrec
      refine ⟨?_, hij, hjt⟩
      unfold PinsDec.readNat
      rw [if_pos (show PinsDec.isDigit (PinsDec.byteAt (bytesFrom t i)) = true by
        rw [← byte_at_refines hb]
        simp only [PinsDec.isDigit, Bool.and_eq_true, decide_eq_true_eq]; omega)]
      exact hrec

/-- A `u64` that fits a `u32` survives the `as usize` narrowing: Aeneas's
`usize` is `System.Platform`-dependent, but never narrower than 32 bits
(`Usize.bounds_eq`), which is why `read_index` guards at `U32.max`. -/
private theorem u64_cast_usize_val {x : Std.U64} (h : x.val ≤ 4294967295) :
    (Std.UScalar.cast .Usize x : Std.Usize).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_of_inBounds_eq _ _ ?_
  have h1 : Std.Usize.max + 1 = 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq]; exact Std.Usize.max_succ_eq_pow
  have h2 : 4294967295 ≤ Std.Usize.max := by scalar_tac
  omega

/-- The full outcome; the `.Err` branch is the module's one `Native` error,
either `read_nat`'s or the `> u32::MAX` guard's own. -/
theorem read_index_refines {t : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (Std.Usize × Std.Usize) core_types.CheckError}
    (h : pins_decode.read_index t i = ok o) :
    match o with
    | .Ok (n, j) => PinsDec.readIndex (bytesFrom t i) = some (n.val, bytesFrom t j)
        ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.read_index] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_nat_refines hr
  | Ok pr =>
    obtain ⟨m, j1⟩ := pr
    replace h : (if m > 4294967295#u64 then _ else _) = ok o := h
    split at h
    · obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce
    · rename_i hbig
      simp only [Std.lift, bind_tc_ok, Result.ok.injEq] at h
      subst h
      obtain ⟨hrec, hij, hjt⟩ := read_nat_refines hr
      refine ⟨?_, hij, hjt⟩
      unfold PinsDec.readIndex
      rw [u64_cast_usize_val (by scalar_tac)]
      exact hrec

/-- The fuel induction behind `read_big_nat_from_refines`.  The accumulator is
the crate's bignum, so the digit step is `nat::mul`/`nat::add` rather than a
machine word, and `Refine/Nat.lean`'s lemmas carry both the value and the
`NatWF` invariant the next step needs. -/
private theorem read_big_nat_from_aux {t : Slice Std.U8} :
    ∀ k (i : Std.Usize) (acc : ron.nat.Nat), t.length - i.val ≤ k → Nat.NatWF acc →
      ∀ (o : core.result.Result (ron.nat.Nat × Std.Usize) core_types.CheckError),
        pins_decode.read_big_nat_from t i acc = ok o →
        match o with
        | .Ok (n, j) =>
            PinsDec.readBigNatFrom (bytesFrom t i) (Nat.toNat acc)
                = some (Nat.toNat n, bytesFrom t j)
              ∧ i.val ≤ j.val ∧ j.val ≤ t.length
        | .Err ce => absErrKind ce = none := by
  intro k
  induction k with
  | zero =>
    intro i acc hk hwf o h
    rw [pins_decode.read_big_nat_from.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbv := byte_at_end hb (by omega)
    rw [if_neg (show ¬ (b < 48#u64) by scalar_tac), if_pos (show b > 57#u64 by scalar_tac),
        if_neg (show ¬ (b = 32#u64) by scalar_tac),
        if_neg (show ¬ (b = 10#u64) by scalar_tac)] at h
    obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce
  | succ k ih =>
    intro i acc hk hwf o h
    rw [pins_decode.read_big_nat_from.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    by_cases hend : t.length ≤ i.val
    · have hbv := byte_at_end hb hend
      rw [if_neg (show ¬ (b < 48#u64) by scalar_tac), if_pos (show b > 57#u64 by scalar_tac),
          if_neg (show ¬ (b = 32#u64) by scalar_tac),
          if_neg (show ¬ (b = 10#u64) by scalar_tac)] at h
      obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce
    · have hi : i.val < t.length := by omega
      have hcons : bytesFrom t i = b.val :: (bytesOf t).drop (i.val + 1) := by
        rw [bytesFrom_cons hi, byte_at_head hb hi]
      split at h
      · split at h
        · simp only [Result.ok.injEq] at h
          subst h
          exact ⟨by rw [hcons]; exact readBigNatFrom_stop (Or.inl (by scalar_tac)),
            le_refl _, by omega⟩
        · split at h
          · simp only [Result.ok.injEq] at h
            subst h
            exact ⟨by rw [hcons]; exact readBigNatFrom_stop (Or.inr (by scalar_tac)),
              le_refl _, by omega⟩
          · obtain ⟨ce, rfl, hce⟩ := err_native h
            exact hce
      · split at h
        · split at h
          · simp only [Result.ok.injEq] at h
            subst h
            exact ⟨by rw [hcons]; exact readBigNatFrom_stop (Or.inl (by scalar_tac)),
              le_refl _, by omega⟩
          · split at h
            · simp only [Result.ok.injEq] at h
              subst h
              exact ⟨by rw [hcons]; exact readBigNatFrom_stop (Or.inr (by scalar_tac)),
                le_refl _, by omega⟩
            · obtain ⟨ce, rfl, hce⟩ := err_native h
              exact hce
        · rename_i hge48 hle57
          have hd1 : 48 ≤ b.val := by scalar_tac
          have hd2 : b.val ≤ 57 := by scalar_tac
          simp only [bind_eq_ok_iff] at h
          obtain ⟨ten, hten, shifted, hshift, d0, hd0, digit, hdig, w1, hw1, nn, hnn, h⟩ := h
          obtain ⟨htenv, htenwf⟩ := Nat.from_u64_refines hten
          obtain ⟨hshiftv, hshiftwf⟩ := Nat.mul_refines hshift
          obtain ⟨w3, hw3, hw3v⟩ := u64_sub_ok (x := b) (y := 48#u64) (by scalar_tac)
          rw [hw3, Result.ok.injEq] at hd0
          subst hd0
          obtain ⟨hdigv, hdigwf⟩ := Nat.from_u64_refines hdig
          obtain ⟨w2, hw2, hw2v⟩ := step_ok hi
          rw [hw2, Result.ok.injEq] at hw1
          subst hw1
          obtain ⟨hnnv, hnnwf⟩ := Nat.add_refines hnn
          cases o with
          | Err ce => exact ih w2 nn (by omega) hnnwf _ h
          | Ok pr =>
          obtain ⟨n, j⟩ := pr
          obtain ⟨hrec, hij, hjt⟩ := ih w2 nn (by omega) hnnwf _ h
          rw [bytesFrom_step hw2v] at hrec
          refine ⟨?_, by omega, hjt⟩
          rw [hcons]
          simp only [PinsDec.readBigNatFrom]
          rw [if_pos (show PinsDec.isDigit b.val = true by
            simp only [PinsDec.isDigit, Bool.and_eq_true, decide_eq_true_eq]; omega)]
          rw [show Nat.toNat acc * 10 + (b.val - 48) = Nat.toNat nn by
            rw [hnnv, hshiftv, hdigv, htenv, hw3v]
            rw [show (10#u64 : Std.U64).val = 10 from by scalar_tac,
              show (48#u64 : Std.U64).val = 48 from by scalar_tac]]
          exact hrec

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem read_big_nat_from_refines {t : Slice Std.U8} {i : Std.Usize}
    {acc : ron.nat.Nat}
    {o : core.result.Result (ron.nat.Nat × Std.Usize) core_types.CheckError}
    (hacc : Nat.NatWF acc)
    (h : pins_decode.read_big_nat_from t i acc = ok o) :
    match o with
    | .Ok (n, j) =>
        PinsDec.readBigNatFrom (bytesFrom t i) (Nat.toNat acc)
            = some (Nat.toNat n, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  cases o <;> exact read_big_nat_from_aux (t.length - i.val) i acc (le_refl _) hacc _ h

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem read_big_nat_refines {t : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (ron.nat.Nat × Std.Usize) core_types.CheckError}
    (h : pins_decode.read_big_nat t i = ok o) :
    match o with
    | .Ok (n, j) => PinsDec.readBigNat (bytesFrom t i) = some (Nat.toNat n, bytesFrom t j)
        ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.read_big_nat] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  split at h
  · obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce
  · split at h
    · obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce
    · rename_i hge48 hle57
      have hd1 : 48 ≤ b.val := by scalar_tac
      have hd2 : b.val ≤ 57 := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨z, hz, h⟩ := h
      obtain ⟨hzv, hzwf⟩ := Nat.zero_refines hz
      cases o with
      | Err ce => exact read_big_nat_from_refines hzwf h
      | Ok pr =>
      obtain ⟨n, j⟩ := pr
      obtain ⟨hrec, hij, hjt⟩ := read_big_nat_from_refines hzwf h
      rw [hzv] at hrec
      refine ⟨?_, hij, hjt⟩
      unfold PinsDec.readBigNat
      rw [if_pos (show PinsDec.isDigit (PinsDec.byteAt (bytesFrom t i)) = true by
        rw [← byte_at_refines hb]
        simp only [PinsDec.isDigit, Bool.and_eq_true, decide_eq_true_eq]; omega)]
      exact hrec

/-- The full outcome; the `.Err` branch is the module's one `Native` error,
either `read_index`'s or the tag mismatch's own. -/
theorem expect_id_refines {t : Slice Std.U8} {i want : Std.Usize}
    {o : core.result.Result Std.Usize core_types.CheckError}
    (h : pins_decode.expect_id t i want = ok o) :
    match o with
    | .Ok j => PinsDec.expectId (bytesFrom t i) want.val = some (bytesFrom t j)
        ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.expect_id] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_index_refines hr
  | Ok pr =>
    obtain ⟨got, j1⟩ := pr
    replace h : (if got = want then _ else _) = ok o := h
    split at h
    · rename_i hgw
      simp only [Result.ok.injEq] at h
      subst h
      obtain ⟨hidx, hij, hjt⟩ := read_index_refines hr
      refine ⟨?_, hij, hjt⟩
      unfold PinsDec.expectId
      simp only [hidx]
      rw [if_pos (show got.val = want.val from by scalar_tac)]
    · obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce

/-! ## Strings -/

theorem hex_digit_refines {b r : Std.U64} (h : pins_decode.hex_digit b = ok r) :
    r.val = PinsDec.hexDigit b.val := by
  rw [pins_decode.hex_digit] at h
  unfold PinsDec.hexDigit
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  split at h
  · split at h
    · obtain ⟨w, hw, hwv⟩ := u64_sub_ok (x := b) (y := 48#u64) (by scalar_tac)
      rw [hw] at h; simp only [Result.ok.injEq] at h; subst h
      split_ifs <;> scalar_tac
    · split at h
      · split at h
        · obtain ⟨w, hw, hwv⟩ := u64_sub_ok (x := b) (y := 87#u64) (by scalar_tac)
          rw [hw] at h; simp only [Result.ok.injEq] at h; subst h
          split_ifs <;> scalar_tac
        · simp only [Result.ok.injEq] at h; subst h
          split_ifs <;> scalar_tac
      · simp only [Result.ok.injEq] at h; subst h
        split_ifs <;> scalar_tac
  · split at h
    · split at h
      · obtain ⟨w, hw, hwv⟩ := u64_sub_ok (x := b) (y := 87#u64) (by scalar_tac)
        rw [hw] at h; simp only [Result.ok.injEq] at h; subst h
        split_ifs <;> scalar_tac
      · simp only [Result.ok.injEq] at h; subst h
        split_ifs <;> scalar_tac
    · simp only [Result.ok.injEq] at h; subst h
      split_ifs <;> scalar_tac

theorem is_valid_char_refines {v : Std.U64} {r : Bool}
    (h : pins_decode.is_valid_char v = ok r) : r = PinsDec.isValidChar v.val := by
  rw [pins_decode.is_valid_char] at h
  unfold PinsDec.isValidChar
  split at h
  · simp only [Result.ok.injEq] at h; subst h
    rw [if_pos (by scalar_tac)]
  · split at h
    · simp only [Result.ok.injEq] at h; subst h
      rw [if_neg (by scalar_tac)]
      have h3 : (57343 : Nat) < v.val := by scalar_tac
      simp only [h3, decide_true, Bool.true_and, decide_eq_decide]
      constructor <;> intro <;> scalar_tac
    · simp only [Result.ok.injEq] at h; subst h
      rw [if_neg (by scalar_tac)]
      have h3 : ¬ (57343 : Nat) < v.val := by scalar_tac
      simp [h3]

/-- A `u64` below `2^32` survives the `as u32` narrowing a code point takes. -/
private theorem u64_cast_u32_val {x : Std.U64} (h : x.val < 4294967296) :
    (Std.UScalar.cast .U32 x : Std.U32).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_of_inBounds_eq _ _ ?_
  simp only [Std.UScalarTy.U32_numBits_eq]
  omega

/-- A valid code point is below `0x110000`, which is all the narrowing needs. -/
private theorem isValidChar_lt {n : Nat} (h : PinsDec.isValidChar n = true) :
    n < 1114112 := by
  unfold PinsDec.isValidChar at h
  split_ifs at h with hc
  · omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega

/-- `hex_digit` is at most `15` unless it is the "not a digit" `16`. -/
private theorem hexDigit_le {n : Nat} (h : PinsDec.hexDigit n ≠ 16) :
    PinsDec.hexDigit n ≤ 15 := by
  unfold PinsDec.hexDigit at *
  split_ifs at * with h1 h2
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1; omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2; omega
  · omega

/-- Pushing onto the accumulator appends to the list of code points. -/
private theorem push_map {out w : alloc.vec.Vec Std.U32} {x : Std.U32}
    (h : alloc.vec.Vec.push out x = ok w) :
    w.val.map (fun c => c.val) = out.val.map (fun c => c.val) ++ [x.val] := by
  rw [vec_push_val h]; simp

/-- The fuel induction behind `unescape_from_refines`. -/
private theorem unescape_from_aux {t : Slice Std.U8} :
    ∀ k (i : Std.Usize) (v : Std.U64) (inEsc : Bool) (out : alloc.vec.Vec Std.U32),
      t.length - i.val ≤ k →
      ∀ (o : core.result.Result (alloc.vec.Vec Std.U32 × Std.Usize)
              core_types.CheckError),
        pins_decode.unescape_from t i v inEsc out = ok o →
        match o with
        | .Ok (s, j) =>
            PinsDec.unescapeFrom (bytesFrom t i) v.val inEsc (out.val.map (fun c => c.val))
                = some (s.val.map (fun c => c.val), bytesFrom t j)
              ∧ i.val ≤ j.val ∧ j.val ≤ t.length
        | .Err ce => absErrKind ce = none := by
  intro k
  induction k with
  | zero =>
    intro i v inEsc out hk o h
    rw [pins_decode.unescape_from.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbv := byte_at_end hb (by omega)
    rw [if_neg (show ¬ (b = 32#u64) by scalar_tac),
        if_neg (show ¬ (b = 10#u64) by scalar_tac),
        if_pos (show b = 256#u64 by scalar_tac)] at h
    obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce
  | succ k ih =>
    intro i v inEsc out hk o h
    rw [pins_decode.unescape_from.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    by_cases hend : t.length ≤ i.val
    · have hbv := byte_at_end hb hend
      rw [if_neg (show ¬ (b = 32#u64) by scalar_tac),
          if_neg (show ¬ (b = 10#u64) by scalar_tac),
          if_pos (show b = 256#u64 by scalar_tac)] at h
      obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce
    · have hi : i.val < t.length := by omega
      have hcons : bytesFrom t i = b.val :: (bytesOf t).drop (i.val + 1) := by
        rw [bytesFrom_cons hi, byte_at_head hb hi]
      split at h
      · -- the token ends at a space
        rename_i h32
        have hbv : b.val = 32 := by scalar_tac
        split at h
        · obtain ⟨ce, rfl, hce⟩ := err_native h
          exact hce
        · rename_i hesc
          simp only [Bool.not_eq_true] at hesc
          simp only [Result.ok.injEq] at h
          subst h
          refine ⟨?_, le_refl _, by omega⟩
          rw [hcons, hbv]
          simp [PinsDec.unescapeFrom, hesc]
      · split at h
        · -- the token ends at a newline
          rename_i h10
          have hbv : b.val = 10 := by scalar_tac
          split at h
          · obtain ⟨ce, rfl, hce⟩ := err_native h
            exact hce
          · rename_i hesc
            simp only [Bool.not_eq_true] at hesc
            simp only [Result.ok.injEq] at h
            subst h
            refine ⟨?_, le_refl _, by omega⟩
            rw [hcons, hbv]
            simp [PinsDec.unescapeFrom, hesc]
        · rename_i h10
          have hn32 : b.val ≠ 32 := by scalar_tac
          have hn10 : b.val ≠ 10 := by scalar_tac
          split at h
          · obtain ⟨ce, rfl, hce⟩ := err_native h
            exact hce
          · split at h
            · -- inside an escape
              rename_i hesc
              split at h
              · -- the `;` that closes it
                rename_i h59
                have hbv : b.val = 59 := by scalar_tac
                simp only [bind_eq_ok_iff] at h
                obtain ⟨b1, hb1, h⟩ := h
                have hb1v := is_valid_char_refines hb1
                split at h
                · rename_i hb1t
                  subst hb1t
                  have hvalid : PinsDec.isValidChar v.val = true := hb1v.symm
                  simp only [bind_eq_ok_iff] at h
                  obtain ⟨c, hc, out1, hpush, w, hw, h⟩ := h
                  simp only [Std.lift, Result.ok.injEq] at hc
                  subst hc
                  obtain ⟨w', hw', hw'v⟩ := step_ok hi
                  rw [hw', Result.ok.injEq] at hw
                  subst hw
                  cases o with
                  | Err ce => exact ih w' 0#u64 false out1 (by omega) _ h
                  | Ok pr =>
                  obtain ⟨s, j⟩ := pr
                  obtain ⟨hrec, hij, hjt⟩ := ih w' 0#u64 false out1 (by omega) _ h
                  rw [bytesFrom_step hw'v, push_map hpush,
                    u64_cast_u32_val (by have := isValidChar_lt hvalid; omega),
                    show (0#u64 : Std.U64).val = 0 from by scalar_tac] at hrec
                  refine ⟨?_, by omega, hjt⟩
                  rw [hcons, hbv]
                  simpa [PinsDec.unescapeFrom, hesc, hvalid] using hrec
                · obtain ⟨ce, rfl, hce⟩ := err_native h
                  exact hce
              · -- a hexadecimal digit of the escape
                rename_i h59
                have hn59 : b.val ≠ 59 := by scalar_tac
                simp only [bind_eq_ok_iff] at h
                obtain ⟨d, hd, h⟩ := h
                have hdv := hex_digit_refines hd
                split at h
                · obtain ⟨ce, rfl, hce⟩ := err_native h
                  exact hce
                · rename_i hd16
                  split at h
                  · obtain ⟨ce, rfl, hce⟩ := err_native h
                    exact hce
                  · rename_i hvbig
                    have hd16' : PinsDec.hexDigit b.val ≠ 16 := by
                      rw [← hdv]; scalar_tac
                    have hdle : PinsDec.hexDigit b.val ≤ 15 := hexDigit_le hd16'
                    have hv : v.val ≤ 1114111 := by scalar_tac
                    simp only [bind_eq_ok_iff] at h
                    obtain ⟨w1, hw1, w2, hw2, w3, hw3, h⟩ := h
                    obtain ⟨w', hw', hw'v⟩ := step_ok hi
                    rw [hw', Result.ok.injEq] at hw1
                    subst hw1
                    obtain ⟨m, hm, hmv⟩ := u64_mul_ok (x := v) (y := 16#u64) (by scalar_tac)
                    rw [hm, Result.ok.injEq] at hw2
                    subst hw2
                    rw [show (16#u64 : Std.U64).val = 16 from by scalar_tac] at hmv
                    obtain ⟨a, ha, hav⟩ := u64_add_ok (x := m) (y := d) (by
                      rw [← hdv] at hdle; scalar_tac)
                    rw [ha, Result.ok.injEq] at hw3
                    subst hw3
                    cases o with
                    | Err ce => exact ih w' a true out (by omega) _ h
                    | Ok pr =>
                    obtain ⟨s, j⟩ := pr
                    obtain ⟨hrec, hij, hjt⟩ := ih w' a true out (by omega) _ h
                    rw [bytesFrom_step hw'v,
                      show a.val = v.val * 16 + PinsDec.hexDigit b.val from by
                        rw [hav, hmv, hdv]] at hrec
                    refine ⟨?_, by omega, hjt⟩
                    rw [hcons]
                    have hstep : PinsDec.unescapeFrom
                        (b.val :: (bytesOf t).drop (i.val + 1)) v.val inEsc
                        (out.val.map (fun c => c.val))
                        = PinsDec.unescapeFrom ((bytesOf t).drop (i.val + 1))
                            (v.val * 16 + PinsDec.hexDigit b.val) true
                            (out.val.map (fun c => c.val)) := by
                      simp [PinsDec.unescapeFrom, hesc, hn32, hn10, hn59, hd16', hv]
                    rw [hstep]
                    exact hrec
            · -- outside an escape
              rename_i hesc
              simp only [Bool.not_eq_true] at hesc
              split at h
              · -- the backslash that opens one
                rename_i h92
                have hbv : b.val = 92 := by scalar_tac
                simp only [bind_eq_ok_iff] at h
                obtain ⟨w, hw, h⟩ := h
                obtain ⟨w', hw', hw'v⟩ := step_ok hi
                rw [hw', Result.ok.injEq] at hw
                subst hw
                cases o with
                | Err ce => exact ih w' 0#u64 true out (by omega) _ h
                | Ok pr =>
                obtain ⟨s, j⟩ := pr
                obtain ⟨hrec, hij, hjt⟩ := ih w' 0#u64 true out (by omega) _ h
                rw [bytesFrom_step hw'v,
                  show (0#u64 : Std.U64).val = 0 from by scalar_tac] at hrec
                refine ⟨?_, by omega, hjt⟩
                rw [hcons, hbv]
                simpa [PinsDec.unescapeFrom, hesc] using hrec
              · rename_i h92
                have hn92 : b.val ≠ 92 := by scalar_tac
                split at h
                · obtain ⟨ce, rfl, hce⟩ := err_native h
                  exact hce
                · rename_i h33
                  split at h
                  · obtain ⟨ce, rfl, hce⟩ := err_native h
                    exact hce
                  · rename_i h126
                    have hb33 : 33 ≤ b.val := by scalar_tac
                    have hb126 : b.val ≤ 126 := by scalar_tac
                    simp only [bind_eq_ok_iff] at h
                    obtain ⟨c, hc, out1, hpush, w, hw, h⟩ := h
                    simp only [Std.lift, Result.ok.injEq] at hc
                    subst hc
                    obtain ⟨w', hw', hw'v⟩ := step_ok hi
                    rw [hw', Result.ok.injEq] at hw
                    subst hw
                    cases o with
                    | Err ce => exact ih w' 0#u64 false out1 (by omega) _ h
                    | Ok pr =>
                    obtain ⟨s, j⟩ := pr
                    obtain ⟨hrec, hij, hjt⟩ := ih w' 0#u64 false out1 (by omega) _ h
                    rw [bytesFrom_step hw'v, push_map hpush,
                      u64_cast_u32_val (by omega),
                      show (0#u64 : Std.U64).val = 0 from by scalar_tac] at hrec
                    refine ⟨?_, by omega, hjt⟩
                    rw [hcons]
                    have hstep : PinsDec.unescapeFrom
                        (b.val :: (bytesOf t).drop (i.val + 1)) v.val inEsc
                        (out.val.map (fun c => c.val))
                        = PinsDec.unescapeFrom ((bytesOf t).drop (i.val + 1)) 0 false
                            (out.val.map (fun c => c.val) ++ [b.val]) := by
                      simp [PinsDec.unescapeFrom, hesc, hn32, hn10, hn92, hb33, hb126]
                    rw [hstep]
                    exact hrec

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem unescape_from_refines {t : Slice Std.U8} {i : Std.Usize}
    {v : Std.U64} {inEsc : Bool} {out : alloc.vec.Vec Std.U32}
    {o : core.result.Result (alloc.vec.Vec Std.U32 × Std.Usize) core_types.CheckError}
    (h : pins_decode.unescape_from t i v inEsc out = ok o) :
    match o with
    | .Ok (s, j) =>
        PinsDec.unescapeFrom (bytesFrom t i) v.val inEsc (out.val.map (fun c => c.val))
            = some (s.val.map (fun c => c.val), bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  cases o <;> exact unescape_from_aux (t.length - i.val) i v inEsc out (le_refl _) _ h

/-- The full outcome; the `.Err` branch is the module's one `Native` error —
`read_index`'s, `after_space`'s, `unescape_from`'s, or the length check's. -/
theorem read_string_refines {t : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (alloc.vec.Vec Std.U32 × Std.Usize) core_types.CheckError}
    (h : pins_decode.read_string t i = ok o) :
    match o with
    | .Ok (s, j) =>
        PinsDec.readString (bytesFrom t i) = some (s.val.map (fun c => c.val), bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.read_string] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_index_refines hr
  | Ok pr =>
    obtain ⟨n, j1⟩ := pr
    replace h : (pins_decode.after_space t j1 >>= _) = ok o := h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    cases r1 with
    | Err e =>
      simp only [Result.ok.injEq] at h
      subst h
      exact after_space_refines hr1
    | Ok k =>
      simp only [] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      cases r2 with
      | Err e =>
        simp only [Result.ok.injEq] at h
        subst h
        exact unescape_from_refines hr2
      | Ok p1 =>
        obtain ⟨s1, m⟩ := p1
        replace h : (if alloc.vec.Vec.len s1 = n then _ else _) = ok o := h
        split at h
        · rename_i hlen
          simp only [Result.ok.injEq] at h
          subst h
          obtain ⟨hidx, hij1, hj1t⟩ := read_index_refines hr
          obtain ⟨hsp, hj1k, hkt⟩ := after_space_refines hr1
          obtain ⟨hun, hkm, hmt⟩ := unescape_from_refines hr2
          rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac,
            show (alloc.vec.Vec.new Std.U32).val.map (fun c => c.val) = [] from rfl] at hun
          have hl : (s1.val.map (fun c => c.val)).length = n.val := by
            simp only [List.length_map]; scalar_tac
          refine ⟨?_, by omega, hmt⟩
          simp only [PinsDec.readString, hidx, hsp, hun]
          rw [if_pos hl]
        · obtain ⟨ce, rfl, hce⟩ := err_native h
          exact hce

/-- The string a field decodes to is `Refine/Abs.lean`'s `absString` of the
port's `Vec<u32>` — the bridge between (A)'s code-point lists and the
`String`s `Read.lean` builds. -/
theorem decString_absString (s : alloc.vec.Vec Std.U32) :
    PinsDec.decString (s.val.map (fun c => c.val)) = absString s := by
  simp [PinsDec.decString, absString, Function.comp_def]

/-! ## Backward references -/

/-- The full outcome; the `.Err` branch is the module's one `Native` error,
either `read_index`'s or the out-of-range back-reference's own. -/
theorem name_ref_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (name.Name × Std.Usize) core_types.CheckError}
    (h : pins_decode.name_ref t i tb = ok o) :
    match o with
    | .Ok (n, j) =>
        PinsDec.nameRef (bytesFrom t i) (absTables tb) = some (absName n, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.name_ref] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_index_refines hr
  | Ok pr =>
    obtain ⟨kk, j1⟩ := pr
    replace h : (if kk < alloc.vec.Vec.len tb.names then _ else _) = ok o := h
    split at h
    · rename_i hkb
      have hkl : kk.val < tb.names.length := by scalar_tac
      rw [vec_index_ok hkl] at h
      simp only [bind_tc_ok, name_dup_eq, Result.ok.injEq] at h
      subst h
      obtain ⟨hidx, hij, hjt⟩ := read_index_refines hr
      refine ⟨?_, hij, hjt⟩
      have htab : (absTables tb).names[kk.val]? = some (absName tb.names.val[kk.val]) := by
        simp only [absTables, List.getElem?_map, List.getElem?_eq_getElem hkl]
        rfl
      simp only [PinsDec.nameRef, hidx, htab]
    · obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce

/-- The full outcome; the `.Err` branch is the module's one `Native` error,
either `read_index`'s or the out-of-range back-reference's own. -/
theorem level_ref_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (level.Level × Std.Usize) core_types.CheckError}
    (h : pins_decode.level_ref t i tb = ok o) :
    match o with
    | .Ok (u, j) =>
        PinsDec.levelRef (bytesFrom t i) (absTables tb) = some (absLevel u, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.level_ref] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_index_refines hr
  | Ok pr =>
    obtain ⟨kk, j1⟩ := pr
    replace h : (if kk < alloc.vec.Vec.len tb.levels then _ else _) = ok o := h
    split at h
    · rename_i hkb
      have hkl : kk.val < tb.levels.length := by scalar_tac
      rw [vec_index_ok hkl] at h
      simp only [bind_tc_ok, level_dup_eq, Result.ok.injEq] at h
      subst h
      obtain ⟨hidx, hij, hjt⟩ := read_index_refines hr
      refine ⟨?_, hij, hjt⟩
      have htab : (absTables tb).levels[kk.val]? = some (absLevel tb.levels.val[kk.val]) := by
        simp only [absTables, List.getElem?_map, List.getElem?_eq_getElem hkl]
        rfl
      simp only [PinsDec.levelRef, hidx, htab]
    · obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce

/-- The full outcome; the `.Err` branch is the module's one `Native` error,
either `read_index`'s or the out-of-range back-reference's own. -/
theorem pw_ref_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (prop_when.PropWhen × Std.Usize) core_types.CheckError}
    (h : pins_decode.pw_ref t i tb = ok o) :
    match o with
    | .Ok (p, j) =>
        PinsDec.pwRef (bytesFrom t i) (absTables tb) = some (absPropWhen p, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.pw_ref] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_index_refines hr
  | Ok pr =>
    obtain ⟨kk, j1⟩ := pr
    replace h : (if kk < alloc.vec.Vec.len tb.pws then _ else _) = ok o := h
    split at h
    · rename_i hkb
      have hkl : kk.val < tb.pws.length := by scalar_tac
      rw [vec_index_ok hkl] at h
      simp only [bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨c, hc, h⟩ := h
      have hcv := PropWhen.dup_eq hc
      subst hcv
      simp only [Result.ok.injEq] at h
      subst h
      obtain ⟨hidx, hij, hjt⟩ := read_index_refines hr
      refine ⟨?_, hij, hjt⟩
      have htab : (absTables tb).pws[kk.val]? = some (absPropWhen tb.pws.val[kk.val]) := by
        simp only [absTables, List.getElem?_map, List.getElem?_eq_getElem hkl]
        rfl
      simp only [PinsDec.pwRef, hidx, htab]
    · obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce

/-- The full outcome; the `.Err` branch is the module's one `Native` error,
either `read_index`'s or the out-of-range back-reference's own. -/
theorem expr_ref_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (expr.Expr × Std.Usize) core_types.CheckError}
    (h : pins_decode.expr_ref t i tb = ok o) :
    match o with
    | .Ok (e, j) =>
        PinsDec.exprRef (bytesFrom t i) (absTables tb) = some (absExpr e, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.expr_ref] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_index_refines hr
  | Ok pr =>
    obtain ⟨kk, j1⟩ := pr
    replace h : (if kk < alloc.vec.Vec.len tb.exprs then _ else _) = ok o := h
    split at h
    · rename_i hkb
      have hkl : kk.val < tb.exprs.length := by scalar_tac
      rw [vec_index_ok hkl] at h
      simp only [bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨c, hc, h⟩ := h
      have hcv := Expr.dup_eq hc
      subst hcv
      simp only [Result.ok.injEq] at h
      subst h
      obtain ⟨hidx, hij, hjt⟩ := read_index_refines hr
      refine ⟨?_, hij, hjt⟩
      have htab : (absTables tb).exprs[kk.val]? = some (absExpr tb.exprs.val[kk.val]) := by
        simp only [absTables, List.getElem?_map, List.getElem?_eq_getElem hkl]
        rfl
      simp only [PinsDec.exprRef, hidx, htab]
    · obtain ⟨ce, rfl, hce⟩ := err_native h
      exact hce

/-! ## Counted lists -/

/-- The induction behind `name_list_from_refines`: the recursion is on the
*counter*, and the `i ≤ t.length` bound is what the `k = 0` arm hands back —
that arm accepts any index, in range or not. -/
private theorem name_list_from_aux {t : Slice Std.U8} {tb : pins_decode.Tables} :
    ∀ (kf : Nat) (i k : Std.Usize) (out : alloc.vec.Vec name.Name),
      k.val ≤ kf → i.val ≤ t.length →
      ∀ (o : core.result.Result (alloc.vec.Vec name.Name × Std.Usize) core_types.CheckError),
        pins_decode.name_list_from t i tb k out = ok o →
        match o with
        | .Ok (res, j) =>
            PinsDec.nameListFrom (bytesFrom t i) (absTables tb) k.val (absNames out)
                = some (absNames res, bytesFrom t j)
              ∧ i.val ≤ j.val ∧ j.val ≤ t.length
        | .Err ce => absErrKind ce = none := by
  intro kf
  induction kf with
  | zero =>
    intro i k out hk hi o h
    rw [pins_decode.name_list_from.eq_def] at h
    rw [if_pos (show k = 0#usize from by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    rw [show k.val = 0 from by scalar_tac]
    exact ⟨by simp [PinsDec.nameListFrom], le_refl _, hi⟩
  | succ kf ih =>
    intro i k out hk hi o h
    rw [pins_decode.name_list_from.eq_def] at h
    split at h
    · simp only [Result.ok.injEq] at h
      subst h
      rename_i hk0
      rw [show k.val = 0 from by scalar_tac]
      exact ⟨by simp [PinsDec.nameListFrom], le_refl _, hi⟩
    · rename_i hk0
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        subst h
        exact after_space_refines hr
      | Ok j1 =>
        simp only [] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r1, hr1, h⟩ := h
        cases r1 with
        | Err e =>
          simp only [Result.ok.injEq] at h
          subst h
          exact name_ref_refines hr1
        | Ok pr =>
          obtain ⟨x0, m⟩ := pr
          replace h : (alloc.vec.Vec.push out x0 >>= _) = ok o := h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨out1, hpush, k1, hk1, h⟩ := h
          obtain ⟨hsp, hij1, hj1t⟩ := after_space_refines hr
          obtain ⟨href, hj1m, hmt⟩ := name_ref_refines hr1
          obtain ⟨w, hw, hwv⟩ := usize_sub_ok (i := k) (show 1 ≤ k.val from by scalar_tac)
          rw [hw, Result.ok.injEq] at hk1
          subst hk1
          cases o with
          | Err ce => exact ih m w out1 (by omega) hmt _ h
          | Ok pr1 =>
          obtain ⟨res, j⟩ := pr1
          obtain ⟨hrec, hmj, hjt⟩ := ih m w out1 (by omega) hmt _ h
          refine ⟨?_, by omega, hjt⟩
          obtain ⟨kv, hkv⟩ : ∃ kv, k.val = kv + 1 := ⟨k.val - 1, by scalar_tac⟩
          rw [hkv]
          simp only [PinsDec.nameListFrom, hsp, href]
          rw [show absNames out ++ [absName x0] = absNames out1 from by
            simp [absNames, vec_push_val hpush]]
          rw [show kv = w.val from by omega]
          exact hrec

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem name_list_from_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables} {k : Std.Usize} {out : alloc.vec.Vec name.Name}
    {o : core.result.Result (alloc.vec.Vec name.Name × Std.Usize) core_types.CheckError}
    (hi : i.val ≤ t.length)
    (h : pins_decode.name_list_from t i tb k out = ok o) :
    match o with
    | .Ok (ns, j) =>
        PinsDec.nameListFrom (bytesFrom t i) (absTables tb) k.val (absNames out)
            = some (absNames ns, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  cases o <;> exact name_list_from_aux k.val i k out (le_refl _) hi _ h

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem name_list_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (alloc.vec.Vec name.Name × Std.Usize) core_types.CheckError}
    (h : pins_decode.name_list t i tb = ok o) :
    match o with
    | .Ok (ns, j) =>
        PinsDec.nameList (bytesFrom t i) (absTables tb) = some (absNames ns, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.name_list] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_index_refines hr
  | Ok pr =>
    obtain ⟨n0, j1⟩ := pr
    replace h : pins_decode.name_list_from t j1 tb n0 (alloc.vec.Vec.new name.Name) = ok o := h
    obtain ⟨hidx, hij1, hj1t⟩ := read_index_refines hr
    cases o with
    | Err ce => exact name_list_from_refines hj1t h
    | Ok pr1 =>
    obtain ⟨ns, j⟩ := pr1
    obtain ⟨hrec, hj1j, hjt⟩ := name_list_from_refines hj1t h
    refine ⟨?_, by omega, hjt⟩
    rw [show absNames (alloc.vec.Vec.new name.Name) = [] from rfl] at hrec
    simp only [PinsDec.nameList, hidx]
    exact hrec

/-- The induction behind `level_list_from_refines`; see `name_list_from_aux`. -/
private theorem level_list_from_aux {t : Slice Std.U8} {tb : pins_decode.Tables} :
    ∀ (kf : Nat) (i k : Std.Usize) (out : alloc.vec.Vec level.Level),
      k.val ≤ kf → i.val ≤ t.length →
      ∀ (o : core.result.Result (alloc.vec.Vec level.Level × Std.Usize) core_types.CheckError),
        pins_decode.level_list_from t i tb k out = ok o →
        match o with
        | .Ok (res, j) =>
            PinsDec.levelListFrom (bytesFrom t i) (absTables tb) k.val (absLevels out)
                = some (absLevels res, bytesFrom t j)
              ∧ i.val ≤ j.val ∧ j.val ≤ t.length
        | .Err ce => absErrKind ce = none := by
  intro kf
  induction kf with
  | zero =>
    intro i k out hk hi o h
    rw [pins_decode.level_list_from.eq_def] at h
    rw [if_pos (show k = 0#usize from by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    rw [show k.val = 0 from by scalar_tac]
    exact ⟨by simp [PinsDec.levelListFrom], le_refl _, hi⟩
  | succ kf ih =>
    intro i k out hk hi o h
    rw [pins_decode.level_list_from.eq_def] at h
    split at h
    · simp only [Result.ok.injEq] at h
      subst h
      rename_i hk0
      rw [show k.val = 0 from by scalar_tac]
      exact ⟨by simp [PinsDec.levelListFrom], le_refl _, hi⟩
    · rename_i hk0
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        subst h
        exact after_space_refines hr
      | Ok j1 =>
        simp only [] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r1, hr1, h⟩ := h
        cases r1 with
        | Err e =>
          simp only [Result.ok.injEq] at h
          subst h
          exact level_ref_refines hr1
        | Ok pr =>
          obtain ⟨x0, m⟩ := pr
          replace h : (alloc.vec.Vec.push out x0 >>= _) = ok o := h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨out1, hpush, k1, hk1, h⟩ := h
          obtain ⟨hsp, hij1, hj1t⟩ := after_space_refines hr
          obtain ⟨href, hj1m, hmt⟩ := level_ref_refines hr1
          obtain ⟨w, hw, hwv⟩ := usize_sub_ok (i := k) (show 1 ≤ k.val from by scalar_tac)
          rw [hw, Result.ok.injEq] at hk1
          subst hk1
          cases o with
          | Err ce => exact ih m w out1 (by omega) hmt _ h
          | Ok pr1 =>
          obtain ⟨res, j⟩ := pr1
          obtain ⟨hrec, hmj, hjt⟩ := ih m w out1 (by omega) hmt _ h
          refine ⟨?_, by omega, hjt⟩
          obtain ⟨kv, hkv⟩ : ∃ kv, k.val = kv + 1 := ⟨k.val - 1, by scalar_tac⟩
          rw [hkv]
          simp only [PinsDec.levelListFrom, hsp, href]
          rw [show absLevels out ++ [absLevel x0] = absLevels out1 from by
            simp [absLevels, vec_push_val hpush]]
          rw [show kv = w.val from by omega]
          exact hrec

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem level_list_from_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables} {k : Std.Usize} {out : alloc.vec.Vec level.Level}
    {o : core.result.Result (alloc.vec.Vec level.Level × Std.Usize) core_types.CheckError}
    (hi : i.val ≤ t.length)
    (h : pins_decode.level_list_from t i tb k out = ok o) :
    match o with
    | .Ok (us, j) =>
        PinsDec.levelListFrom (bytesFrom t i) (absTables tb) k.val (absLevels out)
            = some (absLevels us, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  cases o <;> exact level_list_from_aux k.val i k out (le_refl _) hi _ h

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem level_list_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (alloc.vec.Vec level.Level × Std.Usize) core_types.CheckError}
    (h : pins_decode.level_list t i tb = ok o) :
    match o with
    | .Ok (us, j) =>
        PinsDec.levelList (bytesFrom t i) (absTables tb) = some (absLevels us, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.level_list] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_index_refines hr
  | Ok pr =>
    obtain ⟨n0, j1⟩ := pr
    replace h : pins_decode.level_list_from t j1 tb n0 (alloc.vec.Vec.new level.Level) = ok o := h
    obtain ⟨hidx, hij1, hj1t⟩ := read_index_refines hr
    cases o with
    | Err ce => exact level_list_from_refines hj1t h
    | Ok pr1 =>
    obtain ⟨us, j⟩ := pr1
    obtain ⟨hrec, hj1j, hjt⟩ := level_list_from_refines hj1t h
    refine ⟨?_, by omega, hjt⟩
    rw [show absLevels (alloc.vec.Vec.new level.Level) = [] from rfl] at hrec
    simp only [PinsDec.levelList, hidx]
    exact hrec

/-- The induction behind `expr_list_from_refines`; see `name_list_from_aux`. -/
private theorem expr_list_from_aux {t : Slice Std.U8} {tb : pins_decode.Tables} :
    ∀ (kf : Nat) (i k : Std.Usize) (out : alloc.vec.Vec expr.Expr),
      k.val ≤ kf → i.val ≤ t.length →
      ∀ (o : core.result.Result (alloc.vec.Vec expr.Expr × Std.Usize) core_types.CheckError),
        pins_decode.expr_list_from t i tb k out = ok o →
        match o with
        | .Ok (res, j) =>
            PinsDec.exprListFrom (bytesFrom t i) (absTables tb) k.val (absExprs out)
                = some (absExprs res, bytesFrom t j)
              ∧ i.val ≤ j.val ∧ j.val ≤ t.length
        | .Err ce => absErrKind ce = none := by
  intro kf
  induction kf with
  | zero =>
    intro i k out hk hi o h
    rw [pins_decode.expr_list_from.eq_def] at h
    rw [if_pos (show k = 0#usize from by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    rw [show k.val = 0 from by scalar_tac]
    exact ⟨by simp [PinsDec.exprListFrom], le_refl _, hi⟩
  | succ kf ih =>
    intro i k out hk hi o h
    rw [pins_decode.expr_list_from.eq_def] at h
    split at h
    · simp only [Result.ok.injEq] at h
      subst h
      rename_i hk0
      rw [show k.val = 0 from by scalar_tac]
      exact ⟨by simp [PinsDec.exprListFrom], le_refl _, hi⟩
    · rename_i hk0
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        subst h
        exact after_space_refines hr
      | Ok j1 =>
        simp only [] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r1, hr1, h⟩ := h
        cases r1 with
        | Err e =>
          simp only [Result.ok.injEq] at h
          subst h
          exact expr_ref_refines hr1
        | Ok pr =>
          obtain ⟨x0, m⟩ := pr
          replace h : (alloc.vec.Vec.push out x0 >>= _) = ok o := h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨out1, hpush, k1, hk1, h⟩ := h
          obtain ⟨hsp, hij1, hj1t⟩ := after_space_refines hr
          obtain ⟨href, hj1m, hmt⟩ := expr_ref_refines hr1
          obtain ⟨w, hw, hwv⟩ := usize_sub_ok (i := k) (show 1 ≤ k.val from by scalar_tac)
          rw [hw, Result.ok.injEq] at hk1
          subst hk1
          cases o with
          | Err ce => exact ih m w out1 (by omega) hmt _ h
          | Ok pr1 =>
          obtain ⟨res, j⟩ := pr1
          obtain ⟨hrec, hmj, hjt⟩ := ih m w out1 (by omega) hmt _ h
          refine ⟨?_, by omega, hjt⟩
          obtain ⟨kv, hkv⟩ : ∃ kv, k.val = kv + 1 := ⟨k.val - 1, by scalar_tac⟩
          rw [hkv]
          simp only [PinsDec.exprListFrom, hsp, href]
          rw [show absExprs out ++ [absExpr x0] = absExprs out1 from by
            simp [absExprs, vec_push_val hpush]]
          rw [show kv = w.val from by omega]
          exact hrec

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem expr_list_from_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables} {k : Std.Usize} {out : alloc.vec.Vec expr.Expr}
    {o : core.result.Result (alloc.vec.Vec expr.Expr × Std.Usize) core_types.CheckError}
    (hi : i.val ≤ t.length)
    (h : pins_decode.expr_list_from t i tb k out = ok o) :
    match o with
    | .Ok (es, j) =>
        PinsDec.exprListFrom (bytesFrom t i) (absTables tb) k.val (absExprs out)
            = some (absExprs es, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  cases o <;> exact expr_list_from_aux k.val i k out (le_refl _) hi _ h

/-- The full outcome; the `.Err` branch is the module's one `Native` error. -/
theorem expr_list_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (alloc.vec.Vec expr.Expr × Std.Usize) core_types.CheckError}
    (h : pins_decode.expr_list t i tb = ok o) :
    match o with
    | .Ok (es, j) =>
        PinsDec.exprList (bytesFrom t i) (absTables tb) = some (absExprs es, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.expr_list] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_index_refines hr
  | Ok pr =>
    obtain ⟨n0, j1⟩ := pr
    replace h : pins_decode.expr_list_from t j1 tb n0 (alloc.vec.Vec.new expr.Expr) = ok o := h
    obtain ⟨hidx, hij1, hj1t⟩ := read_index_refines hr
    cases o with
    | Err ce => exact expr_list_from_refines hj1t h
    | Ok pr1 =>
    obtain ⟨es, j⟩ := pr1
    obtain ⟨hrec, hj1j, hjt⟩ := expr_list_from_refines hj1t h
    refine ⟨?_, by omega, hjt⟩
    rw [show absExprs (alloc.vec.Vec.new expr.Expr) = [] from rfl] at hrec
    simp only [PinsDec.exprList, hidx]
    exact hrec

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Con-leche's own three and nothing else — no Aeneas library axiom, no `Arc`
model, and in particular nothing native-decide-shaped: every lemma here is
about *every* byte string, so nothing is ever evaluated.  `read_index_refines`
is the one worth naming, since it is the lemma the port's `> 4294967295` guard
exists for (task #64). -/

/-- info: 'ConRon.Refine.PinsBytes.read_index_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_index_refines

/-- info: 'ConRon.Refine.PinsBytes.unescape_from_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unescape_from_refines

/-- info: 'ConRon.Refine.PinsBytes.expr_list_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expr_list_refines

end ConRon.Refine.PinsBytes
