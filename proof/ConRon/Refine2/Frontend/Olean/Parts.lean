/-
# `ConRon.Refine2.Frontend.Olean.Parts` — the files of a module, in `olean/region.rs`

**Task #142, Theorem 2.**  `part_of_bytes` against the twin's `partOfBytes`, the header
validated; `region_single`, `region_of_parts2`/`3` against upstream's `Region.single` and
`Region.ofParts`.  `PartFits` is what `part_of_bytes` leaves true of a part, and from it
`RegionFits`, which the reads' saturating comparisons ask.
-/
import ConRon.Refine2.Frontend.Olean.Region

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConLeche.Frontend.Olean (rdU8 rdU64)
open ConRon.Refine.HashMap (uscalar_add_eq uscalar_sub_eq)
open ConRon.Refine2.Lockstep (LSP)
open ConRon.Refine2 (AErrKind absAErrKind)

/-- A file, as upstream's `Part`. -/
def absPart (p : frontend.olean.region.Part) : ConLeche.Frontend.Olean.Part :=
  ⟨absWord p.base, absBytes (alloc.vec.Vec.deref p.bytes)⟩

/-- What `part_of_bytes` leaves true of a part. -/
structure PartFits (p : frontend.olean.region.Part) : Prop where
  size : p.bytes.val.length < 2 ^ 60
  base : p.base.val + p.bytes.val.length ≤ 2 ^ 64 - 1

theorem deref_val {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val :=
  Slice.from_val _ _

theorem len_u64 (v : alloc.vec.Vec Std.U8) :
    (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len v)).val = v.val.length := by
  rw [cast_u64_usize]; simp

theorem absRegion_segs_one (bs : Slice Std.U8) (r : frontend.olean.region.Region)
    {s : frontend.olean.region.Seg} (hs : r.segs.val = [s]) :
    (absRegion bs r).segs = #[absSeg s] := by
  simp [absRegion, hs]

/-- **`region_single` is `Region.single`.** -/
theorem region_single_eq {p : frontend.olean.region.Part} {r} (hp : PartFits p)
    (h : region_single p = ok r) :
    absRegion (alloc.vec.Vec.deref p.bytes) r = ConLeche.Frontend.Olean.Region.single (absPart p) ∧
      RegionFits (alloc.vec.Vec.deref p.bytes) r := by
  rw [region_single] at h
  simp only [lift, bind_ok] at h
  peel h as segs1, hs
  cases Result.ok_injective h
  have hv := ConRon.Refine.vec_push_val hs
  have hsv : segs1.val = [({ base := p.base, off := 0#u64, size := UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len p.bytes) } : frontend.olean.region.Seg)] := by
    simpa [alloc.vec.Vec.with_capacity] using hv
  have hl := len_u64 p.bytes
  have hps := hp.size
  constructor
  · have e : segs1.val.map absSeg = [⟨absWord p.base, 0, (absBytes (alloc.vec.Vec.deref p.bytes)).size⟩] := by
      rw [hsv, absBytes_size, deref_val, ← hl]
      rfl
    show (⟨absBytes _, (segs1.val.map absSeg).toArray⟩ : ConLeche.Frontend.Olean.Region) = _
    rw [e]
    rfl
  · intro s hm
    rw [hsv] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    have : (0#u64 : Std.U64).val = 0 := by decide
    simp only [this, hl, deref_val]
    omega

/-- A part's module data address. -/
theorem part_module_data_addr_eq {p : frontend.olean.region.Part} {x : Std.U64}
    (h : part_module_data_addr p = ok x) : absWord x = (absPart p).moduleDataAddr := by
  rw [part_module_data_addr] at h
  have := rd_u64_eq (by simpa using h)
  rw [show (HEADER_SIZE : Std.U64).val = 88 by unfold HEADER_SIZE; decide] at this
  exact this

/-- `parts_ordered`, a step of `partsOrdered`. -/
theorem parts_ordered_eq {a b : frontend.olean.region.Part} {o : Bool} (ha : PartFits a)
    (h : parts_ordered a b = ok o) :
    o = decide ((absPart a).base.toNat + (absPart a).bytes.size ≤ (absPart b).base.toNat) := by
  rw [parts_ordered] at h
  simp only [lift, bind_ok] at h
  peel h as x, hx
  cases Result.ok_injective h
  have hv := sat_add_spec hx
  rw [len_u64] at hv
  have hb := ha.base
  have hx' : x.val = a.base.val + a.bytes.val.length := by omega
  simp only [absPart, absWord_toNat, absBytes_size, deref_val, ← hx']
  by_cases hc : x.val ≤ b.base.val
  · have : x ≤ b.base := hc
    simp [this, hc]
  · have : ¬ x ≤ b.base := hc
    simp [this, hc]

/-- `region_push`: the bytes appended and the segment after them. -/
theorem region_push_eq {bytes : alloc.vec.Vec Std.U8} {segs p o}
    (h : region_push bytes segs p = ok o) :
    o.1.val = bytes.val ++ p.bytes.val ∧
      o.2.val = segs.val ++ [frontend.olean.region.Seg.mk p.base (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes)) (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len p.bytes))] := by
  rw [region_push] at h
  simp only [lift, bind_ok] at h
  peel h as b1, hb1
  peel h as s1, hs1
  cases Result.ok_injective h
  exact ⟨by rw [extend_u8_val hb1, deref_val], ConRon.Refine.vec_push_val hs1⟩

/-- The bytes of a region of parts. -/
theorem absBytes_append {s : Slice Std.U8} {a b : Slice Std.U8} (h : s.val = a.val ++ b.val) :
    absBytes s = absBytes a ++ absBytes b := by
  apply ByteArray.ext
  simp [absBytes, h]

/-- The kinds of the error tails of `part_of_bytes`. -/
theorem err_step {α β : Type} {K : AErrKind} {f : Result β}
    {k : β → Result (core.result.Result α kernel.core_types.CheckError)}
    (hk : ∀ b, LSP (k b) (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some K)) :
    LSP (Std.bind f k) (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some K) :=
  ConRon.Refine2.Lockstep.LSP.bind_eq fun a _ => hk a

theorem err_internal {α : Type} {v} :
    LSP (do let ce ← kernel.core_types.internal v; ok (core.result.Result.Err ce : core.result.Result α _))
      (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) := by
  intro o h
  simp only [kernel.core_types.internal, bind_ok, Result.ok.injEq] at h
  exact ⟨_, h.symm, rfl⟩

theorem err_notimpl {α : Type} {v} :
    LSP (do let ce ← kernel.core_types.not_implemented v; ok (core.result.Result.Err ce : core.result.Result α _))
      (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .notImplemented) := by
  intro o h
  simp only [kernel.core_types.not_implemented, bind_ok, Result.ok.injEq] at h
  exact ⟨_, h.symm, rfl⟩

theorem err_native {α : Type} {v} :
    LSP (do let ce ← kernel.core_types.native v; ok (core.result.Result.Err ce : core.result.Result α _))
      (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .native) := by
  intro o h
  simp only [kernel.core_types.native, bind_ok, Result.ok.injEq] at h
  exact ⟨_, h.symm, rfl⟩

/-- An error tail, of any of the messages `part_of_bytes` builds. -/
macro "err_tail" : tactic => `(tactic| (
  repeat' first
    | exact err_internal
    | exact err_notimpl
    | exact err_native
    | (refine err_step fun _ => ?_)))

theorem part_max_val {x : Std.U64} (h : PART_MAX = ok x) : x.val = 2 ^ 60 := by
  unfold PART_MAX at h
  have := (ConRon.Refine.Nat.ushiftLeftI_val h).2
  rw [this]; decide

theorem absByte_eq_lit {c : Std.U8} {k : UInt8} : absByte c = k ↔ c.val = k.toNat := by
  constructor
  · intro h; rw [← h, absByte_toNat]
  · intro h; apply UInt8.toNat_inj.mp; rw [absByte_toNat, h]

theorem toUTF8_olean : ("olean".toUTF8).data = #[111, 108, 101, 97, 110] := by decide

theorem magic_list : ∀ (l : List Std.U8) (h : 5 ≤ l.length),
    ((l.take 5).map absByte).toArray = #[111, 108, 101, 97, 110] ↔
      (l[0]'(by omega)).val = 111 ∧ (l[1]'(by omega)).val = 108 ∧ (l[2]'(by omega)).val = 101 ∧
      (l[3]'(by omega)).val = 97 ∧ (l[4]'(by omega)).val = 110
  | c0 :: c1 :: c2 :: c3 :: c4 :: t, _ => by
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
      List.getElem_cons_zero, List.getElem_cons_succ]
    constructor
    · intro he
      have := congrArg Array.toList he
      simp only [List.cons.injEq, absByte_eq_lit, and_true] at this
      exact this
    · rintro ⟨h0, h1, h2, h3, h4⟩
      apply Array.ext'
      simp only [List.cons.injEq, absByte_eq_lit, and_true]
      exact ⟨h0, h1, h2, h3, h4⟩

/-- The magic of the header, on the abstraction. -/
theorem magic_iff {b : Slice Std.U8} (h : 96 ≤ b.val.length) :
    ((absBytes b).extract 0 5 == "olean".toUTF8) = true ↔
      (b.val[0]'(by omega)).val = 111 ∧ (b.val[1]'(by omega)).val = 108 ∧ (b.val[2]'(by omega)).val = 101 ∧
      (b.val[3]'(by omega)).val = 97 ∧ (b.val[4]'(by omega)).val = 110 := by
  show (((absBytes b).extract 0 5).data == ("olean".toUTF8).data) = true ↔ _
  rw [toUTF8_olean, beq_iff_eq, ByteArray.data_extract]
  have e : (absBytes b).data.extract 0 5 = (((b.val.take 5).map absByte)).toArray := by
    apply Array.ext'
    simp [absBytes]
  rw [e]
  exact magic_list _ (by omega)

/-- The twin's `partOfBytes` of a file past the cap. -/
theorem partOfBytes_big {path : String} {b : ByteArray} (h : 2 ^ 60 ≤ b.size) :
    ∃ m, Arena.Frontend.Olean.partOfBytes path b = .error (.native m) :=
  ⟨_, by unfold Arena.Frontend.Olean.partOfBytes; rw [ite_eq_left h]⟩

/-- The twin's `partOfBytes` under the cap is upstream's `Part.ofBytes`. -/
theorem partOfBytes_small {path : String} {b : ByteArray} (h : ¬ 2 ^ 60 ≤ b.size) :
    Arena.Frontend.Olean.partOfBytes path b =
      match ConLeche.Frontend.Olean.Part.ofBytes (Arena.Frontend.Olean.displayPathF path) b with
      | .ok p => .ok p
      | .error e => .error (Arena.Frontend.Olean.toArenaError e) := by
  unfold Arena.Frontend.Olean.partOfBytes; rw [ite_eq_right h]; rfl

section ofBytes
open ConLeche.Frontend.Olean (Part dataStart)
variable {p : String} {b : ByteArray}

theorem ofBytes_short (h : ¬ b.size ≥ dataStart) :
    ∃ m, Part.ofBytes p b = .error (.internal m) := by
  simp only [Part.ofBytes, h, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem ofBytes_magic (h0 : b.size ≥ dataStart) (h : ¬ (b.extract 0 5 == "olean".toUTF8) = true) :
    ∃ m, Part.ofBytes p b = .error (.internal m) := by
  simp only [Part.ofBytes, h0, h, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem ofBytes_ver (h0 : b.size ≥ dataStart) (h1 : (b.extract 0 5 == "olean".toUTF8) = true)
    (h : ¬ (rdU8 b 5 == 2) = true) :
    ∃ m, Part.ofBytes p b = .error (.notImplemented m) := by
  simp only [Part.ofBytes, h0, h1, h, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem ofBytes_gmp (h0 : b.size ≥ dataStart) (h1 : (b.extract 0 5 == "olean".toUTF8) = true)
    (h2 : (rdU8 b 5 == 2) = true) (h : ¬ (rdU8 b 6 &&& 1 == 1) = true) :
    ∃ m, Part.ofBytes p b = .error (.notImplemented m) := by
  simp only [Part.ofBytes, h0, h1, h2, h, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem ofBytes_words (h0 : b.size ≥ dataStart) (h1 : (b.extract 0 5 == "olean".toUTF8) = true)
    (h2 : (rdU8 b 5 == 2) = true) (h3 : (rdU8 b 6 &&& 1 == 1) = true) (h : ¬ (b.size % 8 == 0) = true) :
    ∃ m, Part.ofBytes p b = .error (.internal m) := by
  simp only [Part.ofBytes, h0, h1, h2, h3, h, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem ofBytes_base (h0 : b.size ≥ dataStart) (h1 : (b.extract 0 5 == "olean".toUTF8) = true)
    (h2 : (rdU8 b 5 == 2) = true) (h3 : (rdU8 b 6 &&& 1 == 1) = true) (h4 : (b.size % 8 == 0) = true)
    (h : ¬ (rdU64 b 80 % 8 == 0 && decide ((rdU64 b 80).toNat + b.size < 2 ^ 64)) = true) :
    ∃ m, Part.ofBytes p b = .error (.internal m) := by
  simp only [Part.ofBytes, h0, h1, h2, h3, h4, h, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem ofBytes_ok (h0 : b.size ≥ dataStart) (h1 : (b.extract 0 5 == "olean".toUTF8) = true)
    (h2 : (rdU8 b 5 == 2) = true) (h3 : (rdU8 b 6 &&& 1 == 1) = true) (h4 : (b.size % 8 == 0) = true)
    (h : (rdU64 b 80 % 8 == 0 && decide ((rdU64 b 80).toNat + b.size < 2 ^ 64)) = true) :
    Part.ofBytes p b = .ok ⟨rdU64 b 80, b⟩ := by
  simp only [Part.ofBytes, h0, h1, h2, h3, h4, h, ↓reduceIte]
  rfl

end ofBytes

/-- An error of the twin at the kind of the Rust's. -/
theorem twin_err_of_kind {α : Type} {e : kernel.core_types.CheckError} {K : AErrKind}
    {x : Except Arena.CheckError α} {le : Arena.CheckError} (hx : x = .error le)
    (he : absAErrKind e = some K) (hle : ConRon.Refine2.lAErrKind le = some K) :
    ConRon.Refine2.AErrSim e x :=
  ConRon.Refine2.AErrSim.of_kind hx he hle

/-- **`part_of_bytes` is the twin's `partOfBytes`**, whatever the path: a message is not
compared. -/
theorem part_of_bytes_eq {path : alloc.vec.Vec Std.U32} {b : alloc.vec.Vec Std.U8} {o}
    (path' : String) (h : part_of_bytes path b = ok o) :
    match o with
    | .Ok p => Arena.Frontend.Olean.partOfBytes path' (absBytes (alloc.vec.Vec.deref b)) = .ok (absPart p) ∧
        p.bytes = b ∧ PartFits p
    | .Err e => ConRon.Refine2.AErrSim e (Arena.Frontend.Olean.partOfBytes path' (absBytes (alloc.vec.Vec.deref b))) := by
  delta part_of_bytes at h
  dsimp only at h
  obtain ⟨size, hsize0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective (show ok _ = ok size from hsize0)
  peel h as mx, hmx
  have hmxv := part_max_val hmx
  have hsz := len_u64 b
  have hsize : (absBytes (alloc.vec.Vec.deref b)).size = b.val.length := by
    rw [absBytes_size, deref_val]
  generalize hB : absBytes (alloc.vec.Vec.deref b) = B at *
  have hds : ConLeche.Frontend.Olean.dataStart = 96 := rfl
  have d2 := data_start_val
  by_cases hbig : mx ≤ UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b)
  · rw [ite_eq_left hbig] at h
    have hbig' : 2 ^ 60 ≤ b.val.length := by
      have : mx.val ≤ (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b)).val := hbig
      omega
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .native) from by err_tail) o h
    obtain ⟨m, hm⟩ := partOfBytes_big (path := path') (b := B) (by omega)
    exact twin_err_of_kind hm hk rfl
  rw [ite_eq_right hbig] at h
  have hsmall' : ¬ 2 ^ 60 ≤ b.val.length := by
    have : ¬ mx.val ≤ (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b)).val := hbig
    omega
  have hbs : ¬ 2 ^ 60 ≤ B.size := by omega
  have hrw := partOfBytes_small (path := path') hbs
  by_cases hshort : UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b) < DATA_START
  · rw [ite_eq_left hshort] at h
    have hshort' : b.val.length < 96 := by
      have : (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b)).val < DATA_START.val := hshort
      omega
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) o h
    obtain ⟨m, hm⟩ := ofBytes_short (p := Arena.Frontend.Olean.displayPathF path') (b := B) (by rw [hds]; omega)
    rw [hrw, hm]
    exact twin_err_of_kind rfl hk rfl
  rw [ite_eq_right hshort] at h
  have hlong' : 96 ≤ b.val.length := by
    have : ¬ (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b)).val < DATA_START.val := hshort
    omega
  have h0B : B.size ≥ ConLeche.Frontend.Olean.dataStart := by rw [hds]; omega
  have hslice : 96 ≤ (alloc.vec.Vec.deref b).val.length := by rw [deref_val]; exact hlong'
  have hmag := magic_iff hslice
  rw [hB] at hmag
  have dv : ∀ {i} (hi : i < (alloc.vec.Vec.deref b).val.length),
      ((alloc.vec.Vec.deref b).val[i]'hi) = b.val[i]'(by rw [← deref_val]; exact hi) := by
    intro i hi; simp only [deref_val]
  simp only [dv] at hmag
  /- The bad magic, one tail for each of the five bytes. -/
  have bad_end : ∀ {e : kernel.core_types.CheckError},
      (¬ (B.extract 0 5 == "olean".toUTF8) = true) → absAErrKind e = some .internal →
      ConRon.Refine2.AErrSim e (match ConLeche.Frontend.Olean.Part.ofBytes (Arena.Frontend.Olean.displayPathF path') B with
        | .ok p => (.ok p : Except Arena.CheckError _)
        | .error e => .error (Arena.Frontend.Olean.toArenaError e)) := by
    intro e hn hk
    obtain ⟨m, hm⟩ := ofBytes_magic (p := Arena.Frontend.Olean.displayPathF path') h0B hn
    rw [hm]
    exact twin_err_of_kind rfl hk rfl
  peel h as c0, hc0
  obtain ⟨z0, rfl⟩ := vec_index_eq hc0
  by_cases e0 : b.val[(0#usize : Std.Usize).val] = 111#u8
  swap
  · rw [ite_eq_right e0] at h
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) o h
    rw [hrw]
    refine bad_end (fun hm => e0 (UScalar.eq_of_val_eq ?_)) hk
    exact (hmag.mp hm).1
  rw [ite_eq_left e0] at h
  peel h as c1, hc1
  obtain ⟨z1, rfl⟩ := vec_index_eq hc1
  by_cases e1 : b.val[(1#usize : Std.Usize).val] = 108#u8
  swap
  · rw [ite_eq_right e1] at h
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) o h
    rw [hrw]
    refine bad_end (fun hm => e1 (UScalar.eq_of_val_eq ?_)) hk
    exact (hmag.mp hm).2.1
  rw [ite_eq_left e1] at h
  peel h as c2, hc2
  obtain ⟨z2, rfl⟩ := vec_index_eq hc2
  by_cases e2 : b.val[(2#usize : Std.Usize).val] = 101#u8
  swap
  · rw [ite_eq_right e2] at h
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) o h
    rw [hrw]
    refine bad_end (fun hm => e2 (UScalar.eq_of_val_eq ?_)) hk
    exact (hmag.mp hm).2.2.1
  rw [ite_eq_left e2] at h
  peel h as c3, hc3
  obtain ⟨z3, rfl⟩ := vec_index_eq hc3
  by_cases e3 : b.val[(3#usize : Std.Usize).val] = 97#u8
  swap
  · rw [ite_eq_right e3] at h
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) o h
    rw [hrw]
    refine bad_end (fun hm => e3 (UScalar.eq_of_val_eq ?_)) hk
    exact (hmag.mp hm).2.2.2.1
  rw [ite_eq_left e3] at h
  peel h as c4, hc4
  obtain ⟨z4, rfl⟩ := vec_index_eq hc4
  by_cases e4 : b.val[(4#usize : Std.Usize).val] = 110#u8
  swap
  · rw [ite_eq_right e4] at h
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) o h
    rw [hrw]
    refine bad_end (fun hm => e4 (UScalar.eq_of_val_eq ?_)) hk
    exact (hmag.mp hm).2.2.2.2
  rw [ite_eq_left e4] at h
  have hm1 : (B.extract 0 5 == "olean".toUTF8) = true := hmag.mpr
    ⟨by rw [show (b.val[0]'(by omega)) = 111#u8 from e0]; rfl,
     by rw [show (b.val[1]'(by omega)) = 108#u8 from e1]; rfl,
     by rw [show (b.val[2]'(by omega)) = 101#u8 from e2]; rfl,
     by rw [show (b.val[3]'(by omega)) = 97#u8 from e3]; rfl,
     by rw [show (b.val[4]'(by omega)) = 110#u8 from e4]; rfl⟩
  have hdr : ∀ {i x}, rd_u8 (alloc.vec.Vec.deref b) i = ok x → rdU8 B i.val = absByte x := by
    intro i x hx; rw [← hB]; exact (rd_u8_eq hx).symm
  peel h as ver, hver
  have ev : rdU8 B 5 = absByte ver := hdr hver
  by_cases hv : (ver != 2#u8) = true
  · rw [ite_eq_left hv] at h
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .notImplemented) from by err_tail) o h
    have hn : ¬ (rdU8 B 5 == 2) = true := by
      rw [ev, beq_iff_eq, absByte_eq_lit]
      intro he; simp only [bne_iff_ne, ne_eq] at hv; exact hv (UScalar.eq_of_val_eq he)
    obtain ⟨m, hm⟩ := ofBytes_ver (p := Arena.Frontend.Olean.displayPathF path') h0B hm1 hn
    rw [hrw, hm]
    exact twin_err_of_kind rfl hk rfl
  rw [ite_eq_right hv] at h
  have hv2 : (rdU8 B 5 == 2) = true := by
    rw [ev, beq_iff_eq, absByte_eq_lit]
    simp only [bne_iff_ne, ne_eq, not_not] at hv
    rw [hv]; rfl
  peel h as c6, hc6
  have ec6 : rdU8 B 6 = absByte c6 := hdr hc6
  peel h as c7, hc7
  cases Result.ok_injective (show ok _ = ok c7 from hc7)
  have eand : (absByte (c6 &&& 1#u8)) = (rdU8 B 6 &&& 1) := by
    apply UInt8.toNat_inj.mp
    rw [ec6, absByte_toNat, UInt8.toNat_and, absByte_toNat]
    rfl
  by_cases hg : ((c6 &&& 1#u8) != 1#u8) = true
  · rw [ite_eq_left hg] at h
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .notImplemented) from by err_tail) o h
    have hn : ¬ (rdU8 B 6 &&& 1 == 1) = true := by
      rw [← eand, beq_iff_eq, absByte_eq_lit]
      intro he; simp only [bne_iff_ne, ne_eq] at hg; exact hg (UScalar.eq_of_val_eq he)
    obtain ⟨m, hm⟩ := ofBytes_gmp (p := Arena.Frontend.Olean.displayPathF path') h0B hm1 hv2 hn
    rw [hrw, hm]
    exact twin_err_of_kind rfl hk rfl
  rw [ite_eq_right hg] at h
  have hg2 : (rdU8 B 6 &&& 1 == 1) = true := by
    rw [← eand, beq_iff_eq, absByte_eq_lit]
    simp only [bne_iff_ne, ne_eq, not_not] at hg
    rw [hg]; rfl
  peel h as m8, hm8
  have hm8v : m8.val = b.val.length % 8 := by
    rw [ConRon.Refine.CoreK.uscalar_rem_eq (by decide) hm8, hsz]; rfl
  by_cases hw : (m8 != 0#u64) = true
  · rw [ite_eq_left hw] at h
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) o h
    have hn : ¬ (B.size % 8 == 0) = true := by
      rw [beq_iff_eq, hsize, ← hm8v]
      intro he; simp only [bne_iff_ne, ne_eq] at hw; exact hw (UScalar.eq_of_val_eq (by rw [he]; rfl))
    obtain ⟨m, hm⟩ := ofBytes_words (p := Arena.Frontend.Olean.displayPathF path') h0B hm1 hv2 hg2 hn
    rw [hrw, hm]
    exact twin_err_of_kind rfl hk rfl
  rw [ite_eq_right hw] at h
  have hw2 : (B.size % 8 == 0) = true := by
    rw [beq_iff_eq, hsize, ← hm8v]
    simp only [bne_iff_ne, ne_eq, not_not] at hw
    rw [hw]; rfl
  peel h as base, hbase
  have ebase : rdU64 B 80 = absWord base := by
    rw [← hB]; exact (rd_u64_eq hbase).symm
  peel h as m10, hm10
  have hm10v : m10.val = base.val % 8 := ConRon.Refine.CoreK.uscalar_rem_eq (by decide) hm10
  have ebb : (rdU64 B 80 % 8 == 0) = decide (base.val % 8 = 0) := by
    rw [ebase]
    by_cases hc : base.val % 8 = 0
    · have : absWord base % 8 = 0 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_mod, absWord_toNat]; exact hc
      simp [this, hc]
    · have : absWord base % 8 ≠ 0 := by
        intro he; apply hc
        have := congrArg UInt64.toNat he
        rwa [UInt64.toNat_mod, absWord_toNat] at this
      simp [this, hc]
  have hbt := u64_lt base
  by_cases h10 : m10 = 0#u64
  · rw [ite_eq_left h10] at h
    have hb8 : base.val % 8 = 0 := by rw [← hm10v, h10]; rfl
    peel h as room, hroom
    have hroomv := uscalar_sub_eq hroom
    rw [u64_max_val, hsz] at hroomv
    by_cases hle : base ≤ room
    · rw [ite_eq_left hle] at h
      cases Result.ok_injective h
      have hle' : base.val ≤ room.val := hle
      have hsum : base.val + b.val.length < 2 ^ 64 := by omega
      have hOk : (rdU64 B 80 % 8 == 0 && decide ((rdU64 B 80).toNat + B.size < 2 ^ 64)) = true := by
        rw [ebb, ebase, absWord_toNat, hsize]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hb8, hsum⟩
      have := ofBytes_ok (p := Arena.Frontend.Olean.displayPathF path') h0B hm1 hv2 hg2 hw2 hOk
      refine ⟨?_, rfl, ⟨by show b.val.length < 2 ^ 60; omega, by show base.val + b.val.length ≤ _; omega⟩⟩
      rw [hrw, this, ebase]
      simp only [absPart, ← hB]
    · rw [ite_eq_right hle] at h
      obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) o h
      have hle' : ¬ base.val ≤ room.val := hle
      have hn : ¬ (rdU64 B 80 % 8 == 0 && decide ((rdU64 B 80).toNat + B.size < 2 ^ 64)) = true := by
        rw [ebb, ebase, absWord_toNat, hsize]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      obtain ⟨m, hm⟩ := ofBytes_base (p := Arena.Frontend.Olean.displayPathF path') h0B hm1 hv2 hg2 hw2 hn
      rw [hrw, hm]
      exact twin_err_of_kind rfl hk rfl
  · rw [ite_eq_right h10] at h
    obtain ⟨e, rfl, hk⟩ := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) o h
    have hb8 : base.val % 8 ≠ 0 := by
      intro he; apply h10; apply UScalar.eq_of_val_eq; rw [hm10v, he]; rfl
    have hn : ¬ (rdU64 B 80 % 8 == 0 && decide ((rdU64 B 80).toNat + B.size < 2 ^ 64)) = true := by
      rw [ebb]; simp [hb8]
    obtain ⟨m, hm⟩ := ofBytes_base (p := Arena.Frontend.Olean.displayPathF path') h0B hm1 hv2 hg2 hw2 hn
    rw [hrw, hm]
    exact twin_err_of_kind rfl hk rfl

/-- `Region.ofParts` of two files. -/
theorem ofParts2 (a b : ConLeche.Frontend.Olean.Part) :
    ConLeche.Frontend.Olean.Region.ofParts #[a, b] =
      if decide (a.base.toNat + a.bytes.size ≤ b.base.toNat) = true then
        .ok ⟨(ByteArray.emptyWithCapacity (a.bytes.size + b.bytes.size) ++ a.bytes) ++ b.bytes,
          #[⟨a.base, (ByteArray.emptyWithCapacity (a.bytes.size + b.bytes.size)).size, a.bytes.size⟩,
            ⟨b.base, (ByteArray.emptyWithCapacity (a.bytes.size + b.bytes.size) ++ a.bytes).size, b.bytes.size⟩]⟩
      else .error (.internal "the .olean files of a module overlap") := by
  by_cases h : decide (a.base.toNat + a.bytes.size ≤ b.base.toNat) = true
  · simp only [ConLeche.Frontend.Olean.Region.ofParts, ConLeche.Frontend.Olean.partsOrdered, h]
    simp [Nat.add_comm]
    rfl
  · simp only [ConLeche.Frontend.Olean.Region.ofParts, ConLeche.Frontend.Olean.partsOrdered, h]
    simp
    rfl

/-- `Region.ofParts` of three files. -/
theorem ofParts3 (a b c : ConLeche.Frontend.Olean.Part) :
    ConLeche.Frontend.Olean.Region.ofParts #[a, b, c] =
      if (decide (a.base.toNat + a.bytes.size ≤ b.base.toNat) &&
          decide (b.base.toNat + b.bytes.size ≤ c.base.toNat)) = true then
        .ok ⟨(ByteArray.emptyWithCapacity (a.bytes.size + b.bytes.size + c.bytes.size) ++ a.bytes) ++ b.bytes ++ c.bytes,
          #[⟨a.base, (ByteArray.emptyWithCapacity (a.bytes.size + b.bytes.size + c.bytes.size)).size, a.bytes.size⟩,
            ⟨b.base, (ByteArray.emptyWithCapacity (a.bytes.size + b.bytes.size + c.bytes.size) ++ a.bytes).size, b.bytes.size⟩,
            ⟨c.base, ((ByteArray.emptyWithCapacity (a.bytes.size + b.bytes.size + c.bytes.size) ++ a.bytes) ++ b.bytes).size, c.bytes.size⟩]⟩
      else .error (.internal "the .olean files of a module overlap") := by
  by_cases h : (decide (a.base.toNat + a.bytes.size ≤ b.base.toNat) &&
      decide (b.base.toNat + b.bytes.size ≤ c.base.toNat)) = true
  · simp only [ConLeche.Frontend.Olean.Region.ofParts, ConLeche.Frontend.Olean.partsOrdered, Bool.and_true, h]
    simp [Nat.add_comm, Nat.add_left_comm]
    rfl
  · simp only [ConLeche.Frontend.Olean.Region.ofParts, ConLeche.Frontend.Olean.partsOrdered, Bool.and_true, h]
    simp
    rfl

theorem absBytes_size' (s : alloc.vec.Vec Std.U8) :
    (absBytes (alloc.vec.Vec.deref s)).size = s.val.length := by
  rw [absBytes_size, deref_val]

theorem emptyCap_append (n : Nat) (x : ByteArray) : ByteArray.emptyWithCapacity n ++ x = x := by
  apply ByteArray.ext
  simp only [ByteArray.data_append]
  show #[] ++ x.data = x.data
  simp

/-- The bytes of two parts. -/
theorem join_bytes {x a b : alloc.vec.Vec Std.U8} (h : x.val = a.val ++ b.val) :
    absBytes (alloc.vec.Vec.deref x) = absBytes (alloc.vec.Vec.deref a) ++ absBytes (alloc.vec.Vec.deref b) :=
  absBytes_append (by simp only [deref_val]; exact h)

/-- **`region_of_parts2` is `Region.ofParts`**, at two files. -/
theorem region_of_parts2_eq {a b : frontend.olean.region.Part} {o} (ha : PartFits a) (hb : PartFits b)
    (h : region_of_parts2 a b = ok o) :
    match (generalizing := false) o with
    | .Ok buf => ConLeche.Frontend.Olean.Region.ofParts #[absPart a, absPart b] =
        .ok (absRegion (alloc.vec.Vec.deref buf.bytes) buf.region) ∧
        RegionFits (alloc.vec.Vec.deref buf.bytes) buf.region
    | .Err e => absAErrKind e = some .internal ∧
        ∃ m, ConLeche.Frontend.Olean.Region.ofParts #[absPart a, absPart b] = .error (.internal m) := by
  rw [region_of_parts2] at h
  peel h as ord, hord
  have eo := parts_ordered_eq ha hord
  rw [ofParts2, ← eo]
  by_cases ho : ord = true
  · rw [ite_eq_left ho] at h ⊢
    dsimp only at h
    peel h as i2, hi2
    peel h as p1, hp1
    obtain ⟨bytes, segs⟩ := p1
    peel h as p2, hp2
    obtain ⟨bytes1, segs1⟩ := p2
    cases Result.ok_injective h
    obtain ⟨v1, s1⟩ := region_push_eq hp1
    obtain ⟨v2, s2⟩ := region_push_eq hp2
    have hnew : (alloc.vec.Vec.with_capacity Std.U8 i2).val = [] := rfl
    have hnewS : (alloc.vec.Vec.with_capacity frontend.olean.region.Seg 2#usize).val = [] := rfl
    simp only [hnew, hnewS, List.nil_append] at v1 s1
    have hla := len_u64 a.bytes
    have hlb := len_u64 b.bytes
    have hl0 : (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len (alloc.vec.Vec.with_capacity Std.U8 i2))).val = 0 := by
      rw [len_u64, hnew]; rfl
    have hl1 : (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes)).val = a.bytes.val.length := by
      rw [len_u64, v1]
    have es : segs1.val = _ := s2
    rw [s1] at es
    have hA := ha.size
    have hB := hb.size
    refine ⟨?_, ?_⟩
    · simp only [emptyCap_append, (show ∀ n, (ByteArray.emptyWithCapacity n).size = 0 from fun _ => rfl),
        absPart, absBytes_size', absRegion, es, List.map_cons,
        List.map_nil, absSeg, hl0, hl1, hla, hlb, List.cons_append, List.nil_append]
      congr 2
      exact (join_bytes (x := bytes1) (a := a.bytes) (b := b.bytes)
        (by rw [show bytes1.val = _ from v2, v1])).symm
    · intro s hm
      rw [es] at hm
      have hxl : bytes1.val.length = a.bytes.val.length + b.bytes.val.length := by
        rw [v2, v1]; simp
      simp only [deref_val, hxl]
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · show (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len (alloc.vec.Vec.with_capacity Std.U8 i2))).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len a.bytes)).val ≤ _ ∧ (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len (alloc.vec.Vec.with_capacity Std.U8 i2))).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len a.bytes)).val < _
        omega
      · show (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes)).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b.bytes)).val ≤ _ ∧ (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes)).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b.bytes)).val < _
        omega
  · rw [ite_eq_right ho] at h ⊢
    peel h as s, -
    peel h as v, -
    peel h as ce, hce
    cases Result.ok_injective h
    rw [kernel.core_types.internal] at hce
    cases Result.ok_injective hce
    exact ⟨rfl, _, rfl⟩

/-- **`region_of_parts3` is `Region.ofParts`**, at all three files. -/
theorem region_of_parts3_eq {a b c : frontend.olean.region.Part} {o} (ha : PartFits a) (hb : PartFits b)
    (hc : PartFits c) (h : region_of_parts3 a b c = ok o) :
    match (generalizing := false) o with
    | .Ok buf => ConLeche.Frontend.Olean.Region.ofParts #[absPart a, absPart b, absPart c] =
        .ok (absRegion (alloc.vec.Vec.deref buf.bytes) buf.region) ∧
        RegionFits (alloc.vec.Vec.deref buf.bytes) buf.region
    | .Err e => absAErrKind e = some .internal ∧
        ∃ m, ConLeche.Frontend.Olean.Region.ofParts #[absPart a, absPart b, absPart c] = .error (.internal m) := by
  rw [region_of_parts3] at h
  peel h as ord, hord
  have eo := parts_ordered_eq ha hord
  rw [ofParts3, ← eo]
  by_cases ho : ord = true
  · rw [ite_eq_left ho] at h
    peel h as ord2, hord2
    have eo2 := parts_ordered_eq hb hord2
    rw [← eo2, ho, Bool.true_and]
    by_cases ho2 : ord2 = true
    · rw [ite_eq_left ho2] at h ⊢
      dsimp only at h
      peel h as i2, -
      peel h as i4, -
      peel h as p1, hp1
      obtain ⟨bytes, segs⟩ := p1
      peel h as p2, hp2
      obtain ⟨bytes1, segs1⟩ := p2
      peel h as p3, hp3
      obtain ⟨bytes2, segs2⟩ := p3
      cases Result.ok_injective h
      obtain ⟨v1, s1⟩ := region_push_eq hp1
      obtain ⟨v2, s2⟩ := region_push_eq hp2
      obtain ⟨v3, s3⟩ := region_push_eq hp3
      have hnew : (alloc.vec.Vec.with_capacity Std.U8 i4).val = [] := rfl
      have hnewS : (alloc.vec.Vec.with_capacity frontend.olean.region.Seg 3#usize).val = [] := rfl
      simp only [hnew, hnewS, List.nil_append] at v1 s1
      have hla := len_u64 a.bytes
      have hlb := len_u64 b.bytes
      have hlc := len_u64 c.bytes
      have hl0 : (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len (alloc.vec.Vec.with_capacity Std.U8 i4))).val = 0 := by
        rw [len_u64, hnew]; rfl
      have hl1 : (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes)).val = a.bytes.val.length := by
        rw [len_u64, v1]
      have vb1 : bytes1.val = a.bytes.val ++ b.bytes.val := by rw [show bytes1.val = _ from v2, v1]
      have hl2 : (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes1)).val = a.bytes.val.length + b.bytes.val.length := by
        rw [len_u64, vb1]; simp
      have vb2 : bytes2.val = bytes1.val ++ c.bytes.val := v3
      have es : segs2.val = _ := s3
      rw [show segs1.val = _ from s2, s1] at es
      have hA := ha.size
      have hB := hb.size
      have hC := hc.size
      refine ⟨?_, ?_⟩
      · simp only [emptyCap_append, (show ∀ n, (ByteArray.emptyWithCapacity n).size = 0 from fun _ => rfl),
        absPart, absBytes_size', absRegion, es, List.map_cons,
          List.map_nil, absSeg, hl0, hl1, hl2, hla, hlb, hlc, List.cons_append, List.nil_append,
          ByteArray.size_append]
        congr 2
        rw [← join_bytes (x := bytes1) (a := a.bytes) (b := b.bytes) vb1]
        exact (join_bytes (x := bytes2) (a := bytes1) (b := c.bytes) vb2).symm
      · intro s hm
        rw [es] at hm
        have hxl : bytes2.val.length = a.bytes.val.length + b.bytes.val.length + c.bytes.val.length := by
          rw [vb2, vb1]; simp; omega
        simp only [deref_val, hxl]
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · show (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len (alloc.vec.Vec.with_capacity Std.U8 i4))).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len a.bytes)).val ≤ _ ∧ (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len (alloc.vec.Vec.with_capacity Std.U8 i4))).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len a.bytes)).val < _
          omega
        · show (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes)).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b.bytes)).val ≤ _ ∧ (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes)).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len b.bytes)).val < _
          omega
        · show (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes1)).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len c.bytes)).val ≤ _ ∧ (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bytes1)).val + (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len c.bytes)).val < _
          omega
    · rw [ite_eq_right ho2] at h ⊢
      peel h as s, -
      peel h as v, -
      peel h as ce, hce
      cases Result.ok_injective h
      rw [kernel.core_types.internal] at hce
      cases Result.ok_injective hce
      exact ⟨rfl, _, rfl⟩
  · rw [ite_eq_right ho] at h
    rw [ite_eq_right (by simp [ho])]
    peel h as s, -
    peel h as v, -
    peel h as ce, hce
    cases Result.ok_injective h
    rw [kernel.core_types.internal] at hce
    cases Result.ok_injective hce
    exact ⟨rfl, _, rfl⟩

end ConRon.Refine2.Frontend.Olean
