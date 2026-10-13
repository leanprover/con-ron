/-
`kernel::pins_decode`'s records against `ConRon.Refine.PinsDec` — half (A) of
task #64's decoder refinement, the record layer.

One lemma per record function, in the file's order.  Each is forward reasoning
through `Refine/PinsBytes.lean`'s readers and then *one* smart-constructor
lemma from `Refine/{Name,Level,Expr}.lean`: the reader never writes a
cached datum itself, so the node the port installs abstracts to the node
`ConRon/Dump/Pins.lean` installs, and nothing about hashes or packed words is
ever unfolded here.

Every lemma is stated over the model's **whole** outcome (task #67), and its
`.Err` branch claims *nothing*: `absErrKind ce = none`.  `kernel::pins_decode`
is the one module whose errors are wholly the port's own — con-leche has no
decoder to mirror (`natOpPinSets` is elaboration-time data there), so all
twenty-eight throws go through `pins_decode::bad_text`, which builds a
`CheckError::Native`.  `Refine/PinsBytes.lean`'s module note and its
`bad_text_native`/`err_native` are where that is pinned down; here the failure
branch is always either a reader's own `.Err` branch (carried by `peel`) or
that one `bad_text` arm.

`Refine/PinsRun.lean` is the layer above (the payload record and the pass).
-/
import ConRon.Refine.PinsBytes

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.PinsRecords

open ConRon.Refine ConRon.Refine.PinsDec ConRon.Refine.PinsBytes

/-! ## Peeling one reader off a record

Every record function is a `bind` of a reader followed by a `match` that
returns on the `Err` arm, so the whole file is this one step, repeated. -/

private theorem peel {α β : Type}
    {x : Result (core.result.Result α core_types.CheckError)}
    {g : core.result.Result α core_types.CheckError →
      Result (core.result.Result β core_types.CheckError)}
    {o : core.result.Result β core_types.CheckError} (h : Std.bind x g = ok o)
    (herr : ∀ e, g (.Err e) = ok (.Err e) := by intro e; rfl) :
    (∃ a, x = ok (.Ok a) ∧ g (.Ok a) = ok o)
      ∨ (∃ e, x = ok (.Err e) ∧ o = .Err e) := by
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e =>
    rw [herr] at h
    simp only [Result.ok.injEq] at h
    exact Or.inr ⟨e, hr, h.symm⟩
  | Ok a => exact Or.inl ⟨a, hr, h⟩

/-- The suffix at an index whose byte is known, split into that byte and the
rest: `PinsDec`'s dispatch matches `k :: r` where the model reads `byte_at t i`
and then recurses at `i + 1`.  The `256` sentinel is what rules out the end of
the slice — every arm the model takes has read a real byte. -/
private theorem bytesFrom_cons_val {t : Slice Std.U8} {i i' : Std.Usize} {b : Nat}
    (hb : PinsDec.byteAt (bytesFrom t i) = b) (hb256 : b ≠ 256)
    (hi' : i'.val = i.val + 1) :
    bytesFrom t i = b :: bytesFrom t i' := by
  have hlen : i.val < (bytesOf t).length := by
    by_contra hc
    rw [bytesFrom, List.drop_eq_nil_of_le (by omega)] at hb
    exact hb256 hb.symm
  rw [bytesFrom, List.drop_eq_getElem_cons hlen] at hb
  rw [bytesFrom, List.drop_eq_getElem_cons hlen, bytesFrom, hi']
  simp only [PinsDec.byteAt] at hb
  rw [hb]

/-- `i + 1` in the model, as a value equation: the dispatch's `i3 + 1#usize`. -/
private theorem step_val {i i' : Std.Usize} (h : i + 1#usize = ok i') :
    i'.val = i.val + 1 := by
  have he := Std.UScalar.add_equiv i 1#usize
  rw [h] at he
  simpa using he.2.1

/-! ## `N` — the name records -/

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_name_str_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_name_str t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordNameStr (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_name_str] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨pre, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact name_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨str, i4⟩, hr3, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact read_string_refines hce
  obtain ⟨e4, b7, b8⟩ := read_string_refines hr3
  obtain ⟨i5, hr4, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordNameStr, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Name.mk_str_refines hnd, decString_absString]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_name_num_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_name_num t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordNameNum (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_name_num] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨pre, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact name_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨kk, i4⟩, hr3, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact read_nat_refines hce
  obtain ⟨e4, b7, b8⟩ := read_nat_refines hr3
  obtain ⟨i5, hr4, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordNameNum, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Name.mk_num_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_name_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_name t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordName (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_name] at h
  obtain ⟨i2, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expect_id_refines hce
  obtain ⟨e1, b1, b2⟩ := expect_id_refines hr
  obtain ⟨i3, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e2, b3, b4⟩ := after_space_refines hr1
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  have hkv := byte_at_refines hk
  have hlen : (absTables tb).names.length = (alloc.vec.Vec.len tb.names).val := by
    simp [absTables]
  split at h
  · -- `a`: the anonymous name
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 97 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    obtain ⟨i5, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
    case inr => exact after_newline_refines hce
    obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
    obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordName, hlen, e1, e2, hc, reduceIte, e3]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Name.anonymous_refines hnd]
  split at h
  · -- `s`: a string component
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 115 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_name_str_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_name_str_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordName, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `n`: a numeric component
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 110 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_name_num_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_name_num_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordName, hlen, e1, e2, hc]
    simp [e3]
  · obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce

/-! ## `L` — the level records -/

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_level_succ_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_level_succ t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordLevelSucc (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_level_succ] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨u, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact level_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := level_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordLevelSucc, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Level.succ_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_level_binop_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables} {isMax : Bool}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_level_binop t i tb isMax = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordLevelBinop (bytesFrom t i) (absTables tb) isMax
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_level_binop] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨u, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact level_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := level_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨v, i4⟩, hr3, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact level_ref_refines hce
  obtain ⟨e4, b7, b8⟩ := level_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  cases isMax
  · obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordLevelBinop, e1, e2, e3, e4, e5, Bool.false_eq_true,
      ite_false]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Level.imax_refines hnd]
  · obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordLevelBinop, e1, e2, e3, e4, e5, ite_true]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Level.max_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_level_param_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_level_param t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordLevelParam (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_level_param] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨n, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact name_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordLevelParam, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Level.param_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_level_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_level t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordLevel (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_level] at h
  obtain ⟨i2, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expect_id_refines hce
  obtain ⟨e1, b1, b2⟩ := expect_id_refines hr
  obtain ⟨i3, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e2, b3, b4⟩ := after_space_refines hr1
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  have hkv := byte_at_refines hk
  have hlen : (absTables tb).levels.length = (alloc.vec.Vec.len tb.levels).val := by
    simp [absTables]
  split at h
  · -- `z`: zero
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 122 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    obtain ⟨i5, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
    case inr => exact after_newline_refines hce
    obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
    obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordLevel, hlen, e1, e2, hc, reduceIte, e3]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Level.zero_refines hnd]
  split at h
  · -- `s`: succ
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 115 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_level_succ_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_level_succ_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordLevel, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `m`: max
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 109 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_level_binop_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_level_binop_refines h
    rw [hkb] at e3
    simp only [PinsDec.recordLevel, hlen, e1, e2, hc]
    refine ⟨?_, by omega, by omega⟩
    simp at e3 ⊢
    exact e3
  split at h
  · -- `i`: imax
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 105 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_level_binop_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_level_binop_refines h
    rw [hkb] at e3
    simp only [PinsDec.recordLevel, hlen, e1, e2, hc]
    refine ⟨?_, by omega, by omega⟩
    simp at e3 ⊢
    exact e3
  split at h
  · -- `p`: a parameter
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 112 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_level_param_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_level_param_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordLevel, hlen, e1, e2, hc]
    simp [e3]
  · obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce

/-! ## `E` — the expression records -/

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_bvar_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_bvar t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprBvar (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_bvar] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨kk, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact read_nat_refines hce
  obtain ⟨e2, b3, b4⟩ := read_nat_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprBvar, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.bvar_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_fvar_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_fvar t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprFvar (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_fvar] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨idx, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact read_nat_refines hce
  obtain ⟨e2, b3, b4⟩ := read_nat_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨ty, i4⟩, hr3, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expr_ref_refines hce
  obtain ⟨e4, b7, b8⟩ := expr_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprFvar, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.fvar_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_sort_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_sort t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprSort (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_sort] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨ha, ha1, ha2⟩ := after_space_refines hr
  obtain ⟨⟨u, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact level_ref_refines hce
  obtain ⟨hb, hb1, hb2⟩ := level_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨hc, hc1, hc2⟩ := after_newline_refines hr2
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprSort, ha, hb, hc]
  simp only [absTables, vec_push_val hv, List.map_append, List.map_cons,
    List.map_nil, Expr.sort_refines he]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_const_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_const t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprConst (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_const] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨n, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact name_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨us, i4⟩, hr3, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact level_list_refines hce
  obtain ⟨e4, b7, b8⟩ := level_list_refines hr3
  obtain ⟨i5, hr4, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprConst, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.mk_const_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_app_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_app t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprApp (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_app] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨f, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expr_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := expr_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨a, i4⟩, hr3, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expr_ref_refines hce
  obtain ⟨e4, b7, b8⟩ := expr_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprApp, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.app_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_binder_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables} {isLam : Bool}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_binder t i tb isLam = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprBinder (bytesFrom t i) (absTables tb) isLam
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_binder] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨ty, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expr_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := expr_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨body, i4⟩, hr3, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expr_ref_refines hce
  obtain ⟨e4, b7, b8⟩ := expr_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  cases isLam
  · obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExprBinder, e1, e2, e3, e4, e5,
      Bool.false_eq_true, ite_false]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Expr.forall_e_refines hnd]
  · obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExprBinder, e1, e2, e3, e4, e5, ite_true]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Expr.lam_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_let_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_let t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprLet (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_let] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨ty, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expr_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := expr_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨va, i4⟩, hr3, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expr_ref_refines hce
  obtain ⟨e4, b7, b8⟩ := expr_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e5, b9, b10⟩ := after_space_refines hr4
  obtain ⟨⟨body, i6⟩, hr5, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expr_ref_refines hce
  obtain ⟨e6, b11, b12⟩ := expr_ref_refines hr5
  obtain ⟨i7, hr6, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e7, b13, b14⟩ := after_newline_refines hr6
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprLet, e1, e2, e3, e4, e5, e6, e7]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.let_e_refines hnd]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_nat_lit_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_nat_lit t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprNatLit (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_nat_lit] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨n, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact read_big_nat_refines hce
  obtain ⟨e2, b3, b4⟩ := read_big_nat_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨lit, hlit, h⟩ := bind_eq_ok_iff.mp h
  simp only [expr.literal_nat, ptr_new_eq, bind_ok, Result.ok.injEq] at hlit
  subst hlit
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprNatLit, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.lit_refines hnd, absLiteral]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_str_lit_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_str_lit t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprStrLit (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_str_lit] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨str, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact read_string_refines hce
  obtain ⟨e2, b3, b4⟩ := read_string_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨lit, hlit, h⟩ := bind_eq_ok_iff.mp h
  simp only [expr.literal_str, ptr_new_eq, bind_ok, Result.ok.injEq] at hlit
  subst hlit
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprStrLit, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.lit_refines hnd, absLiteral, decString_absString]

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_proj_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr_proj t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExprProj (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr_proj] at h
  obtain ⟨i1, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨sn, i2⟩, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact name_ref_refines hce
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨idx, i4⟩, hr3, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact read_nat_refines hce
  obtain ⟨e4, b7, b8⟩ := read_nat_refines hr3
  obtain ⟨i5, hr4, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e5, b9, b10⟩ := after_space_refines hr4
  obtain ⟨⟨st, i6⟩, hr5, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expr_ref_refines hce
  obtain ⟨e6, b11, b12⟩ := expr_ref_refines hr5
  obtain ⟨i7, hr6, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_newline_refines hce
  obtain ⟨e7, b13, b14⟩ := after_newline_refines hr6
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  subst h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprProj, e1, e2, e3, e4, e5, e6, e7]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.proj_refines hnd]

set_option maxHeartbeats 1000000 in
/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed: con-leche has no decoder
to mirror, so every failure here is `bad_text` — see the module note. -/
theorem record_expr_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_expr t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordExpr (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_expr] at h
  obtain ⟨i2, hr, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact expect_id_refines hce
  obtain ⟨e1, b1, b2⟩ := expect_id_refines hr
  obtain ⟨i3, hr1, h⟩ | ⟨ce, hce, rfl⟩ := peel h
  case inr => exact after_space_refines hce
  obtain ⟨e2, b3, b4⟩ := after_space_refines hr1
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  have hkv := byte_at_refines hk
  have hlen : (absTables tb).exprs.length = (alloc.vec.Vec.len tb.exprs).val := by
    simp [absTables]
  split at h
  · -- `b`: a bound variable
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 98 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_bvar_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_bvar_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `v`: a free variable
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 118 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_fvar_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_fvar_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `s`: a sort
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 115 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_sort_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_sort_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `c`: a constant
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 99 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_const_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_const_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `a`: an application
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 97 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_app_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_app_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `l`: a lambda
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 108 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_binder_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_binder_refines h
    rw [hkb] at e3
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    refine ⟨?_, by omega, by omega⟩
    simp at e3 ⊢
    exact e3
  split at h
  · -- `f`: a pi
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 102 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_binder_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_binder_refines h
    rw [hkb] at e3
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    refine ⟨?_, by omega, by omega⟩
    simp at e3 ⊢
    exact e3
  split at h
  · -- `t`: a `let`
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 116 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_let_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_let_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `n`: a natural literal
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 110 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_nat_lit_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_nat_lit_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `g`: a string literal
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 103 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_str_lit_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_str_lit_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  split at h
  · -- `p`: a projection
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 112 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    cases o with
    | Err ce => exact record_expr_proj_refines h
    | Ok pr =>
    obtain ⟨tb', j⟩ := pr
    obtain ⟨e3, b5, b6⟩ := record_expr_proj_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  · obtain ⟨ce, rfl, hce⟩ := err_native h
    exact hce

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing of this file's own, and nothing from the layer below: the record
lemmas are `ok`-driven by `Refine/PinsBytes.lean`'s readers and close with the
smart-constructor lemmas of `Refine/{Name,Level,Expr}.lean`, all of
which census at con-leche's own three.  `record_expr_refines` is the widest
dispatch, so it is the one worth pinning, with the name record. -/

/-- info: 'ConRon.Refine.PinsRecords.record_expr_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms record_expr_refines

/-- info: 'ConRon.Refine.PinsRecords.record_name_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms record_name_refines

end ConRon.Refine.PinsRecords
