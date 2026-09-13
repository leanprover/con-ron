/-
`kernel::pins_decode`'s records against `ConRon.Refine.PinsDec` — half (A) of
task #64's decoder refinement, the record layer.

One lemma per record function, in the file's order.  Each is forward reasoning
through `Refine/PinsBytes.lean`'s readers and then *one* smart-constructor
lemma from `Refine/{Name,Level,PropWhen,Expr}.lean`: the reader never writes a
cached datum itself, so the node the port installs abstracts to the node
`ConRon.Dump.Read.lean` installs, and nothing about hashes or packed words is
ever unfolded here.

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
    {b : β} (h : x >>= g = ok (.Ok b))
    (herr : ∀ e, g (.Err e) = ok (.Err e) := by intro e; rfl) :
    ∃ a, x = ok (.Ok a) ∧ g (.Ok a) = ok (.Ok b) := by
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => rw [herr] at h; simp at h
  | Ok a => exact ⟨a, hr, h⟩

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

theorem record_name_str_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_name_str t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordNameStr (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_name_str] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨pre, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨str, i4⟩, hr3, h⟩ := peel h
  obtain ⟨e4, b7, b8⟩ := read_string_refines hr3
  obtain ⟨i5, hr4, h⟩ := peel h
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordNameStr, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Name.mk_str_refines hnd, decString_absString]

theorem record_name_num_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_name_num t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordNameNum (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_name_num] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨pre, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨kk, i4⟩, hr3, h⟩ := peel h
  obtain ⟨e4, b7, b8⟩ := read_nat_refines hr3
  obtain ⟨i5, hr4, h⟩ := peel h
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordNameNum, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Name.mk_num_refines hnd]

theorem record_name_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_name t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordName (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_name] at h
  obtain ⟨i2, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := expect_id_refines hr
  obtain ⟨i3, hr1, h⟩ := peel h
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
    obtain ⟨i5, hr2, h⟩ := peel h
    obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
    obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
    obtain ⟨e3, b5, b6⟩ := record_name_num_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordName, hlen, e1, e2, hc]
    simp [e3]
  · obtain ⟨ce, -, h⟩ := bind_eq_ok_iff.mp h
    simp at h

/-! ## `L` — the level records -/

theorem record_level_succ_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_level_succ t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordLevelSucc (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_level_succ] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨u, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := level_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordLevelSucc, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Level.succ_refines hnd]

theorem record_level_binop_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} {isMax : Bool}
    (h : pins_decode.record_level_binop t i tb isMax = ok (.Ok (tb', j))) :
    PinsDec.recordLevelBinop (bytesFrom t i) (absTables tb) isMax
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_level_binop] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨u, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := level_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨v, i4⟩, hr3, h⟩ := peel h
  obtain ⟨e4, b7, b8⟩ := level_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ := peel h
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  cases isMax
  · obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordLevelBinop, e1, e2, e3, e4, e5, Bool.false_eq_true,
      if_false]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Level.imax_refines hnd]
  · obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordLevelBinop, e1, e2, e3, e4, e5, if_true]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Level.max_refines hnd]

theorem record_level_param_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_level_param t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordLevelParam (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_level_param] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨n, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordLevelParam, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Level.param_refines hnd]

theorem record_level_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_level t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordLevel (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_level] at h
  obtain ⟨i2, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := expect_id_refines hr
  obtain ⟨i3, hr1, h⟩ := peel h
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
    obtain ⟨i5, hr2, h⟩ := peel h
    obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
    obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
    obtain ⟨e3, b5, b6⟩ := record_level_param_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordLevel, hlen, e1, e2, hc]
    simp [e3]
  · obtain ⟨ce, -, h⟩ := bind_eq_ok_iff.mp h
    simp at h

/-! ## `prop_when::if_all_zero` without a well-formedness side condition

Everything above installs a node whose abstraction is read straight off the
node (`Refine/Abs.lean`'s `*_inv` lemmas), so nothing needs to know that the
children are well formed.  The `W` record is the exception: it installs
`prop_when::if_all_zero`, which *normalises* its argument with
`prop_when::name_cmp`, and `Refine/PropWhen.lean`'s `if_all_zero_shape`
therefore asks for `NamesWF ps` — its route to the port's comparison agreeing
with `ConLeche.Name.cmp` is `name_cmp_refines`, an induction on the `NameWF`
derivation.  The decoder cannot supply that: `Refine/PinsBytes.lean`'s
`name_list_refines` claims no `NamesWF`, and the `StrWF` a `NameWF.str` needs
would have to come out of `read_string_refines`, which claims only its
`PinsDec` equation.

So the record's equation is proved from a *weaker* fact, which needs no
hypothesis at all: canonicalisation neither invents nor loses a **member**,
and `ConLeche.PropWhen.ifAllZero` is determined by its member set
(`ConLeche.PropWhen.ifAllZero_eq_iff`).  The only step that can drop a name is
a `name_cmp = Eq` comparison, and `name_cmp_eq_abs` below says such a
comparison forces the two names to abstract to the same `ConLeche.Name`.

**Why no invariant is needed.**  `prop_when::name_cmp` never reads the stored
hash word, and it compares a `Str` payload as a raw `u32` list and a `Num`
payload as a raw `u64`.  So `name_cmp a b = Eq` forces `a` and `b` to have the
same kind tree and the same payloads — everything `absName` looks at — and
therefore `absName a = absName b`, whether or not either node was built by a
smart constructor and whatever the code points are.  That is strictly stronger
than what `if_all_zero_shape` gets from `name_cmp_refines`, which buys the
*full* agreement with `ConLeche.Name.cmp` and has to pay `NameWF` for it.

**Where this belongs.**  Everything from `nat_compare_eq` to `if_all_zero_abs`
is `prop_when` theory, not decoder theory; it is parked here only because
`Refine/PropWhen.lean` is outside this task's ownership and moving it would
invalidate most of the `Refine/` oleans.  It is owed to `Refine/PropWhen.lean`,
beside `if_all_zero_shape` — the conditional sibling that `if_all_zero_abs`
generalises — and DESIGN.md records the move as owed work.
-/

private theorem nat_compare_eq {m n : Std.U64}
    (h : prop_when.nat_compare m n = ok .Eq) : m.val = n.val := by
  rw [prop_when.nat_compare] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · scalar_tac

private theorem str_compare_from_eq {a b : alloc.vec.Vec Std.U32} :
    ∀ k (i : Std.Usize), a.length - i.val ≤ k →
      prop_when.str_compare_from a b i = ok .Eq →
      a.val.drop i.val = b.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i hk h
    rw [prop_when.str_compare_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
    rw [List.drop_eq_nil_of_le (show a.val.length ≤ i.val by scalar_tac)]
    by_cases hbl : i.val ≥ b.val.length
    · rw [List.drop_eq_nil_of_le (show b.val.length ≤ i.val by scalar_tac)]
    · exfalso
      rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
      rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      simp at h
  | succ k ih =>
    intro i hk h
    rw [prop_when.str_compare_from.eq_def] at h; simp only [] at h
    by_cases hal : i.val ≥ a.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      rw [List.drop_eq_nil_of_le (show a.val.length ≤ i.val by scalar_tac)]
      by_cases hbl : i.val ≥ b.val.length
      · rw [List.drop_eq_nil_of_le (show b.val.length ≤ i.val by scalar_tac)]
      · exfalso
        rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
        rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
        simp at h
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      have hai : i.val < a.val.length := by scalar_tac
      by_cases hbl : i.val ≥ b.val.length
      · exfalso
        rw [if_pos (show i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
        simp at h
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
        have hbi : i.val < b.val.length := by scalar_tac
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec a i hai)
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b i hbi)
        subst hyv; subst hzv
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz,
          Result.ok.injEq, exists_eq_left'] at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i hnlt hngt
            have heq : a.val[i.val] = b.val[i.val] := by scalar_tac
            have hmax : i.val + 1 ≤ Std.Usize.max := by
              have := a.slice.property; scalar_tac
            obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
            simp only [hw, bind_tc_ok] at h
            rw [List.drop_eq_getElem_cons hai, List.drop_eq_getElem_cons hbi, heq,
              ← hwv, ih w (by scalar_tac) h]

private theorem str_compare_eq {a b : alloc.vec.Vec Std.U32}
    (h : prop_when.str_compare a b = ok .Eq) : a.val = b.val := by
  rw [prop_when.str_compare] at h
  have := str_compare_from_eq a.length 0#usize (by scalar_tac) h
  simpa using this

private theorem name_cmp_eq_abs : ∀ (n : Nat) (a b : name.Name), sizeOf a ≤ n →
    prop_when.name_cmp a b = ok .Eq → absName a = absName b := by
  intro n
  induction n with
  | zero =>
    intro a b hs _
    exfalso
    obtain ⟨⟨ha, ka⟩⟩ := a
    simp at hs
  | succ n ih =>
    intro a b hs hc
    obtain ⟨⟨ha, ka⟩⟩ := a
    obtain ⟨⟨hb, kb⟩⟩ := b
    rw [prop_when.name_cmp.eq_def] at hc
    simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
      name.NameNode.kind._simpLemma_] at hc
    cases ka with
    | Anonymous =>
      cases kb with
      | Anonymous => simp [absName, absNameNode, absNameKind]
      | Str q t => simp at hc
      | Num q k => simp at hc
    | Str p s =>
      cases kb with
      | Anonymous => simp at hc
      | Num q k => simp at hc
      | Str q t =>
        simp only [bind_eq_ok_iff] at hc
        obtain ⟨o, ho, o1, ho1, hc⟩ := hc
        cases o with
        | Lt => simp [prop_when.ord_then] at hc
        | Gt => simp [prop_when.ord_then] at hc
        | Eq =>
          simp only [prop_when.ord_then, Result.ok.injEq] at hc
          subst hc
          have hp := ih p q (by simp at hs; omega) ho
          have hst := str_compare_eq ho1
          simp only [absName, absNameNode, absNameKind, hp, absString, hst]
    | Num p m =>
      cases kb with
      | Anonymous => simp at hc
      | Str q t => simp at hc
      | Num q k =>
        simp only [bind_eq_ok_iff] at hc
        obtain ⟨o, ho, o1, ho1, hc⟩ := hc
        cases o with
        | Lt => simp [prop_when.ord_then] at hc
        | Gt => simp [prop_when.ord_then] at hc
        | Eq =>
          simp only [prop_when.ord_then, Result.ok.injEq] at hc
          subst hc
          have hp := ih p q (by simp at hs; omega) ho
          have hst := nat_compare_eq ho1
          simp only [absName, absNameNode, absNameKind, hp, hst]

private theorem merge_from_mem {as_ bs : alloc.vec.Vec name.Name} :
    ∀ k : Nat, ∀ (i j : Std.Usize) (out v : alloc.vec.Vec name.Name),
      (as_.length - i.val) + (bs.length - j.val) ≤ k →
      prop_when.merge_from as_ i bs j out = ok v →
      ∀ x : ConLeche.Name, x ∈ absNames v ↔
        x ∈ absNames out ∨ x ∈ (as_.val.drop i.val).map absName ∨
        x ∈ (bs.val.drop j.val).map absName := by
  intro k
  induction k with
  | zero =>
    intro i j out v hk h x
    rw [prop_when.merge_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len as_ by scalar_tac)] at h
    have hv := PropWhen.append_from_val bs bs.length j out v (by scalar_tac) h
    rw [List.drop_eq_nil_of_le (show as_.val.length ≤ i.val by scalar_tac)]
    simp [absNames, hv]
  | succ k ih =>
    intro i j out v hk h x
    rw [prop_when.merge_from.eq_def] at h; simp only [] at h
    by_cases hal : i.val ≥ as_.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len as_ by scalar_tac)] at h
      have hv := PropWhen.append_from_val bs bs.length j out v (by scalar_tac) h
      rw [List.drop_eq_nil_of_le (show as_.val.length ≤ i.val by scalar_tac)]
      simp [absNames, hv]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len as_ by scalar_tac)] at h
      have hai : i.val < as_.val.length := by scalar_tac
      by_cases hbl : j.val ≥ bs.val.length
      · rw [if_pos (show j ≥ alloc.vec.Vec.len bs by scalar_tac)] at h
        have hv := PropWhen.append_from_val as_ as_.length i out v (by scalar_tac) h
        rw [List.drop_eq_nil_of_le (show bs.val.length ≤ j.val by scalar_tac)]
        simp [absNames, hv]
      · rw [if_neg (show ¬ j ≥ alloc.vec.Vec.len bs by scalar_tac)] at h
        have hbj : j.val < bs.val.length := by scalar_tac
        have hmaxi : i.val + 1 ≤ Std.Usize.max := by
          have := as_.slice.property; scalar_tac
        have hmaxj : j.val + 1 ≤ Std.Usize.max := by
          have := bs.slice.property; scalar_tac
        obtain ⟨wi, hwi, hwiv⟩ := usize_add_ok hmaxi
        obtain ⟨wj, hwj, hwjv⟩ := usize_add_ok hmaxj
        obtain ⟨y, hy, hyv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec as_ i hai)
        obtain ⟨z, hz, hzv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec bs j hbj)
        subst hyv; subst hzv
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz,
          Result.ok.injEq, exists_eq_left', name_dup_eq, hwi, hwj] at h
        obtain ⟨o, ho, h⟩ := h
        cases o with
        | Lt =>
          simp only [bind_eq_ok_iff, bind_tc_ok] at h
          obtain ⟨out1, hout1, h⟩ := h
          have hrec := ih wi j out1 v (by scalar_tac) h x
          rw [hwiv] at hrec
          rw [hrec, absNames, absNames, vec_push_val hout1,
            List.drop_eq_getElem_cons hai]
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false]
          tauto
        | Eq =>
          simp only [bind_eq_ok_iff, bind_tc_ok] at h
          obtain ⟨out1, hout1, h⟩ := h
          have habs :=
            name_cmp_eq_abs (sizeOf as_.val[i.val]) as_.val[i.val] bs.val[j.val]
              le_rfl ho
          have hrec := ih wi wj out1 v (by scalar_tac) h x
          rw [hwiv, hwjv] at hrec
          rw [hrec, absNames, absNames, vec_push_val hout1,
            List.drop_eq_getElem_cons hai, List.drop_eq_getElem_cons hbj]
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, habs]
          tauto
        | Gt =>
          simp only [bind_eq_ok_iff, bind_tc_ok] at h
          obtain ⟨out1, hout1, h⟩ := h
          have hrec := ih i wj out1 v (by scalar_tac) h x
          rw [hwjv] at hrec
          rw [hrec, absNames, absNames, vec_push_val hout1,
            List.drop_eq_getElem_cons hbj]
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false]
          tauto

private theorem merge_mem {as_ bs v : alloc.vec.Vec name.Name}
    (h : prop_when.merge as_ bs = ok v) :
    ∀ x : ConLeche.Name, x ∈ absNames v ↔ x ∈ absNames as_ ∨ x ∈ absNames bs := by
  rw [prop_when.merge] at h
  intro x
  have hm := merge_from_mem (as_.length + bs.length) 0#usize 0#usize _ v
    (by scalar_tac) h x
  simpa [absNames, alloc.vec.Vec.new,
    show (0#usize : Std.Usize).val = 0 from rfl] using hm

private theorem canon_from_mem {ps : alloc.vec.Vec name.Name} :
    ∀ k : Nat, ∀ (i : Std.Usize) (v : alloc.vec.Vec name.Name),
      ps.length - i.val ≤ k → prop_when.canon_from ps i = ok v →
      ∀ x : ConLeche.Name, x ∈ absNames v ↔ x ∈ (ps.val.drop i.val).map absName := by
  intro k
  induction k with
  | zero =>
    intro i v hk h x
    rw [prop_when.canon_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
    simp only [Result.ok.injEq] at h; subst h
    rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
    simp [absNames, alloc.vec.Vec.new]
  | succ k ih =>
    intro i v hk h x
    rw [prop_when.canon_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ ps.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      simp only [Result.ok.injEq] at h; subst h
      rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
      simp [absNames, alloc.vec.Vec.new]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hi : i.val < ps.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hi)
      subst hyv
      simp only [hw, bind_tc_ok, bind_eq_ok_iff, alloc.vec.Vec.index_slice_index,
        hy] at h
      obtain ⟨rest, hrest, sg, hsg, h⟩ := h
      have hrec := ih w rest (by scalar_tac) hrest x
      rw [hwv] at hrec
      have hsgv := Name.singleton_refines hsg
      rw [merge_mem h x, hsgv, hrec, List.drop_eq_getElem_cons hi]
      simp only [List.map_cons, List.mem_cons, List.not_mem_nil, or_false]

private theorem canon_mem {ps v : alloc.vec.Vec name.Name}
    (h : prop_when.canon ps = ok v) :
    ∀ x : ConLeche.Name, x ∈ absNames v ↔ x ∈ absNames ps := by
  rw [prop_when.canon] at h
  intro x
  have hm := canon_from_mem ps.length 0#usize v (by scalar_tac) h x
  simpa [absNames, show (0#usize : Std.Usize).val = 0 from rfl] using hm

/-- **`prop_when::if_all_zero` refines `PropWhen.ifAllZero`, with no
well-formedness side condition** — the unconditional form of
`Refine/PropWhen.lean`'s `if_all_zero_shape`.  The `0`- and `1`-element cases
install the argument verbatim; `two_prime`'s `Eq` arm and `canon`'s dedup are
the only places a name is dropped, and both drop one whose abstraction is
already there (`name_cmp_eq_abs`), so the member set — all `ifAllZero` reads
(`ConLeche.PropWhen.ifAllZero_eq_iff`) — is unchanged. -/
private theorem if_all_zero_abs {ps : alloc.vec.Vec name.Name}
    {pw : prop_when.PropWhen} (h : prop_when.if_all_zero ps = ok pw) :
    absPropWhen pw = .ifAllZero (absNames ps) := by
  rw [prop_when.if_all_zero.eq_def] at h; simp only [] at h
  by_cases h0 : ps.val.length = 0
  · rw [if_pos (show alloc.vec.Vec.len ps = 0#usize by scalar_tac),
      PropWhen.of_repr_eq, Result.ok.injEq] at h
    subst h
    have hnil : ps.val = [] := List.eq_nil_iff_length_eq_zero.mpr h0
    simp [absPropWhen, absPropWhenRepr, absNames, hnil]
  · rw [if_neg (show ¬ alloc.vec.Vec.len ps = 0#usize by scalar_tac)] at h
    by_cases h1 : ps.val.length = 1
    · rw [if_pos (show alloc.vec.Vec.len ps = 1#usize by scalar_tac)] at h
      obtain ⟨x, hx⟩ := PropWhen.list_len_one h1
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec ps 0#usize (by scalar_tac))
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, name_dup_eq,
        PropWhen.of_repr_eq, Result.ok.injEq, exists_eq_left'] at h
      subst h
      have hyx : y = x := by rw [hyv]; simp [hx]
      subst hyx
      simp [absPropWhen, absPropWhenRepr, absNames, hx]
    · rw [if_neg (show ¬ alloc.vec.Vec.len ps = 1#usize by scalar_tac)] at h
      by_cases h2 : ps.val.length = 2
      · rw [if_pos (show alloc.vec.Vec.len ps = 2#usize by scalar_tac)] at h
        obtain ⟨x, x', hx⟩ := PropWhen.list_len_two h2
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec ps 0#usize (by scalar_tac))
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec ps 1#usize (by scalar_tac))
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz,
          Result.ok.injEq, exists_eq_left'] at h
        have hyx : y = x := by rw [hyv]; simp [hx]
        have hzx : z = x' := by rw [hzv]; simp [hx]
        subst hyx; subst hzx
        rw [prop_when.two_prime] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨o, ho, h⟩ := h
        rw [absNames, hx]
        cases o with
        | Lt =>
          simp only [name_dup_eq, bind_tc_ok, PropWhen.of_repr_eq,
            Result.ok.injEq] at h
          subst h
          simp [absPropWhen, absPropWhenRepr]
        | Eq =>
          simp only [name_dup_eq, bind_tc_ok, PropWhen.of_repr_eq,
            Result.ok.injEq] at h
          subst h
          have habs := name_cmp_eq_abs (sizeOf y) y z le_rfl ho
          simp only [absPropWhen, absPropWhenRepr, List.map_cons, List.map_nil]
          refine (ConLeche.PropWhen.ifAllZero_eq_iff _ _).mpr ?_
          intro n; simp [habs]
        | Gt =>
          simp only [name_dup_eq, bind_tc_ok, PropWhen.of_repr_eq,
            Result.ok.injEq] at h
          subst h
          simp only [absPropWhen, absPropWhenRepr, List.map_cons, List.map_nil]
          refine (ConLeche.PropWhen.ifAllZero_eq_iff _ _).mpr ?_
          intro n; simp; tauto
      · rw [if_neg (show ¬ alloc.vec.Vec.len ps = 2#usize by scalar_tac)] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨v, hv, h⟩ := h
        rw [PropWhen.of_sorted_abs h]
        exact (ConLeche.PropWhen.ifAllZero_eq_iff _ _).mpr (canon_mem hv)

/-! ## `W` — the prop-when records -/

theorem record_pw_zero_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_pw_zero t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordPwZero (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_pw_zero] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨ns, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := name_list_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordPwZero, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, if_all_zero_abs hnd]

theorem record_pw_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_pw t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordPw (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_pw] at h
  obtain ⟨i2, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := expect_id_refines hr
  obtain ⟨i3, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := after_space_refines hr1
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  have hkv := byte_at_refines hk
  have hlen : (absTables tb).pws.length = (alloc.vec.Vec.len tb.pws).val := by
    simp [absTables]
  split at h
  · -- `n`: never
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 110 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    obtain ⟨i5, hr2, h⟩ := peel h
    obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
    obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordPw, hlen, e1, e2, hc, reduceIte, e3]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, PropWhen.absPropWhen_never (PropWhen.never_shape hnd).2]
  split at h
  · -- `z`: `ifAllZero` of a name list
    rename_i hkb
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v := step_val hi4
    have hc : bytesFrom t i3 = 122 :: bytesFrom t i4 :=
      bytesFrom_cons_val (by rw [← hkv, hkb]; rfl) (by omega) hi4v
    obtain ⟨e3, b5, b6⟩ := record_pw_zero_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordPw, hlen, e1, e2, hc]
    simp [e3]
  · obtain ⟨ce, -, h⟩ := bind_eq_ok_iff.mp h
    simp at h

/-! ## `E` — the expression records -/

theorem record_expr_bvar_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr_bvar t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExprBvar (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_bvar] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨kk, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := read_nat_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprBvar, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.bvar_refines hnd]

theorem record_expr_fvar_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr_fvar t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExprFvar (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_fvar] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨idx, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := read_nat_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨ty, i4⟩, hr3, h⟩ := peel h
  obtain ⟨e4, b7, b8⟩ := expr_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ := peel h
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprFvar, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.fvar_refines hnd]

theorem record_expr_sort_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr_sort t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExprSort (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_sort] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨ha, ha1, ha2⟩ := after_space_refines hr
  obtain ⟨⟨u, i2⟩, hr1, h⟩ := peel h
  obtain ⟨hb, hb1, hb2⟩ := level_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨hc, hc1, hc2⟩ := after_newline_refines hr2
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprSort, ha, hb, hc]
  simp only [absTables, vec_push_val hv, List.map_append, List.map_cons,
    List.map_nil, Expr.sort_refines he]

theorem record_expr_const_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr_const t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExprConst (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_const] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨n, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨us, i4⟩, hr3, h⟩ := peel h
  obtain ⟨e4, b7, b8⟩ := level_list_refines hr3
  obtain ⟨i5, hr4, h⟩ := peel h
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprConst, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.mk_const_refines hnd]

theorem record_expr_app_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr_app t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExprApp (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_app] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨f, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := expr_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨a, i4⟩, hr3, h⟩ := peel h
  obtain ⟨e4, b7, b8⟩ := expr_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ := peel h
  obtain ⟨e5, b9, b10⟩ := after_newline_refines hr4
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprApp, e1, e2, e3, e4, e5]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.app_refines hnd]

theorem record_expr_binder_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} {isLam : Bool}
    (h : pins_decode.record_expr_binder t i tb isLam = ok (.Ok (tb', j))) :
    PinsDec.recordExprBinder (bytesFrom t i) (absTables tb) isLam
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_binder] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨ty, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := expr_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨body, i4⟩, hr3, h⟩ := peel h
  obtain ⟨e4, b7, b8⟩ := expr_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ := peel h
  obtain ⟨e5, b9, b10⟩ := after_space_refines hr4
  obtain ⟨⟨pw, i6⟩, hr5, h⟩ := peel h
  obtain ⟨e6, b11, b12⟩ := pw_ref_refines hr5
  obtain ⟨i7, hr6, h⟩ := peel h
  obtain ⟨e7, b13, b14⟩ := after_newline_refines hr6
  obtain ⟨m, hm, h⟩ := bind_eq_ok_iff.mp h
  simp only [expr.binder_meta, ptr_new_eq, bind_tc_ok, Result.ok.injEq] at hm
  subst hm
  cases isLam
  · obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExprBinder, e1, e2, e3, e4, e5, e6, e7,
      Bool.false_eq_true, if_false]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Expr.forall_e_refines hnd, absBinderMeta]
  · obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExprBinder, e1, e2, e3, e4, e5, e6, e7, if_true]
    simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
      List.map_nil, Expr.lam_refines hnd, absBinderMeta]

theorem record_expr_let_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr_let t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExprLet (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_let] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨ty, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := expr_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨va, i4⟩, hr3, h⟩ := peel h
  obtain ⟨e4, b7, b8⟩ := expr_ref_refines hr3
  obtain ⟨i5, hr4, h⟩ := peel h
  obtain ⟨e5, b9, b10⟩ := after_space_refines hr4
  obtain ⟨⟨body, i6⟩, hr5, h⟩ := peel h
  obtain ⟨e6, b11, b12⟩ := expr_ref_refines hr5
  obtain ⟨i7, hr6, h⟩ := peel h
  obtain ⟨e7, b13, b14⟩ := after_newline_refines hr6
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprLet, e1, e2, e3, e4, e5, e6, e7]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.let_e_refines hnd]

theorem record_expr_nat_lit_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr_nat_lit t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExprNatLit (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_nat_lit] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨n, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := read_big_nat_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨lit, hlit, h⟩ := bind_eq_ok_iff.mp h
  simp only [expr.literal_nat, ptr_new_eq, bind_tc_ok, Result.ok.injEq] at hlit
  subst hlit
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprNatLit, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.lit_refines hnd, absLiteral]

theorem record_expr_str_lit_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr_str_lit t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExprStrLit (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_str_lit] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨str, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := read_string_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_newline_refines hr2
  obtain ⟨lit, hlit, h⟩ := bind_eq_ok_iff.mp h
  simp only [expr.literal_str, ptr_new_eq, bind_tc_ok, Result.ok.injEq] at hlit
  subst hlit
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprStrLit, e1, e2, e3]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.lit_refines hnd, absLiteral, decString_absString]

theorem record_expr_proj_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr_proj t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExprProj (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr_proj] at h
  obtain ⟨i1, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := after_space_refines hr
  obtain ⟨⟨sn, i2⟩, hr1, h⟩ := peel h
  obtain ⟨e2, b3, b4⟩ := name_ref_refines hr1
  obtain ⟨i3, hr2, h⟩ := peel h
  obtain ⟨e3, b5, b6⟩ := after_space_refines hr2
  obtain ⟨⟨idx, i4⟩, hr3, h⟩ := peel h
  obtain ⟨e4, b7, b8⟩ := read_nat_refines hr3
  obtain ⟨i5, hr4, h⟩ := peel h
  obtain ⟨e5, b9, b10⟩ := after_space_refines hr4
  obtain ⟨⟨st, i6⟩, hr5, h⟩ := peel h
  obtain ⟨e6, b11, b12⟩ := expr_ref_refines hr5
  obtain ⟨i7, hr6, h⟩ := peel h
  obtain ⟨e7, b13, b14⟩ := after_newline_refines hr6
  obtain ⟨nd, hnd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by omega, by omega⟩
  simp only [PinsDec.recordExprProj, e1, e2, e3, e4, e5, e6, e7]
  simp only [absTables, vec_push_val hw, List.map_append, List.map_cons,
    List.map_nil, Expr.proj_refines hnd]

set_option maxHeartbeats 1000000 in
theorem record_expr_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_expr t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordExpr (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_expr] at h
  obtain ⟨i2, hr, h⟩ := peel h
  obtain ⟨e1, b1, b2⟩ := expect_id_refines hr
  obtain ⟨i3, hr1, h⟩ := peel h
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
    obtain ⟨e3, b5, b6⟩ := record_expr_proj_refines h
    refine ⟨?_, by omega, by omega⟩
    simp only [PinsDec.recordExpr, hlen, e1, e2, hc]
    simp [e3]
  · obtain ⟨ce, -, h⟩ := bind_eq_ok_iff.mp h
    simp at h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing of this file's own, and nothing from the layer below: the record
lemmas are `ok`-driven by `Refine/PinsBytes.lean`'s readers and close with the
smart-constructor lemmas of `Refine/{Name,Level,PropWhen,Expr}.lean`, all of
which census at con-leche's own three.  `record_expr_refines` is the widest
dispatch and `record_pw_zero_refines` the one record that normalises, so they
are the two worth pinning. -/

/-- info: 'ConRon.Refine.PinsRecords.record_expr_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms record_expr_refines

/-- info: 'ConRon.Refine.PinsRecords.record_pw_zero_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms record_pw_zero_refines

/-- info: 'ConRon.Refine.PinsRecords.record_name_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms record_name_refines

end ConRon.Refine.PinsRecords
