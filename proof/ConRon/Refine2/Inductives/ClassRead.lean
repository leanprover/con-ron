/-
# `ConRon.Refine2.Inductives.ClassRead` — Theorem 2 for `arena::inductives::class_read`

**Task #105** (DESIGN.md §8.2, Theorem 2).  `crates/con-ron-core/src/arena/inductives/class_read.rs`
(and `gen_rec.rs`'s `class_n_pc_of`) against
`proof/ConRon/Arena/Inductives/ClassRead.lean`: the generated recursor stage's
pre-pass.

## Shapes

* The record copies (`class_key_dup`, `class_slot_dup`, `pairs_dup`,
  `slots_dup`) are identities (`LSP … (· = ·)`).
* The pure cursor walks (`classes`, `motive_positions`, `u64_find_idx`) are
  the twin's list operations from the cursor on, the pushing accumulator in
  front; `motive_positions` is the `(List.range n).filter …` the twin spells
  inline in `ClassRead.motiveSlot` and `classRead` (`motPosOf` here, equal to
  the twin's spelling by `rfl`).
* `class_read_ih` is the body of `classReadMinor`'s `fvs.filterMapM fun x => …`
  (`classReadIh` here, `classReadMinor_eq` the `rfl` equation), and
  `class_read_ihs` is that `filterMapM`'s own `loop`, whose reversed
  accumulator is the Rust's pushed `out`.
* `class_read_slots` counts a `u64` down against the twin's `Nat` pattern
  (induction on the count), `class_read_rec_cls` walks a cursor against the
  twin's structural recursion, both with the accumulator in front of the
  twin's answer.
-/
import ConRon.Refine2.Inductives.Positivity
import ConRon.Refine2.Inductives.Prims
import ConRon.Arena.Inductives.ClassRead

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

/-! ## The record copies (identities) -/

@[lockstep] theorem class_key_dup_spec (k : arena.inductives.class_read.ClassKey) :
    LSP (arena.inductives.class_read.class_key_dup k) (fun o => o = k) := by
  intro o h
  rw [arena.inductives.class_read.class_key_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_nidx _ _ hn, dupId_lsidx _ _ hl, alloc.vec.Vec.ext _ _ (eidx_vec_dup_val hv)]

@[lockstep] theorem pairs_dup_spec (xs : alloc.vec.Vec (Std.U64 × Std.U64)) :
    LSP (arena.inductives.class_read.pairs_dup xs 0#usize (alloc.vec.Vec.new _))
      (fun o => o = xs) := by
  refine vec_copy_id xs (arena.inductives.class_read.pairs_dup xs) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.class_read.pairs_dup.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.class_read.pairs_dup.eq_def, if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, h⟩

@[lockstep] theorem class_slot_dup_spec (s : arena.inductives.class_read.ClassSlot) :
    LSP (arena.inductives.class_read.class_slot_dup s) (fun o => o = s) := by
  intro o h
  cases s with
  | Motive k =>
    rw [arena.inductives.class_read.class_slot_dup] at h
    obtain ⟨k1, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    rw [class_key_dup_spec _ _ hk]
  | Minor c n ihs =>
    rw [arena.inductives.class_read.class_slot_dup] at h
    obtain ⟨n1, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    rw [dupId_nidx _ _ hn, pairs_dup_spec _ _ hv]

@[lockstep] theorem slots_dup_spec (xs : alloc.vec.Vec arena.inductives.class_read.ClassSlot) :
    LSP (arena.inductives.class_read.slots_dup xs 0#usize (alloc.vec.Vec.new _))
      (fun o => o = xs) := by
  refine vec_copy_id xs (arena.inductives.class_read.slots_dup xs) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.class_read.slots_dup.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.class_read.slots_dup.eq_def, if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [class_slot_dup_spec _ _ hy] at hout1
    exact ⟨i2, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, h⟩

/-! ## `classes` -/

theorem classes_abs {slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.class_read.ClassKey),
      arena.inductives.class_read.classes slots i out = ok o →
      o.val.map absClassKey = out.val.map absClassKey ++
        ClassRead.classes ((slots.val.drop i.val).map absClassSlot) := by
  refine cursor_induction (fun i : Std.Usize => i.val) slots.val.length
    (fun i out => ∀ o, arena.inductives.class_read.classes slots i out = ok o →
      o.val.map absClassKey = out.val.map absClassKey ++
        ClassRead.classes ((slots.val.drop i.val).map absClassSlot)) ?_ ?_
  · intro i out hn o h
    rw [arena.inductives.class_read.classes.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len slots by scalar_tac), Result.ok.injEq] at h
    subst h
    simp [List.drop_eq_nil_of_le hn, ClassRead.classes]
  · intro i out hi ih o h
    rw [arena.inductives.class_read.classes.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len slots by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hq
    obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    rw [List.drop_eq_getElem_cons hb, hxv, List.map_cons]
    cases q with
    | Motive k =>
      obtain ⟨k1, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hj : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out1 hj o h, ConRon.Refine.vec_push_val hout1,
        class_key_dup_spec _ _ hk, hj]
      simp [ClassRead.classes, absClassSlot]
    | Minor c n ihs =>
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hj : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out hj o h, hj]
      simp [ClassRead.classes, absClassSlot]

@[lockstep] theorem classes_twin (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot) :
    LSP (arena.inductives.class_read.classes slots 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (ClassRead.classes (slots.val.map absClassSlot))
        (o.val.map absClassKey)) := by
  intro o h
  rw [TwinEq, classes_abs _ _ o h]
  simp [alloc.vec.Vec.new]

/-! ## `is_motive`, `motive_positions`, `motive_slot` -/

/-- The twin's inline `(List.range slots.length).filter …` (in
`ClassRead.motiveSlot` and `classRead`), named. -/
def motPosOf (slots : List ClassSlot) : List Nat :=
  (List.range slots.length).filter fun s =>
    match slots[s]? with
    | some (.motive _) => true
    | _ => false

/-- The motive test of a slot. -/
def isMotiveSlot : ClassSlot → Bool
  | .motive _ => true
  | .minor _ _ _ => false

theorem motPosOf_eq (slots : List ClassSlot) :
    motPosOf slots = (List.range slots.length).filter fun s =>
      (slots[s]?.map isMotiveSlot).getD false := by
  unfold motPosOf
  congr 1
  funext s
  rcases slots[s]? with _ | (_ | _) <;> rfl

@[lockstep] theorem is_motive_twin (s : arena.inductives.class_read.ClassSlot) :
    LSP (arena.inductives.class_read.is_motive s)
      (fun b => b = isMotiveSlot (absClassSlot s)) := by
  intro b h
  cases s <;> simp only [arena.inductives.class_read.is_motive, Result.ok.injEq] at h <;>
    subst h <;> rfl

theorem motive_positions_abs {slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec Std.U64),
      arena.inductives.class_read.motive_positions slots i out = ok o →
      absNatL o = absNatL out ++ (List.range' i.val (slots.val.length - i.val)).filter
        (fun s => ((slots.val.map absClassSlot)[s]?.map isMotiveSlot).getD false) := by
  refine cursor_induction (fun i : Std.Usize => i.val) slots.val.length
    (fun i out => ∀ o, arena.inductives.class_read.motive_positions slots i out = ok o →
      absNatL o = absNatL out ++ (List.range' i.val (slots.val.length - i.val)).filter
        (fun s => ((slots.val.map absClassSlot)[s]?.map isMotiveSlot).getD false)) ?_ ?_
  · intro i out hn o h
    rw [arena.inductives.class_read.motive_positions.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len slots by scalar_tac), Result.ok.injEq] at h
    subst h
    simp [show slots.val.length - i.val = 0 by omega]
  · intro i out hi ih o h
    rw [arena.inductives.class_read.motive_positions.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len slots by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hq
    obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨b, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := is_motive_twin _ _ hbm
    have hr : List.range' i.val (slots.val.length - i.val) =
        i.val :: List.range' (i.val + 1) (slots.val.length - (i.val + 1)) := by
      rw [show slots.val.length - i.val = (slots.val.length - (i.val + 1)) + 1 by omega,
        List.range'_succ]
    have hPi : ((slots.val.map absClassSlot)[i.val]?.map isMotiveSlot).getD false = b := by
      rw [List.getElem?_map, hx, hbv]; rfl
    rw [hr, List.filter_cons, hPi]
    cases b
    · obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hj : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out hj o h, hj]
      simp
    · obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp only [lift, Result.ok.injEq] at hc
      have hj : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out1 hj o h, hj, absNatL,
        ConRon.Refine.vec_push_val hout1, ← hc]
      simp [absU]

@[lockstep] theorem motive_positions_twin
    (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot) :
    LSP (arena.inductives.class_read.motive_positions slots 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (motPosOf (slots.val.map absClassSlot)) (absNatL o)) := by
  intro o h
  rw [TwinEq, motive_positions_abs _ _ o h, motPosOf_eq]
  simp [absNatL, alloc.vec.Vec.new, List.range_eq_range']

theorem motiveSlot_eq (slots : List ClassSlot) (c : Nat) :
    ClassRead.motiveSlot slots c = (motPosOf slots)[c]? := rfl

@[lockstep] theorem motive_slot_twin
    (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot) (c : Std.U64) :
    LSP (arena.inductives.class_read.motive_slot slots c)
      (fun o => TwinEq (ClassRead.motiveSlot (slots.val.map absClassSlot) (absU c))
        (o.map absU)) := by
  intro o h
  rw [arena.inductives.class_read.motive_slot] at h
  obtain ⟨ms, hms, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hmv : motPosOf (slots.val.map absClassSlot) = absNatL ms :=
    motive_positions_twin _ _ hms
  rw [TwinEq, motiveSlot_eq, hmv]
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [lift, Result.ok.injEq] at hn
  subst hn
  have hnv : (UScalar.cast .U64 (alloc.vec.Vec.len ms)).val = ms.val.length :=
    ConRon.Refine.ExprOps.usize_cast_u64_val _
  split at h
  · rename_i hlt
    obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    have hlt' : c.val < ms.val.length := by
      have := hnv; scalar_tac
    have hkv : k.val = c.val := by
      simp only [lift, Result.ok.injEq] at hk
      subst hk
      simp only [Std.UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      have : ms.val.length ≤ Std.Usize.max := ms.property
      have hmax : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
        simp only [Std.Usize.max, Std.Usize.numBits, Std.UScalarTy.Usize_numBits_eq]
      have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
      simp only [Std.UScalarTy.Usize_numBits_eq]
      omega
    have hy' := vec_index_some hy
    rw [hkv] at hy'
    simp [absNatL, List.getElem?_map, hy', absU]
  · rename_i hge
    simp only [Result.ok.injEq] at h
    subst h
    have : ms.val.length ≤ c.val := by have := hnv; scalar_tac
    simp [absNatL, absU, List.getElem?_eq_none (by simpa using this)]

/-! ## `u64_find_idx`, `class_of_motive_var`, `eidx_last`, `u64_snoc` -/

theorem u64_find_idx_abs {xs : alloc.vec.Vec Std.U64} {x : Std.U64} :
    ∀ (i : Std.Usize) (o : Option Std.U64),
      arena.inductives.class_read.u64_find_idx xs x i = ok o →
      o.map absU = ((absNatLFrom xs i).findIdx? (· == absU x)).map (· + i.val) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i (_ : Unit) => ∀ o, arena.inductives.class_read.u64_find_idx xs x i = ok o →
      o.map absU = ((absNatLFrom xs i).findIdx? (· == absU x)).map (· + i.val))
    ?_ ?_ i ()
  · intro i _ hn o h
    rw [arena.inductives.class_read.u64_find_idx.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    subst h
    simp [absNatLFrom, List.drop_eq_nil_of_le hn]
  · intro i _ hi ih o h
    rw [arena.inductives.class_read.u64_find_idx.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hn1
    obtain ⟨hb', hxv⟩ := List.getElem?_eq_some_iff.mp hx
    have hdrop : absNatLFrom xs i = absU n1 :: (xs.val.drop (i.val + 1)).map absU := by
      rw [absNatLFrom, List.drop_eq_getElem_cons hi, hxv, List.map_cons]
    rw [hdrop, List.findIdx?_cons]
    have hbv : (absU n1 == absU x) = decide (n1 = x) := by
      by_cases hq : n1 = x
      · subst hq; simp
      · have : absU n1 ≠ absU x := fun hc => hq (by
          simp only [absU] at hc; exact Std.UScalar.eq_of_val_eq hc)
        simp [hq, this]
    rw [hbv]
    by_cases hq : n1 = x
    · rw [if_pos hq] at h
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp only [lift, Result.ok.injEq] at hi3 h
      subst hi3 h
      simp only [hq, decide_true, ↓reduceIte, Option.map_some, Nat.zero_add, absU]
      rw [ConRon.Refine.ExprOps.usize_cast_u64_val]
    · rw [if_neg hq] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 () hi2v o h, absNatLFrom, hi2v]
      simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_map]
      congr 1
      funext k; simp; omega

@[lockstep] theorem u64_find_idx_twin (xs : alloc.vec.Vec Std.U64) (x : Std.U64) :
    LSP (arena.inductives.class_read.u64_find_idx xs x 0#usize)
      (fun o => TwinEq ((absNatL xs).findIdx? (· == absU x)) (o.map absU)) := by
  intro o h
  rw [TwinEq, u64_find_idx_abs _ o h, absNatLFrom_zero]
  simp

@[lockstep] theorem class_of_motive_var_twin (n_p : Std.U64) (mot_pos : alloc.vec.Vec Std.U64)
    (p : Std.U64) :
    LSP (arena.inductives.class_read.class_of_motive_var n_p mot_pos p)
      (fun o => TwinEq (classOfMotiveVar (absU n_p) (absNatL mot_pos) (absU p))
        (o.map absU)) := by
  intro o h
  rw [arena.inductives.class_read.class_of_motive_var] at h
  rw [TwinEq, classOfMotiveVar]
  split at h
  · rename_i hle
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [if_pos (by simp only [absU]; scalar_tac)]
    have hdv : absU d = absU p - absU n_p := (ConRon.Refine.Nat.usub_val hd).2
    rw [← hdv]
    exact (u64_find_idx_twin _ _ _ h)
  · rename_i hle
    simp only [Result.ok.injEq] at h
    subst h
    rw [if_neg (by simp only [absU]; scalar_tac)]
    rfl

@[lockstep] theorem eidx_last_twin (xs : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.inductives.class_read.eidx_last xs)
      (fun o => TwinEq (absEIdxL xs).getLast? (o.map absEIdx)) := by
  intro o h
  rw [arena.inductives.class_read.eidx_last] at h
  rw [TwinEq]
  split at h
  · rename_i h0
    simp only [Result.ok.injEq] at h
    subst h
    have : xs.val = [] := by
      have : xs.val.length = 0 := by scalar_tac
      exact List.eq_nil_of_length_eq_zero this
    simp [absEIdxL, this]
  · rename_i h0
    obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    rw [dupId_eidx _ _ he1]
    have hkv : k.val = xs.val.length - 1 := by
      have := (ConRon.Refine.Nat.usub_val hk).2; simpa using this
    have hev := vec_index_some he
    rw [hkv] at hev
    rw [absEIdxL, List.getLast?_map, List.getLast?_eq_getElem?, hev]

@[lockstep] theorem u64_snoc_twin (xs : alloc.vec.Vec Std.U64) (x : Std.U64) :
    LSP (arena.inductives.class_read.u64_snoc xs x)
      (fun o => TwinEq (absNatL xs ++ [absU x]) (absNatL o)) := by
  intro o h
  rw [arena.inductives.class_read.u64_snoc] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [u64_vec_dup_spec _ _ hv] at h
  simp [TwinEq, absNatL, ConRon.Refine.vec_push_val h]

/-! ## Helpers for Shape/Abs

`arena::inductives::block_parts::shape_member_names` is the twin's
`BlockShape.memberNames` (the block-parts sub-lane states it as
`shape_member_names_twin` in `Refine2/Inductives/BlockParts.lean`, which this
file does not import; restated here under a local name). -/

theorem cr_member_names_abs {ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      arena.inductives.block_parts.member_names ms i out = ok o →
      o.val.map absNIdx = out.val.map absNIdx ++
        (ms.val.drop i.val).map (fun m => absNIdx m.cv_t.name) := by
  refine vec_cursor_copy ms absNIdx (fun m => absNIdx m.cv_t.name)
    (arena.inductives.block_parts.member_names ms) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.block_parts.member_names.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_parts.member_names.eq_def, if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_nidx _ _ hn], h⟩

theorem cr_shape_member_names_abs {p : arena.inductives.block_parts.BlockShape}
    {o : alloc.vec.Vec arena.handle.NIdx}
    (h : arena.inductives.block_parts.shape_member_names p = ok o) :
    absNIdxL o = (absBlockShape p).memberNames := by
  rw [arena.inductives.block_parts.shape_member_names] at h
  have := cr_member_names_abs _ _ o h
  simp only [alloc.vec.Vec.new] at this
  simp [absNIdxL, this, BlockShape.memberNames, absBlockShape, absMemberShape, absIConstantVal]

/-! ## `class_n_pc_of` (`gen_rec.rs`; the twin's `classNPcOf` lives in `ClassRead`) -/

@[lockstep] theorem class_n_pc_of_twin {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (p : arena.inductives.block_parts.BlockShape)
    (i : arena.handle.NIdx) :
    LSP (arena.inductives.gen_rec.class_n_pc_of p rf i)
      (fun o => TwinEq (classNPcOf (absBlockShape p) lf (absNIdx i)) (absU o)) := by
  intro o h
  rw [arena.inductives.gen_rec.class_n_pc_of] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hbv : (absNIdxL v).contains (absNIdx i) = b := names_contain_twin _ _ _ hb
  rw [cr_shape_member_names_abs hv] at hbv
  rw [TwinEq, classNPcOf, hbv]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hcv : lf.find? (absNIdx i) = c.map absIConstantInfo :=
      ifenv_find_twin (lf := lf) i (IFEnvInv.coreCtxSelf hfe.rel hfe.inv) _ hc
    rw [hcv]
    rcases c with _ | c
    · simp only [Result.ok.injEq] at h; subst h; rfl
    · cases c <;> simp only [Result.ok.injEq] at h <;> subst h <;> rfl
  · simp only [↓reduceIte, Result.ok.injEq] at h ⊢
    subst h; rfl

/-! ## `fvar_head` -/

@[lockstep] theorem fvar_head_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = a.map absU)
      (arena.inductives.class_read.fvar_head pers st e) st lst (fvarHead (absEIdx e)) := by
  apply LSR.of_LS
  rw [arena.inductives.class_read.fvar_head, fvarHead]
  lockstep

/-! ## `class_read_ih`, `class_read_ihs`: the `filterMapM` of `classReadMinor` -/

/-- The body of `classReadMinor`'s `fvs.filterMapM fun x => …` — the Rust's
`class_read_ih`. -/
def classReadIh (nP : Nat) (motPos : List Nat) (d : Nat) (x : EIdx) :
    AM (Option (Nat × Nat)) := do
  let ty ← fvarTypeD x
  let r ← piResult coreWalkFuel ty
  match ← fvarHead r with
  | none => pure none
  | some p2 =>
    match classOfMotiveVar nP motPos p2 with
    | none => pure none
    | some t => do
      let rargs ← getAppArgs coreWalkFuel r
      match rargs.getLast? with
      | none => pure none
      | some a =>
        match ← fvarHead a with
        | none => pure none
        | some f => pure (if d ≤ f then some (f - d, t) else none)

/-- `classReadMinor` with its `filterMapM` body named. -/
def classReadMinor' (nP : Nat) (motPos : List Nat) (d : Nat) (dom : EIdx) :
    AM (Option ClassSlot) := do
  let (bs, _) ← piBinders coreWalkFuel dom
  match ← openPisAtFvarsF bs.length dom d with
  | none => pure none
  | some (fvs, concl) =>
    match ← fvarHead concl with
    | none => pure none
    | some p =>
      match classOfMotiveVar nP motPos p with
      | none => pure none
      | some c => do
        let args ← getAppArgs coreWalkFuel concl
        match args.getLast? with
        | none => pure none
        | some last => do
          let hd ← getAppFn coreWalkFuel last
          if hd.tag == ETag.const then
            match ← viewConst hd with
            | none => failDanglingE
            | some (cn, _) => do
              let ihs ← fvs.filterMapM (classReadIh nP motPos d)
              pure (some (.minor c cn ihs))
          else pure none

theorem classReadMinor_eq : classReadMinor = classReadMinor' := rfl

@[lockstep] theorem class_read_ih_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n_p : Std.U64) (mot_pos : alloc.vec.Vec Std.U64) (d : Std.U64)
    (x : arena.handle.EIdx) :
    LSR pers (fun a b => b = a.map absNatPair)
      (arena.inductives.class_read.class_read_ih pers st n_p mot_pos d x) st lst
      (classReadIh (absU n_p) (absNatL mot_pos) (absU d) (absEIdx x)) := by
  apply LSR.of_LS
  rw [arena.inductives.class_read.class_read_ih, classReadIh]
  lockstep
  rename_i hP
  rw [if_pos hP.2]
  exact LS.pure (by simp [absNatPair, absU, hP.1]) (by assumption) (by assumption)

theorem class_read_ihs_acc {pers st} (n_p : Std.U64) (mot_pos : alloc.vec.Vec Std.U64)
    (d : Std.U64) (fvs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (q : Std.Usize) (out : alloc.vec.Vec (Std.U64 × Std.U64)) lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.val.map absNatPair)
        (arena.inductives.class_read.class_read_ihs pers st n_p mot_pos d fvs q out) st lst
        (List.filterMapM.loop (classReadIh (absU n_p) (absNatL mot_pos) (absU d))
          ((fvs.val.drop q.val).map absEIdx) (out.val.map absNatPair).reverse) := by
  refine cursor_induction (fun i : Std.Usize => i.val) fvs.val.length
    (fun q out => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.val.map absNatPair)
        (arena.inductives.class_read.class_read_ihs pers st n_p mot_pos d fvs q out) st lst
        (List.filterMapM.loop (classReadIh (absU n_p) (absNatL mot_pos) (absU d))
          ((fvs.val.drop q.val).map absEIdx) (out.val.map absNatPair).reverse)) ?_ ?_
  · intro q out hn lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil, List.filterMapM.loop, List.reverse_reverse]
    apply LSR.of_LS
    rw [arena.inductives.class_read.class_read_ihs.eq_def,
      if_pos (show q ≥ alloc.vec.Vec.len fvs by scalar_tac)]
    lockstep
  · intro q out hq ih lst hrel hinv
    rw [List.drop_eq_getElem_cons hq, List.map_cons, List.filterMapM.loop]
    apply LSR.of_LS
    rw [arena.inductives.class_read.class_read_ihs.eq_def,
      if_neg (show ¬ q ≥ alloc.vec.Vec.len fvs by scalar_tac)]
    lockstep

@[lockstep] theorem class_read_ihs_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n_p : Std.U64) (mot_pos : alloc.vec.Vec Std.U64) (d : Std.U64)
    (fvs : alloc.vec.Vec arena.handle.EIdx) :
    LSR pers (fun a b => b = a.val.map absNatPair)
      (arena.inductives.class_read.class_read_ihs pers st n_p mot_pos d fvs 0#usize
        (alloc.vec.Vec.new _)) st lst
      ((absEIdxL fvs).filterMapM (classReadIh (absU n_p) (absNatL mot_pos) (absU d))) := by
  have h := class_read_ihs_acc (pers := pers) n_p mot_pos d fvs 0#usize (alloc.vec.Vec.new _)
    lst hrel hinv
  have e : (fvs.val.drop (0#usize : Std.Usize).val).map absEIdx = absEIdxL fvs := by
    simp [absEIdxL]
  rw [e] at h
  exact h

/-! ## `class_read_minor` -/

@[lockstep] theorem class_read_minor_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n_p : Std.U64) (mot_pos : alloc.vec.Vec Std.U64) (d : Std.U64)
    (dom : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absClassSlot)
      (arena.inductives.class_read.class_read_minor pers st n_p mot_pos d dom) lst
      (classReadMinor (absU n_p) (absNatL mot_pos) (absU d) (absEIdx dom)) := by
  rw [arena.inductives.class_read.class_read_minor, classReadMinor_eq, classReadMinor']
  lockstep

/-! ## `class_read_slot` -/

@[lockstep] theorem class_read_slot_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (p : arena.inductives.block_parts.BlockShape) (np : Std.U64)
    (mot_pos : alloc.vec.Vec Std.U64) (d : Std.U64) (dom : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absClassSlot)
      (arena.inductives.class_read.class_read_slot pers st p rf np mot_pos d dom) lst
      (classReadSlot (absBlockShape p) lf (absU np) (absNatL mot_pos) (absU d)
        (absEIdx dom)) := by
  rw [arena.inductives.class_read.class_read_slot, classReadSlot]
  lockstep
  rename_i bs _
  have hnil : (absBinderL bs).getLast? = none := by
    have : bs.val.length = 0 := by scalar_tac
    simp [absBinderL, List.eq_nil_of_length_eq_zero this]
  rw [hnil]
  exact LS.pure rfl (by assumption) (by assumption)
  rename_i bs _ hlt v hv
  have hv' : (absBinderL bs).getLast? =
      some ((fun q => (absEIdx q.1, ConRon.Refine.absBinderMeta q.2)) bs.val[a.val]) := by
    rw [absBinderL, List.getLast?_map, List.getLast?_eq_getElem?,
      show bs.val.length - 1 = a.val by scalar_tac, List.getElem?_eq_getElem hlt]
    rfl
  obtain rfl := Option.some_inj.mp (hv.symm.trans hv')
  lockstep
  refine LS.pure ?_ (by assumption) (by assumption)
  simp only [Option.map_some, absClassSlot, absClassKey, absEIdxL_of_takeEidx hP]
  rfl

/-! ## `class_read_slots` -/

theorem class_read_slots_acc {pers} {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (p : arena.inductives.block_parts.BlockShape) (np : Std.U64) :
    ∀ (k : Nat) (n : Std.U64) (mot_pos : alloc.vec.Vec Std.U64) (d : Std.U64)
      (e : arena.handle.EIdx) (out : alloc.vec.Vec arena.inductives.class_read.ClassSlot) st lst,
      n.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map (fun v => v.val.map absClassSlot))
        (arena.inductives.class_read.class_read_slots pers st p rf np n mot_pos d e out) lst
        (do
          let r ← classReadSlots (absBlockShape p) lf (absU np) k (absNatL mot_pos) (absU d)
            (absEIdx e)
          pure (r.map (out.val.map absClassSlot ++ ·))) := by
  intro k
  induction k with
  | zero =>
    intro n mot_pos d e out st lst hn hrel hinv
    rw [arena.inductives.class_read.class_read_slots.eq_def, if_pos (by scalar_tac),
      classReadSlots]
    lockstep
  | succ k ih =>
    intro n mot_pos d e out st lst hn hrel hinv
    rw [arena.inductives.class_read.class_read_slots.eq_def, if_neg (by scalar_tac),
      classReadSlots]
    lockstep
    all_goals
      rename_i out1 hout1 n1 hn1
      refine LS.tail (ih n1 _ _ _ _ _ _ (by scalar_tac) (by assumption) (by assumption)) ?_
        (fun _ _ h => h)
      have hdv : absU a = absU d + 1 := by simp only [absU]; scalar_tac
      rw [hdv]
      rcases hsv : absClassSlot ‹arena.inductives.class_read.ClassSlot› with key | ⟨c, cn, ihs⟩ <;>
        first
        | (simp [hsv, isMotiveSlot] at hc; done)
        | (simp only [hsv]
           congr 1
           funext r
           rcases r with _ | r <;> simp [hout1, hsv])

@[lockstep] theorem class_read_slots_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (p : arena.inductives.block_parts.BlockShape) (np n : Std.U64)
    (mot_pos : alloc.vec.Vec Std.U64) (d : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map (fun v => v.val.map absClassSlot))
      (arena.inductives.class_read.class_read_slots pers st p rf np n mot_pos d e
        (alloc.vec.Vec.new _)) lst
      (classReadSlots (absBlockShape p) lf (absU np) (absU n) (absNatL mot_pos) (absU d)
        (absEIdx e)) := by
  have h := class_read_slots_acc hfe p np n.val n mot_pos d e (alloc.vec.Vec.new _) st lst rfl
    hrel hinv
  refine LS.twin_eq h ?_
  simp [alloc.vec.Vec.new, absU]

/-! ## `class_read_rec_cls` -/

theorem class_read_rec_cls_acc {pers} (n_p : Std.U64) (mot_pos : alloc.vec.Vec Std.U64)
    (recs : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec Std.U64),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absNatL)
        (arena.inductives.class_read.class_read_rec_cls pers st n_p mot_pos recs i out) lst
        (do
          let r ← classReadRecCls (absU n_p) (absNatL mot_pos)
            ((recs.val.drop i.val).map absRecShape)
          pure (r.map (absNatL out ++ ·))) := by
  refine ls_cursor_acc recs absRecShape
    (fun out l => do
      let r ← classReadRecCls (absU n_p) (absNatL mot_pos) l
      pure (r.map (absNatL out ++ ·)))
    (fun st i out => arena.inductives.class_read.class_read_rec_cls pers st n_p mot_pos recs i out)
    ?_ ?_
  · intro st lst i out hn hrel hinv
    rw [arena.inductives.class_read.class_read_rec_cls.eq_def, if_pos (by scalar_tac),
      classReadRecCls]
    lockstep
  · intro st lst i out hb hrel hinv ih
    rw [arena.inductives.class_read.class_read_rec_cls.eq_def, if_neg (by scalar_tac),
      classReadRecCls]
    lockstep
    rename_i out1 hout1
    refine LS.tail (ih _ _ _ _ (by scalar_tac) (by assumption) (by assumption)) ?_
      (fun _ _ h => h)
    rw [show (↑a : Nat) = i.val + 1 by scalar_tac]
    congr 1
    funext r
    rcases r with _ | r <;> simp [absNatL, hout1, absU]

@[lockstep] theorem class_read_rec_cls_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n_p : Std.U64) (mot_pos : alloc.vec.Vec Std.U64)
    (recs : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    LS pers (fun a b => b = a.map absNatL)
      (arena.inductives.class_read.class_read_rec_cls pers st n_p mot_pos recs 0#usize
        (alloc.vec.Vec.new _)) lst
      (classReadRecCls (absU n_p) (absNatL mot_pos) (recs.val.map absRecShape)) := by
  have h := class_read_rec_cls_acc (pers := pers) n_p mot_pos recs 0#usize st lst
    (alloc.vec.Vec.new _) hrel hinv
  refine LS.twin_eq h ?_
  simp [alloc.vec.Vec.new, absNatL]

/-! ## `class_read` -/

/-- `classRead` with its inline motive positions named (`motPosOf`). -/
def classRead' (p : BlockShape) (fe : IFEnv) (nP : Nat) (recs : List RecShape) :
    AM (Option ClassRead) := do
  match recs with
  | [] => pure none
  | rc0 :: _ =>
    match ← openPisAtFvarsF nP rc0.cvR.type 0 with
    | none => pure none
    | some (_, body) =>
      match ← classReadSlots p fe nP (rc0.rP - nP) [] nP body with
      | none => pure none
      | some slots =>
        let motPos := motPosOf slots
        match ← classReadRecCls nP motPos recs with
        | none => pure none
        | some recCls => pure (some ⟨slots, recCls⟩)

theorem classRead_eq : classRead = classRead' := rfl

@[lockstep] theorem class_read_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (p : arena.inductives.block_parts.BlockShape) (n_p : Std.U64)
    (recs : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    LS pers (fun a b => b = a.map absClassRead)
      (arena.inductives.class_read.class_read pers st p rf n_p recs) lst
      (classRead (absBlockShape p) lf (absU n_p) (recs.val.map absRecShape)) := by
  rw [arena.inductives.class_read.class_read, classRead_eq]
  rcases hr : recs.val with _ | ⟨rc0, rest⟩
  · rw [if_pos (by scalar_tac), List.map_nil, classRead']
    lockstep
  · rw [if_neg (by scalar_tac), List.map_cons, classRead']
    lockstep
    simp only [hr] at *
    lockstep

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.class_read_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms class_read_ls

/-- info: 'ConRon.Refine2.class_read_slots_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms class_read_slots_ls

/-- info: 'ConRon.Refine2.class_read_minor_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms class_read_minor_ls

/-- info: 'ConRon.Refine2.class_n_pc_of_twin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms class_n_pc_of_twin

/-- info: 'ConRon.Refine2.motive_slot_twin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms motive_slot_twin

/-- info: 'ConRon.Refine2.classes_twin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms classes_twin

/-- info: 'ConRon.Refine2.slots_dup_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms slots_dup_spec

end ConRon.Refine2
