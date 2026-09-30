/-
# `ConRon.Refine2.Inductives.BlockParts` — Theorem 2 for `arena::inductives::block_parts`

**Task #105** (DESIGN.md §8.2, Theorem 2).
`crates/con-ron-core/src/arena/inductives/block_parts.rs` against
`proof/ConRon/Arena/Inductives/BlockParts.lean`: the k-ary block's record, its
projections and the recogniser `blockParts?`, whose companion `block_parts_ls`
is the tier's contract with the checker lane.

## Shapes

* The record copies (`*_dup`) and the Rust-only list builders (`former_names`,
  `ctors_nf`, `rule_rhss`, `zip_members`, …) are `LSP` steps whose `TwinEq`
  names the twin's pure expression (`cvTs.map (·.name)`, …).
* The Rust's index cursors are the twin's structural recursions from the
  cursor on (`absXLFrom v i`); the accumulator stands in front.
* `blockShape?` is ONE `do` block in the twin; the Rust's `block_shape`,
  `block_shape_at`, `block_shape_sort` and `block_shape_elim` are its
  stretches, and the last three are unfolded in place (`lockstep_inline`).
-/
import ConRon.Refine2.Inductives.Env
import ConRon.Refine2.Inductives.Positivity
import ConRon.Refine2.Core.LS.Lits
import ConRon.Arena.Inductives.BlockParts

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

/-! ## Helpers for Shape/Abs -/

/-- A `Vec<IConstantVal>` as the twin's `List IConstantVal`. -/
def absICVL (v : alloc.vec.Vec arena.env.IConstantVal) : List IConstantVal :=
  v.val.map absIConstantVal

def absICVLFrom (v : alloc.vec.Vec arena.env.IConstantVal) (i : Std.Usize) :
    List IConstantVal :=
  (v.val.drop i.val).map absIConstantVal

@[lockstep_simp] theorem absICVLFrom_zero (v) : absICVLFrom v 0#usize = absICVL v := by
  simp [absICVLFrom, absICVL]

theorem usz_zero_val : ((0#usize : Std.Usize)).val = 0 := by scalar_tac

@[simp] theorem vec_new_val' {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl

/-! ## The record copies -/

/-- `ctors_dup` is the identity on the abstraction from the cursor on. -/
theorem ctors_dup_abs {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)),
      arena.inductives.block_parts.ctors_dup cs i out = ok o →
      absCtorsL o = absCtorsL out ++ absCtorsLFrom cs i := by
  simp only [absCtorsL, absCtorsLFrom]
  refine vec_cursor_copy cs _ _ (arena.inductives.block_parts.ctors_dup cs) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.block_parts.ctors_dup.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.block_parts.ctors_dup.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨iv, nf⟩ := q
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, (iv1, nf), out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by simp [i_constant_val_dup_abs hiv1], h⟩

@[lockstep] theorem ctors_dup_twin
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) (i : Std.Usize)
    (out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSP (arena.inductives.block_parts.ctors_dup cs i out)
      (fun o => TwinEq (absCtorsL out ++ absCtorsLFrom cs i) (absCtorsL o)) :=
  fun o h => (ctors_dup_abs i out o h).symm

/-- `ctors_dup` from `0` into an empty accumulator: the copy of the list. -/
@[lockstep] theorem ctors_dup_twin0
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSP (arena.inductives.block_parts.ctors_dup cs 0#usize
        (alloc.vec.Vec.new (arena.env.IConstantVal × Std.U64)))
      (fun o => TwinEq (absCtorsL cs) (absCtorsL o)) := by
  intro o h
  have h' := ctors_dup_abs _ _ o h
  rw [TwinEq, h']
  simp only [absCtorsL, absCtorsLFrom, vec_new_val', usz_zero_val,
    List.drop_zero, List.map_nil, List.nil_append]

theorem member_shape_dup_abs {m o : arena.inductives.block_parts.MemberShape}
    (h : arena.inductives.block_parts.member_shape_dup m = ok o) :
    absMemberShape o = absMemberShape m := by
  rw [arena.inductives.block_parts.member_shape_dup] at h
  obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  have hv' := ctors_dup_abs _ _ v hv
  simp only [absCtorsL, absCtorsLFrom, vec_new_val', usz_zero_val, List.drop_zero,
    List.map_nil, List.nil_append] at hv'
  simp only [absMemberShape, i_constant_val_dup_abs hiv, absCtorsL, hv']

@[lockstep] theorem member_shape_dup_twin (m : arena.inductives.block_parts.MemberShape) :
    LSP (arena.inductives.block_parts.member_shape_dup m)
      (fun o => TwinEq (absMemberShape m) (absMemberShape o)) :=
  fun _ h => (member_shape_dup_abs h).symm

theorem rec_shape_dup_abs {r o : arena.inductives.block_parts.RecShape}
    (h : arena.inductives.block_parts.rec_shape_dup r = ok o) :
    absRecShape o = absRecShape r := by
  rw [arena.inductives.block_parts.rec_shape_dup] at h
  obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  simp only [absRecShape, i_constant_val_dup_abs hiv, absEIdxL, eidx_vec_dup_val hv]

@[lockstep] theorem rec_shape_dup_twin (r : arena.inductives.block_parts.RecShape) :
    LSP (arena.inductives.block_parts.rec_shape_dup r)
      (fun o => TwinEq (absRecShape r) (absRecShape o)) :=
  fun _ h => (rec_shape_dup_abs h).symm

theorem members_dup_abs {ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.block_parts.MemberShape),
      arena.inductives.block_parts.members_dup ms i out = ok o →
      o.val.map absMemberShape = out.val.map absMemberShape ++
        (ms.val.drop i.val).map absMemberShape := by
  refine vec_cursor_copy ms _ _ (arena.inductives.block_parts.members_dup ms) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.block_parts.members_dup.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < ms.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.block_parts.members_dup.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, y, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      member_shape_dup_abs hy, h⟩

@[lockstep] theorem members_dup_twin
    (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) (i : Std.Usize)
    (out : alloc.vec.Vec arena.inductives.block_parts.MemberShape) :
    LSP (arena.inductives.block_parts.members_dup ms i out)
      (fun o => TwinEq (out.val.map absMemberShape ++ (ms.val.drop i.val).map absMemberShape)
        (o.val.map absMemberShape)) :=
  fun o h => (members_dup_abs i out o h).symm

theorem recs_dup_abs {rs : alloc.vec.Vec arena.inductives.block_parts.RecShape} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.block_parts.RecShape),
      arena.inductives.block_parts.recs_dup rs i out = ok o →
      o.val.map absRecShape = out.val.map absRecShape ++
        (rs.val.drop i.val).map absRecShape := by
  refine vec_cursor_copy rs _ _ (arena.inductives.block_parts.recs_dup rs) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.block_parts.recs_dup.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < rs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.block_parts.recs_dup.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, y, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      rec_shape_dup_abs hy, h⟩

@[lockstep] theorem recs_dup_twin
    (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape) (i : Std.Usize)
    (out : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    LSP (arena.inductives.block_parts.recs_dup rs i out)
      (fun o => TwinEq (out.val.map absRecShape ++ (rs.val.drop i.val).map absRecShape)
        (o.val.map absRecShape)) :=
  fun o h => (recs_dup_abs i out o h).symm

theorem block_shape_dup_abs {p o : arena.inductives.block_parts.BlockShape}
    (h : arena.inductives.block_parts.block_shape_dup p = ok o) :
    absBlockShape o = absBlockShape p := by
  rw [arena.inductives.block_parts.block_shape_dup] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  have e1 := members_dup_abs _ _ v hv
  have e2 := recs_dup_abs _ _ v1 hv1
  simp only [vec_new_val', usz_zero_val, List.drop_zero, List.map_nil,
    List.nil_append] at e1 e2
  simp only [absBlockShape, e1, e2, dupId_nidx _ _ hn, dupId_lidx _ _ hl]

@[lockstep] theorem block_shape_dup_twin (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.block_shape_dup p)
      (fun o => TwinEq (absBlockShape p) (absBlockShape o)) :=
  fun _ h => (block_shape_dup_abs h).symm

end ConRon.Refine2
