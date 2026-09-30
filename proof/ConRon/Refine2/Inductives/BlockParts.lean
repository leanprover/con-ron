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

set_option hygiene false in
/-- The stop arm of a `vec_cursor_copy` instance. -/
macro "bp_copy_stop " F:term:max xs:term:max : tactic => `(tactic| (
  intro i out o hn h
  have hF := $F
  rw [hF] at h
  rw [if_pos (show i ≥ alloc.vec.Vec.len $xs by scalar_tac), Result.ok.injEq] at h
  rw [h]))

set_option hygiene false in
/-- The head of the step arm of a `vec_cursor_copy` instance: the element read. -/
macro "bp_copy_head " F:term:max xs:term:max : tactic => `(tactic| (
  intro i x out o hx h
  have hlt : i.val < ($xs).val.length := (List.getElem?_eq_some_iff.mp hx).1
  have hF := $F
  rw [hF] at h
  rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len $xs by scalar_tac)] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hqx : q = x := by
    have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
  subst hqx))

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

/-! ## The split -/

theorem absICILFrom_cons {block : alloc.vec.Vec arena.env.IConstantInfo} {i j : Std.Usize}
    {ii : arena.env.IConstantInfo} (hx : block.val[i.val]? = some ii)
    (hj : j.val = i.val + 1) :
    absICILFrom block i = absIConstantInfo ii :: absICILFrom block j := by
  obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
  rw [absICILFrom, absICILFrom, List.drop_eq_getElem_cons hb, hxv, List.map_cons, hj]

theorem absICILFrom_cons' {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize}
    {ii : arena.env.IConstantInfo} (hx : block.val[i.val]? = some ii) :
    absICILFrom block i = absIConstantInfo ii :: (block.val.drop (i.val + 1)).map absIConstantInfo := by
  obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
  rw [absICILFrom, List.drop_eq_getElem_cons hb, hxv, List.map_cons]

theorem absICILFrom_nil {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize}
    (hn : block.val.length ≤ i.val) : absICILFrom block i = [] := by
  rw [absICILFrom, List.drop_eq_nil_of_le hn, List.map_nil]

/-- `blockSplitCtors` at a list that does not start with a constructor. -/
theorem blockSplitCtors_of_not_ctor (L : List IConstantInfo)
    (hL : ∀ cv np nf rest, L ≠ .ctorInfo cv np nf :: rest) :
    blockSplitCtors L = (blockSplitRecs L).map (fun rs => ([], rs)) := by
  match L, hL with
  | [], _ => simp [blockSplitCtors, blockSplitRecs]
  | .axiomInfo _ :: _, _ => simp [blockSplitCtors, blockSplitRecs]
  | .defnInfo _ _ _ :: _, _ => simp [blockSplitCtors, blockSplitRecs]
  | .thmInfo _ _ :: _, _ => simp [blockSplitCtors, blockSplitRecs]
  | .indInfo _ _ :: _, _ => simp [blockSplitCtors, blockSplitRecs]
  | .ctorInfo cv np nf :: rest, hL => exact absurd rfl (hL cv np nf rest)
  | .recInfo _ _ _ _ :: rest, _ =>
    simp only [blockSplitCtors, blockSplitRecs]
    cases blockSplitRecs rest <;> rfl
  | .projInfo _ :: _, _ => simp [blockSplitCtors, blockSplitRecs]

/-- `blockSplit` at a list that does not start with a type former. -/
theorem blockSplit_of_not_ind (L : List IConstantInfo)
    (hL : ∀ cv caps rest, L ≠ .indInfo cv caps :: rest) :
    blockSplit L = (blockSplitCtors L).map (fun q => ([], q.1, q.2)) := by
  match L, hL with
  | [], _ => simp only [blockSplit]; cases blockSplitCtors [] <;> rfl
  | .axiomInfo a :: r, _ => simp only [blockSplit]; cases blockSplitCtors (.axiomInfo a :: r) <;> rfl
  | .defnInfo a b c :: r, _ =>
    simp only [blockSplit]; cases blockSplitCtors (.defnInfo a b c :: r) <;> rfl
  | .thmInfo a b :: r, _ => simp only [blockSplit]; cases blockSplitCtors (.thmInfo a b :: r) <;> rfl
  | .indInfo cv caps :: rest, hL => exact absurd rfl (hL cv caps rest)
  | .ctorInfo a b c :: r, _ =>
    simp only [blockSplit]; cases blockSplitCtors (.ctorInfo a b c :: r) <;> rfl
  | .recInfo a b c d :: r, _ =>
    simp only [blockSplit]; cases blockSplitCtors (.recInfo a b c d :: r) <;> rfl
  | .projInfo a :: r, _ => simp only [blockSplit]; cases blockSplitCtors (.projInfo a :: r) <;> rfl

theorem block_split_recs_abs {block : alloc.vec.Vec arena.env.IConstantInfo} :
    ∀ (i : Std.Usize) out o,
      arena.inductives.block_parts.block_split_recs block i out = ok o →
      o.map absRecsL = (blockSplitRecs (absICILFrom block i)).map (absRecsL out ++ ·) := by
  refine cursor_induction (fun i : Std.Usize => i.val) block.val.length
    (fun i out => ∀ o, arena.inductives.block_parts.block_split_recs block i out = ok o →
      o.map absRecsL = (blockSplitRecs (absICILFrom block i)).map (absRecsL out ++ ·)) ?_ ?_
  · intro i out hn o h
    rw [arena.inductives.block_parts.block_split_recs.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [absICILFrom_nil hn]; simp [blockSplitRecs]
  · intro i out hi ih o h
    rw [arena.inductives.block_parts.block_split_recs.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
    obtain ⟨ii, hii, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hii
    clear h
    cases ii with
    | RecInfo cv mi rp rules =>
      obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
      obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out1 hi2v o h, absICILFrom_cons hx hi2v]
      simp only [absIConstantInfo, blockSplitRecs]
      cases blockSplitRecs (absICILFrom block i2) <;>
        simp [absRecsL, ConRon.Refine.vec_push_val hout1, i_constant_val_dup_abs hiv,
          i_rec_rules_dup_abs hv]
    | AxiomInfo _ => simp only [Result.ok.injEq] at h2; subst h2; rw [absICILFrom_cons' hx]; simp [absIConstantInfo, blockSplitRecs]
    | DefnInfo _ _ _ => simp only [Result.ok.injEq] at h2; subst h2; rw [absICILFrom_cons' hx]; simp [absIConstantInfo, blockSplitRecs]
    | ThmInfo _ _ => simp only [Result.ok.injEq] at h2; subst h2; rw [absICILFrom_cons' hx]; simp [absIConstantInfo, blockSplitRecs]
    | IndInfo _ _ => simp only [Result.ok.injEq] at h2; subst h2; rw [absICILFrom_cons' hx]; simp [absIConstantInfo, blockSplitRecs]
    | CtorInfo _ _ _ => simp only [Result.ok.injEq] at h2; subst h2; rw [absICILFrom_cons' hx]; simp [absIConstantInfo, blockSplitRecs]
    | ProjInfo _ => simp only [Result.ok.injEq] at h2; subst h2; rw [absICILFrom_cons' hx]; simp [absIConstantInfo, blockSplitRecs]

@[lockstep] theorem block_split_recs_twin (block : alloc.vec.Vec arena.env.IConstantInfo)
    (i : Std.Usize) out :
    LSP (arena.inductives.block_parts.block_split_recs block i out)
      (fun o => TwinEq ((blockSplitRecs (absICILFrom block i)).map (absRecsL out ++ ·))
        (o.map absRecsL)) :=
  fun o h => (block_split_recs_abs i out o h).symm

theorem block_split_recs_new_abs {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (h : arena.inductives.block_parts.block_split_recs block i (alloc.vec.Vec.new _) = ok o) :
    o.map absRecsL = blockSplitRecs (absICILFrom block i) := by
  rw [block_split_recs_abs i _ o h]
  cases blockSplitRecs (absICILFrom block i) <;> simp [absRecsL]

theorem block_split_ctors_abs {block : alloc.vec.Vec arena.env.IConstantInfo} :
    ∀ (i : Std.Usize) out o,
      arena.inductives.block_parts.block_split_ctors block i out = ok o →
      o.map (fun q => (absCtors3L q.1, absRecsL q.2)) =
        (blockSplitCtors (absICILFrom block i)).map (fun q => (absCtors3L out ++ q.1, q.2)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) block.val.length
    (fun i out => ∀ o, arena.inductives.block_parts.block_split_ctors block i out = ok o →
      o.map (fun q => (absCtors3L q.1, absRecsL q.2)) =
        (blockSplitCtors (absICILFrom block i)).map (fun q => (absCtors3L out ++ q.1, q.2)))
    ?_ ?_
  · intro i out hn o h
    rw [arena.inductives.block_parts.block_split_ctors.eq_def] at h
    rw [if_neg (show ¬ i < alloc.vec.Vec.len block by scalar_tac)] at h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have e := block_split_recs_new_abs ho1
    rw [blockSplitCtors_of_not_ctor _ (by rw [absICILFrom_nil hn]; simp), ← e]
    cases o1 <;> (obtain rfl := Result.ok_injective h; simp)
  · intro i out hi ih o h
    rw [arena.inductives.block_parts.block_split_ctors.eq_def] at h
    rw [if_pos (show i < alloc.vec.Vec.len block by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hii
    by_cases hc : ∃ cv np nf, ii = .CtorInfo cv np nf
    · obtain ⟨cv, np, nf, rfl⟩ := hc
      simp only [arena.inductives.block_parts.is_ctor_info, bind_tc_ok, ite_true,
        arena.inductives.block_parts.ctor_info_parts] at h
      obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨iv, hiv, ht⟩ := ConRon.Refine.bind_eq_ok_iff.mp ht
      simp only [Result.ok.injEq] at ht
      subst ht
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out1 hi2v o h, absICILFrom_cons hx hi2v]
      simp only [absIConstantInfo, blockSplitCtors]
      cases blockSplitCtors (absICILFrom block i2) <;>
        simp [absCtors3L, ConRon.Refine.vec_push_val hout1, i_constant_val_dup_abs hiv]
    · have hb : arena.inductives.block_parts.is_ctor_info ii = ok false := by
        cases ii <;> simp_all [arena.inductives.block_parts.is_ctor_info]
      rw [hb, bind_tc_ok] at h
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have e := block_split_recs_new_abs ho1
      rw [blockSplitCtors_of_not_ctor _ ?_, ← e]
      · cases o1 <;> (obtain rfl := Result.ok_injective h; simp)
      · intro cv np nf rest hc'
        rw [absICILFrom_cons' hx] at hc'
        cases ii <;> simp_all [absIConstantInfo]

@[lockstep] theorem block_split_ctors_twin (block : alloc.vec.Vec arena.env.IConstantInfo)
    (i : Std.Usize) out :
    LSP (arena.inductives.block_parts.block_split_ctors block i out)
      (fun o => TwinEq ((blockSplitCtors (absICILFrom block i)).map
          (fun q => (absCtors3L out ++ q.1, q.2)))
        (o.map (fun q => (absCtors3L q.1, absRecsL q.2)))) :=
  fun o h => (block_split_ctors_abs i out o h).symm

theorem block_split_ctors_new_abs {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize} {o}
    (h : arena.inductives.block_parts.block_split_ctors block i (alloc.vec.Vec.new _) = ok o) :
    o.map (fun q => (absCtors3L q.1, absRecsL q.2)) = blockSplitCtors (absICILFrom block i) := by
  rw [block_split_ctors_abs i _ o h]
  cases blockSplitCtors (absICILFrom block i) <;> simp [absCtors3L]

theorem block_split_abs {block : alloc.vec.Vec arena.env.IConstantInfo} :
    ∀ (i : Std.Usize) out o,
      arena.inductives.block_parts.block_split block i out = ok o →
      o.map (fun q => (absICVL q.1, absCtors3L q.2.1, absRecsL q.2.2)) =
        (blockSplit (absICILFrom block i)).map (fun q => (absICVL out ++ q.1, q.2)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) block.val.length
    (fun i out => ∀ o, arena.inductives.block_parts.block_split block i out = ok o →
      o.map (fun q => (absICVL q.1, absCtors3L q.2.1, absRecsL q.2.2)) =
        (blockSplit (absICILFrom block i)).map (fun q => (absICVL out ++ q.1, q.2)))
    ?_ ?_
  · intro i out hn o h
    rw [arena.inductives.block_parts.block_split.eq_def] at h
    rw [if_neg (show ¬ i < alloc.vec.Vec.len block by scalar_tac)] at h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have e := block_split_ctors_new_abs ho1
    rw [blockSplit_of_not_ind _ (by rw [absICILFrom_nil hn]; simp), ← e]
    cases o1 <;> (obtain rfl := Result.ok_injective h; simp)
  · intro i out hi ih o h
    rw [arena.inductives.block_parts.block_split.eq_def] at h
    rw [if_pos (show i < alloc.vec.Vec.len block by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hii
    by_cases hc : ∃ cv caps, ii = .IndInfo cv caps
    · obtain ⟨cv, caps, rfl⟩ := hc
      simp only [arena.inductives.block_parts.is_ind_info, bind_tc_ok, ite_true,
        arena.inductives.block_parts.ind_info_val] at h
      obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out1 hi2v o h, absICILFrom_cons hx hi2v]
      simp only [absIConstantInfo, blockSplit]
      cases blockSplit (absICILFrom block i2) <;>
        simp [absICVL, ConRon.Refine.vec_push_val hout1, i_constant_val_dup_abs hiv]
    · have hb : arena.inductives.block_parts.is_ind_info ii = ok false := by
        cases ii <;> simp_all [arena.inductives.block_parts.is_ind_info]
      rw [hb, bind_tc_ok] at h
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have e := block_split_ctors_new_abs ho1
      rw [blockSplit_of_not_ind _ ?_, ← e]
      · cases o1 <;> (obtain rfl := Result.ok_injective h; simp)
      · intro cv caps rest hc'
        rw [absICILFrom_cons' hx] at hc'
        cases ii <;> simp_all [absIConstantInfo]

@[lockstep] theorem block_split_twin (block : alloc.vec.Vec arena.env.IConstantInfo)
    (i : Std.Usize) out :
    LSP (arena.inductives.block_parts.block_split block i out)
      (fun o => TwinEq ((blockSplit (absICILFrom block i)).map
          (fun q => (absICVL out ++ q.1, q.2)))
        (o.map (fun q => (absICVL q.1, absCtors3L q.2.1, absRecsL q.2.2)))) :=
  fun o h => (block_split_abs i out o h).symm

/-- `block_split` from `0` into an empty accumulator IS `blockSplit`. -/
@[lockstep] theorem block_split_twin0 (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LSP (arena.inductives.block_parts.block_split block 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (blockSplit (absICIL block))
        (o.map (fun q => (absICVL q.1, absCtors3L q.2.1, absRecsL q.2.2)))) := by
  intro o h
  rw [TwinEq, block_split_abs _ _ o h, absICILFrom_zero]
  cases blockSplit (absICIL block) <;> simp [absICVL]

/-! ## The Rust-only list builders -/

theorem former_names_abs {cvs : alloc.vec.Vec arena.env.IConstantVal} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      arena.inductives.block_parts.former_names cvs i out = ok o →
      absNIdxL o = absNIdxL out ++ (absICVLFrom cvs i).map (·.name) := by
  have := vec_cursor_copy cvs absNIdx (fun c => absNIdx c.name)
    (arena.inductives.block_parts.former_names cvs) ?_ ?_
  · intro i out o h
    simpa [absNIdxL, absICVLFrom, absIConstantVal, Function.comp_def] using this i out o h
  · bp_copy_stop arena.inductives.block_parts.former_names.eq_def cvs
  · bp_copy_head arena.inductives.block_parts.former_names.eq_def cvs
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_nidx _ _ hn], h⟩

@[lockstep] theorem former_names_twin0 (cvs : alloc.vec.Vec arena.env.IConstantVal) :
    LSP (arena.inductives.block_parts.former_names cvs 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((absICVL cvs).map (·.name)) (absNIdxL o)) := by
  intro o h
  rw [TwinEq, former_names_abs _ _ o h, absICVLFrom_zero]
  simp [absNIdxL]

theorem ctors_nf_abs {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)),
      arena.inductives.block_parts.ctors_nf cs i out = ok o →
      absCtorsL o = absCtorsL out ++ (absCtors3LFrom cs i).map (fun c => (c.1, c.2.2)) := by
  have := vec_cursor_copy cs (fun p => (absIConstantVal p.1, absU p.2))
    (fun c => (absIConstantVal c.1, absU c.2.2))
    (arena.inductives.block_parts.ctors_nf cs) ?_ ?_
  · intro i out o h
    simpa [absCtorsL, absCtors3LFrom, Function.comp_def] using this i out o h
  · bp_copy_stop arena.inductives.block_parts.ctors_nf.eq_def cs
  · bp_copy_head arena.inductives.block_parts.ctors_nf.eq_def cs
    obtain ⟨iv, np, nf⟩ := q
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, (iv1, nf), out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by simp [i_constant_val_dup_abs hiv1], h⟩

@[lockstep] theorem ctors_nf_twin0
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) :
    LSP (arena.inductives.block_parts.ctors_nf cs 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((absCtors3L cs).map (fun c => (c.1, c.2.2))) (absCtorsL o)) := by
  intro o h
  rw [TwinEq, ctors_nf_abs _ _ o h, absCtors3LFrom_zero]
  simp [absCtorsL]

theorem rule_rhss_abs {rules : alloc.vec.Vec arena.env.IRecRule} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.EIdx),
      arena.inductives.block_parts.rule_rhss rules i out = ok o →
      absEIdxL o = absEIdxL out ++ (absIRecRuleLFrom rules i).map (·.rhs) := by
  have := vec_cursor_copy rules absEIdx (fun r => absEIdx r.rhs)
    (arena.inductives.block_parts.rule_rhss rules) ?_ ?_
  · intro i out o h
    simpa [absEIdxL, absIRecRuleLFrom, absIRecRule, Function.comp_def] using this i out o h
  · bp_copy_stop arena.inductives.block_parts.rule_rhss.eq_def rules
  · bp_copy_head arena.inductives.block_parts.rule_rhss.eq_def rules
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, e, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_eidx _ _ he], h⟩

@[lockstep] theorem rule_rhss_twin0 (rules : alloc.vec.Vec arena.env.IRecRule) :
    LSP (arena.inductives.block_parts.rule_rhss rules 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((rules.val.map absIRecRule).map (·.rhs)) (absEIdxL o)) := by
  intro o h
  rw [TwinEq, rule_rhss_abs _ _ o h]
  simp [absEIdxL, absIRecRuleLFrom]

theorem member_names_abs {ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      arena.inductives.block_parts.member_names ms i out = ok o →
      absNIdxL o = absNIdxL out ++ ((ms.val.drop i.val).map absMemberShape).map (·.cvT.name) := by
  have := vec_cursor_copy ms absNIdx (fun m => absNIdx m.cv_t.name)
    (arena.inductives.block_parts.member_names ms) ?_ ?_
  · intro i out o h
    simpa [absNIdxL, absMemberShape, absIConstantVal, Function.comp_def] using this i out o h
  · bp_copy_stop arena.inductives.block_parts.member_names.eq_def ms
  · bp_copy_head arena.inductives.block_parts.member_names.eq_def ms
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_nidx _ _ hn], h⟩

@[lockstep] theorem member_names_twin (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape)
    (i : Std.Usize) (out : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.inductives.block_parts.member_names ms i out)
      (fun o => TwinEq (absNIdxL out ++ ((ms.val.drop i.val).map absMemberShape).map (·.cvT.name))
        (absNIdxL o)) :=
  fun o h => (member_names_abs i out o h).symm

@[lockstep] theorem shape_member_names_twin (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.shape_member_names p)
      (fun o => TwinEq (absBlockShape p).memberNames (absNIdxL o)) := by
  intro o h
  rw [arena.inductives.block_parts.shape_member_names] at h
  rw [TwinEq, member_names_abs _ _ o h]
  simp [absNIdxL, BlockShape.memberNames, absBlockShape]

theorem shape_n_idxs_abs {ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec Std.U64),
      arena.inductives.block_parts.shape_n_idxs ms i out = ok o →
      absNatL o = absNatL out ++ ((ms.val.drop i.val).map absMemberShape).map (·.nIdx) := by
  have := vec_cursor_copy ms absU (fun m => absU m.n_idx)
    (arena.inductives.block_parts.shape_n_idxs ms) ?_ ?_
  · intro i out o h
    simpa [absNatL, absMemberShape, Function.comp_def] using this i out o h
  · bp_copy_stop arena.inductives.block_parts.shape_n_idxs.eq_def ms
  · bp_copy_head arena.inductives.block_parts.shape_n_idxs.eq_def ms
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, _, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, rfl, h⟩

@[lockstep] theorem shape_n_idxs_twin (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape)
    (i : Std.Usize) (out : alloc.vec.Vec Std.U64) :
    LSP (arena.inductives.block_parts.shape_n_idxs ms i out)
      (fun o => TwinEq (absNatL out ++ ((ms.val.drop i.val).map absMemberShape).map (·.nIdx))
        (absNatL o)) :=
  fun o h => (shape_n_idxs_abs i out o h).symm

/-- `shape_n_idxs p.members 0 []` IS `p.nIdxs`. -/
@[lockstep] theorem shape_n_idxs_twin0 (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.shape_n_idxs p.members 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (absBlockShape p).nIdxs (absNatL o)) := by
  intro o h
  rw [TwinEq, shape_n_idxs_abs _ _ o h]
  simp [absNatL, BlockShape.nIdxs, absBlockShape]

theorem rec_names_abs {rs : alloc.vec.Vec arena.inductives.block_parts.RecShape} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      arena.inductives.block_parts.rec_names rs i out = ok o →
      absNIdxL o = absNIdxL out ++ ((rs.val.drop i.val).map absRecShape).map (·.cvR.name) := by
  have := vec_cursor_copy rs absNIdx (fun r => absNIdx r.cv_r.name)
    (arena.inductives.block_parts.rec_names rs) ?_ ?_
  · intro i out o h
    simpa [absNIdxL, absRecShape, absIConstantVal, Function.comp_def] using this i out o h
  · bp_copy_stop arena.inductives.block_parts.rec_names.eq_def rs
  · bp_copy_head arena.inductives.block_parts.rec_names.eq_def rs
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_nidx _ _ hn], h⟩

@[lockstep] theorem rec_names_twin0 (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    LSP (arena.inductives.block_parts.rec_names rs 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((rs.val.map absRecShape).map (·.cvR.name)) (absNIdxL o)) := by
  intro o h
  rw [TwinEq, rec_names_abs _ _ o h]
  simp [absNIdxL]

end ConRon.Refine2
