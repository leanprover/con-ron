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

/-! ## The boolean scans -/

set_option hygiene false in
/-- The stop arm of a `vec_cursor_all` instance. -/
macro "bp_all_stop " F:term:max xs:term:max : tactic => `(tactic| (
  intro i o hn h
  have hF := $F
  rw [hF] at h
  rw [if_pos (show i ≥ alloc.vec.Vec.len $xs by scalar_tac), Result.ok.injEq] at h
  rw [h]))

set_option hygiene false in
/-- The head of the step arm of a `vec_cursor_all` instance: the element read. -/
macro "bp_all_head " F:term:max xs:term:max : tactic => `(tactic| (
  intro i x o hx h
  have hlt : i.val < ($xs).val.length := (List.getElem?_eq_some_iff.mp hx).1
  have hF := $F
  rw [hF] at h
  rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len $xs by scalar_tac)] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hqx : q = x := by
    have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
  subst hqx))

theorem names_contain0_abs {ns : alloc.vec.Vec arena.handle.NIdx} {n : arena.handle.NIdx} {o : Bool}
    (h : arena.inductives.positivity.names_contain ns n 0#usize = ok o) :
    o = (absNIdxL ns).contains (absNIdx n) := by
  rw [names_contain_abs _ o h, absNIdxLFrom_zero]

theorem formers_pinned_abs {reserved lps : alloc.vec.Vec arena.handle.NIdx}
    {cvs : alloc.vec.Vec arena.env.IConstantVal} :
    ∀ (i : Std.Usize) (o : Bool),
      arena.inductives.block_parts.formers_pinned reserved cvs lps i = ok o →
      o = (absICVLFrom cvs i).all (fun c =>
        !(absNIdxL reserved).contains c.name && c.levelParams == absNIdxL lps) := by
  have := vec_cursor_all cvs (fun x => (fun c : IConstantVal =>
        !(absNIdxL reserved).contains c.name && c.levelParams == absNIdxL lps)
      (absIConstantVal x))
    (arena.inductives.block_parts.formers_pinned reserved cvs lps) ?_ ?_
  · intro i o h
    rw [this i o h, absICVLFrom, List.all_map]; rfl
  · bp_all_stop arena.inductives.block_parts.formers_pinned.eq_def cvs
  · bp_all_head arena.inductives.block_parts.formers_pinned.eq_def cvs
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := names_contain0_abs hb
    cases b
    · rw [if_neg (by simp)] at h
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hb1v := nidx_vec_beq_abs hb1
      cases b1
      · rw [if_neg (by simp), Result.ok.injEq] at h
        refine Or.inr ⟨?_, h.symm⟩
        simp only [absIConstantVal, ← hbv, Bool.not_false, Bool.true_and]
        exact hb1v.symm
      · rw [if_pos (by simp)] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        refine Or.inl ⟨?_, i2, absSz_add_one hi2, h⟩
        simp only [absIConstantVal, ← hbv, Bool.not_false, Bool.true_and]
        exact hb1v.symm
    · rw [if_pos (by simp), Result.ok.injEq] at h
      refine Or.inr ⟨?_, h.symm⟩
      simp only [absIConstantVal, ← hbv, Bool.not_true, Bool.false_and]

@[lockstep] theorem formers_pinned_twin0 (reserved lps : alloc.vec.Vec arena.handle.NIdx)
    (cvs : alloc.vec.Vec arena.env.IConstantVal) :
    LSP (arena.inductives.block_parts.formers_pinned reserved cvs lps 0#usize)
      (fun o => TwinEq ((absICVL cvs).all (fun c =>
        !(absNIdxL reserved).contains c.name && c.levelParams == absNIdxL lps)) o) := by
  intro o h
  rw [TwinEq, formers_pinned_abs _ o h, absICVLFrom_zero]

theorem recs_unreserved_abs {reserved : alloc.vec.Vec arena.handle.NIdx}
    {rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))} :
    ∀ (i : Std.Usize) (o : Bool),
      arena.inductives.block_parts.recs_unreserved reserved rs i = ok o →
      o = (absRecsLFrom rs i).all (fun r => !(absNIdxL reserved).contains r.1.name) := by
  have := vec_cursor_all rs (fun x => !(absNIdxL reserved).contains (absNIdx x.1.name))
    (arena.inductives.block_parts.recs_unreserved reserved rs) ?_ ?_
  · intro i o h
    rw [this i o h, absRecsLFrom, List.all_map]; rfl
  · bp_all_stop arena.inductives.block_parts.recs_unreserved.eq_def rs
  · bp_all_head arena.inductives.block_parts.recs_unreserved.eq_def rs
    obtain ⟨iv, a, b, c⟩ := q
    obtain ⟨bb, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := names_contain0_abs hb
    cases bb
    · rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine Or.inl ⟨?_, i2, absSz_add_one hi2, h⟩
      show (!(absNIdxL reserved).contains (absNIdx iv.name)) = true
      rw [← hbv]; rfl
    · rw [if_pos (by simp), Result.ok.injEq] at h
      refine Or.inr ⟨?_, h.symm⟩
      show (!(absNIdxL reserved).contains (absNIdx iv.name)) = false
      rw [← hbv]; rfl

@[lockstep] theorem recs_unreserved_twin0 (reserved : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))) :
    LSP (arena.inductives.block_parts.recs_unreserved reserved rs 0#usize)
      (fun o => TwinEq ((absRecsL rs).all (fun r => !(absNIdxL reserved).contains r.1.name)) o) := by
  intro o h
  rw [TwinEq, recs_unreserved_abs _ o h, absRecsLFrom_zero]

theorem ctors_pinned_abs {reserved lps : alloc.vec.Vec arena.handle.NIdx}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)} {n_p : Std.U64} :
    ∀ (i : Std.Usize) (o : Bool),
      arena.inductives.block_parts.ctors_pinned reserved cs n_p lps i = ok o →
      o = (absCtors3LFrom cs i).all (fun c => c.2.1 == absU n_p &&
        c.1.levelParams == absNIdxL lps && !(absNIdxL reserved).contains c.1.name) := by
  have := vec_cursor_all cs (fun x => (fun c : IConstantVal × Nat × Nat => c.2.1 == absU n_p &&
        c.1.levelParams == absNIdxL lps && !(absNIdxL reserved).contains c.1.name)
      (absIConstantVal x.1, absU x.2.1, absU x.2.2))
    (arena.inductives.block_parts.ctors_pinned reserved cs n_p lps) ?_ ?_
  · intro i o h
    rw [this i o h, absCtors3LFrom, List.all_map]; rfl
  · bp_all_stop arena.inductives.block_parts.ctors_pinned.eq_def cs
  · bp_all_head arena.inductives.block_parts.ctors_pinned.eq_def cs
    obtain ⟨iv, np, nf⟩ := q
    change (if np = n_p then _ else _) = ok o at h
    by_cases hnp : np = n_p
    · rw [if_pos hnp] at h
      have e1 : (absU np == absU n_p) = true := by simp [hnp]
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbv := nidx_vec_beq_abs hb
      cases b
      · rw [if_neg (by simp), Result.ok.injEq] at h
        refine Or.inr ⟨?_, h.symm⟩
        have e2 : (List.map absNIdx iv.level_params.val == absNIdxL lps) = false := hbv.symm
        simp only [absIConstantVal, e1, e2, Bool.true_and, Bool.false_and]
      · rw [if_pos (by simp)] at h
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hb1v := names_contain0_abs hb1
        have e2 : (List.map absNIdx iv.level_params.val == absNIdxL lps) = true := hbv.symm
        cases b1
        · rw [if_neg (by simp)] at h
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          refine Or.inl ⟨?_, i2, absSz_add_one hi2, h⟩
          simp only [absIConstantVal, e1, e2, Bool.true_and, ← hb1v, Bool.not_false]
        · rw [if_pos (by simp), Result.ok.injEq] at h
          refine Or.inr ⟨?_, h.symm⟩
          simp only [absIConstantVal, e1, e2, Bool.true_and, ← hb1v, Bool.not_true]
    · rw [if_neg hnp, Result.ok.injEq] at h
      refine Or.inr ⟨?_, h.symm⟩
      have e1 : (absU np == absU n_p) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro hc; exact hnp (by simp only [absU] at hc; scalar_tac)
      simp [e1]

@[lockstep] theorem ctors_pinned_twin0 (reserved lps : alloc.vec.Vec arena.handle.NIdx)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) (n_p : Std.U64) :
    LSP (arena.inductives.block_parts.ctors_pinned reserved cs n_p lps 0#usize)
      (fun o => TwinEq ((absCtors3L cs).all (fun c => c.2.1 == absU n_p &&
        c.1.levelParams == absNIdxL lps && !(absNIdxL reserved).contains c.1.name)) o) := by
  intro o h
  rw [TwinEq, ctors_pinned_abs _ o h, absCtors3LFrom_zero]

theorem names_all_in_abs {xs ys : alloc.vec.Vec arena.handle.NIdx} :
    ∀ (i : Std.Usize) (o : Bool),
      arena.inductives.block_parts.names_all_in xs ys i = ok o →
      o = (absNIdxLFrom xs i).all (fun n => (absNIdxL ys).contains n) := by
  have := vec_cursor_all xs (fun x => (absNIdxL ys).contains (absNIdx x))
    (arena.inductives.block_parts.names_all_in xs ys) ?_ ?_
  · intro i o h
    rw [this i o h, absNIdxLFrom, List.all_map]; rfl
  · bp_all_stop arena.inductives.block_parts.names_all_in.eq_def xs
  · bp_all_head arena.inductives.block_parts.names_all_in.eq_def xs
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := names_contain0_abs hb
    cases b
    · rw [if_neg (by simp), Result.ok.injEq] at h
      exact Or.inr ⟨hbv.symm, h.symm⟩
    · rw [if_pos (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inl ⟨hbv.symm, i2, absSz_add_one hi2, h⟩

@[lockstep] theorem names_all_in_twin0 (xs ys : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.inductives.block_parts.names_all_in xs ys 0#usize)
      (fun o => TwinEq ((absNIdxL xs).all (fun n => (absNIdxL ys).contains n)) o) := by
  intro o h
  rw [TwinEq, names_all_in_abs _ o h, absNIdxLFrom_zero]

/-- The comparison block of `nidx_vec_beq_off` (both cursors in range). -/
theorem nidx_vec_beq_off_cmp {a b : alloc.vec.Vec arena.handle.NIdx} {off i i1 : Std.Usize}
    (hi1v : i1.val = off.val + i.val) (hi : i.val < b.val.length)
    (hlt : off.val + i.val < a.val.length)
    (ih : ∀ (j : Std.Usize) (o : Bool), j.val = i.val + 1 →
      arena.inductives.block_parts.nidx_vec_beq_off a off b j = ok o →
      o = ((a.val.drop (off.val + j.val)).map absNIdx == (b.val.drop j.val).map absNIdx))
    {o : Bool}
    (h : (do
        let n ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          arena.handle.NIdx) a i1
        let n1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          arena.handle.NIdx) b i
        let b1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 n n1
        if b1 then do
          let i6 ← i + 1#usize
          arena.inductives.block_parts.nidx_vec_beq_off a off b i6
        else ok false) = ok o) :
    o = ((a.val.drop (off.val + i.val)).map absNIdx == (b.val.drop i.val).map absNIdx) := by
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ha1, ha2⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hn)
  obtain ⟨hb1', hb2⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hn1)
  have hav : a.val[off.val + i.val] = n := by
    rw [← ha2]; congr 1; exact hi1v.symm
  rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hi, List.map_cons,
    List.map_cons, hav, hb2]
  have hbv : b1 = (absNIdx n == absNIdx n1) := nidx_eq2_abs hb1
  cases hbb : b1
  · rw [hbb] at h hbv
    rw [if_neg (by simp), Result.ok.injEq] at h
    rw [← h, List.cons_beq_cons, ← hbv]; rfl
  · rw [hbb] at h hbv
    rw [if_pos (by simp)] at h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
    rw [ih i2 o hi2v h, hi2v, List.cons_beq_cons, ← hbv, Bool.true_and,
      show off.val + (i.val + 1) = off.val + i.val + 1 by omega]

/-- `nidx_vec_beq_off a off b i` compares `a` from `off + i` with `b` from `i`. -/
theorem nidx_vec_beq_off_abs {a b : alloc.vec.Vec arena.handle.NIdx} {off : Std.Usize} :
    ∀ (i : Std.Usize) (o : Bool),
      arena.inductives.block_parts.nidx_vec_beq_off a off b i = ok o →
      o = ((a.val.drop (off.val + i.val)).map absNIdx == (b.val.drop i.val).map absNIdx) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) b.val.length
    (fun i (_ : Unit) => ∀ o, arena.inductives.block_parts.nidx_vec_beq_off a off b i = ok o →
      o = ((a.val.drop (off.val + i.val)).map absNIdx == (b.val.drop i.val).map absNIdx))
    ?_ ?_ i ()
  · intro i _ hn o h
    rw [arena.inductives.block_parts.nidx_vec_beq_off.eq_def] at h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi1v : i1.val = off.val + i.val := ConRon.Refine.Nat.uadd_val hi1
    rw [List.drop_eq_nil_of_le hn]
    by_cases ha : a.val.length ≤ i1.val
    · rw [if_pos (by scalar_tac), if_pos (by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by omega)]; rfl
    · rw [if_neg (by scalar_tac), if_neg (by scalar_tac), if_pos (by scalar_tac),
        Result.ok.injEq] at h
      rw [← h, List.drop_eq_getElem_cons (by omega : off.val + i.val < a.val.length)]; rfl
  · intro i _ hi ih o h
    rw [arena.inductives.block_parts.nidx_vec_beq_off.eq_def] at h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi1v : i1.val = off.val + i.val := ConRon.Refine.Nat.uadd_val hi1
    by_cases ha : a.val.length ≤ i1.val
    · rw [if_pos (by scalar_tac), if_neg (by scalar_tac), if_pos (by scalar_tac),
        Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by omega), List.drop_eq_getElem_cons hi]; rfl
    · rw [if_neg (by scalar_tac), if_neg (by scalar_tac), if_neg (by scalar_tac)] at h
      exact nidx_vec_beq_off_cmp hi1v hi (by omega) (fun j o hj h => ih j () hj o h) h

/-! ## The recogniser's readers -/

/-- `rec_target_of` ⊑ `recTargetOf`. -/
@[lockstep] theorem rec_target_of_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx) (m_i : Std.U64)
    (ty : arena.handle.EIdx) :
    LSR pers (fun a b => b = absU a)
      (arena.inductives.block_parts.rec_target_of pers st names m_i ty) st lst
      (recTargetOf (absNIdxL names) (absU m_i) (absEIdx ty)) := by
  apply LSR.of_LS
  rw [arena.inductives.block_parts.rec_target_of, recTargetOf]
  lockstep

attribute [local lockstep_inline] arena.inductives.block_parts.block_counts_rec
attribute [local lockstep_simp] absNatPair

set_option maxHeartbeats 2000000 in
/-- `block_counts` ⊑ `blockCounts?` (the Rust's `block_counts_rec` is its
second arm, unfolded in place). -/
@[lockstep] theorem block_counts_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n_pd k n_c n_r : Std.U64) (cv_t : arena.env.IConstantVal)
    (r : Option (Std.U64 × Std.U64)) :
    LSR pers (fun a b => b = a.map absNatPair)
      (arena.inductives.block_parts.block_counts pers st n_pd k n_c n_r cv_t r) st lst
      (blockCounts? (absU n_pd) (absU k) (absU n_c) (absU n_r) (absIConstantVal cv_t)
        (r.map absNatPair)) := by
  apply LSR.of_LS
  rw [arena.inductives.block_parts.block_counts, blockCounts?.eq_def]
  lockstep
  refine LS.pure ?_ hrel hinv
  simp_all [absNatPair, absU, absBinderL]

/-- `ctor_member` ⊑ `ctorMember?`. -/
@[lockstep] theorem ctor_member_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (lvls : arena.handle.LsIdx) (n_p : Std.U64) (c : arena.env.IConstantVal × Std.U64) :
    LSR pers (fun a b => b = a.map absU)
      (arena.inductives.block_parts.ctor_member pers st names lvls n_p c) st lst
      (ctorMember? (absNIdxL names) (absLsIdx lvls) (absU n_p) (absIConstantVal c.1, absU c.2)) := by
  apply LSR.of_LS
  obtain ⟨cv, n⟩ := c
  rw [arena.inductives.block_parts.ctor_member, ctorMember?]
  lockstep

theorem absRecsLFrom_cons {rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))} {i : Std.Usize} (hi : i.val < rs.val.length) :
    absRecsLFrom rs i = (absIConstantVal rs.val[i.val].1, absU rs.val[i.val].2.1,
      absU rs.val[i.val].2.2.1, rs.val[i.val].2.2.2.val.map absIRecRule) ::
      (rs.val.drop (i.val + 1)).map (fun p => (absIConstantVal p.1, absU p.2.1, absU p.2.2.1,
        p.2.2.2.val.map absIRecRule)) := by
  rw [absRecsLFrom, List.drop_eq_getElem_cons hi, List.map_cons]

/-- `rec_for_member` ⊑ `findM?` from the cursor on: the first recursor whose
major names member `m`, its `(mI, rP)`. -/
theorem rec_for_member_ls {pers st} (names : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))) (m : Std.U64) :
    ∀ (i : Std.Usize) lst, AStateRel₀ pers st lst → AStateInv pers st →
    LSR pers (fun a b => b = a.map absNatPair)
      (arena.inductives.block_parts.rec_for_member pers st names rs m i) st lst
      (do
        let q ← (absRecsLFrom rs i).findM? fun q => do
          pure ((← recTargetOf (absNIdxL names) q.2.1 q.1.type) == absU m)
        pure (q.map fun q => (q.2.1, q.2.2.1))) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) rs.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.map absNatPair)
        (arena.inductives.block_parts.rec_for_member pers st names rs m i) st lst
        (do
          let q ← (absRecsLFrom rs i).findM? fun q => do
            pure ((← recTargetOf (absNIdxL names) q.2.1 q.1.type) == absU m)
          pure (q.map fun q => (q.2.1, q.2.2.1)))) ?_ ?_ i ()
  · intro i _ hn lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.rec_for_member.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac)]
    rw [absRecsLFrom, List.drop_eq_nil_of_le hn, List.map_nil, List.findM?]
    lockstep
  · intro i _ hi ih lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.rec_for_member.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac)]
    rw [absRecsLFrom_cons hi, List.findM?]
    lockstep

/-- A read against `do let q ← X; pure (f q)` is a read against `X` at the
relation composed with `f`. -/
theorem LSR.of_map {α β γ : Type} {pers : arena.store.PersTier} {R : α → γ → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {X : AM β} {f : β → γ}
    (h : LSR pers R m st lst (do let q ← X; pure (f q))) :
    LSR pers (fun a q => R a (f q)) m st lst X := by
  intro o hm
  have h1 := h o hm
  cases o with
  | Err e =>
    intro k hk
    obtain ⟨le, hx, hle⟩ := h1 k hk
    refine ⟨le, ?_, hle⟩
    rw [StateT.run_bind] at hx
    cases hX : X.run lst with
    | error e' => rw [hX] at hx; simpa using hx
    | ok p => rw [hX] at hx; cases hx
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h3, h4⟩ := h1
    rw [StateT.run_bind] at hx
    cases hX : X.run lst with
    | error e' => rw [hX] at hx; cases hx
    | ok p =>
      obtain ⟨q, s⟩ := p
      rw [hX] at hx
      cases hx
      exact ⟨q, s, rfl, hR, h3, h4⟩

/-- `rec_for_member` from `0`: the Rust's `(mI, rP)` is the found recursor's. -/
@[lockstep] theorem rec_for_member_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))) (m : Std.U64) :
    LSR pers (fun a q => q.map (fun q => (q.2.1, q.2.2.1)) = a.map absNatPair)
      (arena.inductives.block_parts.rec_for_member pers st names rs m 0#usize) st lst
      ((absRecsL rs).findM? fun q => do
          pure ((← recTargetOf (absNIdxL names) q.2.1 q.1.type) == absU m)) := by
  have h := rec_for_member_ls names rs m 0#usize lst hrel hinv
  rw [absRecsLFrom_zero] at h
  exact LSR.of_map h

/-- `blockMemberCounts?` at a member, with the recursor search's answer
projected in one step (the twin's `let r := match q with …`). -/
theorem blockMemberCounts?_cons (nPd k nC : Nat) (names : List NIdx)
    (rs : List (IConstantVal × Nat × Nat × List IRecRule)) (m : Nat) (cvT : IConstantVal)
    (ts : List IConstantVal) :
    blockMemberCounts? nPd k nC names rs m (cvT :: ts) = (do
      let r ← (do
        let q ← rs.findM? fun q => do pure ((← recTargetOf names q.2.1 q.1.type) == m)
        pure (q.map fun q => (q.2.1, q.2.2.1)))
      match ← blockCounts? nPd k nC rs.length cvT r with
      | none => pure none
      | some c => do
        let ns ← blockMemberCounts? nPd k nC names rs (m + 1) ts
        pure (ns.map (c.2 :: ·))) := by
  rw [blockMemberCounts?, bind_assoc]
  refine am_bind_congr₂ rfl fun q => ?_
  rw [pure_bind]
  cases q <;>
  · refine am_bind_congr₂ rfl fun c => ?_
    cases c with
    | none => rfl
    | some c =>
      refine am_bind_congr₂ rfl fun ns => ?_
      cases ns <;> rfl

theorem absICVL_drop_cons {cv_ts : alloc.vec.Vec arena.env.IConstantVal} {m : Nat}
    (hm : m < cv_ts.val.length) :
    (absICVL cv_ts).drop m = absIConstantVal cv_ts.val[m] :: (absICVL cv_ts).drop (m + 1) := by
  rw [absICVL, List.drop_eq_getElem_cons (by simpa using hm)]
  simp

/-- `block_member_counts` ⊑ `blockMemberCounts?` from member `m` on, the
accumulated counts in front. -/
theorem block_member_counts_ls {pers st} (n_pd k n_c : Std.U64)
    (names : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))) (cv_ts : alloc.vec.Vec arena.env.IConstantVal) :
    ∀ (m : Std.U64) (out : alloc.vec.Vec Std.U64) lst, AStateRel₀ pers st lst →
      AStateInv pers st →
      LSR pers (fun a b => b = a.map absNatL)
        (arena.inductives.block_parts.block_member_counts pers st n_pd k n_c names rs m cv_ts out)
        st lst
        (do
          let r ← blockMemberCounts? (absU n_pd) (absU k) (absU n_c) (absNIdxL names)
            (absRecsL rs) (absU m) ((absICVL cv_ts).drop m.val)
          pure (r.map (absNatL out ++ ·))) := by
  refine cursor_induction (fun m : Std.U64 => m.val) cv_ts.val.length
    (fun m (out : alloc.vec.Vec Std.U64) => ∀ lst, AStateRel₀ pers st lst →
      AStateInv pers st →
      LSR pers (fun a b => b = a.map absNatL)
        (arena.inductives.block_parts.block_member_counts pers st n_pd k n_c names rs m cv_ts out)
        st lst
        (do
          let r ← blockMemberCounts? (absU n_pd) (absU k) (absU n_c) (absNIdxL names)
            (absRecsL rs) (absU m) ((absICVL cv_ts).drop m.val)
          pure (r.map (absNatL out ++ ·)))) ?_ ?_
  · intro m out hn lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.block_member_counts.eq_def,
      List.drop_eq_nil_of_le (by simpa [absICVL] using hn), blockMemberCounts?]
    lockstep
  · intro m out hm ih lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.block_member_counts.eq_def, absICVL_drop_cons hm,
      blockMemberCounts?_cons]
    lockstep
    rename_i sn out1 hout1
    refine LSR.tail_ls (ih a out1 (by simp [hP]) lst1 hrel hinv) ?_ (fun _ _ h => h)
    have ha : a.val = m.val + 1 := by simp [hP]
    rw [show absU a = m.val + 1 from ha, ha]
    refine am_bind_congr₂ rfl fun x => ?_
    cases x <;> simp [absNatL, hout1]

/-- `block_member_counts` from member `0` into an empty accumulator IS
`blockMemberCounts? … 0 cvTs`. -/
@[lockstep] theorem block_member_counts_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n_pd k n_c : Std.U64)
    (names : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))) (cv_ts : alloc.vec.Vec arena.env.IConstantVal) :
    LSR pers (fun a b => b = a.map absNatL)
      (arena.inductives.block_parts.block_member_counts pers st n_pd k n_c names rs 0#u64 cv_ts
        (alloc.vec.Vec.new _)) st lst
      (blockMemberCounts? (absU n_pd) (absU k) (absU n_c) (absNIdxL names) (absRecsL rs) 0
        (absICVL cv_ts)) := by
  have h := block_member_counts_ls n_pd k n_c names rs cv_ts 0#u64 (alloc.vec.Vec.new _) lst
    hrel hinv
  have e : (do
      let r ← blockMemberCounts? (absU n_pd) (absU k) (absU n_c) (absNIdxL names)
        (absRecsL rs) (absU (0#u64 : Std.U64)) ((absICVL cv_ts).drop (0#u64 : Std.U64).val)
      pure (r.map (absNatL (alloc.vec.Vec.new Std.U64) ++ ·)) : AM _) =
      blockMemberCounts? (absU n_pd) (absU k) (absU n_c) (absNIdxL names) (absRecsL rs) 0
        (absICVL cv_ts) := by
    simp [absNatL, absU]
  rwa [e] at h

end ConRon.Refine2
