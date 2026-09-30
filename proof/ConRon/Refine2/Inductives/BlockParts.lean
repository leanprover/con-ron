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

/-- `arena::monad::intern_n_node` ⊑ `internNNode` (restated from
`Inductives/Prims.lean`, which is not below this module). -/
@[lockstep] theorem bp_intern_n_node_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v) :
    LS pers (fun a b => b = absNIdx a) (arena.monad.intern_n_node pers st v) lst
      (Arena.internNNode (absNNodeView v)) :=
  LS.ofSim₀ fun _ h => intern_n_node_run₀ hrel hinv v hvwf h

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

theorem ctors_dup_twin
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

theorem members_dup_twin
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

theorem recs_dup_twin
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

theorem block_split_recs_twin (block : alloc.vec.Vec arena.env.IConstantInfo)
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

theorem block_split_ctors_twin (block : alloc.vec.Vec arena.env.IConstantInfo)
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

theorem block_split_twin (block : alloc.vec.Vec arena.env.IConstantInfo)
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

theorem member_names_twin (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape)
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

theorem shape_n_idxs_twin (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape)
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

/-- `nidx_vec_beq_off a 1 b 0`: `a`'s tail against `b`. -/
@[lockstep] theorem nidx_vec_beq_off_twin1 (a b : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.inductives.block_parts.nidx_vec_beq_off a 1#usize b 0#usize)
      (fun o => TwinEq ((a.val.drop 1).map absNIdx == b.val.map absNIdx) o) := by
  intro o h
  rw [TwinEq, nidx_vec_beq_off_abs _ o h]
  simp [usz_zero_val]

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

/-! ## `struct_parts::param_levels` (restated here: `Inductives/StructParts.lean`
is not below this module yet) -/

/-- `param_levels_go` ⊑ `paramLevels.go` from the cursor on, the accumulated
levels in front. -/
theorem bp_param_levels_go_ls {pers} (lps : alloc.vec.Vec arena.handle.NIdx) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.LIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absLIdxL a)
        (arena.inductives.struct_parts.param_levels_go pers st lps i out) lst
        (do let r ← paramLevels.go ((lps.val.drop i.val).map absNIdx); pure (absLIdxL out ++ r)) := by
  refine ls_cursor_acc lps absNIdx
    (fun (w : alloc.vec.Vec arena.handle.LIdx) L =>
      (do let r ← paramLevels.go L; pure (absLIdxL w ++ r) : AM (List LIdx)))
    (fun st i w => arena.inductives.struct_parts.param_levels_go pers st lps i w) ?_ ?_
  · intro st lst i w hn hrel hinv
    rw [arena.inductives.struct_parts.param_levels_go.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len lps by scalar_tac), paramLevels.go]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [arena.inductives.struct_parts.param_levels_go.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len lps by scalar_tac), paramLevels.go]
    lockstep

/-- `param_levels` ⊑ `paramLevels`. -/
@[lockstep] theorem bp_param_levels_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (lps : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => b = absLsIdx a) (arena.inductives.struct_parts.param_levels pers st lps)
      lst (paramLevels (absNIdxL lps)) := by
  have hgo := bp_param_levels_go_ls (pers := pers) lps 0#usize st lst (alloc.vec.Vec.new _)
    hrel hinv
  have e : (paramLevels.go ((lps.val.drop (0#usize : Std.Usize).val).map absNIdx) >>= fun r =>
      pure (absLIdxL (alloc.vec.Vec.new arena.handle.LIdx) ++ r) : AM _) =
      paramLevels.go (absNIdxL lps) := by
    simp [absLIdxL, absNIdxL]
  rw [e] at hgo
  rw [arena.inductives.struct_parts.param_levels, paramLevels]
  lockstep

/-! ## The groups -/

/-- `blockGroups` with its `filterM` predicate as one comparison. -/
theorem blockGroups_eq (names : List NIdx) (lvls : LsIdx) (nP k : Nat)
    (cs : List (IConstantVal × Nat)) :
    blockGroups names lvls nP k cs = if k == 1 then pure [cs] else
      (List.range k).mapM fun m => cs.filterM fun c =>
        ctorMember? names lvls nP c >>= fun o => pure (o == some m) := by
  rw [blockGroups]
  split
  · rfl
  · congr 1; funext m; congr 1; funext c
    refine am_bind_congr₂ rfl fun o => ?_
    cases o <;> simp

theorem absCtorsLFrom_cons {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    (hi : i.val < cs.val.length) :
    absCtorsLFrom cs i = (absIConstantVal cs.val[i.val].1, absU cs.val[i.val].2) ::
      (cs.val.drop (i.val + 1)).map (fun p => (absIConstantVal p.1, absU p.2)) := by
  rw [absCtorsLFrom, List.drop_eq_getElem_cons hi, List.map_cons]

/-- `block_group` ⊑ `filterM` (as `filterAuxM` with the reversed accumulator)
from the cursor on. -/
theorem block_group_ls {pers st} (names : alloc.vec.Vec arena.handle.NIdx)
    (lvls : arena.handle.LsIdx) (n_p m : Std.U64)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absCtorsL a)
        (arena.inductives.block_parts.block_group pers st names lvls n_p m cs i out) st lst
        (do
          let r ← List.filterAuxM (fun c =>
              ctorMember? (absNIdxL names) (absLsIdx lvls) (absU n_p) c >>= fun o =>
                pure (o == some (absU m)))
            (absCtorsLFrom cs i) (absCtorsL out).reverse
          pure r.reverse) := by
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i out => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absCtorsL a)
        (arena.inductives.block_parts.block_group pers st names lvls n_p m cs i out) st lst
        (do
          let r ← List.filterAuxM (fun c =>
              ctorMember? (absNIdxL names) (absLsIdx lvls) (absU n_p) c >>= fun o =>
                pure (o == some (absU m)))
            (absCtorsLFrom cs i) (absCtorsL out).reverse
          pure r.reverse)) ?_ ?_
  · intro i out hn lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.block_group.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, List.filterAuxM]
    lockstep
  · intro i out hi ih lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.block_group.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom_cons hi,
      List.filterAuxM]
    lockstep
    -- the constructor names another member: the twin's comparison is `false`
    rename_i t
    have e : (some (absU t) == some (absU m)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
      intro h; exact hc (by simp only [absU] at h; scalar_tac)
    have ha : a.val = i.val + 1 := by simp [hP]
    refine LSR.tail_ls (ih a out ha lst1 hrel hinv) ?_ (fun _ _ h => h)
    simp only [absU] at e
    rw [e, cond_false, absCtorsLFrom, ha]

/-- `block_group` from `0` into an empty accumulator IS the `filterM`. -/
@[lockstep] theorem block_group_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (lvls : arena.handle.LsIdx) (n_p m : Std.U64)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSR pers (fun a b => b = absCtorsL a)
      (arena.inductives.block_parts.block_group pers st names lvls n_p m cs 0#usize
        (alloc.vec.Vec.new _)) st lst
      ((absCtorsL cs).filterM fun c =>
        ctorMember? (absNIdxL names) (absLsIdx lvls) (absU n_p) c >>= fun o =>
          pure (o == some (absU m))) := by
  have h := block_group_ls (pers := pers) (st := st) names lvls n_p m cs 0#usize
    (alloc.vec.Vec.new _) lst hrel hinv
  rw [absCtorsLFrom_zero] at h
  exact h

/-- `block_groups_from` ⊑ `(List.range' m (k - m)).mapM` from member `m` on,
the accumulated groups in front. -/
theorem block_groups_from_ls {pers st} (names : alloc.vec.Vec arena.handle.NIdx)
    (lvls : arena.handle.LsIdx) (n_p k : Std.U64)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    ∀ (m : Std.U64) (out : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.val.map absCtorsL)
        (arena.inductives.block_parts.block_groups_from pers st names lvls n_p k m cs out) st lst
        (do
          let r ← (List.range' (absU m) (absU k - absU m)).mapM fun m =>
            (absCtorsL cs).filterM fun c =>
              ctorMember? (absNIdxL names) (absLsIdx lvls) (absU n_p) c >>= fun o =>
                pure (o == some m)
          pure (out.val.map absCtorsL ++ r)) := by
  refine cursor_induction (fun m : Std.U64 => m.val) k.val
    (fun m out => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.val.map absCtorsL)
        (arena.inductives.block_parts.block_groups_from pers st names lvls n_p k m cs out) st lst
        (do
          let r ← (List.range' (absU m) (absU k - absU m)).mapM fun m =>
            (absCtorsL cs).filterM fun c =>
              ctorMember? (absNIdxL names) (absLsIdx lvls) (absU n_p) c >>= fun o =>
                pure (o == some m)
          pure (out.val.map absCtorsL ++ r))) ?_ ?_
  · intro m out hn lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.block_groups_from.eq_def,
      if_pos (show m ≥ k by scalar_tac), show absU k - absU m = 0 by simp only [absU]; omega,
      List.range'_zero, List.mapM_nil]
    lockstep
  · intro m out hm ih lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.block_groups_from.eq_def,
      if_neg (show ¬ m ≥ k by scalar_tac),
      show absU k - absU m = (absU k - (absU m + 1)) + 1 by simp only [absU]; omega,
      List.range'_succ, List.mapM_cons]
    lockstep

/-- `block_groups` ⊑ `blockGroups` (at one member the Rust copies the list the
twin shares). -/
@[lockstep] theorem block_groups_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (lvls : arena.handle.LsIdx) (n_p k : Std.U64)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSR pers (fun a b => b = a.val.map absCtorsL)
      (arena.inductives.block_parts.block_groups pers st names lvls n_p k cs) st lst
      (blockGroups (absNIdxL names) (absLsIdx lvls) (absU n_p) (absU k) (absCtorsL cs)) := by
  have hf := block_groups_from_ls (pers := pers) (st := st) names lvls n_p k cs 0#u64
    (alloc.vec.Vec.new _) lst hrel hinv
  have e : absU (0#u64 : Std.U64) = 0 := rfl
  simp only [e, Nat.sub_zero, vec_new_val', List.map_nil, List.nil_append, bind_pure] at hf
  apply LSR.of_LS
  rw [arena.inductives.block_parts.block_groups, blockGroups_eq, List.range_eq_range']
  lockstep

/-! ## The members and the recursors -/

theorem zip_members_abs {cvs : alloc.vec.Vec arena.env.IConstantVal}
    {n_idxs : alloc.vec.Vec Std.U64}
    {groups : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.block_parts.MemberShape),
      arena.inductives.block_parts.zip_members cvs n_idxs groups i out = ok o →
      o.val.map absMemberShape = out.val.map absMemberShape ++
        ((((cvs.val.drop i.val).map absIConstantVal).zip ((n_idxs.val.drop i.val).map absU)).zip
          ((groups.val.drop i.val).map absCtorsL)).map
          (fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) cvs.val.length
    (fun i out => ∀ o, arena.inductives.block_parts.zip_members cvs n_idxs groups i out = ok o →
      o.val.map absMemberShape = out.val.map absMemberShape ++
        ((((cvs.val.drop i.val).map absIConstantVal).zip ((n_idxs.val.drop i.val).map absU)).zip
          ((groups.val.drop i.val).map absCtorsL)).map
          (fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape))) ?_ ?_
  · intro i out hn o h
    rw [arena.inductives.block_parts.zip_members.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cvs by scalar_tac), Result.ok.injEq] at h
    subst h
    simp [List.drop_eq_nil_of_le hn]
  · intro i out hi ih o h
    rw [arena.inductives.block_parts.zip_members.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cvs by scalar_tac)] at h
    by_cases h2 : n_idxs.val.length ≤ i.val
    · rw [if_pos (show i ≥ alloc.vec.Vec.len n_idxs by scalar_tac), Result.ok.injEq] at h
      subst h
      simp [List.drop_eq_nil_of_le h2]
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len n_idxs by scalar_tac)] at h
    by_cases h3 : groups.val.length ≤ i.val
    · rw [if_pos (show i ≥ alloc.vec.Vec.len groups by scalar_tac), Result.ok.injEq] at h
      subst h
      simp [List.drop_eq_nil_of_le h3]
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len groups by scalar_tac)] at h
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨g, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨g1, hg1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i5, hi5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi5v : i5.val = i.val + 1 := absSz_add_one hi5
    rw [ih i5 out1 hi5v o h, hi5v, ConRon.Refine.vec_push_val hout1]
    obtain ⟨_, hivv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hiv)
    obtain ⟨_, hnv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hn)
    obtain ⟨_, hgv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hg)
    rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons (by omega : i.val < n_idxs.val.length),
      List.drop_eq_getElem_cons (by omega : i.val < groups.val.length), hivv, hnv, hgv]
    have hg1' := ctors_dup_abs _ _ g1 hg1
    simp only [absCtorsL, absCtorsLFrom, vec_new_val', usz_zero_val, List.drop_zero, List.map_nil,
      List.nil_append] at hg1'
    simp [absMemberShape, i_constant_val_dup_abs hiv1, absCtorsL, hg1']

@[lockstep] theorem zip_members_twin0 (cvs : alloc.vec.Vec arena.env.IConstantVal)
    (n_idxs : alloc.vec.Vec Std.U64)
    (groups : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) :
    LSP (arena.inductives.block_parts.zip_members cvs n_idxs groups 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((((absICVL cvs).zip (absNatL n_idxs)).zip (groups.val.map absCtorsL)).map
          (fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape)))
        (o.val.map absMemberShape)) := by
  intro o h
  rw [TwinEq, zip_members_abs _ _ o h]
  simp [absICVL, absNatL]

/-- `rec_shapes` ⊑ the twin's `rs.mapM` from the cursor on, the accumulated
records in front. -/
theorem rec_shapes_ls {pers st} (names : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.inductives.block_parts.RecShape) lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.val.map absRecShape)
        (arena.inductives.block_parts.rec_shapes pers st names rs i out) st lst
        (do
          let r ← (absRecsLFrom rs i).mapM fun r => do
            let tgt ← recTargetOf (absNIdxL names) r.2.1 r.1.type
            pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.map (·.rhs)⟩ : RecShape)
          pure (out.val.map absRecShape ++ r)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) rs.val.length
    (fun i out => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.val.map absRecShape)
        (arena.inductives.block_parts.rec_shapes pers st names rs i out) st lst
        (do
          let r ← (absRecsLFrom rs i).mapM fun r => do
            let tgt ← recTargetOf (absNIdxL names) r.2.1 r.1.type
            pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.map (·.rhs)⟩ : RecShape)
          pure (out.val.map absRecShape ++ r))) ?_ ?_
  · intro i out hn lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.rec_shapes.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), absRecsLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, List.mapM_nil]
    lockstep
  · intro i out hi ih lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.block_parts.rec_shapes.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac), absRecsLFrom_cons hi,
      List.mapM_cons]
    lockstep
    rename_i tgt rhss hrhss out1 hout1
    have ha : a.val = i.val + 1 := by simp [hP]
    refine LSR.tail_ls (ih a out1 ha lst1 hrel hinv) ?_ (fun _ _ h => h)
    rw [absRecsLFrom, ha]
    refine am_bind_congr₂ rfl fun x => ?_
    simp [hout1, absRecShape]

/-- `rec_shapes` from `0` into an empty accumulator IS the twin's `rs.mapM`. -/
@[lockstep] theorem rec_shapes_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))) :
    LSR pers (fun a b => b = a.val.map absRecShape)
      (arena.inductives.block_parts.rec_shapes pers st names rs 0#usize (alloc.vec.Vec.new _))
      st lst
      ((absRecsL rs).mapM fun r => do
        let tgt ← recTargetOf (absNIdxL names) r.2.1 r.1.type
        pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.map (·.rhs)⟩ : RecShape)) := by
  have h := rec_shapes_ls (pers := pers) (st := st) names rs 0#usize (alloc.vec.Vec.new _) lst
    hrel hinv
  simp only [absRecsLFrom_zero, vec_new_val', List.map_nil, List.nil_append, bind_pure] at h
  exact h

/-! ## The recogniser -/

theorem absICVL_eq_cons {v : alloc.vec.Vec arena.env.IConstantVal} {c : IConstantVal}
    {t : List IConstantVal} (h : absICVL v = c :: t) :
    ∃ hw : (0#usize : Std.Usize).val < v.val.length,
      c = absIConstantVal (v.val[(0#usize : Std.Usize).val]'hw) := by
  rcases hv : v.val with _ | ⟨x, xs⟩
  · simp [absICVL, hv] at h
  · refine ⟨by simp [hv, usz_zero_val], ?_⟩
    simp only [absICVL, hv, List.map_cons, List.cons.injEq] at h
    simp [hv, usz_zero_val, h.1]

theorem absRecsL_eq_cons {v : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))} {c : IConstantVal} {a b : Nat} {r : List IRecRule}
    {t : List (IConstantVal × Nat × Nat × List IRecRule)} (h : absRecsL v = (c, a, b, r) :: t) :
    ∃ hw : (0#usize : Std.Usize).val < v.val.length,
      c = absIConstantVal (v.val[(0#usize : Std.Usize).val]'hw).1 := by
  rcases hv : v.val with _ | ⟨x, xs⟩
  · simp [absRecsL, hv] at h
  · refine ⟨by simp [hv, usz_zero_val], ?_⟩
    simp only [absRecsL, hv, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    simp [hv, usz_zero_val, h.1.1]

@[lockstep_simp] theorem absICVL_length (v : alloc.vec.Vec arena.env.IConstantVal) :
    (absICVL v).length = v.len.val := by simp [absICVL]
@[lockstep_simp] theorem absCtors3L_length (v : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) :
    (absCtors3L v).length = v.len.val := by simp [absCtors3L]
@[lockstep_simp] theorem absRecsL_length (v : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 ×
    Std.U64 × (alloc.vec.Vec arena.env.IRecRule))) :
    (absRecsL v).length = v.len.val := by simp [absRecsL]

/-- The first member's index count, as the Rust reads it (`n_idxs.len() == 0`
first). -/
theorem absNatL_headD (v : alloc.vec.Vec Std.U64) :
    (absNatL v).headD 0 = if v.len = 0#usize then 0 else absU (v.val[0]!) := by
  rcases hv : v.val with _ | ⟨x, xs⟩
  · have : v.len = 0#usize := by
      have h0 : v.len.val = 0 := by simp [hv]
      scalar_tac
    simp [absNatL, hv, this]
  · have : ¬ v.len = 0#usize := by
      intro h
      have h0 : v.len.val = 0 := by rw [h]; rfl
      simp [hv] at h0
    simp [absNatL, hv, this]

theorem absNatL_headD_zero {v : alloc.vec.Vec Std.U64} (h : v.len = 0#usize) :
    (absNatL v).headD 0 = 0 := by
  rw [absNatL_headD, if_pos h]

theorem map_headD_of_pos {α β : Type} (f : α → β) (l : List α) (d : β) (p : 0 < l.length) :
    (l.map f).headD d = f (l[0]'p) := by
  cases l with
  | nil => simp at p
  | cons x xs => rfl

theorem absNatL_headD_pos {v : alloc.vec.Vec Std.U64} (h : ¬ v.len = 0#usize) :
    (absNatL v).headD 0 = absU (v.val[0]'(by
      rcases hv : v.val with _ | ⟨x, xs⟩
      · exact absurd (by have h0 : v.len.val = 0 := by simp [hv]
                         scalar_tac) h
      · simp)) :=
  map_headD_of_pos absU v.val 0 _

section recogniser

theorem absIConstantVal_levelParams (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).levelParams = cv.level_params.val.map absNIdx := rfl
theorem absIConstantVal_name (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).name = absNIdx cv.name := rfl
theorem absIConstantVal_type (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).type = absEIdx cv.ty := rfl

attribute [local lockstep_simp] absNIdxL usz_zero_val absIConstantVal_levelParams
  absIConstantVal_name absIConstantVal_type

/-- The twin's eliminator read: `elim :: relps` with `relps == lps` and `elim`
fresh is the large eliminator. -/
def largeOf (rl0 lps : List NIdx) : Option NIdx :=
  match rl0 with
  | [] => none
  | elim :: relps => if relps == lps && !lps.contains elim then some elim else none

/-- The twin's last stretch of `blockShape?` (the Rust's `block_shape_elim`). -/
def elimTwin (members : List MemberShape) (recsL : List RecShape) (nPd : Nat) (s : LIdx)
    (isProp : Bool) (rl0 lps : List NIdx) : AM (Option BlockShape) :=
  match largeOf rl0 lps with
  | some elim => pure (some ⟨members, recsL, nPd, elim, s, true, isProp⟩)
  | none => do
    let anon ← internNNode .anonymous
    pure (some ⟨members, recsL, nPd, anon, s, false, isProp⟩)

theorem vec_len_pos_of_ne {α : Type} {v : alloc.vec.Vec α} (h : ¬ v.len = 0#usize) :
    0 < v.val.length := by
  rcases hv : v.val with _ | ⟨x, xs⟩
  · exact absurd (by have h0 : v.len.val = 0 := by simp [hv]
                     scalar_tac) h
  · simp

/-- `elimTwin` with the Rust's tests. -/
theorem elimTwin_eq (members : List MemberShape) (recsL : List RecShape) (nPd : Nat) (s : LIdx)
    (isProp : Bool) (rl0 lps : alloc.vec.Vec arena.handle.NIdx) :
    elimTwin members recsL nPd s isProp (absNIdxL rl0) (absNIdxL lps) =
      (if h : rl0.len = 0#usize then
        internNNode .anonymous >>= fun anon =>
          pure (some ⟨members, recsL, nPd, anon, s, false, isProp⟩)
      else if ((rl0.val.drop 1).map absNIdx == absNIdxL lps &&
          !(absNIdxL lps).contains (absNIdx (rl0.val[0]'(vec_len_pos_of_ne h)))) = true then
        pure (some ⟨members, recsL, nPd, absNIdx (rl0.val[0]'(vec_len_pos_of_ne h)), s, true,
          isProp⟩)
      else
        internNNode .anonymous >>= fun anon =>
          pure (some ⟨members, recsL, nPd, anon, s, false, isProp⟩) : AM (Option BlockShape)) := by
  by_cases h : rl0.len = 0#usize
  · have hv : rl0.val = [] := by
      have h0 : rl0.len.val = 0 := by rw [h]; rfl
      simpa using h0
    rw [dif_pos h, elimTwin]
    have e : absNIdxL rl0 = [] := by simp [absNIdxL, hv]
    rw [e]; rfl
  · rw [dif_neg h, elimTwin]
    have e : absNIdxL rl0 = absNIdx (rl0.val[0]'(vec_len_pos_of_ne h)) ::
        (rl0.val.drop 1).map absNIdx := by
      have hd := List.drop_eq_getElem_cons (vec_len_pos_of_ne h) (l := rl0.val)
      rw [List.drop_zero] at hd
      simp only [absNIdxL]
      conv_lhs => rw [hd]
      rfl
    rw [e]
    by_cases hc : ((List.map absNIdx (List.drop 1 rl0.val) == absNIdxL lps &&
        !(absNIdxL lps).contains (absNIdx (rl0.val[0]'(vec_len_pos_of_ne h)))) = true)
    · rw [if_pos hc]; simp only [largeOf, if_pos hc]
    · rw [if_neg hc]; simp only [largeOf, if_neg hc]

section elim

attribute [local lockstep_simp] usz_zero_val

/-- `block_shape_elim` ⊑ `elimTwin`. -/
@[lockstep] theorem block_shape_elim_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (members : alloc.vec.Vec arena.inductives.block_parts.MemberShape)
    (recs : alloc.vec.Vec arena.inductives.block_parts.RecShape) (n_p : Std.U64)
    (s : arena.handle.LIdx) (is_prop : Bool) (lps rl0 : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => b = a.map absBlockShape)
      (arena.inductives.block_parts.block_shape_elim pers st members recs n_p s is_prop lps rl0) lst
      (elimTwin (members.val.map absMemberShape) (recs.val.map absRecShape) (absU n_p)
        (absLIdx s) is_prop (absNIdxL rl0) (absNIdxL lps)) := by
  rw [arena.inductives.block_parts.block_shape_elim, elimTwin_eq]
  lockstep

end elim

/-- The twin's `isProp` read off `lvlEq? s zero`. -/
def isPropOf : Option Bool → Bool
  | some true => true
  | some false => false
  | none => false

theorem isPropOf_some (b : Bool) : isPropOf (some b) = b := by cases b <;> rfl
theorem isPropOf_none : isPropOf none = false := rfl

/-- The twin's `blockShape?` from the result sort on (the Rust's
`block_shape_sort`), with the block's pieces as parameters. -/
def bsTail (nPd : Nat) (cvTs : List IConstantVal) (cs : List (IConstantVal × Nat × Nat))
    (rs : List (IConstantVal × Nat × Nat × List IRecRule)) (names : List NIdx) (nIdxs : List Nat)
    (lps rl0 : List NIdx) (s : LIdx) : AM (Option BlockShape) := do
  let z ← zeroLevel
  let eq ← lvlEq? s z
  let isProp : Bool := isPropOf eq
  let ctors : List (IConstantVal × Nat) := cs.map fun c => (c.1, c.2.2)
  let lvls ← paramLevels lps
  let groups ← blockGroups names lvls nPd cvTs.length ctors
  let members : List MemberShape := ((cvTs.zip nIdxs).zip groups).map
    fun a => ⟨a.1.1, a.1.2, a.2⟩
  let recsL ← rs.mapM fun r => do
    let tgt ← recTargetOf names r.2.1 r.1.type
    pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.map (·.rhs)⟩ : RecShape)
  elimTwin members recsL nPd s isProp rl0 lps

section sort

attribute [local lockstep_simp] isPropOf_some isPropOf_none

set_option maxHeartbeats 4000000 in
/-- `block_shape_sort` ⊑ `bsTail`. -/
theorem block_shape_sort_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cv_ts : alloc.vec.Vec arena.env.IConstantVal)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64))
    (rs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule)))
    (names : alloc.vec.Vec arena.handle.NIdx) (n_idxs : alloc.vec.Vec Std.U64)
    (lps : alloc.vec.Vec arena.handle.NIdx) (n_p : Std.U64) (s : arena.handle.LIdx)
    (hrs : 0 < rs.val.length) :
    LS pers (fun a b => b = a.map absBlockShape)
      (arena.inductives.block_parts.block_shape_sort pers st cv_ts cs rs names n_idxs lps n_p s)
      lst
      (bsTail (absU n_p) (absICVL cv_ts) (absCtors3L cs) (absRecsL rs) (absNIdxL names)
        (absNatL n_idxs) (absNIdxL lps) ((rs.val[0]'hrs).1.level_params.val.map absNIdx)
        (absLIdx s)) := by
  rw [arena.inductives.block_parts.block_shape_sort]
  unfold bsTail
  lockstep

end sort

attribute [local lockstep_inline] arena.inductives.block_parts.block_shape_at

set_option maxHeartbeats 4000000 in
/-- `block_shape` ⊑ `blockShape?` (`block_shape_at` is its middle stretch,
unfolded in place; `block_shape_sort` is `bsTail`). -/
@[lockstep] theorem block_shape_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n_pd : Std.U64) (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => b = a.map absBlockShape)
      (arena.inductives.block_parts.block_shape pers st n_pd block) lst
      (blockShape? (absU n_pd) (absICIL block)) := by
  rw [arena.inductives.block_parts.block_shape, blockShape?]
  lockstep
  · split
    · rename_i heqT _
      exfalso
      have h0 := congrArg List.length heqT
      simp only [absICVL, List.length_map, List.length_cons] at h0
      have h1 := congrArg Std.UScalar.val hc
      simp only [alloc.vec.Vec.len_val] at h1
      simp at h1
      simp [h1] at h0
    · lockstep
  · split
    · rename_i heqR
      exfalso
      have h0 := congrArg List.length heqR
      simp only [absRecsL, List.length_map, List.length_cons] at h0
      have h1 := congrArg Std.UScalar.val hc
      simp only [alloc.vec.Vec.len_val] at h1
      simp at h1
      simp [h1] at h0
    · lockstep
  · split
    · rename_i cvTs rs' cvT0 ctail cvR0 rmi rrp rrules rtail heqT heqR
      obtain ⟨hw, rfl⟩ := absICVL_eq_cons heqT
      obtain ⟨hw', rfl⟩ := absRecsL_eq_cons heqR
      lockstep
      all_goals
        first
          | rw [absNatL_headD_zero (by assumption)]
          | rw [absNatL_headD_pos (by assumption)]
      all_goals lockstep
      all_goals try
        (refine LS.tail (block_shape_sort_ls hrel hinv _ _ _ _ _ _ _ _
          (by simpa [usz_zero_val] using hw')) ?_ (fun _ _ h => h)
         simp only [bsTail, isPropOf, absNIdxL, absICVL_length, usz_zero_val]
         rfl)
    · rename_i cvs _ rsv _ hcv _ _ _ _ _ _ hne
      exfalso
      have n1 : absICVL cvs ≠ [] := by
        simpa [absICVL] using List.ne_nil_of_length_pos (vec_len_pos_of_ne hcv)
      have n2 : absRecsL rsv ≠ [] := by
        simpa [absRecsL] using List.ne_nil_of_length_pos (vec_len_pos_of_ne hc)
      obtain ⟨c, t, h1⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨⟨r1, r2, r3, r4⟩, t', h2⟩ := List.exists_cons_of_ne_nil n2
      exact hne _ _ _ _ _ _ _ h1 h2

end recogniser

/-- **`block_parts::block_parts` ⊑ `blockParts?`** — the recogniser. -/
@[lockstep] theorem block_parts_ls {pers st lst} {n_pd : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = Option.map absBlockParts a)
      (arena.inductives.block_parts.block_parts pers st n_pd block) lst
      (blockParts? (absU n_pd) (absICIL block)) := by
  rw [arena.inductives.block_parts.block_parts, blockParts?]
  lockstep


end ConRon.Refine2

/-! ## The projections -/

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

@[lockstep] theorem complete_twin (p0 : arena.inductives.block_parts.BlockParts)
    (p1 : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.complete p0 p1)
      (fun o => TwinEq ((absBlockParts p0).complete (absBlockShape p1)) (absBlockParts o)) := by
  intro o h
  simp only [arena.inductives.block_parts.complete, Result.ok.injEq] at h
  subst h; rfl

@[lockstep] theorem shape_k_twin (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.shape_k p)
      (fun o => TwinEq (absBlockShape p).k (absU o)) := by
  intro o h
  simp only [arena.inductives.block_parts.shape_k, Result.ok.injEq] at h
  subst h
  simp only [TwinEq, BlockShape.k, absBlockShape, List.length_map, absU]
  rw [ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]

theorem num_ctors_of_abs {ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape} :
    ∀ (i : Std.Usize) (o : Std.U64), arena.inductives.block_parts.num_ctors_of ms i = ok o →
      absU o = numCtorsOf ((ms.val.drop i.val).map absMemberShape) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i (_ : Unit) => ∀ o, arena.inductives.block_parts.num_ctors_of ms i = ok o →
      absU o = numCtorsOf ((ms.val.drop i.val).map absMemberShape)) ?_ ?_ i ()
  · intro i _ hn o h
    rw [arena.inductives.block_parts.num_ctors_of.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le hn]; rfl
  · intro i _ hi ih o h
    rw [arena.inductives.block_parts.num_ctors_of.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac)] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, hmv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hm)
    simp only [lift, Result.ok.injEq] at hc
    subst hc
    have e1 := ih i2 () (absSz_add_one hi2) r hr
    have e2 := ConRon.Refine.Nat.uadd_val h
    rw [List.drop_eq_getElem_cons hi, List.map_cons, numCtorsOf, hmv, ← absSz_add_one hi2, ← e1]
    simp only [absU, e2, absMemberShape, absCtorsL, List.length_map]
    rw [ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]

@[lockstep] theorem num_ctors_of_twin0 (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) :
    LSP (arena.inductives.block_parts.num_ctors_of ms 0#usize)
      (fun o => TwinEq (numCtorsOf (ms.val.map absMemberShape)) (absU o)) := by
  intro o h
  rw [TwinEq, num_ctors_of_abs _ o h, usz_zero_val, List.drop_zero]

@[lockstep] theorem shape_num_ctors_twin (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.shape_num_ctors p)
      (fun o => TwinEq (absBlockShape p).numCtors (absU o)) := by
  intro o h
  rw [arena.inductives.block_parts.shape_num_ctors] at h
  rw [TwinEq, num_ctors_of_abs _ o h, usz_zero_val, List.drop_zero]; rfl

@[lockstep] theorem shape_lps_twin (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.shape_lps p)
      (fun o => TwinEq (absBlockShape p).lps (absNIdxL o)) := by
  intro o h
  rw [arena.inductives.block_parts.shape_lps] at h
  simp only [TwinEq, BlockShape.lps, absBlockShape]
  by_cases h0 : alloc.vec.Vec.len p.members = 0#usize
  · rw [if_pos h0, Result.ok.injEq] at h
    subst h
    have hv : p.members.val = [] := by
      have h1 := congrArg Std.UScalar.val h0
      simpa using h1
    simp [hv, absNIdxL]
  · rw [if_neg h0] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hmv := vec_index_some hm
    rw [usz_zero_val] at hmv
    rcases hv : p.members.val with _ | ⟨x, xs⟩
    · simp [hv] at hmv
    · simp only [hv, List.getElem?_cons_zero, Option.some.injEq] at hmv
      subst hmv
      simp [absNIdxL, absMemberShape, absIConstantVal, nidx_vec_dup_val h]

theorem all_ctors_abs {ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)),
      arena.inductives.block_parts.all_ctors ms i out = ok o →
      absCtorsL o = absCtorsL out ++
        (((ms.val.drop i.val).map absMemberShape).map (·.ctors)).flatten := by
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i out => ∀ o, arena.inductives.block_parts.all_ctors ms i out = ok o →
      absCtorsL o = absCtorsL out ++
        (((ms.val.drop i.val).map absMemberShape).map (·.ctors)).flatten) ?_ ?_
  · intro i out hn o h
    rw [arena.inductives.block_parts.all_ctors.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac), Result.ok.injEq] at h
    subst h
    simp [List.drop_eq_nil_of_le hn]
  · intro i out hi ih o h
    rw [arena.inductives.block_parts.all_ctors.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac)] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, hmv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hm)
    have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
    rw [ih i2 o1 hi2v o h, ctors_dup_abs _ _ o1 ho1, hi2v, List.drop_eq_getElem_cons hi, hmv]
    simp [absMemberShape, absCtorsL, absCtorsLFrom, usz_zero_val]

@[lockstep] theorem all_ctors_twin0 (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.all_ctors p.members 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (absBlockShape p).allCtors (absCtorsL o)) := by
  intro o h
  rw [TwinEq, all_ctors_abs _ _ o h]
  simp [BlockShape.allCtors, absBlockShape, absCtorsL, usz_zero_val]

theorem idx_at_abs {α : Type} (v : alloc.vec.Vec α) (r : Std.U64) (f : α → Std.U64)
    (o : Std.U64)
    (h : (do
      let i1 ← lift (UScalar.cast .U64 (alloc.vec.Vec.len v))
      if r < i1 then do
        let i2 ← lift (UScalar.cast .Usize r)
        let rs ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i2
        ok (f rs)
      else ok 0#u64) = ok o) :
    absU o = (match v.val[absU r]? with | some x => absU (f x) | none => 0) := by
  simp only [lift, bind_tc_ok] at h
  have hl : (UScalar.cast .U64 (alloc.vec.Vec.len v)).val = v.val.length := by
    rw [ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
  by_cases hr : r < UScalar.cast .U64 (alloc.vec.Vec.len v)
  · rw [if_pos hr] at h
    have hrv : r.val < v.val.length := by
      have : r.val < (UScalar.cast .U64 (alloc.vec.Vec.len v)).val := hr
      omega
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    have hxv := vec_index_some hx
    have hcv : (UScalar.cast .Usize r).val = r.val := by
      rw [Std.UScalar.cast_val_eq]
      refine Nat.mod_eq_of_lt ?_
      have : v.val.length ≤ Std.Usize.max := by scalar_tac
      have hmax : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
        simp only [Std.Usize.max, Std.Usize.numBits, Std.UScalarTy.Usize_numBits_eq]
      have : Std.UScalarTy.Usize.numBits = System.Platform.numBits := rfl
      rw [this]; omega
    rw [hcv] at hxv
    simp only [absU] at hxv ⊢
    rw [hxv]
  · rw [if_neg hr, Result.ok.injEq] at h
    subst h
    have hrv : ¬ r.val < v.val.length := by
      intro hc; apply hr; show r.val < _; omega
    simp only [absU] at hrv ⊢
    rw [List.getElem?_eq_none (by omega)]; rfl

@[lockstep] theorem rule_prefix_at_twin (p : arena.inductives.block_parts.BlockShape) (r : Std.U64) :
    LSP (arena.inductives.block_parts.rule_prefix_at p r)
      (fun o => TwinEq ((absBlockShape p).rulePrefixAt (absU r)) (absU o)) := by
  intro o h
  rw [arena.inductives.block_parts.rule_prefix_at] at h
  rw [TwinEq, idx_at_abs p.recs r (·.r_p) o h]
  simp only [BlockShape.rulePrefixAt, absBlockShape, List.getElem?_map]
  cases p.recs.val[absU r]? <;> rfl

@[lockstep] theorem major_idx_at_twin (p : arena.inductives.block_parts.BlockShape) (r : Std.U64) :
    LSP (arena.inductives.block_parts.major_idx_at p r)
      (fun o => TwinEq ((absBlockShape p).majorIdxAt (absU r)) (absU o)) := by
  intro o h
  rw [arena.inductives.block_parts.major_idx_at] at h
  rw [TwinEq, idx_at_abs p.recs r (·.m_i) o h]
  simp only [BlockShape.majorIdxAt, absBlockShape, List.getElem?_map]
  cases p.recs.val[absU r]? <;> rfl

/-- `with_sort` ⊑ `BlockShape.withSort`. -/
@[lockstep] theorem with_sort_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_parts.BlockShape)
    (s : arena.handle.LIdx) :
    LS pers (fun a b => b = absBlockShape a) (arena.inductives.block_parts.with_sort pers st p s)
      lst ((absBlockShape p).withSort (absLIdx s)) := by
  rw [arena.inductives.block_parts.with_sort, BlockShape.withSort]
  lockstep
  all_goals (split <;> (refine LS.pure ?_ ‹_› ‹_›; simp_all [absBlockShape]))

/-! ## The recursor records' pins -/

theorem rec_lps_ok_abs {p : arena.inductives.block_parts.BlockShape}
    {lps rl : alloc.vec.Vec arena.handle.NIdx} {o : Bool}
    (h : arena.inductives.block_parts.rec_lps_ok p lps rl = ok o) :
    o = if p.large then (absNIdxL rl == absNIdx p.elim :: absNIdxL lps)
      else (absNIdxL rl == absNIdxL lps) := by
  rw [arena.inductives.block_parts.rec_lps_ok] at h
  cases hl : p.large
  · rw [if_neg (by simp [hl])] at h
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact nidx_vec_beq_abs h
  · rw [if_pos hl] at h
    simp only [↓reduceIte]
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi2v := ConRon.Refine.Nat.uadd_val hi2
    by_cases hlen : alloc.vec.Vec.len rl = i2
    · rw [if_pos hlen] at h
      have hlv : rl.val.length = lps.val.length + 1 := by
        have := congrArg Std.UScalar.val hlen
        scalar_tac
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbv := nidx_eq2_abs hb
      have hnv := vec_index_some hn
      rw [usz_zero_val] at hnv
      rcases hv : rl.val with _ | ⟨x, xs⟩
      · simp [hv] at hlv
      · simp only [hv, List.getElem?_cons_zero, Option.some.injEq] at hnv
        subst hnv
        simp only [absNIdxL, hv, List.map_cons, List.cons_beq_cons]
        cases b
        · rw [if_neg (by simp), Result.ok.injEq] at h
          rw [← h, ← hbv, Bool.false_and]
        · rw [if_pos (by simp)] at h
          rw [nidx_vec_beq_off_abs _ o h, ← hbv, Bool.true_and, hv]
          simp
    · rw [if_neg hlen, Result.ok.injEq] at h
      rw [← h, eq_comm, beq_eq_false_iff_ne]
      intro hc
      have := congrArg List.length hc
      simp only [absNIdxL, List.length_map, List.length_cons] at this
      apply hlen
      scalar_tac

theorem block_rec_lps_ok_from_abs {p : arena.inductives.block_parts.BlockShape}
    {lps : alloc.vec.Vec arena.handle.NIdx} :
    ∀ (i : Std.Usize) (o : Bool),
      arena.inductives.block_parts.block_rec_lps_ok_from p lps i = ok o →
      o = ((p.recs.val.drop i.val).map absRecShape).all fun rc =>
        if p.large then rc.cvR.levelParams == absNIdx p.elim :: absNIdxL lps
        else rc.cvR.levelParams == absNIdxL lps := by
  have := vec_cursor_all p.recs (fun x => (fun rc : RecShape =>
        if p.large then rc.cvR.levelParams == absNIdx p.elim :: absNIdxL lps
        else rc.cvR.levelParams == absNIdxL lps) (absRecShape x))
    (arena.inductives.block_parts.block_rec_lps_ok_from p lps) ?_ ?_
  · intro i o h
    rw [this i o h, List.all_map]; rfl
  · bp_all_stop arena.inductives.block_parts.block_rec_lps_ok_from.eq_def p.recs
  · bp_all_head arena.inductives.block_parts.block_rec_lps_ok_from.eq_def p.recs
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := rec_lps_ok_abs hb
    have e : (if p.large then (absRecShape q).cvR.levelParams == absNIdx p.elim :: absNIdxL lps
        else (absRecShape q).cvR.levelParams == absNIdxL lps) = b := by
      rw [hbv]; rfl
    cases b
    · rw [if_neg (by simp), Result.ok.injEq] at h
      exact Or.inr ⟨e, h.symm⟩
    · rw [if_pos (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inl ⟨e, i2, absSz_add_one hi2, h⟩

@[lockstep] theorem block_rec_lps_ok_twin (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.block_rec_lps_ok p)
      (fun o => TwinEq (blockRecLpsOk (absBlockShape p)) o) := by
  intro o h
  rw [arena.inductives.block_parts.block_rec_lps_ok] at h
  obtain ⟨lps, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e := (shape_lps_twin p lps hl : (absBlockShape p).lps = absNIdxL lps)
  rw [TwinEq, block_rec_lps_ok_from_abs _ o h, blockRecLpsOk, e, usz_zero_val, List.drop_zero]
  simp only [absBlockShape, List.all_map]

/-- `block_rec_names_unreserved` ⊑ `blockRecNamesUnreserved` from the cursor on. -/
theorem block_rec_names_unreserved_ls {pers}
    (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.block_parts.block_rec_names_unreserved st rs i) lst
        (blockRecNamesUnreserved ((rs.val.drop i.val).map absRecShape)) := by
  refine ls_cursor rs absRecShape blockRecNamesUnreserved
    (fun st i => arena.inductives.block_parts.block_rec_names_unreserved st rs i) ?_ ?_
  · intro st lst i hn hrel hinv
    rw [arena.inductives.block_parts.block_rec_names_unreserved.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), blockRecNamesUnreserved]
    lockstep
  · intro st lst i hi hrel hinv ih
    rw [arena.inductives.block_parts.block_rec_names_unreserved.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac), blockRecNamesUnreserved]
    lockstep

@[lockstep] theorem block_rec_names_unreserved_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    LS pers (fun a b => b = a)
      (arena.inductives.block_parts.block_rec_names_unreserved st rs 0#usize) lst
      (blockRecNamesUnreserved (rs.val.map absRecShape)) := by
  have h := block_rec_names_unreserved_ls (pers := pers) rs 0#usize st lst hrel hinv
  rwa [usz_zero_val, List.drop_zero] at h

/-! ## The recursor names (the name part `rec`, restated from `Inductives/Prims.lean`) -/

@[lockstep] theorem bp_lift_to_slice_spec {n : Std.Usize} (X : Array Std.U32 n) :
    LSP (lift (Array.to_slice X)) (fun s => s.val = X.val) := by
  intro s h
  simp only [lift, Result.ok.injEq] at h
  subst h
  simp

@[lockstep] theorem bp_code_points_spec (s : Slice Std.U32) :
    LSP (kernel.core_types.code_points s) (fun v => v.val = s.val) :=
  fun _ h => ConRon.Refine.Env.code_points_val h

open Lean Elab Tactic in
/-- Fails unless the goal mentions a name-part string. -/
elab "bp_str_guard" : tactic => do
  let t ← getMainTarget
  unless t.containsConst (fun n => n == ``ConRon.Refine.absString ||
      n == ``ConRon.Refine.StrWF || n == ``NNodeViewWF || n == ``absNNodeView) do
    throwError "bp_str_guard: no string goal"

/-- The string side goals of a constant name part. -/
macro "bp_str_side" : tactic =>
  `(tactic| (bp_str_guard
             try simp only [global_simps] at *
             simp_all [Array.make, ConRon.Refine.absString, ConRon.Refine.StrWF, NNodeViewWF, absNNodeView]
             try decide))

macro_rules
  | `(tactic| lockstep_side_ext) => `(tactic| (bp_str_side; done))

theorem absMemberShape_cvT (m : arena.inductives.block_parts.MemberShape) :
    (absMemberShape m).cvT = absIConstantVal m.cv_t := rfl

attribute [local lockstep_simp] absMemberShape_cvT absIConstantVal_name

/-- `want_rec_names` ⊑ `members.mapM (internNNode (.str · "rec"))` from the cursor on. -/
theorem want_rec_names_ls {pers}
    (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.NIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absNIdxL a)
        (arena.inductives.block_parts.want_rec_names pers st ms i out) lst
        (do
          let r ← ((ms.val.drop i.val).map absMemberShape).mapM fun m =>
            internNNode (.str m.cvT.name "rec")
          pure (absNIdxL out ++ r)) := by
  refine ls_cursor_acc ms absMemberShape
    (fun (w : alloc.vec.Vec arena.handle.NIdx) L =>
      (do let r ← L.mapM fun m => internNNode (.str m.cvT.name "rec"); pure (absNIdxL w ++ r) :
        AM (List NIdx)))
    (fun st i w => arena.inductives.block_parts.want_rec_names pers st ms i w) ?_ ?_
  · intro st lst i w hn hrel hinv
    rw [arena.inductives.block_parts.want_rec_names.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac), List.mapM_nil]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [arena.inductives.block_parts.want_rec_names.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac), List.mapM_cons]
    lockstep

@[lockstep] theorem want_rec_names_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) :
    LS pers (fun a b => b = absNIdxL a)
      (arena.inductives.block_parts.want_rec_names pers st ms 0#usize (alloc.vec.Vec.new _)) lst
      ((ms.val.map absMemberShape).mapM fun m => internNNode (.str m.cvT.name "rec")) := by
  have h := want_rec_names_ls (pers := pers) ms 0#usize st lst (alloc.vec.Vec.new _) hrel hinv
  simp only [usz_zero_val, List.drop_zero, absNIdxL, vec_new_val', List.map_nil, List.nil_append,
    bind_pure] at h
  exact h

/-- `block_rec_name_set_ok` ⊑ `blockRecNameSetOk`. -/
@[lockstep] theorem block_rec_name_set_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (members : alloc.vec.Vec arena.inductives.block_parts.MemberShape)
    (recs : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    LS pers (fun a b => b = a)
      (arena.inductives.block_parts.block_rec_name_set_ok pers st members recs) lst
      (blockRecNameSetOk (members.val.map absMemberShape) (recs.val.map absRecShape)) := by
  rw [arena.inductives.block_parts.block_rec_name_set_ok, blockRecNameSetOk]
  lockstep
  have hlen : ∀ (x y : alloc.vec.Vec arena.handle.NIdx), x.len = y.len →
      x.val.length = y.val.length := fun x y h => by
    have := congrArg Std.UScalar.val h
    simpa using this
  have hl := hlen _ _ ‹alloc.vec.Vec.len _ = alloc.vec.Vec.len _›
  refine LS.pure ?_ ‹_› ‹_›
  simp only [absNIdxL, List.length_map, hl, beq_self_eq_true, Bool.true_and, Bool.and_true]

end ConRon.Refine2
