/-
# `ConRon.Refine2.Inductives.BlockInstall` — Theorem 2 for `arena::inductives::block_install`

**Task #105** (DESIGN.md §8.2, Theorem 2).
`crates/con-ron-core/src/arena/inductives/block_install.rs` (25 functions)
against `proof/ConRon/Arena/Inductives/BlockInstall.lean`: the capability record
per member, official's `is_rec`, the formers' stage, the constructors' stage,
the positivity check on the stored constructors, the index sorts and the
constructors' cons.

## Audit

No divergence in the order or the set of effectful operations, and every
decline has the twin's kind (`internal`/`invalid`) and message.  The Rust-only
steps are pure: repeated `members[mi]`/`ctors[0]` reads and `dup2`s in
`block_caps_at`, `block_shape_dup` before `with_sort`, the `dup2` before
`intern_e_sort` in `check_block_tele`, the list copies (`ctor_name_list`,
`tele_vals`, `split_outs`/`split_kinds`/`kinds_dup`/`split_nfs`).

## Shapes

* **Inline `map`s** (`ctor_name_list`, `tele_vals`, `split_*`, `kinds_dup`):
  copy loops, stated as `TwinEq`s of the twin's `map` (`vec_cursor_copy`);
  `tele_vals` onto `[cv_ta0]` is `cvTa₀ :: cvs.map (·.1)`
  (`tele_vals_cons_abs`, used in place inside `check_block_inds_ls`).
* **`block_caps_at`**: the Rust tests `mi < len && ctors.len() == 1` where the
  twin matches `members[mi]?` and `[c]`, and builds the record by branches
  (Aeneas lowers `rule_k` through a tuple).  The proof decides the Rust's tests
  first (`bi_vec_index_eq`), then zips; the leaves compare the records field
  by field (`bi_caps_leaf`, `bi_caps_leaf1`).  The answer carries the
  `sort_z`'s `PropWhenWF` (`ifenv_push`'s `IConstantInfoWF`).
* **Cursor loops against structural recursion** (`ctors/members_mention_any`,
  `check_block_teles`, `check_block_agree`, `cons_block_inds`,
  `check_block_ctors`, `check_abs_ctor_sorts(_all)`, `check_block_idx_sorts`,
  `cons_block_ctors`): stated at the cursor (`(v.val.drop i).map abs`), with
  the accumulator in front where the Rust pushes; the zipped twins
  (`checkBlockCtors`, `checkAbsCtorSorts(All)`, `checkBlockIdxSorts`) stop at
  the shorter list exactly as the Rust's two tests do.  The callers' forms
  (`…_ls0`, `…_new_ls`) are separate `@[lockstep]` lemmas.
* **`check_block_inds`**: the Rust's `len == 0` / `members[0]` against the
  twin's `ms₀ :: rest` match is decided first; the Rust calls
  `check_block_teles` at cursor `1` where the twin recurses on `rest`.
* **`vis`**: `shape_nest_ctx` stores its `vis` in `NestCtx.vis`, which
  `absNestCtx` drops — its answer carries `a.vis = vis`; `block_nest_ctx`'s
  answer carries `absU ctx.vis = lf.visibleBelow` (what `CoreCtx ctx.vis rf lf`
  needs beside `IFEnvRelI rf lf`).
* **`pi_doms_mention_any`** takes the twin's fuel (`coreWalkFuel`), one unit per
  binder: induction on the fuel.
* **Environments** are `IFEnvRelI rf lf`; `cons_block_inds`,
  `check_block_inds` and `cons_block_ctors` answer `IFEnvRelI` of the extended
  environments.  `cons_block_ctors` is pure on both sides (`LSP`).
-/
import ConRon.Refine2.Inductives.PositivityNest
import ConRon.Refine2.Inductives.SumInstall
import ConRon.Refine2.Inductives.BlockRec
import ConRon.Arena.Inductives.BlockInstall

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

attribute [local lockstep_simp] Lockstep.core_walk_fuel_val absMemberShape_cvT
@[local lockstep_simp] theorem absMemberShape_nIdx (m : arena.inductives.block_parts.MemberShape) :
    (absMemberShape m).nIdx = absU m.n_idx := rfl
@[local lockstep_simp] theorem absMemberShape_ctors (m : arena.inductives.block_parts.MemberShape) :
    (absMemberShape m).ctors = absCtorsL m.ctors := rfl

/-! ## The Rust-only list builders (the twin's inline `map`s) -/

theorem ctor_name_list_abs {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      arena.inductives.block_install.ctor_name_list cs i out = ok o →
      absNIdxL o = absNIdxL out ++ ((cs.val.drop i.val).map fun p => absNIdx p.1.name) := by
  have := vec_cursor_copy cs absNIdx (fun p => absNIdx p.1.name)
    (arena.inductives.block_install.ctor_name_list cs) ?_ ?_
  · intro i out o h
    simpa [absNIdxL] using this i out o h
  · bp_copy_stop arena.inductives.block_install.ctor_name_list.eq_def cs
  · bp_copy_head arena.inductives.block_install.ctor_name_list.eq_def cs
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_nidx _ _ hn], h⟩

/-- `ctor_name_list` from `0` is `blockCapsAt`'s `cs.map (·.1.name)`. -/
@[lockstep] theorem ctor_name_list_twin0 (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSP (arena.inductives.block_install.ctor_name_list cs 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((absCtorsL cs).map (·.1.name)) (absNIdxL o)) := by
  intro o h
  rw [TwinEq, ctor_name_list_abs _ _ o h]
  simp [absNIdxL, absCtorsL, absIConstantVal]

theorem tele_vals_abs {cvs : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.env.IConstantVal),
      arena.inductives.block_install.tele_vals cvs i out = ok o →
      absICVL o = absICVL out ++ ((cvs.val.drop i.val).map fun p => absIConstantVal p.1) := by
  have := vec_cursor_copy cvs absIConstantVal (fun p => absIConstantVal p.1)
    (arena.inductives.block_install.tele_vals cvs) ?_ ?_
  · intro i out o h
    simpa [absICVL] using this i out o h
  · bp_copy_stop arena.inductives.block_install.tele_vals.eq_def cvs
  · bp_copy_head arena.inductives.block_install.tele_vals.eq_def cvs
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      i_constant_val_dup_abs hn, h⟩

/-! ## The capability record: `block_caps_at` -/


theorem bi_vec_index_eq {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) (k : Nat)
    (hi : i.val = k) (hk : k < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok v.val[k] := by
  subst hi
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
  simp [List.getElem?_eq_getElem hk]

/-- The default-record arm's leaf: the Rust's `{ default with all, nparams,
ctors }` against the twin's record literal. -/
macro "bi_caps_leaf" : tactic => `(tactic| (
  refine LS.pure ⟨?_, by assumption⟩ (by assumption) (by assumption)
  simp only [TwinEq, absIIndCaps, IIndCaps.mk.injEq] at *
  simp_all [absBlockShape, alloc.vec.Vec.new, absNIdxL, absU, absIConstantVal_name]))

/-- The one-constructor arm's leaf: the Rust's record, built by branches, against
the twin's `&&`/`if` record. -/
macro "bi_caps_leaf1" : tactic => `(tactic| (
  refine LS.pure ⟨?_, by simp_all⟩ (by assumption) (by assumption)
  simp only [TwinEq, pn_u64_bne_zero] at *
  simp_all [absIIndCaps, absBlockShape, BlockShape.k, absNIdxL, absU, alloc.vec.Vec.new,
    absIConstantVal_name]))

set_option maxHeartbeats 3000000 in
/-- `block_caps_at` ⊑ `blockCapsAt` — the capability record of member `mi`.
The Rust tests `mi < len && ctors.len() == 1` where the twin matches
`members[mi]?` and `[c]`: the Rust's tests are decided first. -/
@[lockstep] theorem block_caps_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_parts.BlockShape) (mi : Std.U64)
    (is_rec : Bool) :
    LS pers (fun a b => b = absIIndCaps a ∧ ConRon.Refine.PropWhenWF a.sort_z)
      (arena.inductives.block_install.block_caps_at pers st p mi is_rec) lst
      (blockCapsAt (absBlockShape p) (absU mi) is_rec) := by
  rw [arena.inductives.block_install.block_caps_at, blockCapsAt]
  by_cases hm : mi.val < p.members.val.length
  · have hget : (absBlockShape p).members[absU mi]? =
        some (absMemberShape p.members.val[mi.val]) := by
      show (p.members.val.map absMemberShape)[mi.val]? = _
      rw [List.getElem?_map, List.getElem?_eq_getElem hm]; rfl
    rw [hget]
    dsimp only
    have hI : (UScalar.cast .Usize mi : Std.Usize).val = mi.val := by
      rcases lift_cast_usize_of_u64 mi _ rfl with h | h
      · exact h
      · exfalso; have := p.members.property; scalar_tac
    have h1 : mi < UScalar.cast .U64 (alloc.vec.Vec.len p.members) := by
      have := lift_cast_u64_of_usize (alloc.vec.Vec.len p.members) _ rfl
      simp only [alloc.vec.Vec.len] at this
      scalar_tac
    have hidx := bi_vec_index_eq p.members (UScalar.cast .Usize mi) mi.val hI hm
    simp only [lift, bind_tc_ok, if_pos h1, hidx]
    generalize p.members.val[mi.val] = m
    rcases hc : m.ctors.val with _ | ⟨⟨cv, nf⟩, _ | ⟨c2, rest⟩⟩
    · have hlen : ¬ alloc.vec.Vec.len m.ctors = 1#usize := by
        intro h; have := congrArg (·.val) h; simp [alloc.vec.Vec.len, hc] at this
      rw [absMemberShape_ctors, absCtorsL, hc, List.map_nil]
      simp only [if_neg hlen]
      lockstep
      bi_caps_leaf
    · have hlen : alloc.vec.Vec.len m.ctors = 1#usize := by
        have : (alloc.vec.Vec.len m.ctors).val = 1 := by simp [alloc.vec.Vec.len, hc]
        scalar_tac
      have hidx0 : alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice (arena.env.IConstantVal × Std.U64))
          m.ctors 0#usize = ok (cv, nf) := by
        rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
        simp [hc]
      rw [absMemberShape_ctors, absCtorsL, hc, List.map_cons, List.map_nil]
      simp only [hlen, ↓reduceIte, hidx0, bind_tc_ok]
      lockstep
      all_goals bi_caps_leaf1
    · have hlen : ¬ alloc.vec.Vec.len m.ctors = 1#usize := by
        intro h; have := congrArg (·.val) h; simp [alloc.vec.Vec.len, hc] at this
      rw [absMemberShape_ctors, absCtorsL, hc, List.map_cons, List.map_cons]
      simp only [if_neg hlen]
      lockstep
      bi_caps_leaf
  · have hget : (absBlockShape p).members[absU mi]? = none := by
      show (p.members.val.map absMemberShape)[mi.val]? = _
      rw [List.getElem?_eq_none (by simp; omega)]
    rw [hget]
    dsimp only
    lockstep
    bi_caps_leaf

/-! ## Official's `is_rec`: `pi_doms_mention_any`, `ctors_mention_any`,
`members_mention_any`, `block_raw_rec` -/

/-- `pi_doms_mention_any` ⊑ `piDomsMentionAny`, at the same fuel. -/
@[lockstep] theorem pi_doms_mention_any_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64)
    (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = a)
      (arena.inductives.block_install.pi_doms_mention_any pers st names fuel e) st lst
      (piDomsMentionAny (absNIdxL names) (absU fuel) (absEIdx e)) := by
  induction hf : fuel.val generalizing fuel e lst with
  | zero =>
    apply LSR.of_LS
    rw [arena.inductives.block_install.pi_doms_mention_any.eq_def, if_pos (by scalar_tac),
      show absU fuel = 0 from hf, piDomsMentionAny]
    lockstep
  | succ n ih =>
    apply LSR.of_LS
    rw [arena.inductives.block_install.pi_doms_mention_any.eq_def, if_neg (by scalar_tac),
      show absU fuel = n + 1 from hf, piDomsMentionAny]
    lockstep

/-- `ctors_mention_any` ⊑ `blockRawRec`'s inner `anyM`, from the cursor on. -/
@[lockstep] theorem ctors_mention_any_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) (i : Std.Usize) :
    LSR pers (fun a b => b = a)
      (arena.inductives.block_install.ctors_mention_any pers st names cs i) st lst
      ((absCtorsLFrom cs i).anyM fun c => piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type) := by
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → LSR pers (fun a b => b = a)
      (arena.inductives.block_install.ctors_mention_any pers st names cs i) st lst
      ((absCtorsLFrom cs i).anyM fun c => piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type))
    ?_ ?_ i () lst hrel
  · intro i _ hn lst hrel
    apply LSR.of_LS
    rw [arena.inductives.block_install.ctors_mention_any.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, List.anyM]
    lockstep
  · intro i _ hlt ih lst hrel
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ lst, AStateRel₀ pers st lst →
        LSR pers (fun a b => b = a)
        (arena.inductives.block_install.ctors_mention_any pers st names cs j) st lst
        ((absCtorsLFrom cs j).anyM fun c =>
          piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type) :=
      fun j hj => ih j () hj
    clear ih
    apply LSR.of_LS
    rw [arena.inductives.block_install.ctors_mention_any.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, List.anyM]
    lockstep

/-- A member list as the twin's `List MemberShape`, from a cursor on. -/
def absMemberShapeLFrom (v : alloc.vec.Vec arena.inductives.block_parts.MemberShape)
    (i : Std.Usize) : List MemberShape :=
  (v.val.drop i.val).map absMemberShape

/-- `members_mention_any` ⊑ `blockRawRec`'s outer `anyM`, from the cursor on. -/
@[lockstep] theorem members_mention_any_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) (i : Std.Usize) :
    LSR pers (fun a b => b = a)
      (arena.inductives.block_install.members_mention_any pers st names ms i) st lst
      ((absMemberShapeLFrom ms i).anyM fun m => m.ctors.anyM fun c =>
        piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type) := by
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → LSR pers (fun a b => b = a)
      (arena.inductives.block_install.members_mention_any pers st names ms i) st lst
      ((absMemberShapeLFrom ms i).anyM fun m => m.ctors.anyM fun c =>
        piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type))
    ?_ ?_ i () lst hrel
  · intro i _ hn lst hrel
    apply LSR.of_LS
    rw [arena.inductives.block_install.members_mention_any.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac), absMemberShapeLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, List.anyM]
    lockstep
  · intro i _ hlt ih lst hrel
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ lst, AStateRel₀ pers st lst →
        LSR pers (fun a b => b = a)
        (arena.inductives.block_install.members_mention_any pers st names ms j) st lst
        ((absMemberShapeLFrom ms j).anyM fun m => m.ctors.anyM fun c =>
          piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type) :=
      fun j hj => ih j () hj
    clear ih
    apply LSR.of_LS
    rw [arena.inductives.block_install.members_mention_any.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac), absMemberShapeLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, List.anyM]
    lockstep
    cases b
    · have ha : a.val = i.val + 1 := by scalar_tac
      exact LSR.tail_ls (ih' _ ha _ hrel) (by simp only [absMemberShapeLFrom, ha, absNIdxL])
        (fun _ _ h => h)
    · exact absurd rfl hc

@[local lockstep_simp] theorem absBlockParts_shape (p : arena.inductives.block_parts.BlockParts) :
    (absBlockParts p).shape = absBlockShape p.shape := rfl
attribute [local lockstep_simp] absBlockShape_members

/-- `block_raw_rec` ⊑ `blockRawRec` — official's `is_rec`. -/
@[lockstep] theorem block_raw_rec_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_parts.BlockParts) :
    LSR pers (fun a b => b = a)
      (arena.inductives.block_install.block_raw_rec pers st p) st lst
      (blockRawRec (absBlockParts p)) := by
  apply LSR.of_LS
  rw [arena.inductives.block_install.block_raw_rec, blockRawRec]
  lockstep

/-! ## Stage 1: the formers -/

theorem bi_hvis {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) :
    absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm


/-- `check_block_tele` ⊑ `checkBlockTele`: one member's type former. -/
@[lockstep] theorem check_block_tele_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (n_p : Std.U64) (ms : arena.inductives.block_parts.MemberShape) :
    LS pers (fun a b => b = (absIConstantVal a.1, absLIdx a.2))
      (arena.inductives.block_install.check_block_tele pers st mode rf n_p ms) lst
      (checkBlockTele (ConRon.Refine.absMode mode) lf (absU n_p) (absMemberShape ms)) := by
  have hvis := bi_hvis hfe
  rw [arena.inductives.block_install.check_block_tele, checkBlockTele]
  lockstep

/-- The checked formers with their sorts, `Vec<(IConstantVal, LIdx)>`. -/
def absTeleL (v : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)) :
    List (IConstantVal × LIdx) :=
  v.val.map fun p => (absIConstantVal p.1, absLIdx p.2)

theorem check_block_teles_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf lf} {n_p : Std.U64}
      {ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape} {i : Std.Usize}
      {out : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)},
      ms.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf →
      LS pers (fun a b => b = absTeleL a)
        (arena.inductives.block_install.check_block_teles pers st mode rf n_p ms i out) lst
        (do
          let q ← checkBlockTeles (ConRon.Refine.absMode mode) lf (absU n_p)
            (absMemberShapeLFrom ms i)
          pure (absTeleL out ++ q)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf lf n_p ms i out hn hrel hinv hfe
    rw [arena.inductives.block_install.check_block_teles, if_pos (by scalar_tac),
      absMemberShapeLFrom, vecFrom_nil _ _ _ (by omega), checkBlockTeles]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf lf n_p ms i out hn hrel hinv hfe
    rw [arena.inductives.block_install.check_block_teles, if_neg (by scalar_tac),
      absMemberShapeLFrom, vecFrom_cons _ _ _ (by omega), checkBlockTeles]
    lockstep
    rename_i o1 ho1
    have ha : a.val = i.val + 1 := by scalar_tac
    refine LS.tail (ih (i := a) (out := o1) (by omega) hrel hinv hfe) ?_ (fun _ _ h => h)
    simp only [absMemberShapeLFrom, ha, absTeleL, ho1, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- `check_block_teles` ⊑ `checkBlockTeles` from the cursor on, the checked
formers accumulated in front (the Rust pushes, the twin conses on the way
out). -/
@[lockstep] theorem check_block_teles_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (n_p : Std.U64)
    (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) (i : Std.Usize)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)) :
    LS pers (fun a b => b = absTeleL a)
      (arena.inductives.block_install.check_block_teles pers st mode rf n_p ms i out) lst
      (do
        let q ← checkBlockTeles (ConRon.Refine.absMode mode) lf (absU n_p)
          (absMemberShapeLFrom ms i)
        pure (absTeleL out ++ q)) :=
  check_block_teles_aux _ rfl hrel hinv hfe

/-- `j - 1` as a plain value equation (the `lockstep` respelling of a
`TwinEq` reads `↑a = e` facts, not conjunctions). -/
theorem bi_u64_sub_one (x : Std.U64) : LSP (x - 1#u64) (fun z => z.val = x.val - 1) := by
  intro z h
  exact (ConRon.Refine.Nat.usub_val h).2

attribute [local lockstep high] bi_u64_sub_one

attribute [local lockstep_simp] IndInstPrims.unwrapOr_some' IndInstPrims.unwrapOr_none'

/-- `check_block_doms_at` ⊑ `checkBlockDomsAt`, on the binder count. -/
@[lockstep] theorem check_block_doms_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (off : Std.U64) (fvs doms : alloc.vec.Vec arena.handle.EIdx)
    (j : Std.U64) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_install.check_block_doms_at pers st mode rf off fvs doms j) lst
      (checkBlockDomsAt (ConRon.Refine.absMode mode) lf (absU off) (absEIdxL fvs)
        (absEIdxL doms) (absU j)) := by
  have hvis := bi_hvis hfe
  induction hj : j.val generalizing j st lst with
  | zero =>
    rw [arena.inductives.block_install.check_block_doms_at.eq_def, if_pos (by scalar_tac),
      show absU j = 0 from hj, checkBlockDomsAt]
    lockstep
  | succ n ih =>
    rw [arena.inductives.block_install.check_block_doms_at.eq_def, if_neg (by scalar_tac),
      show absU j = n + 1 from hj, checkBlockDomsAt]
    obtain rfl : n = j.val - 1 := by omega
    clear hj
    lockstep
    rename_i k hk _ _ _ _ _ _
    refine LS.tail (ih hrel hinv k hk) ?_ (fun _ _ h => h)
    simp only [absEIdxL, absU, hk]

/-- `check_block_agree` ⊑ `checkBlockAgree`, the other members from the
cursor on. -/
@[lockstep] theorem check_block_agree_ls {pers} (mode : kernel.env.CheckMode)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) (n_p : Std.U64)
    (cv_ta0 : arena.env.IConstantVal) (s0 : arena.handle.LIdx)
    (rest : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun _ _ => True)
        (arena.inductives.block_install.check_block_agree pers st mode rf n_p cv_ta0 s0 rest i) lst
        (checkBlockAgree (ConRon.Refine.absMode mode) lf (absU n_p) (absIConstantVal cv_ta0)
          (absLIdx s0) ((rest.val.drop i.val).map fun p => (absIConstantVal p.1, absLIdx p.2))) := by
  refine ls_cursor rest (fun p => (absIConstantVal p.1, absLIdx p.2))
    (checkBlockAgree (ConRon.Refine.absMode mode) lf (absU n_p) (absIConstantVal cv_ta0) (absLIdx s0))
    (fun st i => arena.inductives.block_install.check_block_agree pers st mode rf n_p cv_ta0 s0 rest i)
    ?_ ?_
  · intro st lst i hn hrel hinv
    rw [arena.inductives.block_install.check_block_agree.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rest by scalar_tac), checkBlockAgree]
    lockstep
  · intro st lst i hi hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun _ _ => True)
          (arena.inductives.block_install.check_block_agree pers st' mode rf n_p cv_ta0 s0 rest j) lst'
          (checkBlockAgree (ConRon.Refine.absMode mode) lf (absU n_p) (absIConstantVal cv_ta0)
            (absLIdx s0) ((rest.val.drop j.val).map fun p => (absIConstantVal p.1, absLIdx p.2))) := ih
    clear ih
    have hvis := bi_hvis hfe
    rw [arena.inductives.block_install.check_block_agree.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rest by scalar_tac), checkBlockAgree]
    lockstep

/-- `cons_block_inds` ⊑ `consBlockInds` from the cursor on: the formers
pushed in block order, each with its capability record. -/
@[lockstep] theorem cons_block_inds_ls {pers} (p1 : arena.inductives.block_parts.BlockShape)
    (is_rec : Bool) (cv_tas : alloc.vec.Vec arena.env.IConstantVal) :
    ∀ (i : Std.Usize) (fe : arena.env.IFEnv) (lf : IFEnv) st lst, IFEnvRelI fe lf →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => IFEnvRelI a b)
        (arena.inductives.block_install.cons_block_inds pers st p1 is_rec cv_tas i fe) lst
        (consBlockInds (absBlockShape p1) is_rec (absICVLFrom cv_tas i) i.val lf) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) cv_tas.val.length
    (fun i (_ : Unit) => ∀ (fe : arena.env.IFEnv) (lf : IFEnv) st lst, IFEnvRelI fe lf →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => IFEnvRelI a b)
        (arena.inductives.block_install.cons_block_inds pers st p1 is_rec cv_tas i fe) lst
        (consBlockInds (absBlockShape p1) is_rec (absICVLFrom cv_tas i) i.val lf)) ?_ ?_ i ()
  · intro i _ hn fe lf st lst hfe hrel hinv
    rw [arena.inductives.block_install.cons_block_inds.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cv_tas by scalar_tac), absICVLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, consBlockInds]
    lockstep
  · intro i _ hlt ih fe lf st lst hfe hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ (fe : arena.env.IFEnv) (lf : IFEnv) st lst,
        IFEnvRelI fe lf → AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => IFEnvRelI a b)
          (arena.inductives.block_install.cons_block_inds pers st p1 is_rec cv_tas j fe) lst
          (consBlockInds (absBlockShape p1) is_rec (absICVLFrom cv_tas j) j.val lf) :=
      fun j hj => ih j () hj
    clear ih
    rw [arena.inductives.block_install.cons_block_inds.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cv_tas by scalar_tac), absICVLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, consBlockInds]
    lockstep
    rename_i caps _ cv1 hcv1 fe2 hfe2
    have ha : a.val = i.val + 1 := by scalar_tac
    refine LS.tail (ih' a ha fe2 (lf.push (IConstantInfo.indInfo
      (absIConstantVal cv_tas.val[i.val]) (absIIndCaps caps))) st1 lst1 ?_ hrel hinv) ?_
      (fun _ _ h => h)
    · have := hfe2.1; simp only [absIConstantInfo, hcv1] at this; exact this
    · simp only [absICVLFrom, ha]

/-- `check_block_teles` from an empty accumulator IS `checkBlockTeles` from
the cursor on (the install calls it at `1`, the twin on `rest`). -/
@[lockstep] theorem check_block_teles_new_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (n_p : Std.U64)
    (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) (i : Std.Usize) :
    LS pers (fun a b => b = absTeleL a)
      (arena.inductives.block_install.check_block_teles pers st mode rf n_p ms i
        (alloc.vec.Vec.new _)) lst
      (checkBlockTeles (ConRon.Refine.absMode mode) lf (absU n_p) (absMemberShapeLFrom ms i)) := by
  have h := check_block_teles_ls hrel hinv mode hfe n_p ms i (alloc.vec.Vec.new _)
  simpa [absTeleL, alloc.vec.Vec.new] using h

/-- `tele_vals` from `0` onto `[cv_ta0]` is the twin's `cvTa₀ :: cvs.map (·.1)`. -/
theorem tele_vals_cons_abs {cvs : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)}
    {out o : alloc.vec.Vec arena.env.IConstantVal} {x : arena.env.IConstantVal}
    (hout : out.val = [x])
    (h : arena.inductives.block_install.tele_vals cvs 0#usize out = ok o) :
    absICVL o = absIConstantVal x :: (absTeleL cvs).map (·.1) := by
  rw [tele_vals_abs _ _ o h]
  simp [absICVL, hout, absTeleL]

/-- `check_block_inds` ⊑ `checkBlockInds` — stage 1. -/
@[lockstep] theorem check_block_inds_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (p : arena.inductives.block_parts.BlockParts) (is_rec : Bool) :
    LS pers (fun a b => IFEnvRelI a.1 b.1 ∧ b.2.1 = absICVL a.2.1 ∧ b.2.2 = absBlockShape a.2.2)
      (arena.inductives.block_install.check_block_inds pers st mode rf p is_rec) lst
      (checkBlockInds (ConRon.Refine.absMode mode) lf (absBlockParts p) is_rec) := by
  rw [arena.inductives.block_install.check_block_inds, checkBlockInds, absBlockParts_shape,
    absBlockShape_members]
  rcases hms : p.shape.members.val with _ | ⟨m0, rest⟩
  · have h0 : alloc.vec.Vec.len p.shape.members = 0#usize := by
      have : (alloc.vec.Vec.len p.shape.members).val = 0 := by simp [alloc.vec.Vec.len, hms]
      scalar_tac
    simp only [h0, ↓reduceIte, List.map_nil]
    lockstep
  · have h0 : ¬ alloc.vec.Vec.len p.shape.members = 0#usize := by
      intro h; have := congrArg (·.val) h; simp [alloc.vec.Vec.len, hms] at this
    have hidx := bi_vec_index_eq p.shape.members 0#usize 0 rfl (by simp [hms])
    simp only [hms, List.getElem_cons_zero] at hidx
    -- the Rust's cursor `1` is the twin's `rest` (the side tier reads this)
    have hrest : absMemberShapeLFrom p.shape.members 1#usize = rest.map absMemberShape := by
      simp [absMemberShapeLFrom, hms]
    simp only [h0, ↓reduceIte, hidx, bind_tc_ok, List.map_cons]
    lockstep
    have e := tele_vals_cons_abs (by simpa [alloc.vec.Vec.new] using hP) hf
    rw [← e]
    lockstep

/-! ## Stage 1b: the constructors, and the positivity check -/

/-- `shape_nest_ctx` ⊑ `BlockShape.nestCtx`.  The Rust stores `vis` in the
context, which `absNestCtx` drops; the answer carries it. -/
@[lockstep] theorem shape_nest_ctx_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_parts.BlockShape)
    (fvs_p : alloc.vec.Vec arena.handle.EIdx) (vis : Std.U64) :
    LS pers (fun a b => b = absNestCtx a ∧ a.vis = vis)
      (arena.inductives.block_install.shape_nest_ctx pers st p fvs_p vis) lst
      ((absBlockShape p).nestCtx (absEIdxL fvs_p)) := by
  rw [arena.inductives.block_install.shape_nest_ctx, BlockShape.nestCtx]
  lockstep
  refine LS.pure ⟨?_, rfl⟩ hrel hinv
  simp_all [TwinEq, absNestCtx, absNatL, absBlockShape]

/-- `check_sum_ctors` from the first constructor with empty accumulators IS
`checkSumCtors` (the block's call). -/
@[lockstep] theorem bi_check_sum_ctors_new_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {mode : kernel.env.CheckMode} {rf0 lf0 rf lf}
    (hfe0 : IFEnvRelI rf0 lf0) (hfe : IFEnvRelI rf lf)
    (t : arena.handle.NIdx) (lps : alloc.vec.Vec arena.handle.NIdx) (n_p n_idx : Std.U64)
    (res_sort : arena.handle.LIdx) (is_prop large : Bool) (cv_ta : arena.env.IConstantVal)
    (ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LS pers (fun a b => b = (absCtorsL a.1, absLIdxLL a.2))
      (arena.inductives.sum_install.check_sum_ctors pers st mode rf0 rf t lps n_p n_idx res_sort
        is_prop large cv_ta ctors 0#usize (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)) lst
      (checkSumCtors (ConRon.Refine.absMode mode) lf0 lf (absNIdx t) (absNIdxL lps) (absU n_p)
        (absU n_idx) (absLIdx res_sort) is_prop large (absIConstantVal cv_ta) (absCtorsL ctors)) := by
  have h := check_sum_ctors_ls (i := 0#usize) (out := alloc.vec.Vec.new _)
    (sout := alloc.vec.Vec.new _) (t := t) (lps := lps) (n_p := n_p) (n_idx := n_idx)
    (res_sort := res_sort) (is_prop := is_prop) (large := large) (cv_ta := cv_ta)
    (ctors := ctors) (mode := mode) hrel hinv hfe0 hfe
  simpa [absCtorsL, absLIdxLL, absCtorsLFrom, alloc.vec.Vec.new] using h

/-- `Vec<Vec<Vec<LIdx>>>` — the fields' sorts, per member, per constructor. -/
def absLIdxLLL (v : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx))) :
    List (List (List LIdx)) := v.val.map absLIdxLL

theorem check_block_ctors_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf0 lf0 rf lf}
      {p : arena.inductives.block_parts.BlockShape}
      {cv_tas : alloc.vec.Vec arena.env.IConstantVal} {i : Std.Usize}
      {out_c : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
      {out_s : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx))},
      p.members.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf0 lf0 → IFEnvRelI rf lf →
      LS pers (fun a b => b = (absCtorsLL a.1, absLIdxLLL a.2))
        (arena.inductives.block_install.check_block_ctors pers st mode rf0 rf p cv_tas i
          out_c out_s) lst
        (do
          let q ← checkBlockCtors (ConRon.Refine.absMode mode) lf0 lf (absBlockShape p)
            (absMemberShapeLFrom p.members i) (absICVLFrom cv_tas i)
          pure (absCtorsLL out_c ++ q.1, absLIdxLLL out_s ++ q.2)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf0 lf0 rf lf p cv_tas i out_c out_s hn hrel hinv hfe0 hfe
    rw [arena.inductives.block_install.check_block_ctors, if_pos (by scalar_tac),
      absMemberShapeLFrom, vecFrom_nil _ _ _ (by omega)]
    simp only [checkBlockCtors]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf0 lf0 rf lf p cv_tas i out_c out_s hn hrel hinv hfe0 hfe
    rw [arena.inductives.block_install.check_block_ctors, if_neg (by scalar_tac),
      absMemberShapeLFrom, vecFrom_cons _ _ _ (by omega)]
    by_cases hc : i.val < cv_tas.val.length
    · rw [if_neg (by scalar_tac), absICVLFrom, vecFrom_cons _ _ _ hc, checkBlockCtors]
      lockstep
      rename_i oc hoc os hos
      have ha : a.val = i.val + 1 := by scalar_tac
      refine LS.tail (ih (i := a) (out_c := oc) (out_s := os) (by omega) hrel hinv hfe0 hfe) ?_
        (fun _ _ h => h)
      simp only [absMemberShapeLFrom, absICVLFrom, ha, absCtorsLL, absLIdxLLL, hoc, hos,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append]
    · rw [if_pos (by scalar_tac), absICVLFrom, vecFrom_nil _ _ _ (by omega)]
      simp only [checkBlockCtors]
      lockstep

/-- `check_block_ctors` ⊑ `checkBlockCtors` from the cursor on, the two
accumulators in front (the twin conses a pair on the way out, stopping at the
shorter list). -/
@[lockstep] theorem check_block_ctors_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf0 : arena.env.IFEnv}
    {lf0 : IFEnv} {rf : arena.env.IFEnv} {lf : IFEnv} (hfe0 : IFEnvRelI rf0 lf0)
    (hfe : IFEnvRelI rf lf) (p : arena.inductives.block_parts.BlockShape)
    (cv_tas : alloc.vec.Vec arena.env.IConstantVal) (i : Std.Usize)
    (out_c : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64)))
    (out_s : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx))) :
    LS pers (fun a b => b = (absCtorsLL a.1, absLIdxLLL a.2))
      (arena.inductives.block_install.check_block_ctors pers st mode rf0 rf p cv_tas i
        out_c out_s) lst
      (do
        let q ← checkBlockCtors (ConRon.Refine.absMode mode) lf0 lf (absBlockShape p)
          (absMemberShapeLFrom p.members i) (absICVLFrom cv_tas i)
        pure (absCtorsLL out_c ++ q.1, absLIdxLLL out_s ++ q.2)) :=
  check_block_ctors_aux _ rfl hrel hinv hfe0 hfe

/-- `check_block_ctors` from member `0` with empty accumulators IS
`checkBlockCtors` on the block's members (the tail's call). -/
@[lockstep] theorem check_block_ctors_new_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf0 : arena.env.IFEnv}
    {lf0 : IFEnv} {rf : arena.env.IFEnv} {lf : IFEnv} (hfe0 : IFEnvRelI rf0 lf0)
    (hfe : IFEnvRelI rf lf) (p : arena.inductives.block_parts.BlockShape)
    (cv_tas : alloc.vec.Vec arena.env.IConstantVal) :
    LS pers (fun a b => b = (absCtorsLL a.1, absLIdxLLL a.2))
      (arena.inductives.block_install.check_block_ctors pers st mode rf0 rf p cv_tas 0#usize
        (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)) lst
      (checkBlockCtors (ConRon.Refine.absMode mode) lf0 lf (absBlockShape p)
        (absBlockShape p).members (absICVL cv_tas)) := by
  have h := check_block_ctors_ls hrel hinv mode hfe0 hfe p cv_tas 0#usize
    (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)
  simpa [absCtorsLL, absLIdxLLL, absMemberShapeLFrom, absICVLFrom, absICVL, absBlockShape,
    alloc.vec.Vec.new] using h

attribute [local lockstep_inline] arena.checker_base.unwrap_or

theorem check_abs_ctor_sorts_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
      {ctx : arena.inductives.positivity.NestCtx} {is_prop : Bool}
      {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
      {os : alloc.vec.Vec (alloc.vec.Vec arena.inductives.positivity.NestFieldKind ×
        arena.handle.EIdx)} {i : Std.Usize},
      cs.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf →
      LS pers (fun _ _ => True)
        (arena.inductives.block_install.check_abs_ctor_sorts pers st mode rf ctx is_prop cs os i)
        lst
        (checkAbsCtorSorts (ConRon.Refine.absMode mode) lf (absNestCtx ctx) is_prop
          (absCtorsLFrom cs i) ((os.val.drop i.val).map absCtorOut)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf lf ctx is_prop cs os i hn hrel hinv hfe
    rw [arena.inductives.block_install.check_abs_ctor_sorts, if_pos (by scalar_tac),
      absCtorsLFrom, vecFrom_nil _ _ _ (by omega)]
    simp only [checkAbsCtorSorts]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf lf ctx is_prop cs os i hn hrel hinv hfe
    have hvis := bi_hvis hfe
    rw [arena.inductives.block_install.check_abs_ctor_sorts, if_neg (by scalar_tac),
      absCtorsLFrom, vecFrom_cons _ _ _ (by omega)]
    by_cases hc : i.val < os.val.length
    · rw [if_neg (by scalar_tac), vecFrom_cons _ _ _ hc, checkAbsCtorSorts]
      lockstep
    · rw [if_pos (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
      simp only [checkAbsCtorSorts]
      lockstep

/-- `check_abs_ctor_sorts` ⊑ `checkAbsCtorSorts` from the cursor on,
pairwise, stopping at the shorter list. -/
@[lockstep] theorem check_abs_ctor_sorts_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (ctx : arena.inductives.positivity.NestCtx) (is_prop : Bool)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (os : alloc.vec.Vec (alloc.vec.Vec arena.inductives.positivity.NestFieldKind ×
      arena.handle.EIdx)) (i : Std.Usize) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_install.check_abs_ctor_sorts pers st mode rf ctx is_prop cs os i)
      lst
      (checkAbsCtorSorts (ConRon.Refine.absMode mode) lf (absNestCtx ctx) is_prop
        (absCtorsLFrom cs i) ((os.val.drop i.val).map absCtorOut)) :=
  check_abs_ctor_sorts_aux _ rfl hrel hinv hfe

theorem check_abs_ctor_sorts_all_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
      {ctx : arena.inductives.positivity.NestCtx} {is_prop : Bool}
      {css : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
      {oss : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
        arena.inductives.positivity.NestFieldKind × arena.handle.EIdx))} {i : Std.Usize},
      css.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf →
      LS pers (fun _ _ => True)
        (arena.inductives.block_install.check_abs_ctor_sorts_all pers st mode rf ctx is_prop
          css oss i) lst
        (checkAbsCtorSortsAll (ConRon.Refine.absMode mode) lf (absNestCtx ctx) is_prop
          ((css.val.drop i.val).map absCtorsL)
          ((oss.val.drop i.val).map fun w => w.val.map absCtorOut)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf lf ctx is_prop css oss i hn hrel hinv hfe
    rw [arena.inductives.block_install.check_abs_ctor_sorts_all, if_pos (by scalar_tac),
      vecFrom_nil _ _ _ (by omega)]
    simp only [checkAbsCtorSortsAll]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf lf ctx is_prop css oss i hn hrel hinv hfe
    rw [arena.inductives.block_install.check_abs_ctor_sorts_all, if_neg (by scalar_tac),
      vecFrom_cons _ _ _ (by omega)]
    by_cases hc : i.val < oss.val.length
    · rw [if_neg (by scalar_tac), vecFrom_cons _ _ _ hc, checkAbsCtorSortsAll]
      lockstep
    · rw [if_pos (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
      simp only [checkAbsCtorSortsAll]
      lockstep

/-- `check_abs_ctor_sorts_all` from member `0` (the positivity check's call). -/
@[lockstep] theorem check_abs_ctor_sorts_all_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (ctx : arena.inductives.positivity.NestCtx) (is_prop : Bool)
    (css : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64)))
    (oss : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
      arena.inductives.positivity.NestFieldKind × arena.handle.EIdx))) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_install.check_abs_ctor_sorts_all pers st mode rf ctx is_prop
        css oss 0#usize) lst
      (checkAbsCtorSortsAll (ConRon.Refine.absMode mode) lf (absNestCtx ctx) is_prop
        (absCtorsLL css) (absCtorOutsL oss)) := by
  have h := check_abs_ctor_sorts_all_aux _ (i := 0#usize) (css := css) (oss := oss)
    (ctx := ctx) (is_prop := is_prop) (mode := mode) rfl hrel hinv hfe
  simpa [absCtorsLL, absCtorOutsL] using h

/-- `block_nest_ctx` ⊑ `blockNestCtx` — the walk's context and the members'
holes.  The context's `vis` is the environment's counter. -/
@[lockstep] theorem block_nest_ctx_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (p : arena.inductives.block_parts.BlockShape) (cv_tas : alloc.vec.Vec arena.env.IConstantVal) :
    LS pers (fun a b => b.1 = absNestCtx a.1 ∧ absU a.1.vis = lf.visibleBelow ∧
        b.2 = absEIdxL a.2)
      (arena.inductives.block_install.block_nest_ctx pers st rf p cv_tas) lst
      (blockNestCtx lf (absBlockShape p) (absICVL cv_tas)) := by
  have hvis := bi_hvis hfe
  rw [arena.inductives.block_install.block_nest_ctx, blockNestCtx.eq_def]
  rcases hcv : cv_tas.val with _ | ⟨c0, rest⟩
  · have h0 : alloc.vec.Vec.len cv_tas = 0#usize := by
      have : (alloc.vec.Vec.len cv_tas).val = 0 := by simp [alloc.vec.Vec.len, hcv]
      scalar_tac
    simp only [h0, ↓reduceIte, absICVL, hcv, List.map_nil]
    lockstep
  · have h0 : ¬ alloc.vec.Vec.len cv_tas = 0#usize := by
      intro h; have := congrArg (·.val) h; simp [alloc.vec.Vec.len, hcv] at this
    have hidx := bi_vec_index_eq cv_tas 0#usize 0 rfl (by simp [hcv])
    simp only [hcv, List.getElem_cons_zero] at hidx
    simp only [h0, ↓reduceIte, hidx, bind_tc_ok, absICVL, hcv, List.map_cons]
    lockstep

/-! ## The root frame's outputs, split (the twin's `outs.map (·.map (·.1))`,
`outs.map (·.map (·.2))`) -/

/-- The kinds, per member, per constructor. -/
def absKindsLLL (v : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
    arena.inductives.positivity.NestFieldKind))) : List (List (List NestFieldKind)) :=
  v.val.map fun w => w.val.map fun k => k.val.map absNestFieldKind

/-- The normal forms, per member, per constructor. -/
def absEIdxLL (v : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx)) : List (List EIdx) :=
  v.val.map absEIdxL

theorem kinds_dup_abs {ks : alloc.vec.Vec arena.inductives.positivity.NestFieldKind} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.positivity.NestFieldKind),
      arena.inductives.block_install.kinds_dup ks i out = ok o →
      o.val.map absNestFieldKind = out.val.map absNestFieldKind ++
        (ks.val.drop i.val).map absNestFieldKind := by
  refine vec_cursor_copy ks absNestFieldKind absNestFieldKind
    (arena.inductives.block_install.kinds_dup ks) ?_ ?_
  · bp_copy_stop arena.inductives.block_install.kinds_dup.eq_def ks
  · bp_copy_head arena.inductives.block_install.kinds_dup.eq_def ks
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [nest_field_kind_dup_spec _ _ hn], h⟩

theorem split_kinds_abs {os : alloc.vec.Vec (alloc.vec.Vec
      arena.inductives.positivity.NestFieldKind × arena.handle.EIdx)} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec (alloc.vec.Vec
        arena.inductives.positivity.NestFieldKind)),
      arena.inductives.block_install.split_kinds os i out = ok o →
      o.val.map (fun k => k.val.map absNestFieldKind) =
        out.val.map (fun k => k.val.map absNestFieldKind) ++
        (os.val.drop i.val).map (fun p => p.1.val.map absNestFieldKind) := by
  refine vec_cursor_copy os (fun k => k.val.map absNestFieldKind)
    (fun p => p.1.val.map absNestFieldKind)
    (arena.inductives.block_install.split_kinds os) ?_ ?_
  · bp_copy_stop arena.inductives.block_install.split_kinds.eq_def os
  · bp_copy_head arena.inductives.block_install.split_kinds.eq_def os
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, ?_, h⟩
    have := kinds_dup_abs _ _ _ hn
    simpa [alloc.vec.Vec.new] using this

theorem split_nfs_abs {os : alloc.vec.Vec (alloc.vec.Vec
      arena.inductives.positivity.NestFieldKind × arena.handle.EIdx)} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.EIdx),
      arena.inductives.block_install.split_nfs os i out = ok o →
      o.val.map absEIdx = out.val.map absEIdx ++ (os.val.drop i.val).map (fun p => absEIdx p.2) := by
  refine vec_cursor_copy os absEIdx (fun p => absEIdx p.2)
    (arena.inductives.block_install.split_nfs os) ?_ ?_
  · bp_copy_stop arena.inductives.block_install.split_nfs.eq_def os
  · bp_copy_head arena.inductives.block_install.split_nfs.eq_def os
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_eidx _ _ hn], h⟩

theorem split_outs_abs {outs : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
      arena.inductives.positivity.NestFieldKind × arena.handle.EIdx))} :
    ∀ (i : Std.Usize) (ks : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
        arena.inductives.positivity.NestFieldKind)))
      (nfs : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx))
      (o : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
        arena.inductives.positivity.NestFieldKind)) × alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx)),
      arena.inductives.block_install.split_outs outs i ks nfs = ok o →
      absKindsLLL o.1 = absKindsLLL ks ++
          ((absCtorOutsL outs).drop i.val).map (·.map (·.1)) ∧
        absEIdxLL o.2 = absEIdxLL nfs ++
          ((absCtorOutsL outs).drop i.val).map (·.map (·.2)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) outs.val.length
    (fun i (_ : Unit) => ∀ ks nfs
      (o : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
        arena.inductives.positivity.NestFieldKind)) × alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx)),
      arena.inductives.block_install.split_outs outs i ks nfs = ok o →
      absKindsLLL o.1 = absKindsLLL ks ++
          ((absCtorOutsL outs).drop i.val).map (·.map (·.1)) ∧
        absEIdxLL o.2 = absEIdxLL nfs ++
          ((absCtorOutsL outs).drop i.val).map (·.map (·.2))) ?_ ?_ i ()
  · intro i _ hn ks nfs o h
    rw [arena.inductives.block_install.split_outs.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len outs by scalar_tac), Result.ok.injEq] at h
    subst h
    have : (absCtorOutsL outs).drop i.val = [] :=
      List.drop_eq_nil_of_le (by simp [absCtorOutsL]; omega)
    simp [this]
  · intro i _ hlt ih ks nfs o h
    rw [arena.inductives.block_install.split_outs.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len outs by scalar_tac)] at h
    obtain ⟨v, hv, g1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, g2⟩ := ConRon.Refine.bind_eq_ok_iff.mp g1
    obtain ⟨ks1, hks1, g3⟩ := ConRon.Refine.bind_eq_ok_iff.mp g2
    obtain ⟨v2, hv2, g4⟩ := ConRon.Refine.bind_eq_ok_iff.mp g3
    obtain ⟨nfs1, hnfs1, g5⟩ := ConRon.Refine.bind_eq_ok_iff.mp g4
    obtain ⟨i2, hi2, g6⟩ := ConRon.Refine.bind_eq_ok_iff.mp g5
    clear h g1 g2 g3 g4 g5
    have hvx : v = outs.val[i.val] := by
      have h1 := vec_index_some hv
      rw [List.getElem?_eq_getElem hlt] at h1
      exact (Option.some_inj.mp h1).symm
    subst hvx
    have hj : i2.val = i.val + 1 := absSz_add_one hi2
    obtain ⟨e1, e2⟩ := ih i2 () hj ks1 nfs1 o g6
    have k1 := split_kinds_abs _ _ _ hv1
    have k2 := split_nfs_abs _ _ _ hv2
    have hks := ConRon.Refine.vec_push_val hks1
    have hnf := ConRon.Refine.vec_push_val hnfs1
    have hd : (absCtorOutsL outs).drop i.val =
        (outs.val[i.val].val.map absCtorOut) :: (absCtorOutsL outs).drop (i.val + 1) := by
      simp only [absCtorOutsL, ← List.map_drop, List.drop_eq_getElem_cons hlt, List.map_cons]
    rw [hj] at e1 e2
    refine ⟨?_, ?_⟩
    · rw [e1, hd]
      simp only [absKindsLLL, hks, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]
      simp only [alloc.vec.Vec.new, Lockstep.usize_zero_val', List.drop_zero] at k1
      simp [k1, absCtorOut, Function.comp_def]
    · rw [e2, hd]
      simp only [absEIdxLL, hnf, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]
      simp only [alloc.vec.Vec.new, Lockstep.usize_zero_val', List.drop_zero] at k2
      simp [absEIdxL, k2, absCtorOut, Function.comp_def]

/-- `split_outs` from `0` with empty accumulators: the twin's two `map`s. -/
@[lockstep] theorem split_outs_twin0 (outs : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
      arena.inductives.positivity.NestFieldKind × arena.handle.EIdx))) :
    LSP (arena.inductives.block_install.split_outs outs 0#usize (alloc.vec.Vec.new _)
        (alloc.vec.Vec.new _))
      (fun q => TwinEq ((absCtorOutsL outs).map (·.map (·.1))) (absKindsLLL q.1) ∧
        TwinEq ((absCtorOutsL outs).map (·.map (·.2))) (absEIdxLL q.2)) := by
  intro q h
  obtain ⟨e1, e2⟩ := split_outs_abs _ _ _ q h
  simp only [absKindsLLL, absEIdxLL, alloc.vec.Vec.new, Lockstep.usize_zero_val', List.drop_zero] at e1 e2
  exact ⟨e1.symm, e2.symm⟩

/-- `check_block_positivity` ⊑ `checkBlockPositivity` — the block's positivity
on its stored constructors: the walk's context, the uniform-occurrence check,
the root frame, the fields' universes at the holes. -/
@[lockstep] theorem check_block_positivity_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (p : arena.inductives.block_parts.BlockParts)
    (cv_tas : alloc.vec.Vec arena.env.IConstantVal)
    (ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) :
    LS pers (fun a b => b = (absKindsLLL a.1, absEIdxLL a.2.1, absNestState a.2.2))
      (arena.inductives.block_install.check_block_positivity pers st mode rf p cv_tas ctors_as)
      lst
      (checkBlockPositivity (ConRon.Refine.absMode mode) lf (absBlockParts p) (absICVL cv_tas)
        (absCtorsLL ctors_as)) := by
  rw [arena.inductives.block_install.check_block_positivity, checkBlockPositivity,
    absBlockParts_shape]
  lockstep

/-! ## Stage 2: the tail -/

theorem check_block_idx_sorts_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
      {p : arena.inductives.block_parts.BlockShape}
      {cv_tas : alloc.vec.Vec arena.env.IConstantVal} {i : Std.Usize}
      {out : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)},
      p.members.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf →
      LS pers (fun a b => b = absLIdxLL a)
        (arena.inductives.block_install.check_block_idx_sorts pers st mode rf p cv_tas i out) lst
        (do
          let q ← checkBlockIdxSorts (ConRon.Refine.absMode mode) lf (absBlockShape p)
            (absMemberShapeLFrom p.members i) (absICVLFrom cv_tas i)
          pure (absLIdxLL out ++ q)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf lf p cv_tas i out hn hrel hinv hfe
    rw [arena.inductives.block_install.check_block_idx_sorts, if_pos (by scalar_tac),
      absMemberShapeLFrom, vecFrom_nil _ _ _ (by omega)]
    simp only [checkBlockIdxSorts]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf lf p cv_tas i out hn hrel hinv hfe
    have hvis := bi_hvis hfe
    rw [arena.inductives.block_install.check_block_idx_sorts, if_neg (by scalar_tac),
      absMemberShapeLFrom, vecFrom_cons _ _ _ (by omega)]
    by_cases hc : i.val < cv_tas.val.length
    · rw [if_neg (by scalar_tac), absICVLFrom, vecFrom_cons _ _ _ hc, checkBlockIdxSorts]
      lockstep
      rename_i o1 ho1
      have ha : a.val = i.val + 1 := by scalar_tac
      refine LS.tail (ih (i := a) (out := o1) (by omega) hrel hinv hfe) ?_ (fun _ _ h => h)
      simp only [absMemberShapeLFrom, absICVLFrom, ha, absLIdxLL, ho1, absLIdxL,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append]
    · rw [if_pos (by scalar_tac), absICVLFrom, vecFrom_nil _ _ _ (by omega)]
      simp only [checkBlockIdxSorts]
      lockstep

/-- `check_block_idx_sorts` ⊑ `checkBlockIdxSorts` from the cursor on, the
accumulated sorts in front. -/
@[lockstep] theorem check_block_idx_sorts_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (p : arena.inductives.block_parts.BlockShape)
    (cv_tas : alloc.vec.Vec arena.env.IConstantVal) (i : Std.Usize)
    (out : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)) :
    LS pers (fun a b => b = absLIdxLL a)
      (arena.inductives.block_install.check_block_idx_sorts pers st mode rf p cv_tas i out) lst
      (do
        let q ← checkBlockIdxSorts (ConRon.Refine.absMode mode) lf (absBlockShape p)
          (absMemberShapeLFrom p.members i) (absICVLFrom cv_tas i)
        pure (absLIdxLL out ++ q)) :=
  check_block_idx_sorts_aux _ rfl hrel hinv hfe

/-- `check_block_idx_sorts` from member `0` with an empty accumulator IS
`checkBlockIdxSorts` on the block's members (the tail's call). -/
@[lockstep] theorem check_block_idx_sorts_new_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (p : arena.inductives.block_parts.BlockShape)
    (cv_tas : alloc.vec.Vec arena.env.IConstantVal) :
    LS pers (fun a b => b = absLIdxLL a)
      (arena.inductives.block_install.check_block_idx_sorts pers st mode rf p cv_tas 0#usize
        (alloc.vec.Vec.new _)) lst
      (checkBlockIdxSorts (ConRon.Refine.absMode mode) lf (absBlockShape p)
        (absBlockShape p).members (absICVL cv_tas)) := by
  have h := check_block_idx_sorts_ls hrel hinv mode hfe p cv_tas 0#usize (alloc.vec.Vec.new _)
  simpa [absLIdxLL, absMemberShapeLFrom, absICVLFrom, absICVL, absBlockShape,
    alloc.vec.Vec.new] using h

/-- `cons_block_ctors` ⊑ `consBlockCtors` from the cursor on — the members'
constructors consed, member by member.  **Pure on both sides**. -/
theorem cons_block_ctors_refines {n_p : Std.U64}
    {ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
    {i : Std.Usize} {rf : arena.env.IFEnv} {lf : IFEnv} {o}
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.block_install.cons_block_ctors n_p ctors_as i rf = ok o) :
    IFEnvRelI o (consBlockCtors (absU n_p) ((ctors_as.val.drop i.val).map absCtorsL) lf) := by
  refine cursor_induction (fun i : Std.Usize => i.val) ctors_as.val.length
    (fun i rf => ∀ lf o, IFEnvRelI rf lf →
      arena.inductives.block_install.cons_block_ctors n_p ctors_as i rf = ok o →
      IFEnvRelI o (consBlockCtors (absU n_p) ((ctors_as.val.drop i.val).map absCtorsL) lf))
    ?_ ?_ i rf lf o hfe hrun
  · intro i rf hn lf o hfe h
    rw [arena.inductives.block_install.cons_block_ctors.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ctors_as by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le hn, List.map_nil, consBlockCtors]
    exact hfe
  · intro i rf hi ih lf o hfe h
    rw [arena.inductives.block_install.cons_block_ctors.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ctors_as by scalar_tac)] at h
    obtain ⟨v, hv, g1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨fe2, hfe2, g2⟩ := ConRon.Refine.bind_eq_ok_iff.mp g1
    obtain ⟨i2, hi2, g3⟩ := ConRon.Refine.bind_eq_ok_iff.mp g2
    have hvx : v = ctors_as.val[i.val] := by
      have h1 := vec_index_some hv
      rw [List.getElem?_eq_getElem hi] at h1
      exact (Option.some_inj.mp h1).symm
    have hj : i2.val = i.val + 1 := absSz_add_one hi2
    rw [List.drop_eq_getElem_cons hi, List.map_cons, consBlockCtors]
    have h2 := cons_sum_ctors_ls hfe fe2 hfe2
    rw [hvx, absCtorsLFrom_zero] at h2
    have := ih i2 fe2 hj _ o h2 g3
    rwa [hj] at this

/-- `cons_block_ctors` against `consBlockCtors`: a pure Rust-only step, the
related environment after the folds. -/
@[lockstep] theorem cons_block_ctors_ls {n_p : Std.U64}
    {ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
    {i : Std.Usize} {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) :
    LSP (arena.inductives.block_install.cons_block_ctors n_p ctors_as i rf)
      (fun o => IFEnvRelI o
        (consBlockCtors (absU n_p) ((ctors_as.val.drop i.val).map absCtorsL) lf)) :=
  fun _ h => cons_block_ctors_refines hfe h

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.block_caps_at_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms block_caps_at_ls

/-- info: 'ConRon.Refine2.check_block_inds_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_block_inds_ls

/-- info: 'ConRon.Refine2.check_block_positivity_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_block_positivity_ls

/-- info: 'ConRon.Refine2.check_block_ctors_new_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_block_ctors_new_ls

/-- info: 'ConRon.Refine2.check_block_idx_sorts_new_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_block_idx_sorts_new_ls

/-- info: 'ConRon.Refine2.block_raw_rec_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms block_raw_rec_ls

end ConRon.Refine2
