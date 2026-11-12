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
* **`block_caps_at`**: the never-zero read (`member_never_zero`, the declared
  former's `former_z`) is lockstep; past it the Rust tests `mi < len &&
  ctors.len() == 1` where the twin matches `members[mi]?` and `[c]`
  (`blockCapsAtP`, `blockCapsAt_eqP`), and builds the record by branches.  The
  proof decides the Rust's tests first (`bi_vec_index_eq`), then compares the
  records field by field.
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
  environments.  `cons_block_ctors` is pure on both sides (`LSP`); `cons_block_inds`
  threads the state, each capability record reading its former's sort.
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

/-! ## The capability record: `block_caps_at` (pure) -/

theorem ctor_name_list_abs {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      arena.inductives.block_install.ctor_name_list cs i out = ok o →
      absNIdxL o = absNIdxL out ++ ((cs.val.drop i.val).map fun p => absNIdx p.1.name) := by
  have key := vec_cursor_copy cs absNIdx (fun p => absNIdx p.1.name)
    (arena.inductives.block_install.ctor_name_list cs) ?_ ?_
  · intro i out o h
    simpa [absNIdxL] using key i out o h
  · intro i out o hn h
    rw [arena.inductives.block_install.ctor_name_list.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_install.ctor_name_list.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cs by
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

/-- `ctor_name_list` from `0` is `blockCapsAt`'s `cs.map (·.1.name)`. -/
@[lockstep] theorem ctor_name_list_twin0 (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSP (arena.inductives.block_install.ctor_name_list cs 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((absCtorsL cs).map (·.1.name)) (absNIdxL o)) := by
  intro o h
  rw [TwinEq, ctor_name_list_abs _ _ o h]
  simp [absNIdxL, absCtorsL, absIConstantVal]

theorem bi_vec_index_eq {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) (k : Nat)
    (hi : i.val = k) (hk : k < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok v.val[k] := by
  subst hi
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
  simp [List.getElem?_eq_getElem hk]

/-- `member_never_zero` ⊑ `memberNeverZero`: the declared former's zero-ness
datum, `never`.  The Rust tests `mi < len` where the twin matches `members[mi]?`. -/
@[lockstep] theorem member_never_zero_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape) (mi : Std.U64) :
    LS pers (fun a b => b = a)
      (arena.inductives.block_install.member_never_zero pers st p mi) lst
      (memberNeverZero (absBlockShape p) (absU mi)) := by
  rw [arena.inductives.block_install.member_never_zero, memberNeverZero]
  simp only [lift, bind_ok]
  by_cases hm : mi.val < p.members.val.length
  · have hget : (absBlockShape p).members[absU mi]? =
        some (absMemberShape p.members.val[mi.val]) := by
      show (p.members.val.map absMemberShape)[mi.val]? = _
      rw [List.getElem?_map, List.getElem?_eq_getElem hm]; rfl
    rw [hget]
    have hI : (UScalar.cast .Usize mi : Std.Usize).val = mi.val := by
      rcases lift_cast_usize_of_u64 mi _ rfl with h | h
      · exact h
      · exfalso; have := p.members.property; scalar_tac
    have h1 : mi < UScalar.cast .U64 (alloc.vec.Vec.len p.members) := by
      have := lift_cast_u64_of_usize (alloc.vec.Vec.len p.members) _ rfl
      simp only [alloc.vec.Vec.len] at this
      scalar_tac
    have hidx := bi_vec_index_eq p.members (UScalar.cast .Usize mi) mi.val hI hm
    simp only [ite_eq_left h1, hidx, bind_ok]
    lockstep
  · have hget : (absBlockShape p).members[absU mi]? = none := by
      show (p.members.val.map absMemberShape)[mi.val]? = _
      rw [List.getElem?_eq_none (by simp; omega)]
    rw [hget]
    have h1 : ¬ mi < UScalar.cast .U64 (alloc.vec.Vec.len p.members) := by
      have := lift_cast_u64_of_usize (alloc.vec.Vec.len p.members) _ rfl
      simp only [alloc.vec.Vec.len] at this
      scalar_tac
    simp only [ite_eq_right h1]
    lockstep

/-- The twin's capability record past its never-zero read. -/
def blockCapsAtP (p : BlockShape) (mi : Nat) (isRec neverZero : Bool) : IIndCaps :=
  match p.members[mi]? with
  | some ms =>
    match ms.ctors with
    | [c] =>
      { eta := if ms.nIdx != 0 then false else if isRec then false else true
        all := p.memberNames, nparams := p.nP, nIdx := ms.nIdx, ctors := [c.1.name],
        neverZero := neverZero }
    | cs => { all := p.memberNames, nparams := p.nP, nIdx := ms.nIdx,
              ctors := cs.map (·.1.name), neverZero := neverZero }
  | none => { all := p.memberNames, nparams := p.nP, nIdx := 0, ctors := [],
              neverZero := neverZero }

theorem blockCapsAt_eqP (p : BlockShape) (mi : Nat) (isRec : Bool) :
    blockCapsAt p mi isRec =
      (memberNeverZero p mi >>= fun nz => pure (blockCapsAtP p mi isRec nz)) := by
  unfold blockCapsAt blockCapsAtP
  congr 1; funext nz
  rcases p.members[mi]? with _ | ms
  · rfl
  · dsimp only
    rcases ms.ctors with _ | ⟨c, _ | ⟨c2, rest⟩⟩ <;> rfl

/-- `block_caps_at` ⊑ `blockCapsAt` — the capability record of member `mi`.
The never-zero read is lockstep (`member_never_zero_ls`); past it, the Rust tests
`mi < len && ctors.len() == 1` where the twin matches `members[mi]?` and `[c]`:
the Rust's tests are decided first. -/
@[lockstep] theorem block_caps_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape) (mi : Std.U64)
    (is_rec : Bool) :
    LS pers (fun a b => b = absIIndCaps a)
      (arena.inductives.block_install.block_caps_at pers st p mi is_rec) lst
      (blockCapsAt (absBlockShape p) (absU mi) is_rec) := by
  rw [arena.inductives.block_install.block_caps_at, blockCapsAt_eqP]
  refine LS.bind (member_never_zero_ls hrel hinv p mi) rfl ?_ ?_
  · exact fun _ _ => errArm_ok
  intro b nz st1 lst1 hb hrel1 hinv1
  subst hb
  intro o st' h
  simp only at h
  obtain ⟨names, hnames, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hn := shape_member_names_twin p names hnames
  simp only [TwinEq] at hn
  suffices hc : ∃ c, o = .Ok c ∧ st' = st1 ∧
      blockCapsAtP (absBlockShape p) (absU mi) is_rec nz = absIIndCaps c by
    obtain ⟨c, rfl, rfl, hc⟩ := hc
    exact ⟨_, lst1, rfl, hc, hrel1, hinv1⟩
  rw [blockCapsAtP]
  simp only [lift, bind_ok] at h
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
    simp only [ite_eq_left h1, hidx, bind_ok] at h
    generalize p.members.val[mi.val] = m at h ⊢
    rcases hc : m.ctors.val with _ | ⟨⟨cv, nf⟩, _ | ⟨c2, rest⟩⟩
    · have hlen : ¬ alloc.vec.Vec.len m.ctors = 1#usize := by
        intro h; have := congrArg (·.val) h; simp [alloc.vec.Vec.len, hc] at this
      simp only [ite_eq_right hlen] at h
      obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨v, hv, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
      cases Result.ok_injective hq
      simp only [arena.env.i_ind_caps_default, bind_ok] at h
      cases Result.ok_injective h
      refine ⟨_, rfl, rfl, ?_⟩
      have hv' := ctor_name_list_twin0 _ v hv
      simp only [TwinEq, absCtorsL, hc, List.map_nil] at hv'
      simp only [absMemberShape, absCtorsL, hc, List.map_nil, absIIndCaps, IIndCaps.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial
    · have hlen : alloc.vec.Vec.len m.ctors = 1#usize := by
        have : (alloc.vec.Vec.len m.ctors).val = 1 := by simp [alloc.vec.Vec.len, hc]
        scalar_tac
      have hidx0 : alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice (arena.env.IConstantVal × Std.U64))
          m.ctors 0#usize = ok (cv, nf) := by
        rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
        simp [hc]
      simp only [hlen, ↓reduceIte, hidx0, bind_ok,
        arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2] at h
      obtain ⟨se, heta, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨ctors, hctors, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hst : se.1 = st1 := by
        revert heta
        split
        · intro heta; cases Result.ok_injective heta; rfl
        · split <;> (intro heta; simp only [bind_ok] at heta; cases Result.ok_injective heta; rfl)
      cases Result.ok_injective h
      refine ⟨_, rfl, hst, ?_⟩
      simp only [absMemberShape, absCtorsL, hc, List.map_cons, List.map_nil,
        absIIndCaps, ConRon.Refine.vec_push_val hctors, alloc.vec.Vec.new,
        IIndCaps.mk.injEq]
      simp only [pn_u64_bne_zero] at heta
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first
        | trivial
        | (split_ifs at heta <;> simp_all [absU] <;> rw [← heta])
    · have hlen : ¬ alloc.vec.Vec.len m.ctors = 1#usize := by
        intro h; have := congrArg (·.val) h; simp [alloc.vec.Vec.len, hc] at this
      simp only [ite_eq_right hlen] at h
      obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨v, hv, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
      cases Result.ok_injective hq
      simp only [arena.env.i_ind_caps_default, bind_ok] at h
      cases Result.ok_injective h
      refine ⟨_, rfl, rfl, ?_⟩
      have hv' := ctor_name_list_twin0 _ v hv
      simp only [TwinEq, absCtorsL, hc] at hv'
      simp only [absMemberShape, absCtorsL, hc, List.map_cons, absIIndCaps, IIndCaps.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial
  · have hget : (absBlockShape p).members[absU mi]? = none := by
      show (p.members.val.map absMemberShape)[mi.val]? = _
      rw [List.getElem?_eq_none (by simp; omega)]
    rw [hget]
    dsimp only
    have h1 : ¬ mi < UScalar.cast .U64 (alloc.vec.Vec.len p.members) := by
      have := lift_cast_u64_of_usize (alloc.vec.Vec.len p.members) _ rfl
      simp only [alloc.vec.Vec.len] at this
      scalar_tac
    simp only [ite_eq_right h1, bind_ok, arena.env.i_ind_caps_default]
      at h
    cases Result.ok_injective h
    refine ⟨_, rfl, rfl, ?_⟩
    simp only [absIIndCaps, hn]
    rfl

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
    rw [arena.inductives.block_install.pi_doms_mention_any.eq_def, ite_eq_left (by scalar_tac),
      show absU fuel = 0 from hf, piDomsMentionAny]
    lockstep
  | succ n ih =>
    apply LSR.of_LS
    rw [arena.inductives.block_install.pi_doms_mention_any.eq_def, ite_eq_right (by scalar_tac),
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
      ((absCtorsLFrom cs i).anyM fun (c : IConstantVal × Nat) =>
        piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type))
    ?_ ?_ i () lst hrel
  · intro i _ hn lst hrel
    apply LSR.of_LS
    rw [arena.inductives.block_install.ctors_mention_any.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom,
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
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, List.anyM]
    lockstep

/-- A member list as the twin's `List MemberShape`, from a cursor on. -/
def absMemberShapeLFrom (v : alloc.vec.Vec arena.inductives.block_shape.MemberShape)
    (i : Std.Usize) : List MemberShape :=
  (v.val.drop i.val).map absMemberShape

/-- `members_mention_any` ⊑ `blockRawRec`'s outer `anyM`, from the cursor on. -/
@[lockstep] theorem members_mention_any_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape) (i : Std.Usize) :
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
      ite_eq_left (show i ≥ alloc.vec.Vec.len ms by scalar_tac), absMemberShapeLFrom,
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
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac), absMemberShapeLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, List.anyM]
    lockstep
    cases b
    · have ha : a.val = i.val + 1 := by scalar_tac
      exact LSR.tail_ls (ih' _ ha _ hrel) (by simp only [absMemberShapeLFrom, ha, absNIdxL])
        (fun _ _ h => h)
    · exact absurd rfl hc

attribute [local lockstep_simp] absBlockShape_members

/-- `block_is_rec` ⊑ `blockIsRec` — official's `is_rec`, read off the block as
declared. -/
@[lockstep] theorem block_is_rec_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape) :
    LSR pers (fun a b => b = a)
      (arena.inductives.block_install.block_is_rec pers st p) st lst
      (blockIsRec (absBlockShape p)) := by
  intro o h
  rw [arena.inductives.block_install.block_is_rec] at h
  obtain ⟨names, hnames, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hn := shape_member_names_twin p names hnames
  simp only [TwinEq] at hn
  have key := members_mention_any_ls hrel hinv names p.members 0#usize o h
  rw [blockIsRec, hn]
  simpa [absMemberShapeLFrom, absBlockShape] using key

/-! ## Stage 1: the formers -/

/-- `check_block_tele` ⊑ `checkBlockTele`. -/
@[lockstep] theorem check_block_tele_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (n_p : Std.U64) (ms : arena.inductives.block_shape.MemberShape) :
    LS pers (fun a b => b = (absIConstantVal a.1, absLIdx a.2))
      (arena.inductives.block_install.check_block_tele pers st mode rf n_p ms) lst
      (checkBlockTele (ConRon.Refine.absMode mode) lf (absU n_p) (absMemberShape ms)) := by
  rw [arena.inductives.block_install.check_block_tele, checkBlockTele]
  lockstep

def absTeleL (v : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)) :
    List (IConstantVal × LIdx) :=
  v.val.map fun p => (absIConstantVal p.1, absLIdx p.2)

theorem check_block_teles_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf lf} {n_p : Std.U64}
      {ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape} {i : Std.Usize}
      {out : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)},
      ms.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI pers rf lf →
      LS pers (fun a b => b = absTeleL a)
        (arena.inductives.block_install.check_block_teles pers st mode rf n_p ms i out) lst
        (do
          let r ← checkBlockTeles (ConRon.Refine.absMode mode) lf (absU n_p)
            (absMemberShapeLFrom ms i)
          pure (absTeleL out ++ r)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf lf n_p ms i out hn hrel hinv hfe
    rw [arena.inductives.block_install.check_block_teles, ite_eq_left (by scalar_tac),
      absMemberShapeLFrom, vecFrom_nil _ _ _ (by omega), checkBlockTeles]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf lf n_p ms i out hn hrel hinv hfe
    rw [arena.inductives.block_install.check_block_teles, ite_eq_right (by scalar_tac),
      absMemberShapeLFrom, vecFrom_cons _ _ _ (by omega), checkBlockTeles]
    lockstep
    rename_i o1 ho1
    have ha : a.val = i.val + 1 := by scalar_tac
    refine LS.tail (ih (i := a) (out := o1) (by omega) hrel hinv hfe) ?_ (fun _ _ h => h)
    simp only [absMemberShapeLFrom, ha, absTeleL, ho1, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- `check_block_teles` ⊑ `checkBlockTeles` from the cursor on, behind the
accumulator. -/
@[lockstep] theorem check_block_teles_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (n_p : Std.U64)
    (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape) (i : Std.Usize)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)) :
    LS pers (fun a b => b = absTeleL a)
      (arena.inductives.block_install.check_block_teles pers st mode rf n_p ms i out) lst
      (do
        let r ← checkBlockTeles (ConRon.Refine.absMode mode) lf (absU n_p)
          (absMemberShapeLFrom ms i)
        pure (absTeleL out ++ r)) :=
  check_block_teles_aux _ rfl hrel hinv hfe

/-- `check_block_teles` from an empty accumulator IS `checkBlockTeles` from
the cursor on (the install calls it at `1`, the twin on `rest`). -/
@[lockstep] theorem check_block_teles_new_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (n_p : Std.U64)
    (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape) (i : Std.Usize) :
    LS pers (fun a b => b = absTeleL a)
      (arena.inductives.block_install.check_block_teles pers st mode rf n_p ms i
        (alloc.vec.Vec.new _)) lst
      (checkBlockTeles (ConRon.Refine.absMode mode) lf (absU n_p) (absMemberShapeLFrom ms i)) := by
  have h := check_block_teles_ls hrel hinv mode hfe n_p ms i (alloc.vec.Vec.new _)
  simpa [absTeleL, alloc.vec.Vec.new] using h

theorem bi_u64_sub_one (x : Std.U64) : LSP (x - 1#u64) (fun z => z.val = x.val - 1) := by
  intro z h
  exact (ConRon.Refine.Nat.usub_val h).2

attribute [local lockstep high] bi_u64_sub_one

attribute [local lockstep_simp] IndInstPrims.unwrapOr_some' IndInstPrims.unwrapOr_none'

/-- `check_block_doms_at` ⊑ `checkBlockDomsAt`, on the binder count. -/
@[lockstep] theorem check_block_doms_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (off : Std.U64) (fvs doms : alloc.vec.Vec arena.handle.EIdx)
    (j : Std.U64) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_install.check_block_doms_at pers st mode rf off fvs doms j) lst
      (checkBlockDomsAt (ConRon.Refine.absMode mode) lf (absU off) (absEIdxL fvs)
        (absEIdxL doms) (absU j)) := by
  induction hj : j.val generalizing j st lst with
  | zero =>
    rw [arena.inductives.block_install.check_block_doms_at.eq_def, ite_eq_left (by scalar_tac),
      show absU j = 0 from hj, checkBlockDomsAt]
    lockstep
  | succ n ih =>
    rw [arena.inductives.block_install.check_block_doms_at.eq_def, ite_eq_right (by scalar_tac),
      show absU j = n + 1 from hj, checkBlockDomsAt]
    obtain rfl : n = j.val - 1 := by omega
    clear hj
    lockstep

/-- `check_block_agree` ⊑ `checkBlockAgree`, the other members from the
cursor on. -/
@[lockstep] theorem check_block_agree_ls {pers} (mode : kernel.env.CheckMode)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) (n_p : Std.U64)
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
      ite_eq_left (show i ≥ alloc.vec.Vec.len rest by scalar_tac), checkBlockAgree]
    lockstep
  · intro st lst i hi hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun _ _ => True)
          (arena.inductives.block_install.check_block_agree pers st' mode rf n_p cv_ta0 s0 rest j) lst'
          (checkBlockAgree (ConRon.Refine.absMode mode) lf (absU n_p) (absIConstantVal cv_ta0)
            (absLIdx s0) ((rest.val.drop j.val).map fun p => (absIConstantVal p.1, absLIdx p.2))) := ih
    clear ih
    rw [arena.inductives.block_install.check_block_agree.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rest by scalar_tac), checkBlockAgree]
    lockstep

/-- `member_declared` ⊑ `p.members.map (·.declared)` from the cursor on. -/
@[lockstep] theorem member_declared_twin
    (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape) :
    LSP (arena.inductives.block_install.member_declared ms 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((ms.val.map absMemberShape).map (·.declared)) (absICVL o)) := by
  intro o h
  have key := vec_cursor_copy ms absIConstantVal (fun m => absIConstantVal m.declared)
    (fun i out => arena.inductives.block_install.member_declared ms i out) ?_ ?_ 0#usize _ o h
  · rw [TwinEq, absICVL, key]
    simp [alloc.vec.Vec.new, absMemberShape]
  · intro i out o hn h
    rw [arena.inductives.block_install.member_declared.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len ms by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_install.member_declared.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ms by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine ⟨i2, iv, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, ?_, h⟩
    rw [Lockstep.PC2.i_constant_val_dup_ls _ _ hiv]

/-- `cons_block_inds` ⊑ `consBlockInds` from the cursor on: the formers pushed
in block order, each with its capability record (`block_caps_at_ls`, which
reads the declared former's sort). -/
@[lockstep] theorem cons_block_inds_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p1 : arena.inductives.block_shape.BlockShape)
    (is_rec : Bool) (cvs : alloc.vec.Vec arena.env.IConstantVal) (i : Std.Usize)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun o lo => IFEnvRelI pers o lo)
      (arena.inductives.block_install.cons_block_inds pers st p1 is_rec cvs i rf) lst
      (consBlockInds (absBlockShape p1) is_rec (absICVLFrom cvs i) i.val lf) := by
  refine cursor_induction (fun i : Std.Usize => i.val) cvs.val.length
    (fun i (_ : Unit) => ∀ st lst (rf : arena.env.IFEnv) (lf : IFEnv),
      AStateRel₀ pers st lst → AStateInv pers st → IFEnvRelI pers rf lf →
      LS pers (fun o lo => IFEnvRelI pers o lo)
        (arena.inductives.block_install.cons_block_inds pers st p1 is_rec cvs i rf) lst
        (consBlockInds (absBlockShape p1) is_rec (absICVLFrom cvs i) i.val lf))
    ?_ ?_ i () st lst rf lf hrel hinv hfe
  · intro i _ hn st lst rf lf hrel hinv hfe
    rw [arena.inductives.block_install.cons_block_inds.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len cvs by scalar_tac)]
    rw [absICVLFrom, List.drop_eq_nil_of_le hn, List.map_nil, consBlockInds]
    intro o st' h
    cases Result.ok_injective h
    exact ⟨lf, lst, rfl, hfe, hrel, hinv⟩
  · intro i _ hlt ih st lst rf lf hrel hinv hfe
    rw [arena.inductives.block_install.cons_block_inds.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cvs by scalar_tac)]
    rw [absICVLFrom, List.drop_eq_getElem_cons hlt, List.map_cons, consBlockInds]
    refine LS.bind_eq fun i2 hi2 => ?_
    have hi2v : absU i2 = i.val := by
      simp only [lift, Result.ok.injEq] at hi2; subst hi2
      exact ConRon.Refine.ExprOps.usize_cast_u64_val i
    refine LS.bind (block_caps_at_ls hrel hinv p1 i2 is_rec) (by rw [hi2v]) ?_ ?_
    · exact fun _ _ => errArm_ok
    intro caps lcaps st1 lst1 hcaps hrel1 hinv1
    subst hcaps
    refine LS.bind_eq fun iv hiv => ?_
    refine LS.bind_eq fun iv1 hiv1 => ?_
    refine LS.bind_eq fun fe2 hfe2 => ?_
    refine LS.bind_eq fun i3 hi3 => ?_
    have hivx : iv = cvs.val[i.val] := by
      have h1 := vec_index_some hiv
      rw [List.getElem?_eq_getElem hlt] at h1
      exact (Option.some_inj.mp h1).symm
    rw [Lockstep.PC2.i_constant_val_dup_ls _ _ hiv1, hivx] at hfe2
    have hfe2' := ifenv_push_refines hfe.rel hfe.inv hfe2
    have hj : i3.val = i.val + 1 := absSz_add_one hi3
    have := ih i3 () hj st1 lst1 fe2 _ hrel1 hinv1 hfe2'
    rw [hj] at this
    simpa [absICVLFrom, absIConstantInfo, hj] using this

/-- `check_block_inds` ⊑ `checkBlockInds` — stage 1. -/
@[lockstep] theorem check_block_inds_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (p : arena.inductives.block_shape.BlockShape) (is_rec : Bool) :
    LS pers (fun a b => IFEnvRelI pers a.1 b.1 ∧ b.2 = absBlockShape a.2)
      (arena.inductives.block_install.check_block_inds pers st mode rf p is_rec) lst
      (checkBlockInds (ConRon.Refine.absMode mode) lf (absBlockShape p) is_rec) := by
  rw [arena.inductives.block_install.check_block_inds, checkBlockInds, absBlockShape_members]
  rcases hms : p.members.val with _ | ⟨m0, rest⟩
  · have h0 : alloc.vec.Vec.len p.members = 0#usize := by
      have : (alloc.vec.Vec.len p.members).val = 0 := by simp [alloc.vec.Vec.len, hms]
      scalar_tac
    simp only [h0, ↓reduceIte, List.map_nil]
    lockstep
  · have h0 : ¬ alloc.vec.Vec.len p.members = 0#usize := by
      intro h; have := congrArg (·.val) h; simp [alloc.vec.Vec.len, hms] at this
    have hidx := bi_vec_index_eq p.members 0#usize 0 rfl (by simp [hms])
    simp only [hms, List.getElem_cons_zero] at hidx
    -- the Rust's cursor `1` is the twin's `rest` (the side tier reads this)
    have hrest : absMemberShapeLFrom p.members 1#usize = rest.map absMemberShape := by
      simp [absMemberShapeLFrom, hms]
    simp only [h0, ↓reduceIte, hidx, bind_ok, List.map_cons]
    lockstep
    have hd := ‹TwinEq (List.map (fun x : MemberShape => x.declared) _) (absICVL _)›
    simp only [TwinEq, hms, List.map_cons] at hd
    rw [hd]
    refine LS.bind (cons_block_inds_ls ‹_› ‹_› _ is_rec _ 0#usize hfe)
      (by rw [absICVLFrom_zero]; rfl) (fun _ _ => errArm_ok) ?_
    intro fe1 lfe1 st2 lst2 hfe1 hrel2 hinv2
    exact LS.pure ⟨hfe1, rfl⟩ hrel2 hinv2

/-! ## Stage 1b: the constructors, and the positivity check -/

/-- `shape_nest_ctx` ⊑ `BlockShape.nestCtx`. -/
@[lockstep] theorem shape_nest_ctx_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape)
    (fvs_p : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absNestCtx a)
      (arena.inductives.block_install.shape_nest_ctx pers st p fvs_p) lst
      ((absBlockShape p).nestCtx (absEIdxL fvs_p)) := by
  rw [arena.inductives.block_install.shape_nest_ctx, BlockShape.nestCtx]
  lockstep

/-- `check_block_ctors` ⊑ `checkBlockCtors` from the member cursor on. -/
@[lockstep] theorem check_block_ctors_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf0 rf : arena.env.IFEnv}
    {lf0 lf : IFEnv} (hfe0 : IFEnvRelI pers rf0 lf0) (hfe : IFEnvRelI pers rf lf)
    (p : arena.inductives.block_shape.BlockShape) (i : Std.Usize) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_install.check_block_ctors pers st mode rf0 rf p i) lst
      (checkBlockCtors (ConRon.Refine.absMode mode) lf0 lf (absBlockShape p)
        (absMemberShapeLFrom p.members i)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) p.members.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun _ _ => True)
        (arena.inductives.block_install.check_block_ctors pers st mode rf0 rf p i) lst
        (checkBlockCtors (ConRon.Refine.absMode mode) lf0 lf (absBlockShape p)
          (absMemberShapeLFrom p.members i))) ?_ ?_ i () st lst hrel hinv
  · intro i _ hn st lst hrel hinv
    rw [arena.inductives.block_install.check_block_ctors, ite_eq_left (by scalar_tac),
      absMemberShapeLFrom, List.drop_eq_nil_of_le hn, List.map_nil, checkBlockCtors]
    lockstep
  · intro i _ hlt ih st lst hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ st lst, AStateRel₀ pers st lst →
        AStateInv pers st → LS pers (fun _ _ => True)
          (arena.inductives.block_install.check_block_ctors pers st mode rf0 rf p j) lst
          (checkBlockCtors (ConRon.Refine.absMode mode) lf0 lf (absBlockShape p)
            (absMemberShapeLFrom p.members j)) := fun j hj => ih j () hj
    clear ih
    rw [arena.inductives.block_install.check_block_ctors, ite_eq_right (by scalar_tac),
      absMemberShapeLFrom, List.drop_eq_getElem_cons hlt, List.map_cons, checkBlockCtors]
    lockstep
    have ha : a.val = i.val + 1 := by scalar_tac
    exact LS.tail (ih' a ha _ _ ‹_› ‹_›) (by simp only [absMemberShapeLFrom, ha])
      (fun _ _ h => h)

attribute [local lockstep_inline] arena.checker_base.unwrap_or

theorem check_abs_ctor_sorts_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
      {ctx : arena.inductives.positivity.NestCtx} {is_prop : Bool}
      {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
      {os : alloc.vec.Vec (alloc.vec.Vec arena.inductives.positivity.NestFieldKind ×
        arena.handle.EIdx)} {i : Std.Usize},
      cs.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI pers rf lf →
      LS pers (fun _ _ => True)
        (arena.inductives.block_install.check_abs_ctor_sorts pers st mode rf ctx is_prop cs os i)
        lst
        (checkAbsCtorSorts (ConRon.Refine.absMode mode) lf (absNestCtx ctx) is_prop
          (absCtorsLFrom cs i) ((os.val.drop i.val).map absCtorOut)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf lf ctx is_prop cs os i hn hrel hinv hfe
    rw [arena.inductives.block_install.check_abs_ctor_sorts, ite_eq_left (by scalar_tac),
      absCtorsLFrom, vecFrom_nil _ _ _ (by omega)]
    simp only [checkAbsCtorSorts]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf lf ctx is_prop cs os i hn hrel hinv hfe
    rw [arena.inductives.block_install.check_abs_ctor_sorts, ite_eq_right (by scalar_tac),
      absCtorsLFrom, vecFrom_cons _ _ _ (by omega)]
    by_cases hc : i.val < os.val.length
    · rw [ite_eq_right (by scalar_tac), vecFrom_cons _ _ _ hc, checkAbsCtorSorts]
      lockstep
    · rw [ite_eq_left (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
      simp only [checkAbsCtorSorts]
      lockstep

/-- `check_abs_ctor_sorts` ⊑ `checkAbsCtorSorts` from the cursor on,
pairwise, stopping at the shorter list. -/
@[lockstep] theorem check_abs_ctor_sorts_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (ctx : arena.inductives.positivity.NestCtx) (is_prop : Bool)
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
      IFEnvRelI pers rf lf →
      LS pers (fun _ _ => True)
        (arena.inductives.block_install.check_abs_ctor_sorts_all pers st mode rf ctx is_prop
          css oss i) lst
        (checkAbsCtorSortsAll (ConRon.Refine.absMode mode) lf (absNestCtx ctx) is_prop
          ((css.val.drop i.val).map absCtorsL)
          ((oss.val.drop i.val).map fun w => w.val.map absCtorOut)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf lf ctx is_prop css oss i hn hrel hinv hfe
    rw [arena.inductives.block_install.check_abs_ctor_sorts_all, ite_eq_left (by scalar_tac),
      vecFrom_nil _ _ _ (by omega)]
    simp only [checkAbsCtorSortsAll]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf lf ctx is_prop css oss i hn hrel hinv hfe
    rw [arena.inductives.block_install.check_abs_ctor_sorts_all, ite_eq_right (by scalar_tac),
      vecFrom_cons _ _ _ (by omega)]
    by_cases hc : i.val < oss.val.length
    · rw [ite_eq_right (by scalar_tac), vecFrom_cons _ _ _ hc, checkAbsCtorSortsAll]
      lockstep
    · rw [ite_eq_left (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
      simp only [checkAbsCtorSortsAll]
      lockstep

/-- `check_abs_ctor_sorts_all` from member `0` (the positivity check's call). -/
@[lockstep] theorem check_abs_ctor_sorts_all_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (ctx : arena.inductives.positivity.NestCtx) (is_prop : Bool)
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

/-- `block_nest_ctx` ⊑ `blockNestCtx`: the walk's context and the members'
holes. -/
@[lockstep] theorem block_nest_ctx_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape) :
    LS pers (fun a b => b = (absNestCtx a.1, absEIdxL a.2))
      (arena.inductives.block_install.block_nest_ctx pers st p) lst
      (blockNestCtx (absBlockShape p)) := by
  rw [arena.inductives.block_install.block_nest_ctx, blockNestCtx.eq_def,
    show (absBlockShape p).formers = (p.members.val.map absMemberShape).map (·.cvT) from rfl]
  rcases hms : p.members.val with _ | ⟨m0, rest⟩
  · have h0 : alloc.vec.Vec.len p.members = 0#usize := by
      have : (alloc.vec.Vec.len p.members).val = 0 := by simp [alloc.vec.Vec.len, hms]
      scalar_tac
    simp only [h0, ↓reduceIte, List.map_nil]
    lockstep
  · have h0 : ¬ alloc.vec.Vec.len p.members = 0#usize := by
      intro h; have := congrArg (·.val) h; simp [alloc.vec.Vec.len, hms] at this
    have hidx := bi_vec_index_eq p.members 0#usize 0 rfl (by simp [hms])
    simp only [hms, List.getElem_cons_zero] at hidx
    simp only [h0, ↓reduceIte, hidx, bind_ok, List.map_cons]
    lockstep

/-- The root frame's outputs, as the twin's `List (List (List NestFieldKind × EIdx))`. -/
def absOutsL (v : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
    arena.inductives.positivity.NestFieldKind × arena.handle.EIdx))) :
    List (List (List NestFieldKind × EIdx)) :=
  v.val.map fun os => os.val.map fun o => (o.1.val.map absNestFieldKind, absEIdx o.2)

theorem kinds_dup_abs {ks : alloc.vec.Vec arena.inductives.positivity.NestFieldKind} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.positivity.NestFieldKind),
      arena.inductives.block_install.kinds_dup ks i out = ok o →
      o.val.map absNestFieldKind = out.val.map absNestFieldKind ++
        (ks.val.drop i.val).map absNestFieldKind := by
  refine vec_cursor_copy ks absNestFieldKind absNestFieldKind
    (arena.inductives.block_install.kinds_dup ks) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.block_install.kinds_dup.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_install.kinds_dup.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ks by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
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
  · intro i out o hn h
    rw [arena.inductives.block_install.split_kinds.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len os by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_install.split_kinds.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len os by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, ?_, h⟩
    have := kinds_dup_abs _ _ _ hn
    simpa [alloc.vec.Vec.new] using this

/-- `nest_out_kinds` ⊑ `nestOutKinds` from the cursor on. -/
@[lockstep] theorem nest_out_kinds_twin
    (outs : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
      arena.inductives.positivity.NestFieldKind × arena.handle.EIdx))) :
    LSP (arena.inductives.block_install.nest_out_kinds outs 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (nestOutKinds (absOutsL outs))
        (o.val.map fun ks => ks.val.map fun k => k.val.map absNestFieldKind)) := by
  intro o h
  have key := vec_cursor_copy outs (fun ks => ks.val.map fun k => k.val.map absNestFieldKind)
    (fun os => os.val.map fun p => p.1.val.map absNestFieldKind)
    (fun i out => arena.inductives.block_install.nest_out_kinds outs i out) ?_ ?_ 0#usize _ o h
  · rw [TwinEq, key]
    simp [alloc.vec.Vec.new, nestOutKinds, absOutsL]
  · intro i out o hn h
    rw [arena.inductives.block_install.nest_out_kinds.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len outs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_install.nest_out_kinds.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len outs by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, ?_, h⟩
    have := split_kinds_abs _ _ _ hn
    simpa [alloc.vec.Vec.new] using this

/-- `member_ctors` ⊑ `BlockShape.memberCtors`: the members' declared constructors. -/
@[lockstep] theorem member_ctors_twin (p : arena.inductives.block_shape.BlockShape) :
    LSP (arena.inductives.block_shape.member_ctors p.members 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (absBlockShape p).memberCtors (absCtorsLL o)) := by
  intro o h
  have key := vec_cursor_copy p.members absCtorsL (fun m => absCtorsL m.ctors)
    (fun i out => arena.inductives.block_shape.member_ctors p.members i out) ?_ ?_ 0#usize _ o h
  · rw [TwinEq, absCtorsLL, key]
    simp [alloc.vec.Vec.new, BlockShape.memberCtors, absBlockShape, absMemberShape]
  · intro i out o hn h
    rw [arena.inductives.block_shape.member_ctors.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len p.members by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_shape.member_ctors.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len p.members by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine ⟨i2, v, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, ?_, h⟩
    exact (ctors_dup_twin0 _ v hv).symm

/-- A vector of constructor groups, abstracted: each member's name and its
constructors. -/
def absGroupsL (v : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) :
    List (NIdx × List (IConstantVal × Nat)) := v.val.map fun g => (absNIdx g.1, absCtorsL g.2)

/-- `ctor_groups` ⊑ `BlockShape.ctorGroups`: the members' constructors, each group
under its member's name. -/
@[lockstep] theorem ctor_groups_twin (p : arena.inductives.block_shape.BlockShape) :
    LSP (arena.inductives.block_shape.ctor_groups p.members 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (absBlockShape p).ctorGroups (absGroupsL o)) := by
  intro o h
  have key := vec_cursor_copy p.members (fun g => (absNIdx g.1, absCtorsL g.2))
    (fun m => (absNIdx m.cv_t.name, absCtorsL m.ctors))
    (fun i out => arena.inductives.block_shape.ctor_groups p.members i out) ?_ ?_ 0#usize _ o h
  · rw [TwinEq, absGroupsL, key]
    simp [alloc.vec.Vec.new, BlockShape.ctorGroups, absBlockShape, absMemberShape,
      absIConstantVal]
  · intro i out o hn h
    rw [arena.inductives.block_shape.ctor_groups.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len p.members by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_shape.ctor_groups.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len p.members by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine ⟨i2, (n, v), out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, ?_, h⟩
    have hc : absCtorsL q.ctors = absCtorsL v := ctors_dup_twin0 _ v hv
    show (absNIdx n, absCtorsL v) = (absNIdx q.cv_t.name, absCtorsL q.ctors)
    rw [dupId_nidx _ _ hn, hc]

/-- `check_block_positivity` ⊑ `checkBlockPositivity`. -/
@[lockstep] theorem check_block_positivity_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (p : arena.inductives.block_shape.BlockShape) :
    LS pers (fun a b => b = (absOutsL a.1, absNestState a.2))
      (arena.inductives.block_install.check_block_positivity pers st mode rf p) lst
      (checkBlockPositivity (ConRon.Refine.absMode mode) lf (absBlockShape p)) := by
  rw [arena.inductives.block_install.check_block_positivity, checkBlockPositivity]
  lockstep

/-! ## Stage 2: the tail -/

/-- `check_block_idx_sorts` ⊑ `checkBlockIdxSorts` from the member cursor on. -/
@[lockstep] theorem check_block_idx_sorts_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (p : arena.inductives.block_shape.BlockShape) (i : Std.Usize) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_install.check_block_idx_sorts pers st mode rf p i) lst
      (checkBlockIdxSorts (ConRon.Refine.absMode mode) lf (absBlockShape p)
        (absMemberShapeLFrom p.members i)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) p.members.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun _ _ => True)
        (arena.inductives.block_install.check_block_idx_sorts pers st mode rf p i) lst
        (checkBlockIdxSorts (ConRon.Refine.absMode mode) lf (absBlockShape p)
          (absMemberShapeLFrom p.members i))) ?_ ?_ i () st lst hrel hinv
  · intro i _ hn st lst hrel hinv
    rw [arena.inductives.block_install.check_block_idx_sorts, ite_eq_left (by scalar_tac),
      absMemberShapeLFrom, List.drop_eq_nil_of_le hn, List.map_nil, checkBlockIdxSorts]
    lockstep
  · intro i _ hlt ih st lst hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ st lst, AStateRel₀ pers st lst →
        AStateInv pers st → LS pers (fun _ _ => True)
          (arena.inductives.block_install.check_block_idx_sorts pers st mode rf p j) lst
          (checkBlockIdxSorts (ConRon.Refine.absMode mode) lf (absBlockShape p)
            (absMemberShapeLFrom p.members j)) := fun j hj => ih j () hj
    clear ih
    rw [arena.inductives.block_install.check_block_idx_sorts, ite_eq_right (by scalar_tac),
      absMemberShapeLFrom, List.drop_eq_getElem_cons hlt, List.map_cons, checkBlockIdxSorts]
    lockstep
    have ha : a.val = i.val + 1 := by scalar_tac
    exact LS.tail (ih' a ha _ _ ‹_› ‹_›) (by simp only [absMemberShapeLFrom, ha])
      (fun _ _ h => h)

theorem cons_block_ctors_refines {pers : arena.store.PersTier} {n_p : Std.U64}
    {gs : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
    {i : Std.Usize} {rf : arena.env.IFEnv} {lf : IFEnv} {o}
    (hfe : IFEnvRelI pers rf lf)
    (hrun : arena.inductives.block_install.cons_block_ctors n_p gs i rf = ok o) :
    IFEnvRelI pers o (consBlockCtors (absU n_p)
      ((gs.val.drop i.val).map fun g => (absNIdx g.1, absCtorsL g.2)) lf) := by
  refine cursor_induction (fun i : Std.Usize => i.val) gs.val.length
    (fun i rf => ∀ lf o, IFEnvRelI pers rf lf →
      arena.inductives.block_install.cons_block_ctors n_p gs i rf = ok o →
      IFEnvRelI pers o (consBlockCtors (absU n_p)
        ((gs.val.drop i.val).map fun g => (absNIdx g.1, absCtorsL g.2)) lf))
    ?_ ?_ i rf lf o hfe hrun
  · intro i rf hn lf o hfe h
    rw [arena.inductives.block_install.cons_block_ctors.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len gs by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le hn, List.map_nil, consBlockCtors]
    exact hfe
  · intro i rf hi ih lf o hfe h
    rw [arena.inductives.block_install.cons_block_ctors.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len gs by scalar_tac)] at h
    obtain ⟨⟨n, v⟩, hv, g1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨fe2, hfe2, g2⟩ := ConRon.Refine.bind_eq_ok_iff.mp g1
    obtain ⟨i2, hi2, g3⟩ := ConRon.Refine.bind_eq_ok_iff.mp g2
    have hvx : (n, v) = gs.val[i.val] := by
      have h1 := vec_index_some hv
      rw [List.getElem?_eq_getElem hi] at h1
      exact (Option.some_inj.mp h1).symm
    have hj : i2.val = i.val + 1 := absSz_add_one hi2
    rw [List.drop_eq_getElem_cons hi, List.map_cons, ← hvx]
    simp only [consBlockCtors]
    have h2 := cons_sum_ctors_ls hfe fe2 hfe2
    rw [absCtorsLFrom_zero] at h2
    have := ih i2 fe2 hj _ o h2 g3
    rwa [hj] at this

/-- `cons_block_ctors` against `consBlockCtors`: a pure Rust-only step, the
related environment after the folds. -/
@[lockstep] theorem cons_block_ctors_ls {pers : arena.store.PersTier} {n_p : Std.U64}
    {gs : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
    {i : Std.Usize} {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) :
    LSP (arena.inductives.block_install.cons_block_ctors n_p gs i rf)
      (fun o => IFEnvRelI pers o
        (consBlockCtors (absU n_p) ((gs.val.drop i.val).map fun g => (absNIdx g.1, absCtorsL g.2))
          lf)) :=
  fun _ h => cons_block_ctors_refines hfe h

/-! ## The axiom census -/

end ConRon.Refine2
