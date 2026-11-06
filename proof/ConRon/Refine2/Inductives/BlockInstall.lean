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
@[local lockstep_simp] theorem absMemberShape_nIdx (m : arena.inductives.block_shape.MemberShape) :
    (absMemberShape m).nIdx = absU m.n_idx := rfl
@[local lockstep_simp] theorem absMemberShape_ctors (m : arena.inductives.block_shape.MemberShape) :
    (absMemberShape m).ctors = absCtorsL m.ctors := rfl

/-! ## The capability record: `block_caps_at` (pure) -/

/-- `block_caps_at` ⊑ `blockCapsAt` — the capability record of member `mi`. -/
@[lockstep] theorem block_caps_at_twin (p : arena.inductives.block_shape.BlockShape) (mi : Std.U64)
    (is_rec : Bool) :
    LSP (arena.inductives.block_install.block_caps_at p mi is_rec)
      (fun o => TwinEq (blockCapsAt (absBlockShape p) (absU mi) is_rec) (absIIndCaps o)) := by
  sorry -- T143-STUB

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
  sorry -- T143-STUB

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
        pure (absTeleL out ++ r)) := by
  sorry -- T143-STUB

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
  sorry -- T143-STUB

/-- `cons_block_inds` ⊑ `consBlockInds` from the cursor on: the formers pushed
in block order, each with its capability record.  Pure on both sides. -/
@[lockstep] theorem cons_block_inds_ls {pers} (p1 : arena.inductives.block_shape.BlockShape)
    (is_rec : Bool) (cvs : alloc.vec.Vec arena.env.IConstantVal) (i : Std.Usize)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) :
    LSP (arena.inductives.block_install.cons_block_inds p1 is_rec cvs i rf)
      (fun o => IFEnvRelI pers o
        (consBlockInds (absBlockShape p1) is_rec (absICVLFrom cvs i) i.val lf)) := by
  sorry -- T143-STUB

/-- `check_block_inds` ⊑ `checkBlockInds` — stage 1. -/
@[lockstep] theorem check_block_inds_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (p : arena.inductives.block_shape.BlockShape) (is_rec : Bool) :
    LS pers (fun a b => IFEnvRelI pers a.1 b.1 ∧ b.2 = absBlockShape a.2)
      (arena.inductives.block_install.check_block_inds pers st mode rf p is_rec) lst
      (checkBlockInds (ConRon.Refine.absMode mode) lf (absBlockShape p) is_rec) := by
  sorry -- T143-STUB

/-! ## Stage 1b: the constructors, and the positivity check -/

/-- `shape_nest_ctx` ⊑ `BlockShape.nestCtx`. -/
@[lockstep] theorem shape_nest_ctx_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape)
    (fvs_p : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absNestCtx a)
      (arena.inductives.block_install.shape_nest_ctx pers st p fvs_p) lst
      ((absBlockShape p).nestCtx (absEIdxL fvs_p)) := by
  sorry -- T143-STUB

/-- `check_block_ctors` ⊑ `checkBlockCtors` from the member cursor on. -/
@[lockstep] theorem check_block_ctors_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf0 rf : arena.env.IFEnv}
    {lf0 lf : IFEnv} (hfe0 : IFEnvRelI pers rf0 lf0) (hfe : IFEnvRelI pers rf lf)
    (p : arena.inductives.block_shape.BlockShape) (i : Std.Usize) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_install.check_block_ctors pers st mode rf0 rf p i) lst
      (checkBlockCtors (ConRon.Refine.absMode mode) lf0 lf (absBlockShape p)
        (absMemberShapeLFrom p.members i)) := by
  sorry -- T143-STUB

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
  sorry -- T143-STUB

/-- The root frame's outputs, as the twin's `List (List (List NestFieldKind × EIdx))`. -/
def absOutsL (v : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
    arena.inductives.positivity.NestFieldKind × arena.handle.EIdx))) :
    List (List (List NestFieldKind × EIdx)) :=
  v.val.map fun os => os.val.map fun o => (o.1.val.map absNestFieldKind, absEIdx o.2)

/-- `nest_out_kinds` ⊑ `nestOutKinds` from the cursor on. -/
@[lockstep] theorem nest_out_kinds_twin
    (outs : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
      arena.inductives.positivity.NestFieldKind × arena.handle.EIdx))) :
    LSP (arena.inductives.block_install.nest_out_kinds outs 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (nestOutKinds (absOutsL outs))
        (o.val.map fun ks => ks.val.map fun k => k.val.map absNestFieldKind)) := by
  sorry -- T143-STUB

/-- `check_block_positivity` ⊑ `checkBlockPositivity`. -/
@[lockstep] theorem check_block_positivity_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (p : arena.inductives.block_shape.BlockShape) :
    LS pers (fun a b => b = (absOutsL a.1, absNestState a.2))
      (arena.inductives.block_install.check_block_positivity pers st mode rf p) lst
      (checkBlockPositivity (ConRon.Refine.absMode mode) lf (absBlockShape p)) := by
  sorry -- T143-STUB

/-! ## Stage 2: the tail -/

/-- `check_block_idx_sorts` ⊑ `checkBlockIdxSorts` from the member cursor on. -/
@[lockstep] theorem check_block_idx_sorts_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (p : arena.inductives.block_shape.BlockShape) (i : Std.Usize) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_install.check_block_idx_sorts pers st mode rf p i) lst
      (checkBlockIdxSorts (ConRon.Refine.absMode mode) lf (absBlockShape p)
        (absMemberShapeLFrom p.members i)) := by
  sorry -- T143-STUB

theorem cons_block_ctors_refines {pers : arena.store.PersTier} {n_p : Std.U64}
    {ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
    {i : Std.Usize} {rf : arena.env.IFEnv} {lf : IFEnv} {o}
    (hfe : IFEnvRelI pers rf lf)
    (hrun : arena.inductives.block_install.cons_block_ctors n_p ctors_as i rf = ok o) :
    IFEnvRelI pers o (consBlockCtors (absU n_p) ((ctors_as.val.drop i.val).map absCtorsL) lf) := by
  refine cursor_induction (fun i : Std.Usize => i.val) ctors_as.val.length
    (fun i rf => ∀ lf o, IFEnvRelI pers rf lf →
      arena.inductives.block_install.cons_block_ctors n_p ctors_as i rf = ok o →
      IFEnvRelI pers o (consBlockCtors (absU n_p) ((ctors_as.val.drop i.val).map absCtorsL) lf))
    ?_ ?_ i rf lf o hfe hrun
  · intro i rf hn lf o hfe h
    rw [arena.inductives.block_install.cons_block_ctors.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len ctors_as by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le hn, List.map_nil, consBlockCtors]
    exact hfe
  · intro i rf hi ih lf o hfe h
    rw [arena.inductives.block_install.cons_block_ctors.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ctors_as by scalar_tac)] at h
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
@[lockstep] theorem cons_block_ctors_ls {pers : arena.store.PersTier} {n_p : Std.U64}
    {ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
    {i : Std.Usize} {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) :
    LSP (arena.inductives.block_install.cons_block_ctors n_p ctors_as i rf)
      (fun o => IFEnvRelI pers o
        (consBlockCtors (absU n_p) ((ctors_as.val.drop i.val).map absCtorsL) lf)) :=
  fun _ h => cons_block_ctors_refines hfe h

/-! ## The axiom census -/

end ConRon.Refine2
