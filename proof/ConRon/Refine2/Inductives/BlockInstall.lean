/-
# `ConRon.Refine2.Inductives.BlockInstall` — Theorem 2 for `arena::inductives::block_install`

**Task #105** (DESIGN.md §8.2, Theorem 2).
`crates/con-ron-core/src/arena/inductives/block_install.rs` against
`proof/ConRon/Arena/Inductives/BlockInstall.lean`: the capability record per
member, official's `is_rec`, the formers' stage, the constructors' stage, the
positivity check on the stored constructors, the index sorts and the
constructors' cons.
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

@[local lockstep_simp] theorem bi_core_walk_fuel_val :
    (arena.core.CORE_WALK_FUEL).val = coreWalkFuel := core_walk_fuel_abs

attribute [local lockstep_simp] absMemberShape_cvT
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

theorem shape_k_spec (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.shape_k p) (fun r => r.val = p.members.val.length) := by
  intro r h
  rw [arena.inductives.block_parts.shape_k] at h
  have := lift_cast_u64_of_usize _ r h
  simpa [alloc.vec.Vec.len] using this

attribute [local lockstep] shape_k_spec

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
@[local lockstep_simp] theorem absBlockShape_members (p : arena.inductives.block_parts.BlockShape) :
    (absBlockShape p).members = p.members.val.map absMemberShape := rfl

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
      absMemberShapeLFrom, sp_vecFrom_nil _ _ _ (by omega), checkBlockTeles]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf lf n_p ms i out hn hrel hinv hfe
    rw [arena.inductives.block_install.check_block_teles, if_neg (by scalar_tac),
      absMemberShapeLFrom, sp_vecFrom_cons _ _ _ (by omega), checkBlockTeles]
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

@[local lockstep_simp] theorem bi_unwrapOr_some {α : Type} (a : α) (e : Arena.CheckError) :
    unwrapOr (some a) e = pure a := rfl

@[local lockstep_simp] theorem bi_unwrapOr_none {α : Type} (e : Arena.CheckError) :
    unwrapOr (none : Option α) e = Arena.fail e := rfl

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

/-- `check_block_agree` at the cursor `0` (the install's call). -/
@[lockstep] theorem check_block_agree_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) (n_p : Std.U64)
    (cv_ta0 : arena.env.IConstantVal) (s0 : arena.handle.LIdx)
    (rest : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_install.check_block_agree pers st mode rf n_p cv_ta0 s0 rest 0#usize) lst
      (checkBlockAgree (ConRon.Refine.absMode mode) lf (absU n_p) (absIConstantVal cv_ta0)
        (absLIdx s0) (absTeleL rest)) := by
  have h := check_block_agree_ls mode hfe n_p cv_ta0 s0 rest 0#usize st lst hrel hinv
  simpa [absTeleL] using h

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

/-- `cons_block_inds` from the first former (the install's call). -/
@[lockstep] theorem cons_block_inds_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p1 : arena.inductives.block_parts.BlockShape)
    (is_rec : Bool) (cv_tas : alloc.vec.Vec arena.env.IConstantVal)
    {fe : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI fe lf) :
    LS pers (fun a b => IFEnvRelI a b)
      (arena.inductives.block_install.cons_block_inds pers st p1 is_rec cv_tas 0#usize fe) lst
      (consBlockInds (absBlockShape p1) is_rec (absICVL cv_tas) 0 lf) := by
  have h := cons_block_inds_ls p1 is_rec cv_tas 0#usize fe lf st lst hfe hrel hinv
  rwa [absICVLFrom_zero, show (0#usize : Std.Usize).val = 0 from rfl] at h

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

end ConRon.Refine2
