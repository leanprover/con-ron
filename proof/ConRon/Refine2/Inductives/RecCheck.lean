/-
# `ConRon.Refine2.Inductives.RecCheck` — Theorem 2 for `arena::inductives::rec_check`

**Task #105** (DESIGN.md §8.2, Theorem 2).
`crates/con-ron-core/src/arena/inductives/rec_check.rs` against
`proof/ConRon/Arena/Inductives/RecCheck.lean`: the recursor stage's class kit.
One `@[lockstep]` companion per Rust function with a twin counterpart.

## Shapes

* **Fragments unfolded in place** (`lockstep_inline`, Rust side): `target_abs_node`
  (unfolded in `target_abs_go`'s fuel induction), `pair_closed` (the twin's
  inline `closed` block), `target_k53_leaf/_args/_class`,
  `target_major_member/_outside/_outside_aux`.
* **Two cursors, one twin**: `target_params_def_eq`/`_infer` by one cursor
  induction, the infer arm derived from the main walk one step on.
* **`target_major_nfs`**: the Rust counts `i` down pushing matches, then
  reverses; the twin recurses on the tail first.  `targetMajorNfs_append`
  (each entry's test does not read the answer so far) turns the twin over
  `take (i+1)` into the last entry's test followed by the twin over `take i`;
  `target_major_nfs_rev_aux` states the Rust at `acc ++ r.reverse`.
* **`want_aux_names`**: `rec_` ++ `nat_to_dec (i+1)` is `s!"rec_{i+1}"`
  (`rc_aux_name_str`, from `nat_to_dec_spec`).
* **The split counter**: every function that reads the environment takes
  `CoreCtx vis rf lf`; the stored family (`tgt_stored_rules`,
  `cons_block_recs_t`) runs at the constructors' `vis2`
  beside the GROWING index, so it takes `IFEnvRelI rf lf` and reads
  `lf.restrictTo (absU vis)` — the twin's `fe.restrictTo vis₂`
  (`IFEnvInv.coreCtxAt` gives the core's `CoreCtx`).
* **Telescopes are plain handles** since task #119: `target_k53` erases both
  telescopes with `erase_list` and compares them with `eidx_vec_beq`.

## Helpers restated here (they belong elsewhere)

`rec_rule_k_of/eta_of/bits` and `sum_rules` at `CoreCtx` (Prims/SumInstall
have them at `IFEnvRelI` + `hvis` only), `take_eidx_n` as `List.take`, and raw-identity copies (`rc_ctors_dup_id`,
`rc_rec_shape_dup_id`; `eidx_vec_dup` is `PA1.eidx_vec_dup_ls`).  `targetRecPins` is split at its
two binds (`targetRecPins_split`, `rcPinsAux`, `rcPinsTail`, by `rfl`) to meet
the Rust's `_aux`/`_names` fragments.
-/
import ConRon.Refine2.Inductives.PositivityNest
import ConRon.Refine2.Inductives.BlockShape
import ConRon.Refine2.Inductives.Prims
import ConRon.Arena.Inductives.RecCheck

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

attribute [local lockstep_simp] core_walk_fuel_abs Lockstep.core_walk_fuel_val


/-! ## The stored rules: `sum_rules` (pure on both sides) -/

/-- `sum_rules` ⊑ `sumRules` from the cursor on, behind the accumulator:
constructor `j`'s rule with the generated right-hand side `j`, `.plain`. -/
theorem sum_rules_abs (ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (rhss : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.env.IRecRule),
      arena.inductives.sum_install.sum_rules ctors rhss i out = ok o →
      o.val.map absIRecRule = out.val.map absIRecRule ++
        sumRules (absCtorsLFrom ctors i) (absEIdxLFrom rhss i) := by
  sorry -- T143-STUB

/-- `sum_rules` from `0` into an empty accumulator IS `sumRules`. -/
@[lockstep] theorem sum_rules_twin0 (ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (rhss : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.inductives.sum_install.sum_rules ctors rhss 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (sumRules (absCtorsL ctors) (absEIdxL rhss)) (o.val.map absIRecRule)) := by
  intro o h
  rw [TwinEq, sum_rules_abs ctors rhss _ _ o h]
  simp [absCtorsLFrom, absEIdxLFrom, absCtorsL, absEIdxL, alloc.vec.Vec.new]

/-! ## The member abstraction: `target_abs_go` / `target_abs_node` / `target_abs` -/

theorem target_abs_go_aux {pers} (names : alloc.vec.Vec arena.handle.NIdx)
    (lvls : arena.handle.LsIdx) (holes : alloc.vec.Vec arena.handle.EIdx) (n : Nat) :
    ∀ (rm : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx)
      (lm : Std.HashMap EIdx EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) st lst,
      fuel.val = n → PEMemoRel rm lm → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => ∃ m', PEMemoRel a.2 m' ∧ b = (absEIdx a.1, m'))
        (arena.inductives.rec_check.target_abs_go pers st names lvls holes rm fuel h) lst
        (targetAbsGo (absNIdxL names) (absLsIdx lvls) (absEIdxL holes) lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro rm lm fuel h st lst hn hm hrel hinv
    rw [arena.inductives.rec_check.target_abs_go, targetAbsGo]
    lockstep
  | succ m ih =>
    intro rm lm fuel h st lst hn hm hrel hinv
    rw [arena.inductives.rec_check.target_abs_go, targetAbsGo]
    unfold arena.inductives.rec_check.target_abs_node
    lockstep

@[lockstep] theorem target_abs_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (lvls : arena.handle.LsIdx) (holes : alloc.vec.Vec arena.handle.EIdx)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx}
    {lm : Std.HashMap EIdx EIdx} (hm : PEMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.EIdx) :
    LS pers (fun a b => ∃ m', PEMemoRel a.2 m' ∧ b = (absEIdx a.1, m'))
      (arena.inductives.rec_check.target_abs_go pers st names lvls holes rm fuel h) lst
      (targetAbsGo (absNIdxL names) (absLsIdx lvls) (absEIdxL holes) lm (absU fuel)
        (absEIdx h)) :=
  target_abs_go_aux names lvls holes _ rm lm fuel h st lst rfl hm hrel hinv

@[lockstep] theorem target_abs_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (lvls : arena.handle.LsIdx) (holes : alloc.vec.Vec arena.handle.EIdx)
    (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.rec_check.target_abs pers st names lvls holes e) lst
      (targetAbs (absNIdxL names) (absLsIdx lvls) (absEIdxL holes) (absEIdx e)) := by
  rw [arena.inductives.rec_check.target_abs, targetAbs]
  lockstep

/-! ## `target_holes`: the cursor from `t`, the frame base `base + t` -/

theorem target_holes_acc {pers} (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (base : Std.U64) :
    ∀ (t : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.rec_check.target_holes pers st former_tys base t out) lst
        (do
          let r ← targetHoles (absEIdxLFrom former_tys t) (absU base + t.val)
          pure (absEIdxL out ++ r)) := by
  intro t
  refine cursor_induction (fun i : Std.Usize => i.val) former_tys.val.length
    (fun t (_ : Unit) => ∀ st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.rec_check.target_holes pers st former_tys base t out) lst
        (do
          let r ← targetHoles (absEIdxLFrom former_tys t) (absU base + t.val)
          pure (absEIdxL out ++ r))) ?_ ?_ t ()
  · intro t _ hn st lst out hrel hinv
    rw [arena.inductives.rec_check.target_holes.eq_def,
      ite_eq_left (show t ≥ alloc.vec.Vec.len former_tys by scalar_tac), absEIdxLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, targetHoles]
    simp only [pure_bind, List.append_nil]
    lockstep
  · intro t _ hlt ih st lst out hrel hinv
    have ih' : ∀ (j : Std.Usize), j.val = t.val + 1 → ∀ st lst
        (out : alloc.vec.Vec arena.handle.EIdx),
        AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = absEIdxL a)
          (arena.inductives.rec_check.target_holes pers st former_tys base j out) lst
          (do
            let r ← targetHoles (absEIdxLFrom former_tys j) (absU base + j.val)
            pure (absEIdxL out ++ r)) := fun j hj => ih j () hj
    clear ih
    rw [arena.inductives.rec_check.target_holes.eq_def,
      ite_eq_right (show ¬ t ≥ alloc.vec.Vec.len former_tys by scalar_tac), absEIdxLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, targetHoles]
    simp only [bind_assoc, pure_bind]
    lockstep
    refine LS.tail (ih' _ (by scalar_tac) _ _ _ (by assumption) (by assumption)) ?_
      (fun _ _ h => h)
    simp [absEIdxLFrom, absEIdxL, *, Nat.add_assoc]

/-- `target_holes` from `0` into an empty accumulator IS `targetHoles`. -/
@[lockstep] theorem target_holes_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (base : Std.U64) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.rec_check.target_holes pers st former_tys base 0#usize
        (alloc.vec.Vec.new arena.handle.EIdx)) lst
      (targetHoles (absEIdxL former_tys) (absU base)) := by
  have h := target_holes_acc former_tys base 0#usize st lst
    (alloc.vec.Vec.new arena.handle.EIdx) hrel hinv
  have e : (do
      let r ← targetHoles (absEIdxLFrom former_tys 0#usize) (absU base + (0#usize : Std.Usize).val)
      pure (absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ r) : AM _)
      = targetHoles (absEIdxL former_tys) (absU base) := by
    simp [absEIdxL, absEIdxLFrom, alloc.vec.Vec.new]
  rwa [e] at h

/-! ## The two `FvMap` variants: `erase_fvar_tys`, `target_canon_params` -/

@[lockstep] theorem erase_fvar_tys_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.rec_check.erase_fvar_tys pers st e) lst
      (eraseFVarTys (absEIdx e)) := by
  rw [arena.inductives.rec_check.erase_fvar_tys, eraseFVarTys]
  lockstep

@[lockstep] theorem target_canon_params_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pfvs : alloc.vec.Vec arena.handle.EIdx)
    (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.rec_check.target_canon_params pers st pfvs e) lst
      (targetCanonParams (absEIdxL pfvs) (absEIdx e)) := by
  rw [arena.inductives.rec_check.target_canon_params, targetCanonParams]
  lockstep

/-! ## `target_params_def_eq` / `target_params_def_eq_infer` (one twin function
over two cursors; `pair_closed` is the twin's inline `closed` block) -/

attribute [local lockstep_inline] arena.inductives.rec_check.pair_closed

section ParamsDefEq

variable {pers : arena.store.PersTier} {mode : kernel.env.CheckMode}
  {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) (d : Std.U64)
  (names : alloc.vec.Vec arena.handle.NIdx) (lvls : arena.handle.LsIdx)
  (holes pfvs xs ys : alloc.vec.Vec arena.handle.EIdx)

include hfe in
/-- The infer arm at `i` from the main walk at `i + 1`. -/
theorem target_params_def_eq_infer_of (i : Std.Usize)
    (hmain : ∀ (j : Std.Usize), j.val = i.val + 1 → ∀ st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_params_def_eq pers st mode rf d names lvls
          holes pfvs xs ys j) lst
        (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
          (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) ((xs.val.drop j.val).map absEIdx)
          ((ys.val.drop j.val).map absEIdx)))
    (a2 b2 : arena.handle.EIdx) :
    ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_params_def_eq_infer pers st mode rf d names
          lvls holes pfvs xs ys i a2 b2) lst
        (do
          let _ ← inferTypeCore (ConRon.Refine.absMode mode) lf checkFuel (absU d) (absEIdx a2)
          let _ ← inferTypeCore (ConRon.Refine.absMode mode) lf checkFuel (absU d) (absEIdx b2)
          if ← isDefEqCore (ConRon.Refine.absMode mode) lf checkFuel (absU d) (absEIdx a2)
              (absEIdx b2) then
            targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
              (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs)
              ((xs.val.drop (i.val + 1)).map absEIdx) ((ys.val.drop (i.val + 1)).map absEIdx)
          else pure false) := by
  intro st lst hrel hinv
  rw [arena.inductives.rec_check.target_params_def_eq_infer]
  lockstep

include hfe in
theorem target_params_def_eq_aux :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_params_def_eq pers st mode rf d names lvls
          holes pfvs xs ys i) lst
        (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
          (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) ((xs.val.drop i.val).map absEIdx)
          ((ys.val.drop i.val).map absEIdx)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_params_def_eq pers st mode rf d names lvls
          holes pfvs xs ys i) lst
        (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
          (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) ((xs.val.drop i.val).map absEIdx)
          ((ys.val.drop i.val).map absEIdx))) ?_ ?_ i ()
  · intro i _ hn st lst hrel hinv
    rw [arena.inductives.rec_check.target_params_def_eq.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len xs by scalar_tac), List.drop_eq_nil_of_le hn,
      List.map_nil]
    by_cases hy : ys.val.length ≤ i.val
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ys by scalar_tac), List.drop_eq_nil_of_le hy,
        List.map_nil, targetParamsDefEq]
      lockstep
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ys by scalar_tac),
        ite_eq_left (show i ≥ alloc.vec.Vec.len xs by scalar_tac),
        List.drop_eq_getElem_cons (show i.val < ys.val.length by omega), List.map_cons,
        targetParamsDefEq]
      lockstep
      all_goals simp
  · intro i _ hlt ih st lst hrel hinv
    have hmain : ∀ (j : Std.Usize), j.val = i.val + 1 → ∀ st lst,
        AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = a)
          (arena.inductives.rec_check.target_params_def_eq pers st mode rf d names lvls
            holes pfvs xs ys j) lst
          (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
            (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) ((xs.val.drop j.val).map absEIdx)
            ((ys.val.drop j.val).map absEIdx)) := fun j hj => ih j () hj
    clear ih
    have hinfer := target_params_def_eq_infer_of hfe d names lvls holes pfvs xs ys i hmain
    rw [arena.inductives.rec_check.target_params_def_eq.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons]
    by_cases hy : ys.val.length ≤ i.val
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ys by scalar_tac), List.drop_eq_nil_of_le hy,
        List.map_nil, targetParamsDefEq]
      lockstep
      all_goals simp
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ys by scalar_tac),
        List.drop_eq_getElem_cons (show i.val < ys.val.length by omega), List.map_cons,
        targetParamsDefEq]
      lockstep

end ParamsDefEq

@[lockstep] theorem target_params_def_eq_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (d : Std.U64) (names : alloc.vec.Vec arena.handle.NIdx) (lvls : arena.handle.LsIdx)
    (holes pfvs xs ys : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_params_def_eq pers st mode rf d names lvls
        holes pfvs xs ys i) lst
      (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
        (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) (absEIdxLFrom xs i)
        (absEIdxLFrom ys i)) :=
  target_params_def_eq_aux hfe d names lvls holes pfvs xs ys i st lst hrel hinv

/-! ## The major record -/

@[lockstep_simp] theorem absTargetMajor_ind (m : arena.inductives.rec_check.TargetMajor) :
    (absTargetMajor m).ind = absNIdx m.ind := rfl
@[lockstep_simp] theorem absTargetMajor_lvls (m : arena.inductives.rec_check.TargetMajor) :
    (absTargetMajor m).lvls = absLsIdx m.lvls := rfl
@[lockstep_simp] theorem absTargetMajor_ds (m : arena.inductives.rec_check.TargetMajor) :
    (absTargetMajor m).ds = absEIdxL m.ds := rfl
@[lockstep_simp] theorem absTargetMajor_nPc (m : arena.inductives.rec_check.TargetMajor) :
    (absTargetMajor m).nPc = absU m.n_pc := rfl
@[lockstep_simp] theorem absTargetMajor_nIdx (m : arena.inductives.rec_check.TargetMajor) :
    (absTargetMajor m).nIdx = absU m.n_idx := rfl
@[lockstep_simp] theorem absTargetMajor_ctors (m : arena.inductives.rec_check.TargetMajor) :
    (absTargetMajor m).ctors = absCtorsL m.ctors := rfl
@[lockstep_simp] theorem absTargetMajor_member (m : arena.inductives.rec_check.TargetMajor) :
    (absTargetMajor m).member = m.member.map absU := rfl
@[lockstep_simp] theorem absTargetMajor_nfs (m : arena.inductives.rec_check.TargetMajor) :
    (absTargetMajor m).nfs = m.nfs.val.map absNestCtorNf := rfl
@[lockstep_simp] theorem absTargetMajor_pfvs (m : arena.inductives.rec_check.TargetMajor) :
    (absTargetMajor m).pfvs = absEIdxL m.pfvs := rfl

/-! ## `ctors_name`: the twin's inline `ctors.any (·.1.name == c)` -/

theorem ctors_name_abs (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (c : arena.handle.NIdx) :
    ∀ (i : Std.Usize) (o : Bool), arena.inductives.rec_check.ctors_name cs c i = ok o →
      o = (absCtorsLFrom cs i).any (·.1.name == absNIdx c) := by
  intro i o h
  have key := vec_cursor_any cs (fun p => absNIdx p.1.name == absNIdx c)
    (fun i => arena.inductives.rec_check.ctors_name cs c i) ?_ ?_ i o h
  · rw [key, absCtorsLFrom, List.any_map]; rfl
  · intro i o hn h
    rw [arena.inductives.rec_check.ctors_name.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    exact h.symm
  · intro i x o hx h
    have hlt : i.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.rec_check.ctors_name.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨⟨iv, k⟩, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnx : (iv, k) = x := by
      have h1 := vec_index_some hiv; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hnx
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv : b = (absNIdx iv.name == absNIdx c) := nidx_eq2_abs hb
    cases hbb : b
    · rw [hbb] at h hbv
      rw [ite_eq_right (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
    · rw [hbb] at h hbv
      rw [ite_eq_left (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨hbv.symm, h.symm⟩

@[lockstep] theorem ctors_name_twin (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (c : arena.handle.NIdx) :
    LSP (arena.inductives.rec_check.ctors_name cs c 0#usize)
      (fun o => TwinEq ((absCtorsL cs).any (·.1.name == absNIdx c)) o) := by
  intro o h
  rw [TwinEq, ctors_name_abs cs c 0#usize o h, absCtorsLFrom_zero]

/-! ## `target_pin_tys`, `target_major_pins` -/

theorem target_pin_tys_aux {pers} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) (d : Std.U64)
    (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_pin_tys pers st mode rf d xs i) lst
        (targetPinTys (ConRon.Refine.absMode mode) lf (absU d)
          ((xs.val.drop i.val).map absEIdx)) := by
  refine ls_cursor xs absEIdx
    (fun l => targetPinTys (ConRon.Refine.absMode mode) lf (absU d) l)
    (fun st i => arena.inductives.rec_check.target_pin_tys pers st mode rf d xs i) ?_ ?_
  · intro st lst i hn hrel hinv
    rw [arena.inductives.rec_check.target_pin_tys.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len xs by scalar_tac), targetPinTys]
    lockstep
  · intro st lst i hlt hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = a)
          (arena.inductives.rec_check.target_pin_tys pers st' mode rf d xs j) lst'
          (targetPinTys (ConRon.Refine.absMode mode) lf (absU d)
            ((xs.val.drop j.val).map absEIdx)) := ih
    clear ih
    rw [arena.inductives.rec_check.target_pin_tys.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac), targetPinTys]
    lockstep

@[lockstep] theorem target_pin_tys_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (d : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_pin_tys pers st mode rf d xs i) lst
      (targetPinTys (ConRon.Refine.absMode mode) lf (absU d) (absEIdxLFrom xs i)) :=
  target_pin_tys_aux hfe d xs i st lst hrel hinv

@[lockstep] theorem target_major_pins_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (r_p : Std.U64) (m : arena.inductives.rec_check.TargetMajor) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_major_pins pers st mode rf r_p m) lst
      (targetMajorPins (ConRon.Refine.absMode mode) lf (absU r_p) (absTargetMajor m)) := by
  rw [arena.inductives.rec_check.target_major_pins, targetMajorPins]
  lockstep

/-! ## `target_ctor_at` -/

@[lockstep] theorem target_ctor_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (m : arena.inductives.rec_check.TargetMajor)
    (c : arena.env.IConstantVal) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.rec_check.target_ctor_at pers st m c) lst
      (targetCtorAt (absTargetMajor m) (absIConstantVal c)) := by
  rw [arena.inductives.rec_check.target_ctor_at, targetCtorAt]
  lockstep

/-! ## The pure list builders: `nfs_reverse`, `refire`, `some_aux_rec`, `block_nested_bit` -/

/-- `nfs_reverse xs i out` pushes `xs[i-1], …, xs[0]` onto `out`. -/
theorem nfs_reverse_abs (xs : alloc.vec.Vec arena.inductives.positivity.NestCtorNf) :
    ∀ (n : Nat) (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.positivity.NestCtorNf),
      i.val = n → i.val ≤ xs.val.length →
      arena.inductives.rec_check.nfs_reverse xs i out = ok o →
      o.val = out.val ++ (xs.val.take i.val).reverse := by
  intro n
  induction n with
  | zero =>
    intro i out o hn _ h
    rw [arena.inductives.rec_check.nfs_reverse.eq_def, ite_eq_left (by scalar_tac),
      Result.ok.injEq] at h
    subst h; simp [hn]
  | succ n ih =>
    intro i out o hn hle h
    rw [arena.inductives.rec_check.nfs_reverse.eq_def, ite_eq_right (by scalar_tac)] at h
    obtain ⟨i1, hi1, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi1v : i1.val = n := by
      have := ConRon.Refine.Nat.usub_val hi1; simp at this; omega
    obtain ⟨x, hx, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
    obtain ⟨x1, hx1, h3⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
    obtain ⟨out1, hout1, h4⟩ := ConRon.Refine.bind_eq_ok_iff.mp h3
    have hxx : x1 = x := nest_ctor_nf_dup_spec _ _ hx1
    have hlt : n < xs.val.length := by omega
    have hxv : xs.val[n] = x := by
      have := vec_index_some hx; rw [hi1v, List.getElem?_eq_getElem hlt] at this
      exact Option.some_inj.mp this
    rw [ih i1 out1 o hi1v (by omega) h4, ConRon.Refine.vec_push_val hout1, hi1v, hn,
      List.take_add_one, List.getElem?_eq_getElem hlt, hxx, hxv]
    simp

theorem refire_abs (rules : alloc.vec.Vec arena.env.IRecRule) (f : arena.env.IRecRuleFire) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.env.IRecRule),
      arena.inductives.rec_check.refire rules f i out = ok o →
      absIRecRuleL o = absIRecRuleL out ++
        (absIRecRuleLFrom rules i).map fun rl => { rl with fire := absIRecRuleFire f } := by
  intro i out o h
  have key := vec_cursor_copy rules absIRecRule
    (fun r => { absIRecRule r with fire := absIRecRuleFire f })
    (fun i out => arena.inductives.rec_check.refire rules f i out) ?_ ?_ i out o h
  · simp only [absIRecRuleL, absIRecRuleLFrom, key, List.map_map]; rfl
  · intro i out o hn h
    rw [arena.inductives.rec_check.refire.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len rules by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.rec_check.refire.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rules by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨rl, hrl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨irf, hirf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine ⟨i2, _, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, ?_, h⟩
    have e1 := i_rec_rule_dup_abs hrl
    have e2 := i_rec_rule_fire_dup_abs hirf
    simp only [absIRecRule] at e1 ⊢
    simp only [e2]
    injection e1 with h1 h2 h3 h4
    rw [h1, h2, h4]

@[lockstep] theorem refire_twin (rules : alloc.vec.Vec arena.env.IRecRule)
    (f : arena.env.IRecRuleFire) :
    LSP (arena.inductives.rec_check.refire rules f 0#usize
        (alloc.vec.Vec.new arena.env.IRecRule))
      (fun o => TwinEq ((absIRecRuleL rules).map fun rl => { rl with fire := absIRecRuleFire f })
        (absIRecRuleL o)) := by
  intro o h
  rw [TwinEq, refire_abs rules f _ _ o h]
  simp [absIRecRuleL, absIRecRuleLFrom, alloc.vec.Vec.new]

theorem some_aux_rec_abs (rs : alloc.vec.Vec arena.inductives.block_shape.RecShape)
    (k : Std.U64) :
    ∀ (i : Std.Usize) (o : Bool), arena.inductives.rec_check.some_aux_rec rs k i = ok o →
      o = ((rs.val.drop i.val).map absRecShape).any (fun rc => !(rc.tgt < absU k)) := by
  intro i o h
  have key := vec_cursor_any rs (fun r => !(decide ((absRecShape r).tgt < absU k)))
    (fun i => arena.inductives.rec_check.some_aux_rec rs k i) ?_ ?_ i o h
  · rw [key, List.any_map]; rfl
  · intro i o hn h
    rw [arena.inductives.rec_check.some_aux_rec.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
    exact h.symm
  · intro i x o hx h
    rw [arena.inductives.rec_check.some_aux_rec.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rs by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    by_cases hlt : q.tgt < k
    · rw [ite_eq_left hlt] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine Or.inr ⟨?_, i2, absSz_add_one hi2, h⟩
      simp only [absRecShape, absU]; scalar_tac
    · rw [ite_eq_right hlt, Result.ok.injEq] at h
      refine Or.inl ⟨?_, h.symm⟩
      simp only [absRecShape, absU]; scalar_tac

@[lockstep] theorem block_nested_bit_twin (p : arena.inductives.block_shape.BlockShape)
    (kinds : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
      arena.inductives.positivity.NestFieldKind))) :
    LSP (arena.inductives.rec_check.block_nested_bit p kinds)
      (fun o => TwinEq (blockNestedBit (absBlockShape p)
        (kinds.val.map fun v => v.val.map fun w => w.val.map absNestFieldKind)) o) := by
  intro o h
  rw [arena.inductives.rec_check.block_nested_bit] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb' := nest_kinds_flat_twin kinds b hb
  simp only [TwinEq] at hb' ⊢
  rw [blockNestedBit, hb']
  cases b
  · rw [ite_eq_right (by simp), Result.ok.injEq] at h
    simp [h]
  · rw [ite_eq_left rfl] at h
    obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [arena.inductives.block_shape.shape_k] at hk
    have hk' : k.val = p.members.val.length := by
      have := lift_cast_u64_of_usize _ k hk; simpa using this
    rw [some_aux_rec_abs _ _ _ o h]
    simp only [ite_true, absBlockShape, BlockShape.k, List.length_map,
      show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]
    rw [show absU k = p.members.val.length from hk']

/-! ## `erase_list`: the twin's inline `mapM eraseFVarTys` -/

theorem erase_list_acc {pers} (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.rec_check.erase_list pers st xs i out) lst
        (do
          let r ← (absEIdxLFrom xs i).mapM eraseFVarTys
          pure (absEIdxL out ++ r)) := by
  intro i st lst out hrel hinv
  refine ls_cursor_acc xs absEIdx
    (fun (w : alloc.vec.Vec arena.handle.EIdx) l => do
      let r ← l.mapM eraseFVarTys
      pure (absEIdxL w ++ r))
    (fun st k w => arena.inductives.rec_check.erase_list pers st xs k w)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst k w hn hrel hinv
    rw [arena.inductives.rec_check.erase_list.eq_def,
      ite_eq_left (show k ≥ alloc.vec.Vec.len xs by scalar_tac)]
    simp only [List.mapM_nil, pure_bind, List.append_nil]
    lockstep
  · intro st lst k w hk hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize) (w' : alloc.vec.Vec arena.handle.EIdx),
        j.val = k.val + 1 → AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = absEIdxL a)
          (arena.inductives.rec_check.erase_list pers st' xs j w') lst'
          (do
            let r ← (absEIdxLFrom xs j).mapM eraseFVarTys
            pure (absEIdxL w' ++ r)) := ih
    clear ih
    rw [arena.inductives.rec_check.erase_list.eq_def,
      ite_eq_right (show ¬ k ≥ alloc.vec.Vec.len xs by scalar_tac)]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    lockstep

@[lockstep] theorem erase_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.rec_check.erase_list pers st xs 0#usize
        (alloc.vec.Vec.new arena.handle.EIdx)) lst
      ((absEIdxL xs).mapM eraseFVarTys) := by
  have h := erase_list_acc xs 0#usize st lst (alloc.vec.Vec.new arena.handle.EIdx) hrel hinv
  have e : (do
      let r ← (absEIdxLFrom xs 0#usize).mapM eraseFVarTys
      pure (absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ r) : AM _)
      = (absEIdxL xs).mapM eraseFVarTys := by
    simp [absEIdxL, absEIdxLFrom, alloc.vec.Vec.new]
  rwa [e] at h

/-! ## `target_pi_doms_with`: cursor and accumulator against the twin's
non-tail `some (d :: ds)` -/

theorem target_pi_doms_with_acc {pers} (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst (e : arena.handle.EIdx) (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdxL)
        (arena.inductives.rec_check.target_pi_doms_with pers st xs i e out) lst
        (do
          let r ← targetPiDomsWith (absEIdxLFrom xs i) (absEIdx e)
          pure (r.map (absEIdxL out ++ ·))) := by
  intro i st lst e out hrel hinv
  refine ls_cursor_acc xs absEIdx
    (fun (w : arena.handle.EIdx × alloc.vec.Vec arena.handle.EIdx) l => do
      let r ← targetPiDomsWith l (absEIdx w.1)
      pure (r.map (absEIdxL w.2 ++ ·)))
    (fun st k w => arena.inductives.rec_check.target_pi_doms_with pers st xs k w.1 w.2)
    ?_ ?_ i st lst (e, out) hrel hinv
  · intro st lst k w hn hrel hinv
    rw [arena.inductives.rec_check.target_pi_doms_with.eq_def,
      ite_eq_left (show k ≥ alloc.vec.Vec.len xs by scalar_tac), targetPiDomsWith]
    simp only [pure_bind, Option.map_some, List.append_nil]
    lockstep
  · intro st lst k w hk hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize) (w' : arena.handle.EIdx × alloc.vec.Vec arena.handle.EIdx),
        j.val = k.val + 1 → AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = a.map absEIdxL)
          (arena.inductives.rec_check.target_pi_doms_with pers st' xs j w'.1 w'.2) lst'
          (do
            let r ← targetPiDomsWith ((xs.val.drop j.val).map absEIdx) (absEIdx w'.1)
            pure (r.map (absEIdxL w'.2 ++ ·))) := ih
    clear ih
    rw [arena.inductives.rec_check.target_pi_doms_with.eq_def,
      ite_eq_right (show ¬ k ≥ alloc.vec.Vec.len xs by scalar_tac), targetPiDomsWith]
    lockstep
    rename_i d _ _ _ _ e2 acc hacc
    have hj : a.val = k.val + 1 := by scalar_tac
    refine LS.tail (ih' st1 lst1 a (e2, acc) hj hrel hinv) ?_ (fun _ _ h => h)
    simp only [hj]
    congr 1; funext x; cases x <;> simp [absEIdxL, hacc]

@[lockstep] theorem target_pi_doms_with_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (xs : alloc.vec.Vec arena.handle.EIdx) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absEIdxL)
      (arena.inductives.rec_check.target_pi_doms_with pers st xs 0#usize e
        (alloc.vec.Vec.new arena.handle.EIdx)) lst
      (targetPiDomsWith (absEIdxL xs) (absEIdx e)) := by
  have h := target_pi_doms_with_acc xs 0#usize st lst e (alloc.vec.Vec.new arena.handle.EIdx)
    hrel hinv
  have e' : (do
      let r ← targetPiDomsWith (absEIdxLFrom xs 0#usize) (absEIdx e)
      pure (r.map (absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ ·)) : AM _)
      = targetPiDomsWith (absEIdxL xs) (absEIdx e) := by
    simp [absEIdxL, absEIdxLFrom, alloc.vec.Vec.new]
  rwa [e'] at h

/-! ## `target_major_nfs`: the Rust counts down with a reversed accumulator,
the twin recurses on the tail first — the same examination order -/

/-- The twin's `targetMajorNfs` over an append: the right part is examined
first, and the two answers concatenate (each entry's test does not read the
answer built so far). -/
theorem targetMajorNfs_append (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape)
    (formerTys pfvs : List EIdx) (us : LsIdx) (ds : List EIdx)
    (ctors : List (IConstantVal × Nat)) (L l2 : List NestCtorNf) :
    targetMajorNfs mode fe p formerTys pfvs us ds ctors (L ++ l2) = (do
      let r2 ← targetMajorNfs mode fe p formerTys pfvs us ds ctors l2
      let r1 ← targetMajorNfs mode fe p formerTys pfvs us ds ctors L
      pure (r1 ++ r2)) := by
  induction L with
  | nil => simp [targetMajorNfs]
  | cons a L ih =>
    rw [List.cons_append, targetMajorNfs, targetMajorNfs, ih]
    simp only [bind_assoc, pure_bind]
    congr 1; funext r2; congr 1; funext r1
    split
    · simp only [bind_assoc]
      congr 1; funext b
      split <;> simp
    · simp


/-! ## `target_class_match` -/

@[lockstep] theorem target_class_match_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (p : arena.inductives.block_shape.BlockShape)
    (former_tys pfvs : alloc.vec.Vec arena.handle.EIdx) (us : arena.handle.LsIdx)
    (ds : alloc.vec.Vec arena.handle.EIdx) (lvls : arena.handle.LsIdx)
    (eds : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_class_match pers st mode rf p former_tys pfvs us
        ds lvls eds) lst
      (targetClassMatch (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (absEIdxL pfvs) (absLsIdx us) (absEIdxL ds) (absLsIdx lvls) (absEIdxL eds)) := by
  rw [arena.inductives.rec_check.target_class_match, targetClassMatch]
  lockstep

/-! ## `target_major_nfs_rev`, `target_major_nfs` -/

@[lockstep_simp] theorem absNestCtorNf_ctor (e : arena.inductives.positivity.NestCtorNf) :
    (absNestCtorNf e).ctor = absNIdx e.ctor := rfl
@[lockstep_simp] theorem absNestCtorNf_lvls (e : arena.inductives.positivity.NestCtorNf) :
    (absNestCtorNf e).lvls = absLsIdx e.lvls := rfl
@[lockstep_simp] theorem absNestCtorNf_ds (e : arena.inductives.positivity.NestCtorNf) :
    (absNestCtorNf e).ds = absEIdxL e.ds := rfl

section MajorNfs

variable {pers : arena.store.PersTier} {mode : kernel.env.CheckMode}
  {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf)
  (p : arena.inductives.block_shape.BlockShape)
  (former_tys pfvs : alloc.vec.Vec arena.handle.EIdx) (us : arena.handle.LsIdx)
  (ds : alloc.vec.Vec arena.handle.EIdx)
  (ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
  (tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)

include hfe in
/-- The Rust examines `tbl[i-1], …, tbl[0]` pushing the matches; the twin's
`targetMajorNfs` over the first `i` entries examines them in the same order
and answers the matches in table order, i.e. the pushed ones reversed. -/
theorem target_major_nfs_rev_aux (n : Nat) :
    ∀ (i : Std.Usize) st lst (acc : alloc.vec.Vec arena.inductives.positivity.NestCtorNf),
      i.val = n → i.val ≤ tbl.val.length → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.val.map absNestCtorNf)
        (arena.inductives.rec_check.target_major_nfs_rev pers st mode rf p former_tys pfvs
          us ds ctors tbl i acc) lst
        (do
          let r ← targetMajorNfs (ConRon.Refine.absMode mode) lf (absBlockShape p)
            (absEIdxL former_tys) (absEIdxL pfvs) (absLsIdx us) (absEIdxL ds) (absCtorsL ctors)
            ((tbl.val.take i.val).map absNestCtorNf)
          pure (acc.val.map absNestCtorNf ++ r.reverse)) := by
  induction n with
  | zero =>
    intro i st lst acc hn _ hrel hinv
    rw [arena.inductives.rec_check.target_major_nfs_rev.eq_def, ite_eq_left (by scalar_tac), hn]
    simp only [List.take_zero, List.map_nil, targetMajorNfs, pure_bind, List.reverse_nil,
      List.append_nil]
    lockstep
  | succ n ih =>
    intro i st lst acc hn hle hrel hinv
    rw [arena.inductives.rec_check.target_major_nfs_rev.eq_def, ite_eq_right (by scalar_tac)]
    obtain ⟨i1, hi1, hi1n⟩ : ∃ z, i - 1#usize = ok z ∧ z.val = n := by
      obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (Std.UScalar.sub_spec
        (x := i) (y := 1#usize) (by scalar_tac))
      exact ⟨z, hz, by have := hzv.1; scalar_tac⟩
    rw [hi1]
    clear hi1
    have hlt : i1.val < tbl.val.length := by omega
    subst hi1n
    rw [hn, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      List.map_append, targetMajorNfs_append, List.map_cons, List.map_nil, targetMajorNfs,
      targetMajorNfs]
    simp only [pure_bind, bind_assoc]
    lockstep

include hfe in
@[lockstep] theorem target_major_nfs_rev_ls {st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (i : Std.Usize)
    (acc : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)
    (hle : i.val ≤ tbl.val.length) :
    LS pers (fun a b => b = a.val.map absNestCtorNf)
      (arena.inductives.rec_check.target_major_nfs_rev pers st mode rf p former_tys pfvs
        us ds ctors tbl i acc) lst
      (do
        let r ← targetMajorNfs (ConRon.Refine.absMode mode) lf (absBlockShape p)
          (absEIdxL former_tys) (absEIdxL pfvs) (absLsIdx us) (absEIdxL ds) (absCtorsL ctors)
          ((tbl.val.take i.val).map absNestCtorNf)
        pure (acc.val.map absNestCtorNf ++ r.reverse)) :=
  target_major_nfs_rev_aux hfe p former_tys pfvs us ds ctors tbl _ i st lst acc rfl hle hrel hinv

end MajorNfs

@[lockstep] theorem nfs_reverse_twin (xs : alloc.vec.Vec arena.inductives.positivity.NestCtorNf) :
    LSP (arena.inductives.rec_check.nfs_reverse xs (alloc.vec.Vec.len xs)
        (alloc.vec.Vec.new arena.inductives.positivity.NestCtorNf))
      (fun o => TwinEq ((xs.val.map absNestCtorNf).reverse) (o.val.map absNestCtorNf)) := by
  intro o h
  rw [TwinEq, nfs_reverse_abs xs _ _ _ o rfl (by simp [alloc.vec.Vec.len]) h]
  simp [alloc.vec.Vec.new, alloc.vec.Vec.len, List.map_reverse]

@[lockstep] theorem target_major_nfs_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (p : arena.inductives.block_shape.BlockShape)
    (former_tys pfvs : alloc.vec.Vec arena.handle.EIdx) (us : arena.handle.LsIdx)
    (ds : alloc.vec.Vec arena.handle.EIdx)
    (ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf) :
    LS pers (fun a b => b = a.val.map absNestCtorNf)
      (arena.inductives.rec_check.target_major_nfs pers st mode rf p former_tys pfvs us ds
        ctors tbl) lst
      (targetMajorNfs (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (absEIdxL pfvs) (absLsIdx us) (absEIdxL ds) (absCtorsL ctors)
        (tbl.val.map absNestCtorNf)) := by
  have e : targetMajorNfs (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (absEIdxL pfvs) (absLsIdx us) (absEIdxL ds) (absCtorsL ctors)
        (tbl.val.map absNestCtorNf) = (do
      let rev ← (do
        let r ← targetMajorNfs (ConRon.Refine.absMode mode) lf (absBlockShape p)
          (absEIdxL former_tys) (absEIdxL pfvs) (absLsIdx us) (absEIdxL ds) (absCtorsL ctors)
          ((tbl.val.take (alloc.vec.Vec.len tbl).val).map absNestCtorNf)
        pure ((alloc.vec.Vec.new arena.inductives.positivity.NestCtorNf).val.map absNestCtorNf ++
          r.reverse))
      pure rev.reverse) := by
    simp [alloc.vec.Vec.len, alloc.vec.Vec.new]
  rw [e, arena.inductives.rec_check.target_major_nfs]
  lockstep

/-! ## `target_k53` (with `_leaf`, `_args`, `_class`: fragments of the one twin
`targetK53`, unfolded in place) -/

attribute [local lockstep_inline] arena.inductives.rec_check.target_k53_leaf
  arena.inductives.rec_check.target_k53_args arena.inductives.rec_check.target_k53_class

attribute [local lockstep high] take_eidx_n_twin

@[lockstep] theorem target_k53_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (p : arena.inductives.block_shape.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (mc : arena.inductives.rec_check.TargetMajor)
    (tele : alloc.vec.Vec arena.handle.EIdx)
    (maj_dom f : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_k53 pers st mode rf p former_tys mc tele maj_dom f)
      lst
      (targetK53 (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (absTargetMajor mc) (absBinderL tele) (absEIdx maj_dom) (absEIdx f)) := by
  rw [arena.inductives.rec_check.target_k53, targetK53]
  lockstep

/-! ## The major record: copy, default, lookup -/

theorem rc_ctors_dup_id (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    ∀ o, arena.inductives.block_shape.ctors_dup cs 0#usize
      (alloc.vec.Vec.new (arena.env.IConstantVal × Std.U64)) = ok o → o = cs := by
  refine vec_copy_id cs (arena.inductives.block_shape.ctors_dup cs) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.block_shape.ctors_dup.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_shape.ctors_dup.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cs by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨⟨iv, k⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : (iv, k) = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [Lockstep.PC2.i_constant_val_dup_ls _ _ hiv1] at hout1
    exact ⟨i2, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, h⟩

/-- `target_major_dup` is the identity. -/
@[lockstep] theorem target_major_dup_spec (m : arena.inductives.rec_check.TargetMajor) :
    LSP (arena.inductives.rec_check.target_major_dup m) (fun o => o = m) := by
  intro o h
  rw [arena.inductives.rec_check.target_major_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨li, hli, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v2, hv2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v3, hv3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  have hom : o1 = m.member := by
    cases hm : m.member <;> rw [hm] at ho1 <;> exact (Result.ok_injective ho1).symm
  rw [dupId_nidx _ _ hn, dupId_lsidx _ _ hli, alloc.vec.Vec.ext _ _ (eidx_vec_dup_val hv),
    rc_ctors_dup_id _ _ hv1, hom, nest_ctor_nfs_dup_spec _ _ hv2,
    alloc.vec.Vec.ext _ _ (eidx_vec_dup_val hv3)]

@[lockstep] theorem target_major_default_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absTargetMajor a)
      (arena.inductives.rec_check.target_major_default pers st) lst targetMajorDefault := by
  rw [arena.inductives.rec_check.target_major_default, targetMajorDefault]
  lockstep

@[lockstep] theorem target_major_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor)
    (c : Std.U64) :
    LS pers (fun a b => b = absTargetMajor a)
      (arena.inductives.rec_check.target_major_at pers st ms c) lst
      (targetMajorAt (ms.val.map absTargetMajor) (absU c)) := by
  rw [arena.inductives.rec_check.target_major_at, targetMajorAt]
  by_cases hc : c.val < ms.val.length
  · rw [List.getElem?_map, List.getElem?_eq_getElem (show absU c < ms.val.length from hc)]
    simp only [Option.map_some]
    lockstep
  · rw [List.getElem?_eq_none (by simp only [List.length_map, absU]; omega)]
    lockstep

/-! ## The outside major's type former: `target_outside_inst` -/

attribute [local lockstep_inline] arena.inductives.rec_check.target_outside_inst_at
attribute [local lockstep high] Lockstep.PC2.i_constant_val_dup_ls

@[lockstep] theorem target_outside_inst_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (i_name : arena.handle.NIdx) (us : arena.handle.LsIdx) (ds : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = (absU a.1, absLIdx a.2))
      (arena.inductives.rec_check.target_outside_inst pers st mode rf i_name us ds) lst
      (targetOutsideInst (ConRon.Refine.absMode mode) lf (absNIdx i_name) (absLsIdx us)
        (absEIdxL ds)) := by
  rw [arena.inductives.rec_check.target_outside_inst, targetOutsideInst]
  lockstep

/-! ## A recursor's major, resolved: `target_major_of` (with `_member`,
`_outside`, `_outside_aux`: fragments of the one twin `targetMajorOf`) -/


@[lockstep] theorem target_ctors_of_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rf : arena.env.IFEnv}
    {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) (c : arena.handle.NIdx) :
    LSR pers (fun a b => b = a.map fun p => (absU p.1, absCtorsL p.2))
      (arena.inductives.rec_check.target_ctors_of pers st rf c) st lst
      (targetCtorsOf lf (absNIdx c)) := by
  rw [arena.inductives.rec_check.target_ctors_of, targetCtorsOf]
  exact nest_container_ls hrel hinv hfe c

/-- The twin's `unwrapOr l[i]? e` as the bounds test the port makes. -/
theorem rc_unwrapOr_getElem? {α : Type} (l : List α) (i : Nat) (e : Arena.CheckError) :
    unwrapOr l[i]? e = if h : i < l.length then pure l[i] else Arena.fail e := by
  by_cases h : i < l.length
  · rw [dite_eq_left h, List.getElem?_eq_getElem h]; rfl
  · rw [dite_eq_right h, List.getElem?_eq_none (by omega)]; rfl

theorem rc_absBlockShape_members_length (p : arena.inductives.block_shape.BlockShape) :
    (absBlockShape p).members.length = p.members.val.length := by
  simp [absBlockShape]

theorem rc_absCtorsLL_length
    (v : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) :
    (absCtorsLL v).length = v.val.length := by
  simp [absCtorsLL]

theorem rc_absBlockShape_nP (p : arena.inductives.block_shape.BlockShape) :
    (absBlockShape p).nP = p.n_p.val := rfl

theorem rc_absBlockShape_members_getElem (p : arena.inductives.block_shape.BlockShape) (i : Nat)
    (h : i < (absBlockShape p).members.length) :
    (absBlockShape p).members[i] = absMemberShape (p.members.val[i]'(by
      simpa [absBlockShape] using h)) := by
  simp [absBlockShape]

theorem rc_absCtorsLL_getElem
    (v : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) (i : Nat)
    (h : i < (absCtorsLL v).length) :
    (absCtorsLL v)[i] = absCtorsL (v.val[i]'(by simpa [absCtorsLL] using h)) := by
  simp [absCtorsLL]

theorem rc_ctors_dup_spec (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSP (arena.inductives.block_shape.ctors_dup cs 0#usize
      (alloc.vec.Vec.new (arena.env.IConstantVal × Std.U64))) (fun o => o = cs) :=
  rc_ctors_dup_id cs

attribute [local lockstep high] rc_ctors_dup_spec

attribute [local lockstep_simp] rc_unwrapOr_getElem? rc_absBlockShape_members_length
  rc_absCtorsLL_length rc_absBlockShape_nP rc_absBlockShape_members_getElem rc_absCtorsLL_getElem

attribute [local lockstep_inline] arena.inductives.rec_check.target_major_member
  arena.inductives.rec_check.target_major_outside arena.inductives.rec_check.target_major_outside_aux

@[lockstep] theorem target_major_of_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (p : arena.inductives.block_shape.BlockShape)
    (pfvs fvs : alloc.vec.Vec arena.handle.EIdx) (mty : arena.handle.EIdx) :
    LS pers (fun a b => b = absTargetMajor a)
      (arena.inductives.rec_check.target_major_of pers st mode rf p pfvs fvs mty) lst
      (targetMajorOf (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL pfvs)
        (absEIdxL fvs) (absEIdx mty)) := by
  rw [arena.inductives.rec_check.target_major_of, targetMajorOf]
  lockstep
  all_goals sorry -- T143-STUB

/-! ## The recursor records' pins: the auxiliary names `T₀.rec_1 … T₀.rec_n` -/

theorem cps_append_val (s t : alloc.vec.Vec Std.U32) :
    ∀ (i : Std.Usize) (o : alloc.vec.Vec Std.U32),
      arena.inductives.rec_check.cps_append s t i = ok o → o.val = s.val ++ t.val.drop i.val := by
  intro i o h
  have key := vec_cursor_copy t id id (fun i s => arena.inductives.rec_check.cps_append s t i)
    ?_ ?_ i s o h
  · simpa using key
  · intro i out o hn h
    rw [arena.inductives.rec_check.cps_append.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len t by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.rec_check.cps_append.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len t by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, q, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, rfl, h⟩

/-- An auxiliary recursor's name part: `rec_` followed by the decimal digits. -/
theorem rc_aux_name_str {s1 d s2 : alloc.vec.Vec Std.U32} {k : Nat}
    (h1 : s1.val = (arena.inductives.rec_check.REC_AUX_PREFIX).val)
    (h2 : s2.val = s1.val ++ d.val) (hd : ConRon.Refine.absCodes d.val = toString k)
    (hwf : ConRon.Refine.StrWF d) :
    ConRon.Refine.absString s2 = s!"rec_{k}" ∧ ConRon.Refine.StrWF s2 := by
  simp only [global_simps, Array.make] at h1
  constructor
  · rw [ConRon.Refine.absString_eq, h2, h1]
    rw [ConRon.Refine.absCodes] at hd ⊢
    rw [List.map_append, String.ofList_append, hd]
    rfl
  · intro c hc
    rw [h2, h1] at hc
    rcases List.mem_append.mp hc with hc | hc
    · simp at hc; rcases hc with rfl | rfl | rfl | rfl <;> decide
    · exact hwf c hc

theorem rc_cps_append_twin0 (s t : alloc.vec.Vec Std.U32) :
    LSP (arena.inductives.rec_check.cps_append s t 0#usize) (fun o => o.val = s.val ++ t.val) := by
  intro o h
  rw [cps_append_val s t _ o h]; simp

/-- Interning `n.rec_k` from the port's code points. -/
theorem rc_intern_aux_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {n : arena.handle.NIdx} {s s1 d s2 : alloc.vec.Vec Std.U32}
    {k : Nat} (hs : s1.val = s.val)
    (h0 : s.val = (arena.inductives.rec_check.REC_AUX_PREFIX).val)
    (h2 : s2.val = s1.val ++ d.val)
    (hd : ConRon.Refine.absCodes d.val = toString k ∧ ConRon.Refine.StrWF d) :
    LS pers (fun a b => b = absNIdx a) (arena.monad.intern_n_node pers st (.Str n s2)) lst
      (Arena.internNNode (.str (absNIdx n) s!"rec_{k}")) := by
  obtain ⟨e, hw⟩ := rc_aux_name_str (hs.trans h0) h2 hd.1 hd.2
  have := intern_n_node_ls hrel hinv (.Str n s2) hw
  simpa [absNNodeView, e] using this

attribute [local lockstep] rc_cps_append_twin0
attribute [local lockstep high] rc_intern_aux_name_ls

theorem want_aux_names_acc {pers} (n0 : arena.handle.NIdx) (n : Std.U64) :
    ∀ (i : Std.U64) st lst (out : alloc.vec.Vec arena.handle.NIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absNIdxL a)
        (arena.inductives.rec_check.want_aux_names pers st n0 n i out) lst
        (do
          let r ← (List.range' i.val (n.val - i.val)).mapM fun j =>
            Arena.internNNode (.str (absNIdx n0) s!"rec_{j + 1}")
          pure (absNIdxL out ++ r)) := by
  intro i st lst out hrel hinv
  refine ls_counted n
    (fun (w : alloc.vec.Vec arena.handle.NIdx) m k => do
      let r ← (List.range' k m).mapM fun j =>
        Arena.internNNode (.str (absNIdx n0) s!"rec_{j + 1}")
      pure (absNIdxL w ++ r))
    (fun st k w => arena.inductives.rec_check.want_aux_names pers st n0 n k w) ?_ ?_
    i st lst out hrel hinv
  · intro st lst k w hn hrel hinv
    rw [arena.inductives.rec_check.want_aux_names.eq_def, ite_eq_left (by scalar_tac)]
    simp only [List.range'_zero, List.mapM_nil, pure_bind, List.append_nil]
    lockstep
  · intro st lst k w m hk hm hrel hinv ih
    rw [arena.inductives.rec_check.want_aux_names.eq_def, ite_eq_right (by scalar_tac)]
    simp only [List.range'_succ, List.mapM_cons, bind_assoc, pure_bind]
    lockstep

@[lockstep] theorem want_aux_names_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n0 : arena.handle.NIdx) (n : Std.U64) :
    LS pers (fun a b => b = absNIdxL a)
      (arena.inductives.rec_check.want_aux_names pers st n0 n 0#u64
        (alloc.vec.Vec.new arena.handle.NIdx)) lst
      ((List.range (absU n)).mapM fun i =>
        Arena.internNNode (.str (absNIdx n0) s!"rec_{i + 1}")) := by
  have h := want_aux_names_acc n0 n 0#u64 st lst (alloc.vec.Vec.new arena.handle.NIdx) hrel hinv
  have e : (do
      let r ← (List.range' (0#u64 : Std.U64).val (n.val - (0#u64 : Std.U64).val)).mapM fun j =>
        Arena.internNNode (.str (absNIdx n0) s!"rec_{j + 1}")
      pure (absNIdxL (alloc.vec.Vec.new arena.handle.NIdx) ++ r) : AM _)
      = (List.range (absU n)).mapM fun i =>
        Arena.internNNode (.str (absNIdx n0) s!"rec_{i + 1}") := by
    simp [absNIdxL, alloc.vec.Vec.new, absU, List.range_eq_range']
  rwa [e] at h

/-! ## The name lists: `ctor_names`, `ctor3_names`, `recs_by_target` -/

theorem ctor_names_abs (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      arena.inductives.rec_check.ctor_names cs i out = ok o →
      absNIdxL o = absNIdxL out ++ (absCtorsLFrom cs i).map (·.1.name) := by
  intro i out o h
  have key := vec_cursor_copy cs absNIdx (fun p => absNIdx p.1.name)
    (fun i out => arena.inductives.rec_check.ctor_names cs i out) ?_ ?_ i out o h
  · simp only [absNIdxL, key, absCtorsLFrom, List.map_map]; rfl
  · intro i out o hn h
    rw [arena.inductives.rec_check.ctor_names.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.rec_check.ctor_names.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cs by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨⟨iv, k⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : (iv, k) = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_nidx _ _ hn], h⟩

/-- `ctor_names` from `0` into an empty accumulator: the constructors' names. -/
@[lockstep] theorem ctor_names_twin (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSP (arena.inductives.rec_check.ctor_names cs 0#usize (alloc.vec.Vec.new arena.handle.NIdx))
      (fun o => TwinEq ((absCtorsL cs).map (·.1.name)) (absNIdxL o)) := by
  intro o h
  rw [TwinEq, ctor_names_abs cs _ _ o h, absCtorsLFrom_zero]
  simp [absNIdxL, alloc.vec.Vec.new]

theorem ctor3_names_abs (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      arena.inductives.rec_check.ctor3_names cs i out = ok o →
      absNIdxL o = absNIdxL out ++ (absCtors3LFrom cs i).map (·.1.name) := by
  intro i out o h
  have key := vec_cursor_copy cs absNIdx (fun p => absNIdx p.1.name)
    (fun i out => arena.inductives.rec_check.ctor3_names cs i out) ?_ ?_ i out o h
  · simp only [absNIdxL, key, absCtors3LFrom, List.map_map]; rfl
  · intro i out o hn h
    rw [arena.inductives.rec_check.ctor3_names.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.rec_check.ctor3_names.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cs by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨⟨iv, k, k2⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : (iv, k, k2) = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_nidx _ _ hn], h⟩

@[lockstep] theorem ctor3_names_twin (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) :
    LSP (arena.inductives.rec_check.ctor3_names cs 0#usize (alloc.vec.Vec.new arena.handle.NIdx))
      (fun o => TwinEq ((absCtors3L cs).map (·.1.name)) (absNIdxL o)) := by
  intro o h
  rw [TwinEq, ctor3_names_abs cs _ _ o h, absCtors3LFrom_zero]
  simp [absNIdxL, alloc.vec.Vec.new]

theorem rc_rec_shape_dup_id (r : arena.inductives.block_shape.RecShape) :
    LSP (arena.inductives.block_shape.rec_shape_dup r) (fun o => o = r) := by
  intro o h
  rw [arena.inductives.block_shape.rec_shape_dup] at h
  obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [Lockstep.PC2.i_constant_val_dup_ls _ _ hiv, Lockstep.PC2.i_rec_rules_dup_ls _ _ hv]

/-- `recs_by_target` keeps the recursors whose major is a member iff `own`. -/
theorem recs_by_target_val (rs : alloc.vec.Vec arena.inductives.block_shape.RecShape)
    (k : Std.U64) (own : Bool) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.block_shape.RecShape),
      arena.inductives.rec_check.recs_by_target rs k own i out = ok o →
      o.val = out.val ++ (rs.val.drop i.val).filter (fun r => decide (r.tgt < k) == own) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) rs.val.length
    (fun i (_ : Unit) => ∀ (out o : alloc.vec.Vec arena.inductives.block_shape.RecShape),
      arena.inductives.rec_check.recs_by_target rs k own i out = ok o →
      o.val = out.val ++ (rs.val.drop i.val).filter (fun r => decide (r.tgt < k) == own))
    ?_ ?_ i ()
  · intro i _ hn out o h
    rw [arena.inductives.rec_check.recs_by_target.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
    rw [h, List.drop_eq_nil_of_le hn]; simp
  · intro i _ hlt ih out o h
    rw [arena.inductives.rec_check.recs_by_target.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : rs.val[i.val] = q := by
      have h1 := vec_index_some hq; rw [List.getElem?_eq_getElem hlt] at h1
      exact Option.some_inj.mp h1
    rw [List.drop_eq_getElem_cons hlt, List.filter_cons, hqx]
    by_cases hc : (q.tgt < k) = (own = true)
    · rw [ite_eq_left hc] at h
      have hb : (decide (q.tgt < k) == own) = true := by cases own <;> simp_all
      obtain ⟨q2, hq2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [ih i2 () (absSz_add_one hi2) out1 o h, ConRon.Refine.vec_push_val hout1,
        rc_rec_shape_dup_id _ _ hq2, show i2.val = i.val + 1 from absSz_add_one hi2, hb]
      simp
    · rw [ite_eq_right hc] at h
      have hb : (decide (q.tgt < k) == own) = false := by cases own <;> simp_all
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [ih i2 () (absSz_add_one hi2) out o h, show i2.val = i.val + 1 from absSz_add_one hi2, hb]
      simp

/-! ## The stored family: `aux_rule_fire`, `tgt_stored_rules`, `cons_block_recs_t`

These run at the constructors' visibility bound `vis` beside a LARGER index
`rf` (`cons_block_recs_t` pushes the recursors above `vis2`), so they are
stated at `IFEnvRelI rf lf` with the twin reading `lf.restrictTo (absU vis)`,
which is the twin's `fe.restrictTo vis₂`.  The firing mode at an OUTSIDE
major is computed from the major since task #119 (`auxRuleFire`, con-leche's
task #342 S5C): the class's levels and its parameters closed over the rule
prefix (`abstract_prefix`, `abstract_prefix_list`). -/

theorem abstract_prefix_aux (n : Nat) :
    ∀ {pers st lst} (k c : Std.U64) (e : arena.handle.EIdx),
      k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a)
        (arena.inductives.rec_check.abstract_prefix pers st k c e) lst
        (abstractPrefix n (absU c) (absEIdx e)) := by
  induction n with
  | zero =>
    intro pers st lst k c e hk hrel hinv
    rw [arena.inductives.rec_check.abstract_prefix, ite_eq_left (by scalar_tac), abstractPrefix]
    lockstep
  | succ n ih =>
    intro pers st lst k c e hk hrel hinv
    rw [arena.inductives.rec_check.abstract_prefix, ite_eq_right (by scalar_tac), abstractPrefix]
    lockstep

@[lockstep] theorem abstract_prefix_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k c : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.rec_check.abstract_prefix pers st k c e) lst
      (abstractPrefix (absU k) (absU c) (absEIdx e)) :=
  abstract_prefix_aux _ k c e rfl hrel hinv

theorem abstract_prefix_list_acc {pers} (r_p : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.rec_check.abstract_prefix_list pers st r_p xs i out) lst
        (do
          let r ← abstractPrefixList (absU r_p) (absEIdxLFrom xs i)
          pure (absEIdxL out ++ r)) := by
  intro i st lst out hrel hinv
  refine ls_cursor_acc xs absEIdx
    (fun (w : alloc.vec.Vec arena.handle.EIdx) l => do
      let r ← abstractPrefixList (absU r_p) l
      pure (absEIdxL w ++ r))
    (fun st j w => arena.inductives.rec_check.abstract_prefix_list pers st r_p xs j w)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst j w hn hrel hinv
    rw [arena.inductives.rec_check.abstract_prefix_list.eq_def,
      ite_eq_left (show j ≥ alloc.vec.Vec.len xs by scalar_tac), abstractPrefixList]
    simp only [pure_bind, List.append_nil]
    lockstep
  · intro st lst j w hk hrel hinv ih
    have ih' : ∀ st' lst' (j' : Std.Usize) (w' : alloc.vec.Vec arena.handle.EIdx),
        j'.val = j.val + 1 → AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = absEIdxL a)
          (arena.inductives.rec_check.abstract_prefix_list pers st' r_p xs j' w') lst'
          (do
            let r ← abstractPrefixList (absU r_p) ((xs.val.drop j'.val).map absEIdx)
            pure (absEIdxL w' ++ r)) := ih
    clear ih
    rw [arena.inductives.rec_check.abstract_prefix_list.eq_def,
      ite_eq_right (show ¬ j ≥ alloc.vec.Vec.len xs by scalar_tac), abstractPrefixList]
    simp only [bind_assoc, pure_bind]
    lockstep

@[lockstep] theorem abstract_prefix_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (r_p : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.rec_check.abstract_prefix_list pers st r_p xs 0#usize
        (alloc.vec.Vec.new arena.handle.EIdx)) lst
      (abstractPrefixList (absU r_p) (absEIdxL xs)) := by
  have h := abstract_prefix_list_acc r_p xs 0#usize st lst
    (alloc.vec.Vec.new arena.handle.EIdx) hrel hinv
  have e : (do
      let r ← abstractPrefixList (absU r_p) (absEIdxLFrom xs 0#usize)
      pure (absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ r) : AM _)
      = abstractPrefixList (absU r_p) (absEIdxL xs) := by
    simp [absEIdxL, absEIdxLFrom, alloc.vec.Vec.new]
  rwa [e] at h

/-- `aux_rule_fire` ⊑ `auxRuleFire` — the firing mode at an OUTSIDE major:
`.nested` at the class's levels and its parameters closed over the rule
prefix. -/
@[lockstep] theorem aux_rule_fire_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (m : arena.inductives.rec_check.TargetMajor) (r_p : Std.U64) :
    LS pers (fun a b => b = absIRecRuleFire a)
      (arena.inductives.rec_check.aux_rule_fire pers st m r_p) lst
      (auxRuleFire (absTargetMajor m) (absU r_p)) := by
  rw [arena.inductives.rec_check.aux_rule_fire, auxRuleFire]
  simp only [absTargetMajor]
  lockstep

/-- `generated_rules` ⊑ `generatedRules`: one generated recursor's rules at its
major — `sumRules` at the major's constructors, refired at an outside major. -/
@[lockstep] theorem generated_rules_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (r_p : Std.U64) (m : arena.inductives.rec_check.TargetMajor)
    (rhss : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absIRecRuleL a)
      (arena.inductives.rec_check.generated_rules pers st r_p m rhss) lst
      (generatedRules (absU r_p) (absTargetMajor m) (absEIdxL rhss)) := by
  rw [arena.inductives.rec_check.generated_rules, generatedRules]
  lockstep
  all_goals sorry -- T143-STUB

/-- `rec_k_expected` ⊑ `recKExpected`: the K flag a recursor of this block has. -/
@[lockstep] theorem rec_k_expected_twin (p : arena.inductives.block_shape.BlockShape)
    (m : arena.inductives.rec_check.TargetMajor) :
    LSP (arena.inductives.rec_check.rec_k_expected p m)
      (fun o => TwinEq (recKExpected (absBlockShape p) (absTargetMajor m)) o) := by
  intro o h
  rw [arena.inductives.rec_check.rec_k_expected] at h
  simp only [TwinEq, recKExpected, absTargetMajor]
  cases hm : m.member with
  | none =>
    simp only [hm] at h
    cases Result.ok_injective h
    rfl
  | some t =>
    simp only [hm, Option.map_some] at h ⊢
    by_cases h1 : m.ctors.val.length = 1
    · obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp h1
      have hl : alloc.vec.Vec.len m.ctors = 1#usize := by
        have : (alloc.vec.Vec.len m.ctors).val = 1 := by simp [alloc.vec.Vec.len, hc]
        scalar_tac
      rw [if_pos hl] at h
      obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hk' := shape_k_twin p k hk
      simp only [TwinEq] at hk'
      simp only [absCtorsL, hc, List.map_cons, List.map_nil]
      have hidx : alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice (arena.env.IConstantVal × Std.U64))
          m.ctors 0#usize = ok c := by
        rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
        simp [hc]
      by_cases hk1 : k = 1#u64
      · rw [if_pos hk1] at h
        have hk1' : (absBlockShape p).k = 1 := by rw [hk', hk1]; rfl
        rw [hk1']
        cases hp : p.is_prop
        · rw [if_neg (by simp [hp])] at h
          cases Result.ok_injective h
          simp [absBlockShape, hp]
        · rw [if_pos hp, hidx, bind_ok] at h
          cases Result.ok_injective h
          simp only [absBlockShape, hp, absU]
          by_cases hc0 : c.2 = 0#u64
          · simp [hc0]
          · have : c.2.val ≠ 0 := fun hv => hc0 (by scalar_tac)
            simp [hc0, this]
      · rw [if_neg hk1] at h
        cases Result.ok_injective h
        have : (absBlockShape p).k ≠ 1 := by
          rw [hk']; intro hv; exact hk1 (by simp [absU] at hv; scalar_tac)
        simp [this]
    · have hl : ¬ alloc.vec.Vec.len m.ctors = 1#usize := by
        intro hv; exact h1 (by have := congrArg (·.val) hv; simpa [alloc.vec.Vec.len] using this)
      rw [if_neg hl] at h
      cases Result.ok_injective h
      rcases hc : m.ctors.val with _ | ⟨c, _ | ⟨c2, rest⟩⟩
      · simp [absCtorsL, hc]
      · exact absurd (by simp [hc]) h1
      · simp [absCtorsL, hc]

/-- A checked recursor with its major and its right-hand sides. -/
def absRecOut (x : arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
    alloc.vec.Vec arena.handle.EIdx) : IConstantVal × TargetMajor × List EIdx :=
  (absIConstantVal x.1, absTargetMajor x.2.1, absEIdxL x.2.2)

/-- `block_rec_infos_tf` ⊑ `blockRecInfosTF` from the recursor cursor on, behind
the accumulator: each generated recursor's record at its major. -/
@[lockstep] theorem block_rec_infos_tf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape) (m : Std.U64)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) (acc : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => a.val.map absIConstantInfo = acc.val.map absIConstantInfo ++ b)
      (arena.inductives.rec_check.block_rec_infos_tf pers st p m out acc) lst
      (blockRecInfosTF (absBlockShape p) (absU m) ((out.val.drop m.val).map absRecOut)) := by
  sorry -- T143-STUB

/-- `recs_by_target … true`: the member recursors (`p.recs.filter (·.tgt < k)`). -/
@[lockstep] theorem recs_by_target_own_twin (rs : alloc.vec.Vec arena.inductives.block_shape.RecShape)
    (k : Std.U64) :
    LSP (arena.inductives.rec_check.recs_by_target rs k true 0#usize
        (alloc.vec.Vec.new arena.inductives.block_shape.RecShape))
      (fun o => TwinEq ((rs.val.map absRecShape).filter fun rc => rc.tgt < absU k)
        (o.val.map absRecShape)) := by
  intro o h
  rw [TwinEq, recs_by_target_val rs k true _ _ o h, List.filter_map]
  simp only [alloc.vec.Vec.new, List.drop_zero,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
  congr 1

/-- `recs_by_target … false`: the auxiliary recursors. -/
@[lockstep] theorem recs_by_target_aux_twin (rs : alloc.vec.Vec arena.inductives.block_shape.RecShape)
    (k : Std.U64) :
    LSP (arena.inductives.rec_check.recs_by_target rs k false 0#usize
        (alloc.vec.Vec.new arena.inductives.block_shape.RecShape))
      (fun o => TwinEq ((rs.val.map absRecShape).filter fun rc => !(rc.tgt < absU k))
        (o.val.map absRecShape)) := by
  intro o h
  rw [TwinEq, recs_by_target_val rs k false _ _ o h, List.filter_map]
  simp only [alloc.vec.Vec.new, List.drop_zero,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
  congr 1

/-! ## `target_rec_pins`, `_aux`, `_names`: one twin `targetRecPins`, split
at its two binds (`rcPinsTail` is the twin's continuation after `n₀`) -/

/-- `targetRecPins` after `n₀` (the Rust's `target_rec_pins_names`). -/
def rcPinsTail (p : BlockShape) (block : List IConstantInfo) (n₀ : NIdx) : AM Unit := do
  let aux := p.recs.filter fun rc => !(rc.tgt < p.k)
  let wantAux ← (List.range aux.length).mapM fun i =>
    internNNode (.str n₀ s!"rec_{i + 1}")
  let gotAux := aux.map (·.cvR.name)
  unless gotAux.length == wantAux.length && wantAux.all (gotAux.contains ·) &&
      gotAux.all (wantAux.contains ·) do
    fail (.invalid "target rec: the block's auxiliary recursor names are not the generated \
      ones (T.rec_1 … T.rec_n)")
  unless nameNodup (p.recs.map (·.cvR.name)) do
    fail (.invalid "target rec: two recursors of the block share a name")
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    unless cvTs.length == p.k && rs.length == p.recs.length &&
        p.allCtors.map (·.1.name) == cs.map (·.1.name) do
      fail (.invalid "target rec: the recursor record is not the generated recursor \
        (constructor grouping)")
  | none => fail (.invalid "target rec: the block does not split")

/-- `targetRecPins` after its member-name pin (the Rust's `target_rec_pins_aux`). -/
def rcPinsAux (p : BlockShape) (block : List IConstantInfo) : AM Unit := do
  let n₀ ← match p.members with
    | [] => internNNode .anonymous
    | ms :: _ => pure ms.cvT.name
  rcPinsTail p block n₀

theorem targetRecPins_split (p : BlockShape) (block : List IConstantInfo) :
    targetRecPins p block = (do
      unless blockRecLpsOk p do
        fail (.invalid "target rec: the recursor's level parameters are not the generated ones")
      unless ← blockRecNamesUnreserved p.recs do
        fail (.invalid "target rec: a recursor is named for a pinned basis constant, a literal \
          guard's slot or a certified Nat operation")
      let own := p.recs.filter fun rc => rc.tgt < p.k
      unless ← blockRecNameSetOk p.members own do
        fail (.invalid "target rec: the block's recursor names are not the generated ones \
          (one T.rec per member)")
      rcPinsAux p block) := rfl

@[lockstep] theorem target_rec_pins_names_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape)
    (block : alloc.vec.Vec arena.env.IConstantInfo) (n0 : arena.handle.NIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_rec_pins_names pers st p block n0) lst
      (rcPinsTail (absBlockShape p) (absICIL block) (absNIdx n0)) := by
  rw [arena.inductives.rec_check.target_rec_pins_names, rcPinsTail]
  simp only [absBlockShape_recs]
  lockstep

@[lockstep] theorem target_rec_pins_aux_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape)
    (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_rec_pins_aux pers st p block) lst
      (rcPinsAux (absBlockShape p) (absICIL block)) := by
  rw [arena.inductives.rec_check.target_rec_pins_aux, rcPinsAux]
  simp only [absBlockShape_members]
  rcases hm : p.members.val with _ | ⟨m0, ms⟩
  · simp only [List.map_nil]
    rw [ite_eq_left (by have : p.members.val.length = 0 := by simp [hm]
                        scalar_tac)]
    lockstep
  · simp only [List.map_cons, pure_bind]
    rw [ite_eq_right (by simp [alloc.vec.Vec.len, hm])]
    lockstep

@[lockstep] theorem target_rec_pins_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape)
    (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_rec_pins pers st p block) lst
      (targetRecPins (absBlockShape p) (absICIL block)) := by
  rw [arena.inductives.rec_check.target_rec_pins, targetRecPins_split]
  simp only [absBlockShape_members, absBlockShape_recs]
  lockstep


/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.target_abs_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms target_abs_ls

-- T143-CENSUS /-- info: 'ConRon.Refine2.target_major_nfs_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- T143-CENSUS #guard_msgs in #print axioms target_major_nfs_ls

-- T143-CENSUS /-- info: 'ConRon.Refine2.target_major_of_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- T143-CENSUS #guard_msgs in #print axioms target_major_of_ls

-- T143-CENSUS /-- info: 'ConRon.Refine2.target_k53_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- T143-CENSUS #guard_msgs in #print axioms target_k53_ls

-- T143-CENSUS /-- info: 'ConRon.Refine2.cons_block_recs_t_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- T143-CENSUS #guard_msgs in #print axioms cons_block_recs_t_ls

/-- info: 'ConRon.Refine2.target_rec_pins_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms target_rec_pins_ls

/-- info: 'ConRon.Refine2.want_aux_names_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms want_aux_names_ls

end ConRon.Refine2
