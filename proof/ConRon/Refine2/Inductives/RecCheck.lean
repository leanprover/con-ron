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
  `CoreCtx vis rf lf`; the stored family (`aux_rule_fire_r`,
  `tgt_stored_rules`, `cons_block_recs_t`) runs at the constructors' `vis2`
  beside the GROWING index, so it takes `IFEnvRelI rf lf` and reads
  `lf.restrictTo (absU vis)` — the twin's `fe.restrictTo vis₂`
  (`IFEnvInv.coreCtxAt` gives the core's `CoreCtx`).
* **Binder data**: `binders_beq` compares raw `BinderMeta`s, so the two erased
  telescopes carry `TeleWF` (`erase_binders_ls`'s answer; `strip_pis`'s from
  `rc_strip_pis_wf`); `target_k53_ls` takes `TeleWF tele`.

## Helpers restated here (they belong elsewhere)

`rec_rule_k_of/eta_of/bits` and `sum_rules` at `CoreCtx` (Prims/SumInstall
have them at `IFEnvRelI` + `hvis` only), `nested_rule_syn` and its body
(checker tier; nobody had them), `strip_pis`'s telescope well-formedness,
`take_eidx_n` as `List.take`, and raw-identity copies (`rc_ctors_dup_id`,
`rc_rec_shape_dup_id`; `eidx_vec_dup` is `PA1.eidx_vec_dup_ls`).  `targetRecPins` is split at its
two binds (`targetRecPins_split`, `rcPinsAux`, `rcPinsTail`, by `rfl`) to meet
the Rust's `_aux`/`_names` fragments.
-/
import ConRon.Refine2.Inductives.PositivityNest
import ConRon.Refine2.Inductives.BlockParts
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


/-! ## Helpers for Shape/Abs

`core::rec_rule_*` and `sum_install::sum_rules` at a SPLIT counter: the
statements in `Inductives/Prims.lean` / `Inductives/SumInstall.lean` take
`IFEnvRelI rf lf` and `absU vis = lf.visibleBelow`, which `cons_block_recs_t`
(the constructors' `vis2` beside the growing index) cannot supply; these take
`CoreCtx vis rf lf`, which `IFEnvInv.coreCtxAt` builds there.  They belong
beside their `IFEnvRelI` forms. -/

section CtxHelpers
open IndModeledPrims
attribute [local lockstep_simp] absIRecRule_ctor_eq absIRecRule_nfields_eq
  IndModeledPrims.absIRecRule_ctorParams Lockstep.absIRecRule_fire
  absIRecRule_rhs_eq Lockstep.absIRecRule_k Lockstep.absIRecRule_eta
  IndModeledPrims.absIRecRule_paramsBlind Lockstep.absIIndCaps_eta
  Lockstep.absIIndCaps_etaCtor IndModeledPrims.absIIndCaps_ruleK
  IndModeledPrims.decide_u64_eq_zero etag_const_abs

@[lockstep] theorem rec_rule_k_of_ctx_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis rf lf) (ctor : arena.handle.NIdx) :
    LS pers (fun a b => b = a) (arena.core.rec_rule_k_of pers vis st rf ctor) lst
      (recRuleKOf lf (absNIdx ctor)) := by
  rw [arena.core.rec_rule_k_of, recRuleKOf]
  lockstep

@[lockstep] theorem rec_rule_eta_of_ctx_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis rf lf) (rn ctor : arena.handle.NIdx) :
    LS pers (fun a b => b = a) (arena.core.rec_rule_eta_of pers vis st rf rn ctor) lst
      (recRuleEtaOf lf (absNIdx rn) (absNIdx ctor)) := by
  rw [arena.core.rec_rule_eta_of, recRuleEtaOf]
  lockstep
  all_goals
    refine LS.pure ?_ ‹_› ‹_›
    simp_all [absNIdxList]
    exact beq_eq_decide _ _

@[lockstep] theorem rec_rule_bits_ctx_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis rf lf) (rn : arena.handle.NIdx) (rl : arena.env.IRecRule) :
    LS pers (fun a b => b = absIRecRule a) (arena.core.rec_rule_bits pers vis st rf rn rl) lst
      (recRuleBits lf (absNIdx rn) (absIRecRule rl)) := by
  rw [arena.core.rec_rule_bits, recRuleBits]
  lockstep

set_option maxHeartbeats 800000 in
theorem sum_rules_ctx_aux (m : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf lf} {rec_name : arena.handle.NIdx}
      {n_p m_i r_p : Std.U64} {rec_ty : arena.handle.EIdx}
      {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
      {rhss : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
      {out : alloc.vec.Vec arena.env.IRecRule},
      ctors.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      CoreCtx vis rf lf →
      Lockstep.LS pers (fun a b => b = absIRecRuleL a)
        (arena.inductives.sum_install.sum_rules pers vis st rf rec_name n_p m_i
          r_p rec_ty ctors rhss i out) lst
        (do pure (absIRecRuleL out ++
          (← sumRules lf (absNIdx rec_name) (absU n_p) (absU m_i) (absU r_p)
            (absEIdx rec_ty) (absCtorsLFrom ctors i) (absEIdxLFrom rhss i)))) := by
  induction m with
  | zero =>
    intro pers st lst vis rf lf rec_name n_p m_i r_p rec_ty ctors rhss i out hn hrel hinv hctx
    rw [arena.inductives.sum_install.sum_rules, if_pos (by scalar_tac), absCtorsLFrom,
      vecFrom_nil _ _ _ (by omega)]
    simp only [sumRules]
    lockstep
  | succ m ih =>
    intro pers st lst vis rf lf rec_name n_p m_i r_p rec_ty ctors rhss i out hn hrel hinv hctx
    rw [arena.inductives.sum_install.sum_rules, if_neg (by scalar_tac), absCtorsLFrom,
      vecFrom_cons _ _ _ (by omega)]
    by_cases hr : i.val < rhss.val.length
    · rw [if_neg (by scalar_tac), absEIdxLFrom, vecFrom_cons _ _ _ hr]
      simp only [sumRules]
      lockstep
    · rw [if_pos (by scalar_tac), absEIdxLFrom, vecFrom_nil _ _ _ (by omega)]
      simp only [sumRules]
      lockstep

/-- `sum_rules` ⊑ `sumRules` at a split counter (`CoreCtx`). -/
@[lockstep] theorem sum_rules_ctx_ls {pers st lst} {vis : Std.U64} {rf lf}
    {rec_name : arena.handle.NIdx} {n_p m_i r_p : Std.U64} {rec_ty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {rhss : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf) :
    LS pers (fun a b => b = absIRecRuleL a)
      (arena.inductives.sum_install.sum_rules pers vis st rf rec_name n_p m_i r_p rec_ty ctors
        rhss i out) lst
      (do pure (absIRecRuleL out ++
        (← sumRules lf (absNIdx rec_name) (absU n_p) (absU m_i) (absU r_p)
          (absEIdx rec_ty) (absCtorsLFrom ctors i) (absEIdxLFrom rhss i)))) :=
  sum_rules_ctx_aux _ rfl hrel hinv hctx

/-- `sum_rules` from `0` into an empty accumulator IS `sumRules`. -/
@[lockstep] theorem sum_rules_ctx_new_ls {pers st lst} {vis : Std.U64} {rf lf}
    {rec_name : arena.handle.NIdx} {n_p m_i r_p : Std.U64} {rec_ty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {rhss : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf) :
    LS pers (fun a b => b = absIRecRuleL a)
      (arena.inductives.sum_install.sum_rules pers vis st rf rec_name n_p m_i r_p rec_ty ctors
        rhss 0#usize (alloc.vec.Vec.new arena.env.IRecRule)) lst
      (sumRules lf (absNIdx rec_name) (absU n_p) (absU m_i) (absU r_p)
          (absEIdx rec_ty) (absCtorsL ctors) (absEIdxL rhss)) := by
  have h := sum_rules_ctx_ls (rec_name := rec_name) (n_p := n_p) (m_i := m_i) (r_p := r_p)
    (rec_ty := rec_ty) (ctors := ctors) (rhss := rhss) (i := 0#usize)
    (out := alloc.vec.Vec.new arena.env.IRecRule) hrel hinv hctx
  have e : (do pure (absIRecRuleL (alloc.vec.Vec.new arena.env.IRecRule) ++
        (← sumRules lf (absNIdx rec_name) (absU n_p) (absU m_i) (absU r_p)
          (absEIdx rec_ty) (absCtorsLFrom ctors 0#usize) (absEIdxLFrom rhss 0#usize))) : AM _) =
      sumRules lf (absNIdx rec_name) (absU n_p) (absU m_i) (absU r_p)
          (absEIdx rec_ty) (absCtorsL ctors) (absEIdxL rhss) := by
    simp [absIRecRuleL, alloc.vec.Vec.new]
  rwa [e] at h

end CtxHelpers

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
      if_pos (show t ≥ alloc.vec.Vec.len former_tys by scalar_tac), absEIdxLFrom,
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
      if_neg (show ¬ t ≥ alloc.vec.Vec.len former_tys by scalar_tac), absEIdxLFrom,
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

variable {pers : arena.store.PersTier} {mode : kernel.env.CheckMode} {vis : Std.U64}
  {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx vis rf lf) (d : Std.U64)
  (names : alloc.vec.Vec arena.handle.NIdx) (lvls : arena.handle.LsIdx)
  (holes pfvs xs ys : alloc.vec.Vec arena.handle.EIdx)

include hctx in
/-- The infer arm at `i` from the main walk at `i + 1`. -/
theorem target_params_def_eq_infer_of (i : Std.Usize)
    (hmain : ∀ (j : Std.Usize), j.val = i.val + 1 → ∀ st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_params_def_eq pers st mode vis rf d names lvls
          holes pfvs xs ys j) lst
        (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
          (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) ((xs.val.drop j.val).map absEIdx)
          ((ys.val.drop j.val).map absEIdx)))
    (a2 b2 : arena.handle.EIdx) :
    ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_params_def_eq_infer pers st mode vis rf d names
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

include hctx in
theorem target_params_def_eq_aux :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_params_def_eq pers st mode vis rf d names lvls
          holes pfvs xs ys i) lst
        (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
          (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) ((xs.val.drop i.val).map absEIdx)
          ((ys.val.drop i.val).map absEIdx)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_params_def_eq pers st mode vis rf d names lvls
          holes pfvs xs ys i) lst
        (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
          (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) ((xs.val.drop i.val).map absEIdx)
          ((ys.val.drop i.val).map absEIdx))) ?_ ?_ i ()
  · intro i _ hn st lst hrel hinv
    rw [arena.inductives.rec_check.target_params_def_eq.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), List.drop_eq_nil_of_le hn,
      List.map_nil]
    by_cases hy : ys.val.length ≤ i.val
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ys by scalar_tac), List.drop_eq_nil_of_le hy,
        List.map_nil, targetParamsDefEq]
      lockstep
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ys by scalar_tac),
        if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac),
        List.drop_eq_getElem_cons (show i.val < ys.val.length by omega), List.map_cons,
        targetParamsDefEq]
      lockstep
      all_goals simp
  · intro i _ hlt ih st lst hrel hinv
    have hmain : ∀ (j : Std.Usize), j.val = i.val + 1 → ∀ st lst,
        AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = a)
          (arena.inductives.rec_check.target_params_def_eq pers st mode vis rf d names lvls
            holes pfvs xs ys j) lst
          (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
            (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) ((xs.val.drop j.val).map absEIdx)
            ((ys.val.drop j.val).map absEIdx)) := fun j hj => ih j () hj
    clear ih
    have hinfer := target_params_def_eq_infer_of hctx d names lvls holes pfvs xs ys i hmain
    rw [arena.inductives.rec_check.target_params_def_eq.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons]
    by_cases hy : ys.val.length ≤ i.val
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ys by scalar_tac), List.drop_eq_nil_of_le hy,
        List.map_nil, targetParamsDefEq]
      lockstep
      all_goals simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ys by scalar_tac),
        List.drop_eq_getElem_cons (show i.val < ys.val.length by omega), List.map_cons,
        targetParamsDefEq]
      lockstep

end ParamsDefEq

@[lockstep] theorem target_params_def_eq_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (d : Std.U64) (names : alloc.vec.Vec arena.handle.NIdx) (lvls : arena.handle.LsIdx)
    (holes pfvs xs ys : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_params_def_eq pers st mode vis rf d names lvls
        holes pfvs xs ys i) lst
      (targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
        (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs) (absEIdxLFrom xs i)
        (absEIdxLFrom ys i)) :=
  target_params_def_eq_aux hctx d names lvls holes pfvs xs ys i st lst hrel hinv

@[lockstep] theorem target_params_def_eq_infer_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (d : Std.U64) (names : alloc.vec.Vec arena.handle.NIdx) (lvls : arena.handle.LsIdx)
    (holes pfvs xs ys : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
    (a2 b2 : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_params_def_eq_infer pers st mode vis rf d names
        lvls holes pfvs xs ys i a2 b2) lst
      (do
        let _ ← inferTypeCore (ConRon.Refine.absMode mode) lf checkFuel (absU d) (absEIdx a2)
        let _ ← inferTypeCore (ConRon.Refine.absMode mode) lf checkFuel (absU d) (absEIdx b2)
        if ← isDefEqCore (ConRon.Refine.absMode mode) lf checkFuel (absU d) (absEIdx a2)
            (absEIdx b2) then
          targetParamsDefEq (ConRon.Refine.absMode mode) lf (absU d) (absNIdxL names)
            (absLsIdx lvls) (absEIdxL holes) (absEIdxL pfvs)
            ((xs.val.drop (i.val + 1)).map absEIdx) ((ys.val.drop (i.val + 1)).map absEIdx)
        else pure false) :=
  target_params_def_eq_infer_of hctx d names lvls holes pfvs xs ys i
    (fun j _ st lst hrel hinv => target_params_def_eq_aux hctx d names lvls holes pfvs xs ys
      j st lst hrel hinv) a2 b2 st lst hrel hinv

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
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    exact h.symm
  · intro i x o hx h
    have hlt : i.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.rec_check.ctors_name.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨⟨iv, k⟩, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnx : (iv, k) = x := by
      have h1 := vec_index_some hiv; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hnx
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv : b = (absNIdx iv.name == absNIdx c) := nidx_eq2_abs hb
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨hbv.symm, h.symm⟩

@[lockstep] theorem ctors_name_twin (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (c : arena.handle.NIdx) :
    LSP (arena.inductives.rec_check.ctors_name cs c 0#usize)
      (fun o => TwinEq ((absCtorsL cs).any (·.1.name == absNIdx c)) o) := by
  intro o h
  rw [TwinEq, ctors_name_abs cs c 0#usize o h, absCtorsLFrom_zero]

/-! ## `target_pin_tys`, `target_major_pins` -/

theorem target_pin_tys_aux {pers} {mode : kernel.env.CheckMode} {vis : Std.U64}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx vis rf lf) (d : Std.U64)
    (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.rec_check.target_pin_tys pers st mode vis rf d xs i) lst
        (targetPinTys (ConRon.Refine.absMode mode) lf (absU d)
          ((xs.val.drop i.val).map absEIdx)) := by
  refine ls_cursor xs absEIdx
    (fun l => targetPinTys (ConRon.Refine.absMode mode) lf (absU d) l)
    (fun st i => arena.inductives.rec_check.target_pin_tys pers st mode vis rf d xs i) ?_ ?_
  · intro st lst i hn hrel hinv
    rw [arena.inductives.rec_check.target_pin_tys.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), targetPinTys]
    lockstep
  · intro st lst i hlt hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = a)
          (arena.inductives.rec_check.target_pin_tys pers st' mode vis rf d xs j) lst'
          (targetPinTys (ConRon.Refine.absMode mode) lf (absU d)
            ((xs.val.drop j.val).map absEIdx)) := ih
    clear ih
    rw [arena.inductives.rec_check.target_pin_tys.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac), targetPinTys]
    lockstep

@[lockstep] theorem target_pin_tys_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (d : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_pin_tys pers st mode vis rf d xs i) lst
      (targetPinTys (ConRon.Refine.absMode mode) lf (absU d) (absEIdxLFrom xs i)) :=
  target_pin_tys_aux hctx d xs i st lst hrel hinv

@[lockstep] theorem target_major_pins_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (r_p : Std.U64) (m : arena.inductives.rec_check.TargetMajor) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_major_pins pers st mode vis rf r_p m) lst
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
    rw [arena.inductives.rec_check.nfs_reverse.eq_def, if_pos (by scalar_tac),
      Result.ok.injEq] at h
    subst h; simp [hn]
  | succ n ih =>
    intro i out o hn hle h
    rw [arena.inductives.rec_check.nfs_reverse.eq_def, if_neg (by scalar_tac)] at h
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
      if_pos (show i ≥ alloc.vec.Vec.len rules by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.rec_check.refire.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rules by
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
    injection e1 with h1 h2 h3 h4 h5 h6 h7 h8
    rw [h1, h2, h3, h5, h6, h7, h8]

@[lockstep] theorem refire_twin (rules : alloc.vec.Vec arena.env.IRecRule)
    (f : arena.env.IRecRuleFire) :
    LSP (arena.inductives.rec_check.refire rules f 0#usize
        (alloc.vec.Vec.new arena.env.IRecRule))
      (fun o => TwinEq ((absIRecRuleL rules).map fun rl => { rl with fire := absIRecRuleFire f })
        (absIRecRuleL o)) := by
  intro o h
  rw [TwinEq, refire_abs rules f _ _ o h]
  simp [absIRecRuleL, absIRecRuleLFrom, alloc.vec.Vec.new]

theorem some_aux_rec_abs (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (k : Std.U64) :
    ∀ (i : Std.Usize) (o : Bool), arena.inductives.rec_check.some_aux_rec rs k i = ok o →
      o = ((rs.val.drop i.val).map absRecShape).any (fun rc => !(rc.tgt < absU k)) := by
  intro i o h
  have key := vec_cursor_any rs (fun r => !(decide ((absRecShape r).tgt < absU k)))
    (fun i => arena.inductives.rec_check.some_aux_rec rs k i) ?_ ?_ i o h
  · rw [key, List.any_map]; rfl
  · intro i o hn h
    rw [arena.inductives.rec_check.some_aux_rec.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
    exact h.symm
  · intro i x o hx h
    rw [arena.inductives.rec_check.some_aux_rec.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    by_cases hlt : q.tgt < k
    · rw [if_pos hlt] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine Or.inr ⟨?_, i2, absSz_add_one hi2, h⟩
      simp only [absRecShape, absU]; scalar_tac
    · rw [if_neg hlt, Result.ok.injEq] at h
      refine Or.inl ⟨?_, h.symm⟩
      simp only [absRecShape, absU]; scalar_tac

@[lockstep] theorem block_nested_bit_twin (p : arena.inductives.block_parts.BlockShape)
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
  · rw [if_neg (by simp), Result.ok.injEq] at h
    simp [h]
  · rw [if_pos rfl] at h
    obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [arena.inductives.block_parts.shape_k] at hk
    have hk' : k.val = p.members.val.length := by
      have := lift_cast_u64_of_usize _ k hk; simpa using this
    rw [some_aux_rec_abs _ _ _ o h]
    simp only [if_true, absBlockShape, BlockShape.k, List.length_map,
      show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]
    rw [show absU k = p.members.val.length from hk']

/-! ## `erase_list`, `erase_binders`: the twin's inline `mapM eraseFVarTys` -/

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
      if_pos (show k ≥ alloc.vec.Vec.len xs by scalar_tac)]
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
      if_neg (show ¬ k ≥ alloc.vec.Vec.len xs by scalar_tac)]
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

/-- `erase_binders` ⊑ the twin's `mapM fun b => do pure ((← eraseFVarTys b.1), b.2)`,
behind the accumulator; a telescope of well-formed binder data stays so (the
comparison `binders_beq` needs it). -/
theorem erase_binders_acc {pers} (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (hbs : TeleWF bs) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)),
      TeleWF out → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absBinderL a ∧ TeleWF a)
        (arena.inductives.rec_check.erase_binders pers st bs i out) lst
        (do
          let r ← (absBinderLFrom bs i).mapM fun b => do pure ((← eraseFVarTys b.1), b.2)
          pure (absBinderL out ++ r)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) bs.val.length
    (fun i (_ : Unit) => ∀ st lst
      (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)),
      TeleWF out → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absBinderL a ∧ TeleWF a)
        (arena.inductives.rec_check.erase_binders pers st bs i out) lst
        (do
          let r ← (absBinderLFrom bs i).mapM fun b => do pure ((← eraseFVarTys b.1), b.2)
          pure (absBinderL out ++ r))) ?_ ?_ i ()
  · intro i _ hn st lst out hout hrel hinv
    rw [arena.inductives.rec_check.erase_binders.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len bs by scalar_tac), absBinderLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil]
    simp only [List.mapM_nil, pure_bind, List.append_nil]
    exact LS.pure ⟨rfl, hout⟩ hrel hinv
  · intro i _ hlt ih st lst out hout hrel hinv
    have ih' : ∀ (j : Std.Usize), j.val = i.val + 1 → ∀ st lst
        (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)),
        TeleWF out → AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = absBinderL a ∧ TeleWF a)
          (arena.inductives.rec_check.erase_binders pers st bs j out) lst
          (do
            let r ← (absBinderLFrom bs j).mapM fun b => do pure ((← eraseFVarTys b.1), b.2)
            pure (absBinderL out ++ r)) := fun j hj => ih j () hj
    clear ih
    have hwi := TeleWF.get hbs i.val hlt
    rw [arena.inductives.rec_check.erase_binders.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len bs by scalar_tac), absBinderLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    lockstep

@[lockstep] theorem erase_binders_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (hbs : TeleWF bs) :
    LS pers (fun a b => b = absBinderL a ∧ TeleWF a)
      (arena.inductives.rec_check.erase_binders pers st bs 0#usize
        (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta))) lst
      ((absBinderL bs).mapM fun b => do pure ((← eraseFVarTys b.1), b.2)) := by
  have h := erase_binders_acc bs hbs 0#usize st lst
    (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) TeleWF.new hrel hinv
  have e : (do
      let r ← (absBinderLFrom bs 0#usize).mapM fun b => do pure ((← eraseFVarTys b.1), b.2)
      pure (absBinderL (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) ++ r) :
        AM _)
      = (absBinderL bs).mapM (fun b => do pure ((← eraseFVarTys b.1), b.2)) := by
    simp [absBinderL, absBinderLFrom, alloc.vec.Vec.new]
  rwa [e] at h

/-! ## `binders_beq`: the twin's inline `!=` on two telescopes -/

theorem binders_beq_abs (a b : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (ha : TeleWF a) (hb : TeleWF b) :
    ∀ (i : Std.Usize) (o : Bool), arena.inductives.rec_check.binders_beq a b i = ok o →
      o = decide (absBinderLFrom a i = absBinderLFrom b i) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) a.val.length
    (fun i (_ : Unit) => ∀ (o : Bool), arena.inductives.rec_check.binders_beq a b i = ok o →
      o = decide (absBinderLFrom a i = absBinderLFrom b i)) ?_ ?_ i ()
  · intro i _ hn o h
    rw [arena.inductives.rec_check.binders_beq.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
    simp only [absBinderLFrom, List.drop_eq_nil_of_le hn, List.map_nil]
    by_cases hy : b.val.length ≤ i.val
    · rw [if_pos (show i ≥ alloc.vec.Vec.len b by scalar_tac), Result.ok.injEq] at h
      rw [List.drop_eq_nil_of_le hy]; simp [← h]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac),
        if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac), Result.ok.injEq] at h
      rw [List.drop_eq_getElem_cons (show i.val < b.val.length by omega)]; simp [← h]; omega
  · intro i _ hlt ih o h
    rw [arena.inductives.rec_check.binders_beq.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac),
      if_neg (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
    simp only [absBinderLFrom, List.drop_eq_getElem_cons hlt, List.map_cons]
    by_cases hy : b.val.length ≤ i.val
    · rw [if_pos (show i ≥ alloc.vec.Vec.len b by scalar_tac), Result.ok.injEq] at h
      rw [List.drop_eq_nil_of_le hy]; simp [← h]
    · have hlb : i.val < b.val.length := by omega
      rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
      rw [List.drop_eq_getElem_cons hlb, List.map_cons]
      obtain ⟨⟨e, bm⟩, he, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨⟨e1, bm1⟩, he1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
      obtain ⟨b1, hb1, h3⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
      have hb1v := eidx_eq2_abs_decide hb1
      have hea : a.val[i.val] = (e, bm) := by
        have := vec_index_some he; rw [List.getElem?_eq_getElem hlt] at this
        exact Option.some_inj.mp this
      have heb : b.val[i.val] = (e1, bm1) := by
        have := vec_index_some he1; rw [List.getElem?_eq_getElem hlb] at this
        exact Option.some_inj.mp this
      have hwa : ConRon.Refine.PropWhenWF bm.pw := by
        have := TeleWF.get ha i.val hlt; rw [hea] at this; exact this
      have hwb : ConRon.Refine.PropWhenWF bm1.pw := by
        have := TeleWF.get hb i.val hlb; rw [heb] at this; exact this
      rw [hea, heb]
      cases b1 with
      | false =>
        rw [if_neg (by simp), Result.ok.injEq] at h3
        subst h3
        have hne : absEIdx e ≠ absEIdx e1 := by simpa using hb1v.symm
        simp [hne]
      | true =>
        rw [if_pos rfl] at h3
        have hee : absEIdx e = absEIdx e1 := by simpa using hb1v.symm
        obtain ⟨b2, hb2, h4⟩ := ConRon.Refine.bind_eq_ok_iff.mp h3
        have hb2v := ConRon.Refine.Expr.binder_meta_beq_refines hwa hwb hb2
        cases b2 with
        | false =>
          rw [if_neg (by simp), Result.ok.injEq] at h4
          subst h4
          have hne : ConRon.Refine.absPropWhen bm.pw ≠ ConRon.Refine.absPropWhen bm1.pw := by
            simpa [ConRon.Refine.absBinderMeta] using hb2v.symm
          simp [hee, hne]
        | true =>
          rw [if_pos rfl] at h4
          have hbm : ConRon.Refine.absPropWhen bm.pw = ConRon.Refine.absPropWhen bm1.pw := by
            simpa [ConRon.Refine.absBinderMeta] using hb2v.symm
          obtain ⟨i5, hi5, h5⟩ := ConRon.Refine.bind_eq_ok_iff.mp h4
          rw [ih i5 () (absSz_add_one hi5) o h5]
          simp only [absBinderLFrom, absSz_add_one hi5]
          simp [hee, hbm]

@[lockstep] theorem binders_beq_twin (a b : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (ha : TeleWF a) (hb : TeleWF b) :
    LSP (arena.inductives.rec_check.binders_beq a b 0#usize)
      (fun o => TwinEq (absBinderL a == absBinderL b) o) := by
  intro o h
  rw [TwinEq, binders_beq_abs a b ha hb 0#usize o h, absBinderLFrom_zero, absBinderLFrom_zero]
  exact beq_eq_decide _ _

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
      if_pos (show k ≥ alloc.vec.Vec.len xs by scalar_tac), targetPiDomsWith]
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
      if_neg (show ¬ k ≥ alloc.vec.Vec.len xs by scalar_tac), targetPiDomsWith]
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
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape)
    (former_tys pfvs : alloc.vec.Vec arena.handle.EIdx) (us : arena.handle.LsIdx)
    (ds : alloc.vec.Vec arena.handle.EIdx) (lvls : arena.handle.LsIdx)
    (eds : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_class_match pers st mode vis rf p former_tys pfvs us
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

variable {pers : arena.store.PersTier} {mode : kernel.env.CheckMode} {vis : Std.U64}
  {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx vis rf lf)
  (p : arena.inductives.block_parts.BlockShape)
  (former_tys pfvs : alloc.vec.Vec arena.handle.EIdx) (us : arena.handle.LsIdx)
  (ds : alloc.vec.Vec arena.handle.EIdx)
  (ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
  (tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)

include hctx in
/-- The Rust examines `tbl[i-1], …, tbl[0]` pushing the matches; the twin's
`targetMajorNfs` over the first `i` entries examines them in the same order
and answers the matches in table order, i.e. the pushed ones reversed. -/
theorem target_major_nfs_rev_aux (n : Nat) :
    ∀ (i : Std.Usize) st lst (acc : alloc.vec.Vec arena.inductives.positivity.NestCtorNf),
      i.val = n → i.val ≤ tbl.val.length → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.val.map absNestCtorNf)
        (arena.inductives.rec_check.target_major_nfs_rev pers st mode vis rf p former_tys pfvs
          us ds ctors tbl i acc) lst
        (do
          let r ← targetMajorNfs (ConRon.Refine.absMode mode) lf (absBlockShape p)
            (absEIdxL former_tys) (absEIdxL pfvs) (absLsIdx us) (absEIdxL ds) (absCtorsL ctors)
            ((tbl.val.take i.val).map absNestCtorNf)
          pure (acc.val.map absNestCtorNf ++ r.reverse)) := by
  induction n with
  | zero =>
    intro i st lst acc hn _ hrel hinv
    rw [arena.inductives.rec_check.target_major_nfs_rev.eq_def, if_pos (by scalar_tac), hn]
    simp only [List.take_zero, List.map_nil, targetMajorNfs, pure_bind, List.reverse_nil,
      List.append_nil]
    lockstep
  | succ n ih =>
    intro i st lst acc hn hle hrel hinv
    rw [arena.inductives.rec_check.target_major_nfs_rev.eq_def, if_neg (by scalar_tac)]
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

include hctx in
@[lockstep] theorem target_major_nfs_rev_ls {st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (i : Std.Usize)
    (acc : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)
    (hle : i.val ≤ tbl.val.length) :
    LS pers (fun a b => b = a.val.map absNestCtorNf)
      (arena.inductives.rec_check.target_major_nfs_rev pers st mode vis rf p former_tys pfvs
        us ds ctors tbl i acc) lst
      (do
        let r ← targetMajorNfs (ConRon.Refine.absMode mode) lf (absBlockShape p)
          (absEIdxL former_tys) (absEIdxL pfvs) (absLsIdx us) (absEIdxL ds) (absCtorsL ctors)
          ((tbl.val.take i.val).map absNestCtorNf)
        pure (acc.val.map absNestCtorNf ++ r.reverse)) :=
  target_major_nfs_rev_aux hctx p former_tys pfvs us ds ctors tbl _ i st lst acc rfl hle hrel hinv

end MajorNfs

@[lockstep] theorem nfs_reverse_twin (xs : alloc.vec.Vec arena.inductives.positivity.NestCtorNf) :
    LSP (arena.inductives.rec_check.nfs_reverse xs (alloc.vec.Vec.len xs)
        (alloc.vec.Vec.new arena.inductives.positivity.NestCtorNf))
      (fun o => TwinEq ((xs.val.map absNestCtorNf).reverse) (o.val.map absNestCtorNf)) := by
  intro o h
  rw [TwinEq, nfs_reverse_abs xs _ _ _ o rfl (by simp [alloc.vec.Vec.len]) h]
  simp [alloc.vec.Vec.new, alloc.vec.Vec.len, List.map_reverse]

@[lockstep] theorem target_major_nfs_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape)
    (former_tys pfvs : alloc.vec.Vec arena.handle.EIdx) (us : arena.handle.LsIdx)
    (ds : alloc.vec.Vec arena.handle.EIdx)
    (ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf) :
    LS pers (fun a b => b = a.val.map absNestCtorNf)
      (arena.inductives.rec_check.target_major_nfs pers st mode vis rf p former_tys pfvs us ds
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

/-! ## A stripped telescope's binder data are well formed (for `binders_beq`)

`strip_pis` conses the viewed binders (`AStateInv`'s datum clause) onto a
copy of the rest; a copy of a `Vec` of binders is the identity on the raw
data. -/

theorem rc_binder_copy_from_val (xs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)),
      arena.expr_ops.binder_copy_from xs i out = ok o → o.val = out.val ++ xs.val.drop i.val := by
  intro i out o h
  have key := vec_cursor_copy xs id id (fun i out => arena.expr_ops.binder_copy_from xs i out)
    ?_ ?_ i out o h
  · simpa using key
  · intro i out o hn h
    rw [arena.expr_ops.binder_copy_from.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.expr_ops.binder_copy_from.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by
        have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨⟨e, bm⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : (e, bm) = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨bm1, hbm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine ⟨i2, (e1, bm1), out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, ?_, h⟩
    rw [dupId_eidx _ _ he1, binder_meta_dup_spec _ _ hbm1]

theorem rc_cons_binder_val {ty : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    {xs r : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (h : arena.expr_ops.cons_binder ty m xs = ok r) : r.val = (ty, m) :: xs.val := by
  rw [arena.expr_ops.cons_binder] at h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [rc_binder_copy_from_val xs _ out r h, ConRon.Refine.vec_push_val hout,
    dupId_eidx _ _ he, binder_meta_dup_spec _ _ hbm]
  simp [alloc.vec.Vec.new]

theorem rc_strip_pis_wf {pers st} (hinv : AStateInv pers st) (n : Nat) :
    ∀ (k : Std.U64) (h : arena.handle.EIdx) bs leaf, k.val = n →
      arena.expr_ops.strip_pis pers st k h = ok (.Ok (some (bs, leaf))) → TeleWF bs := by
  induction n with
  | zero =>
    intro k h bs leaf hk hrun
    rw [arena.expr_ops.strip_pis, if_pos (by scalar_tac)] at hrun
    obtain ⟨e, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    exact TeleWF.new
  | succ n ih =>
    intro k h bs leaf hk hrun
    rw [arena.expr_ops.strip_pis, if_neg (by scalar_tac)] at hrun
    obtain ⟨tg, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    split at hrun
    · obtain ⟨o, hvb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases o with
      | none => simp [arena.monad.fail_dangling_e, arena.monad.fail] at hrun
      | some t =>
        obtain ⟨ty, b, m⟩ := t
        have hm := view_bind_meta_wf hinv hvb
        simp only at hrun
        obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases r with
        | Err _ => cases Result.ok_injective hrun
        | Ok o1 =>
          cases o1 with
          | none => cases Result.ok_injective hrun
          | some q =>
            obtain ⟨v, e⟩ := q
            simp only at hrun
            obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hvr := ih k1 b v e
            cases Result.ok_injective hrun
            have hv := hvr (by have := ConRon.Refine.Nat.usub_val hk1; scalar_tac) hr
            intro p hp
            rw [rc_cons_binder_val hv1] at hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact hm
            · exact hv p hp
    · cases Result.ok_injective hrun

/-- A `strip_pis` answer's telescope is well formed. -/
def StripWF : Option (alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta) ×
    arena.handle.EIdx) → Prop
  | some q => TeleWF q.1
  | none => True

@[lockstep_simp] theorem stripWF_some (q : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta) ×
    arena.handle.EIdx) : StripWF (some q) = TeleWF q.1 := rfl

/-- `strip_pis` with its telescope's well-formedness in the answer. -/
theorem rc_strip_pis_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = ExprOps.absStrip a ∧ StripWF a)
      (arena.expr_ops.strip_pis pers st k h) st lst (stripPis (absU k) (absEIdx h)) := by
  intro o hrun
  have h1 := ExprOps.strip_pis_ls hrel hinv k h o hrun
  cases o with
  | Err e => exact h1
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h2, h3⟩ := h1
    refine ⟨b, lst', hx, ⟨hR, ?_⟩, h2, h3⟩
    cases a with
    | none => trivial
    | some q => exact rc_strip_pis_wf hinv _ k h q.1 q.2 rfl hrun

/-! ## `target_k53` (with `_leaf`, `_args`, `_class`: fragments of the one twin
`targetK53`, unfolded in place) -/

attribute [local lockstep_inline] arena.inductives.rec_check.target_k53_leaf
  arena.inductives.rec_check.target_k53_args arena.inductives.rec_check.target_k53_class
attribute [local lockstep high] rc_strip_pis_wf_ls

/-- `take_eidx_n` as the twin's `List.take` on the abstracted list. -/
theorem rc_take_eidx_n_twin (xs : alloc.vec.Vec arena.handle.EIdx) (c : Std.U64) :
    LSP (arena.expr_ops.take_eidx_n xs c)
      (fun r => TwinEq ((xs.val.map absEIdx).take c.val) (r.val.map absEIdx)) := by
  intro r h
  have := absEIdxL_of_takeEidx (take_eidx_n_spec xs c r h)
  simpa [TwinEq, absEIdxL] using this.symm

attribute [local lockstep high] rc_take_eidx_n_twin

@[lockstep] theorem target_k53_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (mc : arena.inductives.rec_check.TargetMajor)
    (tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (htele : TeleWF tele)
    (maj_dom f : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_k53 pers st mode vis rf p former_tys mc tele maj_dom f)
      lst
      (targetK53 (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (absTargetMajor mc) (absBinderL tele) (absEIdx maj_dom) (absEIdx f)) := by
  rw [arena.inductives.rec_check.target_k53, targetK53]
  lockstep

/-! ## The major record: copy, default, lookup -/

theorem rc_ctors_dup_id (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    ∀ o, arena.inductives.block_parts.ctors_dup cs 0#usize
      (alloc.vec.Vec.new (arena.env.IConstantVal × Std.U64)) = ok o → o = cs := by
  refine vec_copy_id cs (arena.inductives.block_parts.ctors_dup cs) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.block_parts.ctors_dup.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.block_parts.ctors_dup.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by
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

attribute [local lockstep_inline] arena.inductives.positivity.ind_cv_of
attribute [local lockstep high] Lockstep.PC2.i_constant_val_dup_ls

@[lockstep] theorem target_outside_inst_ls {pers st lst} {vis : Std.U64}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (i_name : arena.handle.NIdx) (us : arena.handle.LsIdx) (ds : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = (absU a.1, absLIdx a.2))
      (arena.inductives.rec_check.target_outside_inst pers st vis rf i_name us ds) lst
      (targetOutsideInst lf (absNIdx i_name) (absLsIdx us) (absEIdxL ds)) := by
  rw [arena.inductives.rec_check.target_outside_inst, targetOutsideInst]
  lockstep

/-! ## A recursor's major, resolved: `target_major_of` (with `_member`,
`_outside`, `_outside_aux`: fragments of the one twin `targetMajorOf`) -/


@[lockstep] theorem target_ctors_of_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hctx : CoreCtx vis rf lf) (c : arena.handle.NIdx) :
    LSR pers (fun a b => b = a.map fun p => (absU p.1, absCtorsL p.2))
      (arena.inductives.rec_check.target_ctors_of pers st vis rf c) st lst
      (targetCtorsOf lf (absNIdx c)) := by
  rw [arena.inductives.rec_check.target_ctors_of, targetCtorsOf]
  exact nest_container_ls hrel hinv hctx c

/-- The twin's `unwrapOr l[i]? e` as the bounds test the port makes. -/
theorem rc_unwrapOr_getElem? {α : Type} (l : List α) (i : Nat) (e : Arena.CheckError) :
    unwrapOr l[i]? e = if h : i < l.length then pure l[i] else Arena.fail e := by
  by_cases h : i < l.length
  · rw [dif_pos h, List.getElem?_eq_getElem h]; rfl
  · rw [dif_neg h, List.getElem?_eq_none (by omega)]; rfl

theorem rc_absBlockShape_members_length (p : arena.inductives.block_parts.BlockShape) :
    (absBlockShape p).members.length = p.members.val.length := by
  simp [absBlockShape]

theorem rc_absCtorsLL_length
    (v : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) :
    (absCtorsLL v).length = v.val.length := by
  simp [absCtorsLL]

theorem rc_absBlockShape_nP (p : arena.inductives.block_parts.BlockShape) :
    (absBlockShape p).nP = p.n_p.val := rfl

theorem rc_absBlockShape_members_getElem (p : arena.inductives.block_parts.BlockShape) (i : Nat)
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
    LSP (arena.inductives.block_parts.ctors_dup cs 0#usize
      (alloc.vec.Vec.new (arena.env.IConstantVal × Std.U64))) (fun o => o = cs) :=
  rc_ctors_dup_id cs

attribute [local lockstep high] rc_ctors_dup_spec

attribute [local lockstep_simp] rc_unwrapOr_getElem? rc_absBlockShape_members_length
  rc_absCtorsLL_length rc_absBlockShape_nP rc_absBlockShape_members_getElem rc_absCtorsLL_getElem

attribute [local lockstep_inline] arena.inductives.rec_check.target_major_member
  arena.inductives.rec_check.target_major_outside arena.inductives.rec_check.target_major_outside_aux

@[lockstep] theorem target_major_of_ls {pers st lst} {vis : Std.U64}
    {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape)
    (ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64)))
    (pfvs fvs : alloc.vec.Vec arena.handle.EIdx) (mty : arena.handle.EIdx) :
    LS pers (fun a b => b = absTargetMajor a)
      (arena.inductives.rec_check.target_major_of pers st vis rf p ctors_as pfvs fvs mty) lst
      (targetMajorOf lf (absBlockShape p) (absCtorsLL ctors_as) (absEIdxL pfvs) (absEIdxL fvs)
        (absEIdx mty)) := by
  rw [arena.inductives.rec_check.target_major_of, targetMajorOf]
  lockstep
  refine LS.pure ?_ ‹_› ‹_›
  simp only [absTargetMajor, absMemberShape]
  casesm* _ ∨ _
  all_goals first | (exfalso; scalar_tac) | skip
  rename_i h5
  simp only [h5, hP, absEIdxL, absU, Option.map_some]
  rfl

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
      if_pos (show i ≥ alloc.vec.Vec.len t by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.rec_check.cps_append.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len t by
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
    rw [arena.inductives.rec_check.want_aux_names.eq_def, if_pos (by scalar_tac)]
    simp only [List.range'_zero, List.mapM_nil, pure_bind, List.append_nil]
    lockstep
  · intro st lst k w m hk hm hrel hinv ih
    rw [arena.inductives.rec_check.want_aux_names.eq_def, if_neg (by scalar_tac)]
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
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.rec_check.ctor_names.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by
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
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.inductives.rec_check.ctor3_names.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by
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

theorem rc_rec_shape_dup_id (r : arena.inductives.block_parts.RecShape) :
    LSP (arena.inductives.block_parts.rec_shape_dup r) (fun o => o = r) := by
  intro o h
  rw [arena.inductives.block_parts.rec_shape_dup] at h
  obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [Lockstep.PC2.i_constant_val_dup_ls _ _ hiv, alloc.vec.Vec.ext _ _ (eidx_vec_dup_val hv)]

/-- `recs_by_target` keeps the recursors whose major is a member iff `own`. -/
theorem recs_by_target_val (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (k : Std.U64) (own : Bool) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.block_parts.RecShape),
      arena.inductives.rec_check.recs_by_target rs k own i out = ok o →
      o.val = out.val ++ (rs.val.drop i.val).filter (fun r => decide (r.tgt < k) == own) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) rs.val.length
    (fun i (_ : Unit) => ∀ (out o : alloc.vec.Vec arena.inductives.block_parts.RecShape),
      arena.inductives.rec_check.recs_by_target rs k own i out = ok o →
      o.val = out.val ++ (rs.val.drop i.val).filter (fun r => decide (r.tgt < k) == own))
    ?_ ?_ i ()
  · intro i _ hn out o h
    rw [arena.inductives.rec_check.recs_by_target.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
    rw [h, List.drop_eq_nil_of_le hn]; simp
  · intro i _ hlt ih out o h
    rw [arena.inductives.rec_check.recs_by_target.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : rs.val[i.val] = q := by
      have h1 := vec_index_some hq; rw [List.getElem?_eq_getElem hlt] at h1
      exact Option.some_inj.mp h1
    rw [List.drop_eq_getElem_cons hlt, List.filter_cons, hqx]
    by_cases hc : (q.tgt < k) = (own = true)
    · rw [if_pos hc] at h
      have hb : (decide (q.tgt < k) == own) = true := by cases own <;> simp_all
      obtain ⟨q2, hq2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [ih i2 () (absSz_add_one hi2) out1 o h, ConRon.Refine.vec_push_val hout1,
        rc_rec_shape_dup_id _ _ hq2, show i2.val = i.val + 1 from absSz_add_one hi2, hb]
      simp
    · rw [if_neg hc] at h
      have hb : (decide (q.tgt < k) == own) = false := by cases own <;> simp_all
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [ih i2 () (absSz_add_one hi2) out o h, show i2.val = i.val + 1 from absSz_add_one hi2, hb]
      simp

/-! ## The stored family: `aux_rule_fire_r`, `tgt_stored_rules`, `cons_block_recs_t`

These run at the constructors' visibility bound `vis` beside a LARGER index
`rf` (`cons_block_recs_t` pushes the recursors above `vis2`), so they are
stated at `IFEnvRelI rf lf` with the twin reading `lf.restrictTo (absU vis)`,
which is the twin's `fe.restrictTo vis₂`. -/

/-! ### Helpers for Shape/Abs: `expr_ops::nested_rule_syn` and its body

`nested_rule_syn` ⊑ `nestedRuleSyn` (`Arena/CheckerBase.lean`), with
`nested_rule_syn_at`, `_guards`, `lower_list`, `lift_list`, `pins_wf`,
`levels_declared(_from)`: the checker tier's functions, which no lane had
proved; they belong beside `Checker/Base.lean`'s. -/

theorem rc_lower_list_acc {pers} (k : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.expr_ops.lower_list pers st k xs i out) lst
        (do
          let r ← lowerList (absU k) (absEIdxLFrom xs i)
          pure (absEIdxL out ++ r)) := by
  intro i st lst out hrel hinv
  refine ls_cursor_acc xs absEIdx
    (fun (w : alloc.vec.Vec arena.handle.EIdx) l => do
      let r ← lowerList (absU k) l
      pure (absEIdxL w ++ r))
    (fun st j w => arena.expr_ops.lower_list pers st k xs j w)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst j w hn hrel hinv
    rw [arena.expr_ops.lower_list.eq_def,
      if_pos (show j ≥ alloc.vec.Vec.len xs by scalar_tac), lowerList]
    simp only [pure_bind, List.append_nil]
    lockstep
  · intro st lst j w hk hrel hinv ih
    have ih' : ∀ st' lst' (j' : Std.Usize) (w' : alloc.vec.Vec arena.handle.EIdx),
        j'.val = j.val + 1 → AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = absEIdxL a)
          (arena.expr_ops.lower_list pers st' k xs j' w') lst'
          (do
            let r ← lowerList (absU k) ((xs.val.drop j'.val).map absEIdx)
            pure (absEIdxL w' ++ r)) := ih
    clear ih
    rw [arena.expr_ops.lower_list.eq_def,
      if_neg (show ¬ j ≥ alloc.vec.Vec.len xs by scalar_tac), lowerList]
    simp only [bind_assoc, pure_bind]
    lockstep

theorem rc_lower_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.expr_ops.lower_list pers st k xs 0#usize (alloc.vec.Vec.new arena.handle.EIdx)) lst
      (lowerList (absU k) (absEIdxL xs)) := by
  have h := rc_lower_list_acc k xs 0#usize st lst (alloc.vec.Vec.new arena.handle.EIdx) hrel hinv
  have e : (do
      let r ← lowerList (absU k) (absEIdxLFrom xs 0#usize)
      pure (absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ r) : AM _)
      = lowerList (absU k) (absEIdxL xs) := by
    simp [absEIdxL, absEIdxLFrom, alloc.vec.Vec.new]
  rwa [e] at h

theorem rc_lift_list_acc {pers} (k : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.expr_ops.lift_list pers st k xs i out) lst
        (do
          let r ← liftList (absU k) (absEIdxLFrom xs i)
          pure (absEIdxL out ++ r)) := by
  intro i st lst out hrel hinv
  refine ls_cursor_acc xs absEIdx
    (fun (w : alloc.vec.Vec arena.handle.EIdx) l => do
      let r ← liftList (absU k) l
      pure (absEIdxL w ++ r))
    (fun st j w => arena.expr_ops.lift_list pers st k xs j w)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst j w hn hrel hinv
    rw [arena.expr_ops.lift_list.eq_def,
      if_pos (show j ≥ alloc.vec.Vec.len xs by scalar_tac), liftList]
    simp only [pure_bind, List.append_nil]
    lockstep
  · intro st lst j w hk hrel hinv ih
    have ih' : ∀ st' lst' (j' : Std.Usize) (w' : alloc.vec.Vec arena.handle.EIdx),
        j'.val = j.val + 1 → AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = absEIdxL a)
          (arena.expr_ops.lift_list pers st' k xs j' w') lst'
          (do
            let r ← liftList (absU k) ((xs.val.drop j'.val).map absEIdx)
            pure (absEIdxL w' ++ r)) := ih
    clear ih
    rw [arena.expr_ops.lift_list.eq_def,
      if_neg (show ¬ j ≥ alloc.vec.Vec.len xs by scalar_tac), liftList]
    simp only [bind_assoc, pure_bind]
    lockstep

theorem rc_lift_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.expr_ops.lift_list pers st k xs 0#usize (alloc.vec.Vec.new arena.handle.EIdx)) lst
      (liftList (absU k) (absEIdxL xs)) := by
  have h := rc_lift_list_acc k xs 0#usize st lst (alloc.vec.Vec.new arena.handle.EIdx) hrel hinv
  have e : (do
      let r ← liftList (absU k) (absEIdxLFrom xs 0#usize)
      pure (absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ r) : AM _)
      = liftList (absU k) (absEIdxL xs) := by
    simp [absEIdxL, absEIdxLFrom, alloc.vec.Vec.new]
  rwa [e] at h

theorem rc_pins_wf_aux {pers} {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (lps : alloc.vec.Vec arena.handle.NIdx) (r_p : Std.U64)
    (pins : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.expr_ops.pins_wf pers vis st rf lps r_p pins i) lst
        (pinsWf (lf.restrictTo (absU vis)) (absNIdxL lps) (absU r_p)
          ((pins.val.drop i.val).map absEIdx)) := by
  refine ls_cursor pins absEIdx
    (fun l => pinsWf (lf.restrictTo (absU vis)) (absNIdxL lps) (absU r_p) l)
    (fun st i => arena.expr_ops.pins_wf pers vis st rf lps r_p pins i) ?_ ?_
  · intro st lst i hn hrel hinv
    rw [arena.expr_ops.pins_wf.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len pins by scalar_tac), pinsWf]
    lockstep
  · intro st lst i hlt hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = a)
          (arena.expr_ops.pins_wf pers vis st' rf lps r_p pins j) lst'
          (pinsWf (lf.restrictTo (absU vis)) (absNIdxL lps) (absU r_p)
            ((pins.val.drop j.val).map absEIdx)) := ih
    clear ih
    rw [arena.expr_ops.pins_wf.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len pins by scalar_tac), pinsWf]
    lockstep

theorem rc_levels_declared_from_aux {pers st} (ps : alloc.vec.Vec kernel.name.Name)
    (hps : ConRon.Refine.NamesWF ps) (lvls : alloc.vec.Vec arena.handle.LIdx) :
    ∀ (i : Std.Usize) lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a)
        (arena.expr_ops.levels_declared_from pers st ps lvls i) st lst
        (levelsDeclaredFrom (ConRon.Refine.absNames ps) ((lvls.val.drop i.val).map absLIdx)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) lvls.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a)
        (arena.expr_ops.levels_declared_from pers st ps lvls i) st lst
        (levelsDeclaredFrom (ConRon.Refine.absNames ps) ((lvls.val.drop i.val).map absLIdx)))
    ?_ ?_ i ()
  · intro i _ hn lst hrel hinv
    apply LSR.of_LS
    rw [arena.expr_ops.levels_declared_from.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len lvls by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, levelsDeclaredFrom]
    lockstep
  · intro i _ hlt ih lst hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ lst, AStateRel₀ pers st lst →
        AStateInv pers st →
        LSR pers (fun a b => b = a)
          (arena.expr_ops.levels_declared_from pers st ps lvls j) st lst
          (levelsDeclaredFrom (ConRon.Refine.absNames ps) ((lvls.val.drop j.val).map absLIdx)) :=
      fun j hj => ih j () hj
    clear ih
    apply LSR.of_LS
    rw [arena.expr_ops.levels_declared_from.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len lvls by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, levelsDeclaredFrom]
    lockstep

theorem rc_levels_declared_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (lps : alloc.vec.Vec arena.handle.NIdx)
    (lvls : alloc.vec.Vec arena.handle.LIdx) :
    LSR pers (fun a b => b = a)
      (arena.expr_ops.levels_declared pers st lps lvls) st lst
      (levelsDeclared (absNIdxL lps) (lvls.val.map absLIdx)) := by
  have hf : ∀ ps, ConRon.Refine.NamesWF ps → ∀ lst, AStateRel₀ pers st lst →
      AStateInv pers st →
      LSR pers (fun a b => b = a)
        (arena.expr_ops.levels_declared_from pers st ps lvls 0#usize) st lst
        (levelsDeclaredFrom (ConRon.Refine.absNames ps) (lvls.val.map absLIdx)) := by
    intro ps hps lst hrel hinv
    have := rc_levels_declared_from_aux ps hps lvls 0#usize lst hrel hinv
    simpa using this
  apply LSR.of_LS
  rw [arena.expr_ops.levels_declared, levelsDeclared]
  lockstep

attribute [local lockstep] rc_lower_list_ls rc_lift_list_ls rc_levels_declared_ls

theorem rc_nested_rule_syn_guards_ls {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (lps : alloc.vec.Vec arena.handle.NIdx) (lvls : arena.handle.LsIdx)
    (r_p : Std.U64) (pins : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a.map fun q => (q.1.val.map absLIdx, q.2.val.map absEIdx))
      (arena.expr_ops.nested_rule_syn_guards pers vis st rf lps lvls r_p pins) lst
      (nestedRuleSynGuards (lf.restrictTo (absU vis)) (absNIdxL lps) (absLsIdx lvls) (absU r_p)
        (absEIdxL pins)) := by
  have hp : ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.expr_ops.pins_wf pers vis st rf lps r_p pins 0#usize) lst
        (pinsWf (lf.restrictTo (absU vis)) (absNIdxL lps) (absU r_p) (absEIdxL pins)) := by
    intro st lst hrel hinv
    have := rc_pins_wf_aux (vis := vis) hfe lps r_p pins 0#usize st lst hrel hinv
    simpa [absEIdxL] using this
  rw [arena.expr_ops.nested_rule_syn_guards, nestedRuleSynGuards]
  lockstep

attribute [local lockstep] rc_nested_rule_syn_guards_ls

theorem rc_nested_rule_syn_at_ls {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (lps : alloc.vec.Vec arena.handle.NIdx) (dom : arena.handle.EIdx)
    (lvls : arena.handle.LsIdx) (k r_p cn_p : Std.U64) :
    LS pers (fun a b => b = a.map fun q => (q.1.val.map absLIdx, q.2.val.map absEIdx))
      (arena.expr_ops.nested_rule_syn_at pers vis st rf lps dom lvls k r_p cn_p) lst
      (nestedRuleSynAt (lf.restrictTo (absU vis)) (absNIdxL lps) (absEIdx dom) (absLsIdx lvls)
        (absU k) (absU r_p) (absU cn_p)) := by
  rw [arena.expr_ops.nested_rule_syn_at, nestedRuleSynAt]
  lockstep

attribute [local lockstep] rc_nested_rule_syn_at_ls

theorem rc_nested_rule_syn_ls {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (lps : alloc.vec.Vec arena.handle.NIdx) (ty_a : arena.handle.EIdx)
    (m_i r_p cn_p : Std.U64) :
    LS pers (fun a b => b = a.map fun q => (q.1.val.map absLIdx, q.2.val.map absEIdx))
      (arena.expr_ops.nested_rule_syn pers vis st rf lps ty_a m_i r_p cn_p) lst
      (nestedRuleSyn (lf.restrictTo (absU vis)) (lps.val.map absNIdx) (absEIdx ty_a) (absU m_i)
        (absU r_p) (absU cn_p)) := by
  rw [arena.expr_ops.nested_rule_syn, nestedRuleSyn]
  lockstep

attribute [local lockstep] rc_nested_rule_syn_ls

@[lockstep] theorem aux_rule_fire_r_ls {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (cv : arena.env.IConstantVal) (m_i r_p n_pc : Std.U64) :
    LS pers (fun a b => b = absIRecRuleFire a)
      (arena.inductives.rec_check.aux_rule_fire_r pers vis st rf cv m_i r_p n_pc) lst
      (auxRuleFireR (lf.restrictTo (absU vis)) (absIConstantVal cv) (absU m_i) (absU r_p)
        (absU n_pc)) := by
  rw [arena.inductives.rec_check.aux_rule_fire_r, auxRuleFireR]
  lockstep

/-- The side tier's move for a split counter: `CoreCtx vis rf (lf.restrictTo vis)`
from `IFEnvRelI rf lf` (`IFEnvInv.coreCtxAt`). -/
local macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (exact IFEnvInv.coreCtxAt _ (IFEnvRelI.rel ‹_›) (IFEnvRelI.inv ‹_›)))

@[lockstep] theorem tgt_stored_rules_ls {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (cv : arena.env.IConstantVal) (m_i r_p : Std.U64)
    (m : arena.inductives.rec_check.TargetMajor) (rhss : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absIRecRuleL a)
      (arena.inductives.rec_check.tgt_stored_rules pers vis st rf cv m_i r_p m rhss) lst
      (tgtStoredRules (lf.restrictTo (absU vis)) (absIConstantVal cv) (absU m_i) (absU r_p)
        (absTargetMajor m) (absEIdxL rhss)) := by
  rw [arena.inductives.rec_check.tgt_stored_rules, tgtStoredRules]
  lockstep


/-- A checked recursor with its major and its right-hand sides. -/
def absRecOut (x : arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
    alloc.vec.Vec arena.handle.EIdx) : IConstantVal × TargetMajor × List EIdx :=
  (absIConstantVal x.1, absTargetMajor x.2.1, absEIdxL x.2.2)

attribute [local lockstep high] Lockstep.PA1.eidx_vec_dup_ls

theorem cons_block_recs_t_aux {pers} (vis2 : Std.U64) (p : arena.inductives.block_parts.BlockShape)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) (n : Nat) :
    ∀ (m : Std.U64) st lst (rf : arena.env.IFEnv) (lf : IFEnv),
      out.val.length - m.val = n → IFEnvRelI rf lf →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => IFEnvRelI a b)
        (arena.inductives.rec_check.cons_block_recs_t pers vis2 st p m out rf) lst
        (consBlockRecsTF (absU vis2) (absBlockShape p) (absU m)
          ((out.val.drop m.val).map absRecOut) lf) := by
  induction n with
  | zero =>
    intro m st lst rf lf hn hfe hrel hinv
    rw [arena.inductives.rec_check.cons_block_recs_t.eq_def,
      List.drop_eq_nil_of_le (by omega), List.map_nil, consBlockRecsTF]
    lockstep
  | succ n ih =>
    intro m st lst rf lf hn hfe hrel hinv
    rw [arena.inductives.rec_check.cons_block_recs_t.eq_def,
      List.drop_eq_getElem_cons (show m.val < out.val.length by omega), List.map_cons,
      consBlockRecsTF]
    lockstep
    rename_i i6 h6 _ _ _ _ _ _ _ mi _ rp _ rules fe2 hfe2
    have e6 : i6.val = m.val := by
      rcases h6 with h | h
      · exact h
      · exfalso; scalar_tac
    have ha : a.val = m.val + 1 := by scalar_tac
    refine LS.tail (ih a st1 lst1 fe2
      (lf.push (IConstantInfo.recInfo (absRecOut out.val[m.val]).1 (absU mi) (absU rp)
        (absIRecRuleL rules))) (by omega) ?_ hrel hinv) ?_ (fun _ _ h => h)
    · have h1 := hfe2.1
      have e : out.val[i6.val] = out.val[m.val] := by simp only [e6]
      simp only [absIConstantInfo, e] at h1
      exact h1
    · simp only [ha, absU]

@[lockstep] theorem cons_block_recs_t_ls {pers st lst} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (vis2 : Std.U64) (p : arena.inductives.block_parts.BlockShape) (m : Std.U64)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LS pers (fun a b => IFEnvRelI a b)
      (arena.inductives.rec_check.cons_block_recs_t pers vis2 st p m out rf) lst
      (consBlockRecsTF (absU vis2) (absBlockShape p) (absU m)
        ((out.val.drop m.val).map absRecOut) lf) :=
  cons_block_recs_t_aux vis2 p out _ m st lst rf lf rfl hfe hrel hinv

/-- `cons_block_recs_t` from the first recursor (the callers' form). -/
@[lockstep] theorem cons_block_recs_t_ls0 {pers st lst} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (vis2 : Std.U64) (p : arena.inductives.block_parts.BlockShape)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LS pers (fun a b => IFEnvRelI a b)
      (arena.inductives.rec_check.cons_block_recs_t pers vis2 st p 0#u64 out rf) lst
      (consBlockRecsTF (absU vis2) (absBlockShape p) 0 (out.val.map absRecOut) lf) := by
  have h := cons_block_recs_t_ls hrel hinv hfe vis2 p 0#u64 out
  simpa [absU] using h

/-- `recs_by_target … true`: the member recursors (`p.recs.filter (·.tgt < k)`). -/
@[lockstep] theorem recs_by_target_own_twin (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (k : Std.U64) :
    LSP (arena.inductives.rec_check.recs_by_target rs k true 0#usize
        (alloc.vec.Vec.new arena.inductives.block_parts.RecShape))
      (fun o => TwinEq ((rs.val.map absRecShape).filter fun rc => rc.tgt < absU k)
        (o.val.map absRecShape)) := by
  intro o h
  rw [TwinEq, recs_by_target_val rs k true _ _ o h, List.filter_map]
  simp only [alloc.vec.Vec.new, List.drop_zero,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
  congr 1
  simp [Function.comp_def, absRecShape, absU]

/-- `recs_by_target … false`: the auxiliary recursors. -/
@[lockstep] theorem recs_by_target_aux_twin (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (k : Std.U64) :
    LSP (arena.inductives.rec_check.recs_by_target rs k false 0#usize
        (alloc.vec.Vec.new arena.inductives.block_parts.RecShape))
      (fun o => TwinEq ((rs.val.map absRecShape).filter fun rc => !(rc.tgt < absU k))
        (o.val.map absRecShape)) := by
  intro o h
  rw [TwinEq, recs_by_target_val rs k false _ _ o h, List.filter_map]
  simp only [alloc.vec.Vec.new, List.drop_zero,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
  congr 1
  simp [Function.comp_def, absRecShape, absU]

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
    (hinv : AStateInv pers st) (p : arena.inductives.block_parts.BlockShape)
    (block : alloc.vec.Vec arena.env.IConstantInfo) (n0 : arena.handle.NIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_rec_pins_names pers st p block n0) lst
      (rcPinsTail (absBlockShape p) (absICIL block) (absNIdx n0)) := by
  rw [arena.inductives.rec_check.target_rec_pins_names, rcPinsTail]
  simp only [absBlockShape_recs]
  lockstep

@[lockstep] theorem target_rec_pins_aux_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_parts.BlockShape)
    (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => b = a)
      (arena.inductives.rec_check.target_rec_pins_aux pers st p block) lst
      (rcPinsAux (absBlockShape p) (absICIL block)) := by
  rw [arena.inductives.rec_check.target_rec_pins_aux, rcPinsAux]
  simp only [absBlockShape_members]
  rcases hm : p.members.val with _ | ⟨m0, ms⟩
  · simp only [List.map_nil]
    rw [if_pos (by have : p.members.val.length = 0 := by simp [hm]
                   scalar_tac)]
    lockstep
  · simp only [List.map_cons, pure_bind]
    rw [if_neg (by simp [alloc.vec.Vec.len, hm])]
    lockstep

@[lockstep] theorem target_rec_pins_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_parts.BlockShape)
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

/-- info: 'ConRon.Refine2.target_major_nfs_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms target_major_nfs_ls

/-- info: 'ConRon.Refine2.target_major_of_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms target_major_of_ls

/-- info: 'ConRon.Refine2.target_k53_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms target_k53_ls

/-- info: 'ConRon.Refine2.cons_block_recs_t_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cons_block_recs_t_ls

/-- info: 'ConRon.Refine2.target_rec_pins_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms target_rec_pins_ls

/-- info: 'ConRon.Refine2.want_aux_names_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms want_aux_names_ls

end ConRon.Refine2
