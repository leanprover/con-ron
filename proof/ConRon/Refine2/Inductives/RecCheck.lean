/-
# `ConRon.Refine2.Inductives.RecCheck` — Theorem 2 for `arena::inductives::rec_check`

**Task #105** (DESIGN.md §8.2, Theorem 2).
`crates/con-ron-core/src/arena/inductives/rec_check.rs` against
`proof/ConRon/Arena/Inductives/RecCheck.lean`: the recursor stage's class kit.
-/
import ConRon.Refine2.Inductives.Positivity
import ConRon.Refine2.Inductives.Prims
import ConRon.Arena.Inductives.RecCheck

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

attribute [local lockstep_simp] pos_core_walk_fuel_abs pos_core_walk_fuel_val


/-! ## Helpers for Shape/Abs

`core::rec_rule_*` and `sum_install::sum_rules` at a SPLIT counter: the
statements in `Inductives/Prims.lean` / `Inductives/SumInstall.lean` take
`IFEnvRelI rf lf` and `absU vis = lf.visibleBelow`, which `cons_block_recs_t`
(the constructors' `vis2` beside the growing index) cannot supply; these take
`CoreCtx vis rf lf`, which `IFEnvInv.coreCtxAt` builds there.  They belong
beside their `IFEnvRelI` forms. -/

section CtxHelpers
open IndModeledPrims
attribute [local lockstep_simp] IndModeledPrims.absIRecRule_ctor IndModeledPrims.absIRecRule_nfields
  IndModeledPrims.absIRecRule_ctorParams IndModeledPrims.absIRecRule_fire
  IndModeledPrims.absIRecRule_rhs IndModeledPrims.absIRecRule_k IndModeledPrims.absIRecRule_eta
  IndModeledPrims.absIRecRule_paramsBlind IndModeledPrims.absIIndCaps_eta
  IndModeledPrims.absIIndCaps_etaCtor IndModeledPrims.absIIndCaps_ruleK
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

theorem rc_vecFrom_nil {α β : Type} (v : alloc.vec.Vec α) (f : α → β) (i : Std.Usize)
    (hi : v.val.length ≤ i.val) : (v.val.drop i.val).map f = [] := by
  rw [List.drop_eq_nil_of_le hi]; rfl

theorem rc_vecFrom_cons {α β : Type} (v : alloc.vec.Vec α) (f : α → β) (i : Std.Usize)
    (hi : i.val < v.val.length) :
    (v.val.drop i.val).map f = f v.val[i.val] :: (v.val.drop (i.val + 1)).map f := by
  rw [List.drop_eq_getElem_cons hi]; rfl

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
      rc_vecFrom_nil _ _ _ (by omega)]
    simp only [sumRules]
    lockstep
  | succ m ih =>
    intro pers st lst vis rf lf rec_name n_p m_i r_p rec_ty ctors rhss i out hn hrel hinv hctx
    rw [arena.inductives.sum_install.sum_rules, if_neg (by scalar_tac), absCtorsLFrom,
      rc_vecFrom_cons _ _ _ (by omega)]
    by_cases hr : i.val < rhss.val.length
    · rw [if_neg (by scalar_tac), absEIdxLFrom, rc_vecFrom_cons _ _ _ hr]
      simp only [sumRules]
      lockstep
    · rw [if_pos (by scalar_tac), absEIdxLFrom, rc_vecFrom_nil _ _ _ (by omega)]
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

end ConRon.Refine2
