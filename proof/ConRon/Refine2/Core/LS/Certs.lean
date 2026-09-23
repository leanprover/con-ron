/-
# `ConRon.Refine2.Core.LS.Certs` — region C1: the certificates, in lockstep

Task #97-P5-Core round 5, region C1.  Theorem 2's lockstep lemmas for the
certificate bodies of `arena::core` against `Arena/Core.lean`:
`iotaCertsAux`/`iotaCerts`, `defEqList`, `iotaIndexOk`, `proofIrrel`,
`propIrrel`, `structEtaProjCerts`, `structEtaCertWith`, `structEtaCert`,
`structUnitCert`, `etaCert`, `stuckIrrel`.
-/
import ConRon.Refine2.Core.LS.PrimsC1

set_option maxHeartbeats 1000000

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

/-- Drop a metadata wrapper on the goal (a `have` leaves one, and the lockstep
judgement tests do not look through it). -/
elab "strip_mdata" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← Lean.instantiateMVars (← g.getType)
  Lean.Elab.Tactic.replaceMainGoal [← g.replaceTargetDefEq t.consumeMData]

/-! ## `defEqList` (`def_eq_list`, a cursor loop) -/

theorem def_eq_list_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth} (xs ys : alloc.vec.Vec arena.handle.EIdx)
      (i : Std.Usize) {lst},
      xs.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = a)
        (arena.core.def_eq_list pers vis st mode lane fu fe depth xs ys i) lst
        (defEqList (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
          (absEIdxListFrom xs i) (absEIdxListFrom ys i)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe depth xs ys i lst hn hrel hinv hctx hf
    rw [arena.core.def_eq_list, listFrom_nil xs i (by omega)]
    by_cases hy : ys.val.length ≤ i.val
    · rw [listFrom_nil ys i hy]
      simp only [defEqList]
      lockstep_core
    · rw [listFrom_cons ys i (by omega)]
      simp only [defEqList]
      lockstep_core
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe depth xs ys i lst hn hrel hinv hctx hf
    rw [arena.core.def_eq_list, listFrom_cons xs i (by omega)]
    by_cases hy : ys.val.length ≤ i.val
    · rw [listFrom_nil ys i hy]
      simp only [defEqList]
      lockstep_core
    · rw [listFrom_cons ys i (by omega)]
      simp only [defEqList]
      lockstep_core

@[lockstep] theorem def_eq_list_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth xs ys i lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.def_eq_list pers vis st mode lane fu fe depth xs ys i) lst
      (defEqList (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdxListFrom xs i) (absEIdxListFrom ys i)) :=
  def_eq_list_aux hk _ xs ys i rfl hrel hinv hctx hf

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

@[lockstep] theorem stub_pi_residual_ls {pers st lst} {e : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = Option.map absEIdx a) (arena.core.pi_residual pers st e args i) lst
      (piResidual (absEIdx e) (absEIdxListFrom args i)) := by
  sorry

@[lockstep] theorem stub_is_unit_like_ty_ls {pers vis st fe lfe h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.is_unit_like_ty pers vis st fe h) lst
      (isUnitLikeTy lfe (absEIdx h)) := by
  sorry

@[lockstep] theorem stub_zero_level_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLIdx a) (arena.core.zero_level st) st lst zeroLevel := by
  sorry

@[lockstep] theorem stub_lvl_eq_ls {pers st u v lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.lvl_eq pers st u v) lst
      (lvlEq? (absLIdx u) (absLIdx v)) := by
  sorry

@[lockstep] theorem stub_lift_fueled_ls {pers st o lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst
      (liftFueled "level comparison" o) := by
  sorry

@[lockstep] theorem stub_reserved_basis_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxList a) (arena.core.reserved_basis_names st) st lst
      reservedBasisNames := by
  sorry

@[lockstep] theorem stub_const_ty_at_ls {pers st lst cv us}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.const_ty_at pers st cv us) lst
      (constTyAt (absIConstantVal cv) (absLsIdx us)) := by
  sorry

/-! ## `iotaIndexOk` -/

@[lockstep] theorem iota_index_ok_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth m_i r_p cn_p ty_ctor margs idx lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.iota_index_ok pers vis st mode lane fu fe depth m_i r_p cn_p ty_ctor margs idx)
      lst
      (iotaIndexOk (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absU m_i) (absU r_p) (absU cn_p) (absEIdx ty_ctor) (absEIdxList margs)
        (absEIdxList idx)) := by
  rw [arena.core.iota_index_ok, iotaIndexOk]
  lockstep_core

/-! ## `iotaCertsAux` (a loop, lexicographic in `(args.size - i, acc.size)`) -/

attribute [local lockstep_simp] absEIdxArr_size absSz in
theorem iota_certs_aux_aux {f : Nat} (hk : KnotRel f) (N : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth lic} (h : arena.handle.EIdx)
      (acc args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) {lst},
      2 * (args.val.length - i.val) + min acc.val.length 1 < N →
      ExprOpsHyp pers →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = a)
        (arena.core.iota_certs_aux pers vis st mode lane fu fe depth lic h acc args i) lst
        (iotaCertsAux (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) lic
          (absEIdx h) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction N with
  | zero => intros; omega
  | succ N ih =>
    intro pers vis st mode lane fu fe lfe depth lic h acc args i lst hN hx hrel hinv hctx hf
    rw [arena.core.iota_certs_aux, iotaCertsAux]
    by_cases hi : absSz i < (absEIdxArr args).size
    · rw [dif_pos hi]
      simp only [absEIdxArr_size, absSz] at hi
      lockstep_core
      -- glue: the bvar arm's re-entry with the flushed accumulator
      have hne : acc.val.length ≠ 0 := by scalar_tac
      have := ih (lic := lic) (mode := mode) (lane := lane) (depth := depth) a
        (alloc.vec.Vec.new _) args i
        (by
          have h0 : (alloc.vec.Vec.new arena.handle.EIdx).val = [] := rfl
          have hm : min acc.val.length 1 = 1 := by omega
          rw [h0, List.length_nil]; omega) hx hrel hinv hctx hf
      simpa [absEIdxArr, alloc.vec.Vec.new] using this
    · rw [dif_neg hi]
      simp only [absEIdxArr_size, absSz] at hi
      lockstep_core

@[lockstep] theorem iota_certs_aux_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth lic h acc args i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.iota_certs_aux pers vis st mode lane fu fe depth lic h acc args i) lst
      (iotaCertsAux (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) lic
        (absEIdx h) (absEIdxArr acc) (absEIdxArr args) (absSz i)) :=
  iota_certs_aux_aux hk _ h acc args i (Nat.lt_succ_self _) hx hrel hinv hctx hf

/-- `iota_certs` against `iotaCerts`.  Every port call site passes the cursor
`0` (the twin's `iotaCerts` has none), so the statement is at `0#usize`. -/
@[lockstep] theorem iota_certs_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth lic h args lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.iota_certs pers vis st mode lane fu fe depth lic h args 0#usize) lst
      (iotaCerts (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) lic
        (absEIdx h) (absEIdxList args)) := by
  rw [arena.core.iota_certs, iotaCerts]
  exact iota_certs_aux_ls hk hx hrel hinv hctx hf

/-! ## `proofIrrel` (fragments `prop_sorts_zero`, `prop_sorts_zero_right`) -/

attribute [lockstep_inline] arena.core.prop_sorts_zero arena.core.prop_sorts_zero_right

@[lockstep] theorem proof_irrel_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.proof_irrel pers vis st mode lane fu fe depth a b) lst
      (proofIrrel (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.proof_irrel, proofIrrel]
  lockstep_core
  -- DIVERGENCE (D-C1-1): the port re-reads the pinned level `0` for the second
  -- side (`prop_sorts_zero_right`, core.rs `zero_level(st)` before the second
  -- `lvl_eq`), the twin reuses the `z` it read for the first side
  -- (Arena/Core.lean `proofIrrel`/`propIrrel`, inner `.sort vT` arm).  The
  -- port's second `zero_level` has no twin partner.  Fix: `let z ← zeroLevel`
  -- again before `lvlEq? vT z` (see `proof_irrel_fix_ls`, which closes).
  all_goals sorry

@[lockstep] theorem prop_irrel_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.prop_irrel pers vis st mode lane fu fe depth a b) lst
      (propIrrel (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.prop_irrel, propIrrel]
  lockstep_core
  -- DIVERGENCE (D-C1-1): the port re-reads the pinned level `0` for the second
  -- side (`prop_sorts_zero_right`, core.rs `zero_level(st)` before the second
  -- `lvl_eq`), the twin reuses the `z` it read for the first side
  -- (Arena/Core.lean `proofIrrel`/`propIrrel`, inner `.sort vT` arm).  The
  -- port's second `zero_level` has no twin partner.  Fix: `let z ← zeroLevel`
  -- again before `lvlEq? vT z` (see `proof_irrel_fix_ls`, which closes).
  all_goals sorry

/-! ## `etaCert` (fragment `eta_cert_body`) -/

attribute [lockstep_inline] arena.core.eta_cert_body

/-- `hm1`: the λ's binder datum is well formed — a representation fact about
the port's input (every binder datum the port reads out of the store is, by
`AStateInv`'s `bms` clause; `PropWhen.beq` is exact only there). -/
@[lockstep] theorem eta_cert_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty1 body1 m1 b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hm1 : ConRon.Refine.PropWhenWF m1.pw) :
    LS pers (fun a b => b = a)
      (arena.core.eta_cert pers vis st mode lane fu fe depth ty1 body1 m1 b) lst
      (etaCert (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx ty1) (absEIdx body1) (ConRon.Refine.absBinderMeta m1)
        (absEIdx b)) := by
  rw [arena.core.eta_cert, etaCert]
  have hvb : PC1.ViewBindWF pers := PC1.viewBindWF_holds pers
  unfold PC1.ViewBindWF at hvb
  strip_mdata
  lockstep_core

/-! ## `structUnitCert` (fragment `struct_unit_cert_tail`) -/

attribute [lockstep_inline] arena.core.struct_unit_cert_tail

@[lockstep] theorem struct_unit_cert_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.struct_unit_cert pers vis st mode lane fu fe depth a b) lst
      (structUnitCert (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx a) (absEIdx b)) := by
  rw [arena.core.struct_unit_cert, structUnitCert]
  lockstep_core
  -- glue: the port's `view_ls` against the twin's `viewLsLen` + `failDanglingLs`
  refine PC1.LS.view_ls_len_bind (by assumption) rfl (fun _ => errArm_ok) (fun v => ?_)
  dsimp only
  lockstep_core

/-! ## Divergence evidence (D-C1-1)

`proofIrrel` with the one-line twin fix applied (a second `zeroLevel` read
before the second `lvlEq?`), and the lockstep lemma against it, closed by one
`lockstep_core` call.  Delete once the twin carries the fix. -/

/-- `proofIrrel` with the second `zeroLevel` read (the divergence fix). -/
def proofIrrelFix (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM Bool := do
  let ta ← r.inferIO depth a
  if ← isUnitLikeTy fe (← r.whnf depth ta) then do
    let tb ← r.inferIO depth b
    if ← isUnitLikeTy fe (← r.whnf depth tb) then pure true else pure false
  else do
    let hh ← r.whnf depth (← r.inferIO depth ta)
    if hh.tag == ETag.sort then
      match ← view hh with
      | .sort uT => do
        let z ← zeroLevel
        let okA ← liftFueled "level comparison" (← lvlEq? uT z)
        let tb ← r.inferIO depth b
        let hh ← r.whnf depth (← r.inferIO depth tb)
        if hh.tag == ETag.sort then
          match ← view hh with
          | .sort vT => do
            let z ← zeroLevel
            let okB ← liftFueled "level comparison" (← lvlEq? vT z)
            pure (okA && okB)
          | _ => pure false
        else pure false
      | _ => pure false
    else pure false

theorem proof_irrel_fix_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.proof_irrel pers vis st mode lane fu fe depth a b) lst
      (proofIrrelFix (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.proof_irrel, proofIrrelFix]
  lockstep_core

end ConRon.Refine2.Lockstep
