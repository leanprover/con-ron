/-
# `ConRon.Refine2.Core.LS.Certs` — region C1: the certificates, in lockstep

Task #97-P5-Core round 5, region C1.  Theorem 2's lockstep lemmas for the
certificate bodies of `arena::core` against `Arena/Core.lean`:
`iotaCertsFullAux`/`iotaCertsFull`, `defEqList`, `iotaIndexOk`, `proofIrrel`,
`propIrrel`, `structEtaCertWith`, `structEtaCert`,
`structUnitCert`, `etaCert`, `stuckIrrel`.
-/
import ConRon.Refine2.Core.LS.PrimsC1
import ConRon.Refine2.Core.LS.Leaves
import ConRon.Refine2.Core.LS.Shapes

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PC1.CoreLSReg

set_option maxHeartbeats 1000000

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

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

/-! ## `iotaCertsFullAux` (a loop, lexicographic in `(args.size - i, acc.size)`) -/

attribute [local lockstep_simp] absEIdxArr_size absSz in
theorem iota_certs_full_aux_aux {f : Nat} (hk : KnotRel f) (N : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth} (h : arena.handle.EIdx)
      (acc args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) {lst},
      2 * (args.val.length - i.val) + min acc.val.length 1 < N →
      ExprOpsHyp pers →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = a)
        (arena.core.iota_certs_full_aux pers vis st mode lane fu fe depth h acc args i) lst
        (iotaCertsFullAux (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
          (absEIdx h) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction N with
  | zero => intros; omega
  | succ N ih =>
    intro pers vis st mode lane fu fe lfe depth h acc args i lst hN hx hrel hinv hctx hf
    rw [arena.core.iota_certs_full_aux, iotaCertsFullAux]
    by_cases hi : absSz i < (absEIdxArr args).size
    · rw [dite_eq_left hi]
      simp only [absEIdxArr_size, absSz] at hi
      lockstep_core
      -- glue: the bvar arm's re-entry with the flushed accumulator
      have hne : acc.val.length ≠ 0 := by scalar_tac
      have := ih (mode := mode) (lane := lane) (depth := depth) a
        (alloc.vec.Vec.new _) args i
        (by
          have h0 : (alloc.vec.Vec.new arena.handle.EIdx).val = [] := rfl
          have hm : min acc.val.length 1 = 1 := by omega
          rw [h0, List.length_nil]; omega) hx hrel hinv hctx hf
      simpa [absEIdxArr, alloc.vec.Vec.new] using this
    · rw [dite_eq_right hi]
      simp only [absEIdxArr_size, absSz] at hi
      lockstep_core

@[lockstep] theorem iota_certs_full_aux_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h acc args i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.iota_certs_full_aux pers vis st mode lane fu fe depth h acc args i) lst
      (iotaCertsFullAux (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h) (absEIdxArr acc) (absEIdxArr args) (absSz i)) :=
  iota_certs_full_aux_aux hk _ h acc args i (Nat.lt_succ_self _) hx hrel hinv hctx hf

/-- `iota_certs_full` against `iotaCertsFull`.  Every port call site passes
the cursor `0` (the twin's `iotaCertsFull` has none), so the statement is at
`0#usize`. -/
@[lockstep] theorem iota_certs_full_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h args lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.iota_certs_full pers vis st mode lane fu fe depth h args 0#usize) lst
      (iotaCertsFull (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h) (absEIdxList args)) := by
  rw [arena.core.iota_certs_full, iotaCertsFull]
  exact iota_certs_full_aux_ls hk hx hrel hinv hctx hf

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

/-! ## `etaCert` (fragment `eta_cert_body`) -/

attribute [lockstep_inline] arena.core.eta_cert_body

@[lockstep] theorem eta_cert_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty1 body1 b lst}
    (_hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.eta_cert pers vis st mode lane fu fe depth ty1 body1 b) lst
      (etaCert (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx ty1) (absEIdx body1) (absEIdx b)) := by
  rw [arena.core.eta_cert, etaCert]
  lockstep_core

/-! ## `structUnitCert` (fragment `struct_unit_cert_tail`) -/

attribute [lockstep_inline] arena.core.struct_unit_cert_tail

attribute [local lockstep_simp] isForallE

@[lockstep] theorem struct_unit_cert_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (_hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.struct_unit_cert pers vis st mode lane fu fe depth a b) lst
      (structUnitCert (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx a) (absEIdx b)) := by
  rw [arena.core.struct_unit_cert, structUnitCert]
  lockstep_core
  -- glue: the port's `view_ls` against the twin's `viewLsLen` + `failDanglingLs`
  refine PC1.LS.view_ls_len_bind (by assumption) rfl (fun _ => errArm_ok) (fun v => ?_)
  dsimp only
  lockstep_core

/-! ## `structEtaCertWith` (port fragments `struct_eta_cert_{at,tail}`)

The port splits `structEtaCertWith` into three functions; inlining all of them
into one `lockstep` run is too large a goal (it exhausts the heartbeat budget
and ~11 GB).  So each fragment gets its own lemma against the twin's
corresponding SUB-TERM, named here (`sectTail`, `sectAt`: each is literally
the twin's text from that point on, the next one folded), and the caller's
tail call closes the fold by `rfl`. -/

/-- `structEtaCertWith` from the level comparison on (the port's
`struct_eta_cert_tail`). -/
def sectTail (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (us : LsIdx) (T : NIdx) (us' : LsIdx) (targs aargs : List EIdx)
    (b : EIdx) (eP eF : Nat) : AM Bool := do
  if ← liftFueled "level comparison" (← lvlsEq? us us') then do
    if ← defEqList r fe depth (aargs.take eP) targs then do
      let projs ← etaProjs T b eF
      defEqList r fe depth (aargs.drop eP) projs
    else pure false
  else pure false

/-- `structEtaCertWith` from the stuck side's type head on (`struct_eta_cert_at`). -/
def sectAt (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (cvc : IConstantVal) (c : NIdx) (us : LsIdx) (b wtb : EIdx) (aargs : List EIdx) :
    AM Bool := do
  let hh ← getAppFn coreWalkFuel wtb
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T us' =>
      match fe.find? T with
      | some (.indInfo cvT caps) => do
        let targs ← getAppArgs coreWalkFuel wtb
        let reserved ← reservedBasisNames
        match ← viewLsLen us' with
        | none => failDanglingLs
        | some uslen =>
        let slots := towerSlotsAll fe T caps.etaFields
        if caps.eta = true ∧ caps.etaCtor = c ∧
            reserved.contains T = false ∧ reserved.contains c = false ∧
            targs.length = caps.etaParams ∧
            uslen = cvT.levelParams.length ∧
            cvc.levelParams = cvT.levelParams ∧ slots = true then
          sectTail r fe depth us T us' targs aargs b caps.etaParams caps.etaFields
        else pure false
      | _ => pure false
    | _ => pure false
  else pure false

-- the region's own `take_eidx_n` pair (a list `take`, as `sectTail` reads it)
-- before the shared `Arr`-form one of `Tactic/Prims`
open ConRon.Refine2.Lockstep.PC1 in
@[lockstep] theorem struct_eta_cert_tail_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth us t us2 targs b aargs eta_params eta_fields lst}
    (_hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.struct_eta_cert_tail pers vis st mode lane fu fe depth us t us2 targs b
        aargs eta_params eta_fields) lst
      (sectTail (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absLsIdx us) (absNIdx t) (absLsIdx us2)
        (absEIdxList targs) (absEIdxList aargs) (absEIdx b) (absU eta_params) (absU eta_fields)) := by
  rw [arena.core.struct_eta_cert_tail, sectTail]
  lockstep_core

@[lockstep] theorem struct_eta_cert_at_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth cvc c us b wtb aargs lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.struct_eta_cert_at pers vis st mode lane fu fe depth cvc c us b wtb aargs) lst
      (sectAt (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absIConstantVal cvc) (absNIdx c) (absLsIdx us) (absEIdx b) (absEIdx wtb)
        (absEIdxList aargs)) := by
  rw [arena.core.struct_eta_cert_at, sectAt]
  lockstep_core
  -- glue: the port's `view_ls` against the twin's `viewLsLen` + `failDanglingLs`
  refine PC1.LS.view_ls_len_bind (by assumption) rfl (fun _ => errArm_ok) (fun v => ?_)
  dsimp only
  lockstep_core
  -- glue: the slot test reads the port's copy of the caps (`i_ind_caps_dup`)
  -- and the twin the stored caps; the copy's `eta_fields` is the original's
  all_goals
    obtain ⟨-, -, -, hef, -⟩ := ‹(_ : arena.env.IIndCaps).eta = _ ∧ _›
    have hts := ‹TwinEq (towerSlotsAll _ _ _) _›
    rw [← hef] at hts
    rw [show towerSlotsAll _ _ _ = _ from hts]
    lockstep_core

/-- `structEtaCertWith` with its second half folded into `sectAt`. -/
theorem structEtaCertWith_eq (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b wtb : EIdx) :
    structEtaCertWith r fe depth a b wtb = (do
      let hh ← getAppFn coreWalkFuel a
      if hh.tag == ETag.const then
        match ← view hh with
        | .const c us =>
          match fe.find? c with
          | some (.ctorInfo cvc cnP cnF) => do
            let aargs ← getAppArgs coreWalkFuel a
            if aargs.length = cnP + cnF then sectAt r fe depth cvc c us b wtb aargs
            else pure false
          | _ => pure false
        | _ => pure false
      else pure false) := by
  unfold structEtaCertWith sectAt sectTail
  rfl

-- the `twin_view_const_name` rule's `hg` side (`intros; rfl`) is a defeq check
-- between two `sectAt` continuations that differ in `us`: it does not fail fast
-- but exhausts the heartbeats, so the rule is switched off here (tactic gap)
attribute [-lockstep_twin] LS.twin_view_const_name in
@[lockstep] theorem struct_eta_cert_with_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b wtb lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.struct_eta_cert_with pers vis st mode lane fu fe depth a b wtb) lst
      (structEtaCertWith
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b) (absEIdx wtb)) := by
  rw [arena.core.struct_eta_cert_with, structEtaCertWith_eq]
  lockstep_core

@[lockstep] theorem struct_eta_cert_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.struct_eta_cert pers vis st mode lane fu fe depth a b) lst
      (structEtaCert
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.struct_eta_cert, structEtaCert]
  lockstep_core

@[lockstep] theorem stuck_irrel_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.stuck_irrel pers vis st mode lane fu fe depth a b) lst
      (stuckIrrel
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.stuck_irrel, stuckIrrel]
  lockstep_core

end ConRon.Refine2.Lockstep
