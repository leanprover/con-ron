/-
# `ConRon.Refine2.Core.LS.Iota` — region C2: the stuck-major rescue and the ι step

Task #97-P5-Core round 5, region C2.  The Theorem-2 lockstep lemmas of

* `majorToCtor` (Rust `major_to_ctor` and its nine fragments
  `major_to_ctor_{certs,k,eta_certs,eta,eta_build,and,and_build,at}`,
  `iota_certs_fam`), `etaFabArgsE`;
* `litMajorToCtor`, `projLitToCtor`, `prepareMajor`;
* `iotaRec` and `iotaRecAt` (Rust `iota_rec`, `iota_rec_at` and the fragments
  `iota_rec_{major,fire,params,certs,fam,reduct}`, `get_d_eidx`);
* `projCert`, `projCertAt`.

Each is one `lockstep_c2` run (the shared `lockstep` plus this file's local moves) over the Rust body with its fragments inlined
(`@[lockstep_inline]`) against the twin's body.
-/
import ConRon.Refine2.Core.LS.PrimsC2

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

/-! ## Local moves

The shared `lockstep` (task #97-P5-Core round 5's central fix) steps `ok v >>= k`
soundly and closes error arms through `ok`-bind chains.  Four moves remain
local to this region:

* an error arm through a `(b >>= g) >>= k` chain (`ErrArm.of_assoc`; the
  central `errArmChain` handles only `ok v >>= k` links) — `c2_bind_state`;
* the level-list length read (`c2_lslen`), the bounds-checked list read
  (`c2_getelem`), the split-match equations (`c2_heq`) and the `u64 as
  usize` cast (`c2_cast`), each documented at its definition. -/

theorem ErrArm.of_assoc {γ δ ε : Type} {b : Result ε} {g : ε → Result δ}
    {k : δ → Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {e : kernel.core_types.CheckError} (h : ErrArm (b >>= fun y => g y >>= k) e) :
    ErrArm ((b >>= g) >>= k) e := by
  rw [Aeneas.Std.bind_assoc_eq]; exact h

open Lean Meta Elab Tactic in
/-- `ErrArm` through a chain of `ok v >>= k` links and `(b >>= g) >>= k`
re-associations (an inlined fragment's result re-matched by the caller). -/
partial def c2ErrArmChain (g : MVarId) : TacticM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let m ← headNorm (ty.getArg! 1)
  let g ← g.replaceTargetDefEq (mkAppN ty.getAppFn (ty.getAppArgs.set! 1 m))
  if m.isAppOfArity ``Bind.bind 6 then
    let f ← headNorm (m.getArg! 4)
    if f.isAppOfArity ``Result.ok 2 then
      let gs ← applyRule g ``ErrArm.of_ok_bind
      return ← c2ErrArmChain (← pick gs `h)
    if f.isAppOfArity ``Bind.bind 6 then
      let gs ← applyRule g ``ErrArm.of_assoc
      return ← c2ErrArmChain (← pick gs `h)
  runClosed g (evalT `(tactic| lockstep_errarm))

open Lean Meta Elab Tactic in
/-- `rustStep`'s state-threading bind, with `errArmChain` for the error arm. -/
elab "c2_bind_state" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``LS 7 do throwError "c2_bind_state: not LS"
    let m := (ty.getArg! 4).headBeta
    unless m.isAppOfArity ``Bind.bind 6 do throwError "c2_bind_state: not a bind"
    let gs ← applyRule g ``LS.bind
    specCore (← pick gs `hf)
    runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
    let (_, ge) ← (← pick gs `he).introN 2 [`e, `st1]
    c2ErrArmChain ge
    let rest ← cont (← pick gs `hk) [`a, `b, `st1, `lst1, `hR, `hrel, `hinv] (some `hR)
    setGoals ((← normAll rest) ++ others)

open Lean Meta Elab Tactic in
/-- A `u64 as usize` cast whose value is known to fit: turn `CastFits x r`
into `r.val = x.val` (by `scalar_tac` from the context) and rewrite the
`TwinEq` facts with it. -/
elab "c2_cast" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut found := none
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``PC2.CastFits 2 then found := some d
    let some d := found | throwError "c2_cast: no CastFits"
    let h := mkIdent d.userName
    let hs ← (← getLCtx).foldlM (init := #[]) fun acc d' => do
      if d'.isImplementationDetail then return acc
      let t ← instantiateMVars d'.type
      return if t.isAppOfArity ``TwinEq 3 then acc.push d'.fvarId else acc
    let hv ← mkFreshUserName `hv
    let hvI := mkIdent hv
    evalTactic (← `(tactic| have $hvI:ident := PC2.CastFits.val (by assumption) (by scalar_tac)))
    let g ← getMainGoal
    let g ← g.clear d.fvarId
    setGoals [g]
    for fv in hs do
      let n := mkIdent ((← g.getDecl).lctx.get! fv).userName
      try evalTactic (← `(tactic| simp only [$hvI:ident] at $n:ident)) catch _ => pure ()
    let g ← getMainGoal
    let g ← g.replaceTargetDefEq ((← instantiateMVars (← g.getType)).consumeMData)
    setGoals (← normAll [g])
    let _ := h

/-! ### The level-list length read

`majorToCtor`'s `And` branch reads `viewLsLen ust` and fails with
`failDanglingLs` on `none`; the port reads the whole list (`view_ls`, which
fails with the same error) and takes its `len()`.  The same operation at a
different projection — the store's `viewLen` IS `view`'s length — so the twin
is rewritten to the whole read (`LS.twin_viewLsLen`). -/

theorem LsStore_viewLen_eq (st : LsStore) (i : LsIdx) :
    st.viewLen i = (st.view i).map List.length := by
  unfold LsStore.viewLen LsStore.view LsStore.persGetLen LsTables.getLen LsTables.get
  split_ifs <;> simp [Option.map_map] <;> rfl

theorem viewLsLen_bind {β : Type} (h : LsIdx) (k : Option Nat → AM β)
    (hk : k none = failDanglingLs) :
    (viewLsLen h >>= k) = (viewLs h >>= fun v => k (some v.length)) := by
  funext lst
  show (viewLsLen h >>= k).run lst = (viewLs h >>= _).run lst
  rw [StateT.run_bind, StateT.run_bind]
  show (k (lst.store.lss.viewLen h)).run lst = _
  rw [LsStore_viewLen_eq]
  show _ = ((match lst.store.lss.view h with
      | some v => (pure v : AM LsNodeView)
      | none => Arena.fail (.internal "arena: dangling level-list handle")).run lst >>= _)
  cases lst.store.lss.view h with
  | none => rw [Option.map_none, hk]; rfl
  | some v => rfl

theorem LS.twin_viewLsLen {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : LsIdx} {k : Option Nat → AM β} (hk : k none = failDanglingLs)
    (hls : LS pers R m lst (viewLs h >>= fun v => k (some v.length))) :
    LS pers R m lst (viewLsLen h >>= k) := by
  rw [viewLsLen_bind h k hk]; exact hls

open Lean Meta Elab Tactic in
elab "c2_lslen" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``LS 7 do throwError "c2_lslen: not LS"
    let x := (ty.getArg! 6).headBeta
    unless x.isAppOfArity ``Bind.bind 6 && (x.getArg! 4).headBeta.isAppOf ``Arena.viewLsLen do
      throwError "c2_lslen: no viewLsLen"
    let gs ← applyRule g ``LS.twin_viewLsLen
    runClosed (← pick gs `hk) (evalT `(tactic| rfl))
    setGoals ((← normAll [← pick gs `hls]) ++ others)

open Lean Meta Elab Tactic in
/-- A twin `l[i]?` read at an index the Rust has bounds-checked (`vec_index`
left `i < l.length` in the context): the twin read is `some l[i]`. -/
elab "c2_getelem" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut done := false
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``LT.lt 4 && (t.getArg! 3).isAppOf ``List.length then
        let h := mkIdent d.userName
        try
          evalTactic (← `(tactic| simp only [List.getElem?_eq_getElem $h:ident, Option.map_some,
            Option.bind_some]))
          done := true
        catch _ => pure ()
    unless done do throwError "c2_getelem: nothing to rewrite"
    let g ← getMainGoal
    let g ← g.replaceTargetDefEq ((← instantiateMVars (← g.getType)).consumeMData)
    setGoals (← normAll [g])

open Lean Meta Elab Tactic in
/-- A Rust `match` on a non-variable discriminant (`rl.fire`) was `split`, which
leaves `heq : rl.fire = C` in the context but does not touch the twin's own
`match` on the same field: rewrite the goal with it. -/
elab "c2_heq" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut done := false
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``Eq 3 && !(t.getArg! 1).isFVar then
        let r := t.getArg! 2
        if let some c := r.getAppFn.constName? then
          if (← getEnv).isConstructor c then
            let h := mkIdent d.userName
            try
              evalTactic (← `(tactic| simp only [$h:ident]))
              done := true
            catch _ => pure ()
    unless done do throwError "c2_heq: nothing to rewrite"
    let g ← getMainGoal
    let g ← g.replaceTargetDefEq ((← instantiateMVars (← g.getType)).consumeMData)
    setGoals (← normAll [g])

/-- The shared `lockstep` step with this region's moves around it. -/
macro "lockstep_c2" : tactic =>
  `(tactic| repeat' (first
    | c2_heq | lockstep_step | c2_bind_state | c2_lslen | c2_getelem | c2_cast))

/-! ## Local normalisation: record projections and lengths

The twin reads fields of the abstracted records (`cvj.levelParams`,
`caps.etaParams`); the Rust reads the same fields of the Rust records.  The
record copies are identities (`PrimsC2.i_*_dup_ls`), so these projections are
all the glue the two readings need. -/

theorem absIConstantVal_name (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).name = absNIdx cv.name := rfl
theorem absIConstantVal_levelParams (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).levelParams = cv.level_params.val.map absNIdx := rfl
theorem absIConstantVal_type (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).type = absEIdx cv.ty := rfl
theorem absIIndCaps_eta (c : arena.env.IIndCaps) : (absIIndCaps c).eta = c.eta := rfl
theorem absIIndCaps_etaCtor (c : arena.env.IIndCaps) :
    (absIIndCaps c).etaCtor = absNIdx c.eta_ctor := rfl
theorem absIIndCaps_etaParams (c : arena.env.IIndCaps) :
    (absIIndCaps c).etaParams = c.eta_params.val := rfl
theorem absIIndCaps_etaFields (c : arena.env.IIndCaps) :
    (absIIndCaps c).etaFields = c.eta_fields.val := rfl
theorem absLsNodeView_length (v : alloc.vec.Vec arena.handle.LIdx) :
    (absLsNodeView v).length = v.val.length := by simp [absLsNodeView]
theorem absEIdxList_length (v : alloc.vec.Vec arena.handle.EIdx) :
    (absEIdxList v).length = v.val.length := by simp [absEIdxList]
theorem vec_len_eq_iff {α β : Type} (x : alloc.vec.Vec α) (y : alloc.vec.Vec β) :
    (alloc.vec.Vec.len x = alloc.vec.Vec.len y) = (x.val.length = y.val.length) := by
  apply propext
  constructor
  · intro h; have := congrArg (·.val) h; simpa using this
  · intro h; apply UScalar.eq_imp; simpa using h

attribute [local lockstep_simp] absIConstantVal_name absIConstantVal_levelParams
  absIConstantVal_type absIIndCaps_eta absIIndCaps_etaCtor absIIndCaps_etaParams
  absIIndCaps_etaFields absLsNodeView_length absEIdxList_length vec_len_eq_iff List.length_map

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

/-- Region A1. -/
@[lockstep] theorem stub_const_ty_at_ls {pers st cv us lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.const_ty_at pers st cv us) lst
      (constTyAt (absIConstantVal cv) (absLsIdx us)) := by
  sorry

/-- Region C1. -/
@[lockstep] theorem stub_iota_certs_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth lic h args lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.iota_certs pers vis st mode lane fu fe depth lic h args 0#usize) lst
      (iotaCerts (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) lic
        (absEIdx h) (absEIdxList args)) := by
  sorry

/-- Region B. -/
@[lockstep] theorem stub_lit_to_ctor_if_nat_ls {pers vis st fe lfe h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = absEIdx a) (arena.core.lit_to_ctor_if_nat pers vis st fe h) lst
      (litToCtorIfNat lfe (absEIdx h)) := by
  sorry

/-- Region B. -/
@[lockstep] theorem stub_str_lit_supported_ls {pers vis st fe lfe lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.str_lit_supported pers vis st fe) lst
      (strLitSupported lfe) := by
  sorry

/-- Region B. -/
@[lockstep] theorem stub_str_lit_to_constructor_ls {pers st s lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.str_lit_to_constructor pers st s) lst
      (strLitToConstructor (ConRon.Refine.absString s)) := by
  sorry

/-- Region A2. -/
@[lockstep] theorem stub_eta_projs_ls {pers vis st fe lfe t us targs b nF lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = absEIdxList a)
      (arena.core.eta_projs pers vis st fe t us targs b nF) lst
      (etaProjs lfe (absNIdx t) (absLsIdx us) (absEIdxList targs) (absEIdx b) (absU nF)) := by
  sorry

/-- Region A1. -/
@[lockstep] theorem stub_is_ctor_app_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.is_ctor_app pers vis st fe e) lst
      (isCtorApp lfe (absEIdx e)) := by
  sorry

/-- Region A1. -/
@[lockstep] theorem stub_caps_never_zero_ls {pers st lps us caps lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.caps_never_zero pers st lps us caps) lst
      (capsNeverZero (lps.val.map absNIdx) (absLsIdx us) (absIIndCaps caps)) := by
  sorry

/-- Region A2. -/
@[lockstep] theorem stub_fab_scope_ok_ls {pers st depth fab major lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.fab_scope_ok pers st depth fab major) lst
      (fabScopeOk (absU depth) (absEIdx fab) (absEIdx major)) := by
  sorry

/-- Region A2. -/
@[lockstep] theorem stub_and_rescue_slots_ls {pers vis st fe lfe ctor nP ust lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.and_rescue_slots pers vis st fe ctor nP ust) lst
      (andRescueSlots lfe (absNIdx ctor) (absU nP) (absLsIdx ust)) := by
  sorry

/-- Region C1. -/
@[lockstep] theorem stub_proof_irrel_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.proof_irrel pers vis st mode lane fu fe depth a b) lst
      (proofIrrel (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) := by
  sorry

/-- Region C1. -/
@[lockstep] theorem stub_struct_eta_cert_with_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b wtb lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.struct_eta_cert_with pers vis st mode lane fu fe depth a b wtb) lst
      (structEtaCertWith (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b) (absEIdx wtb)) := by
  sorry

/-- Region A1. -/
@[lockstep] theorem stub_rec_rule_k_ls (rules : alloc.vec.Vec arena.env.IRecRule) :
    LSP (arena.core.rec_rule_k rules) (fun b => b = recRuleK (rules.val.map absIRecRule)) := by
  sorry

/-- Region A1. -/
@[lockstep] theorem stub_find_rule_ls (rules : alloc.vec.Vec arena.env.IRecRule)
    (c : arena.handle.NIdx) :
    LSP (arena.core.find_rule rules c 0#usize)
      (fun o => TwinEq (findRule (rules.val.map absIRecRule) (absNIdx c))
        (o.bind (fun j => (rules.val[j.val]?).map absIRecRule))) := by
  sorry

/-- Region A1. -/
@[lockstep] theorem stub_lvls_eq_ls {pers st us vs lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.lvls_eq pers st us vs) lst
      (lvlsEq? (absLsIdx us) (absLsIdx vs)) := by
  sorry

/-- Region A1. -/
@[lockstep] theorem stub_lift_fueled_ls {pers st lst} (what : String) (o : Option Bool)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst (liftFueled what o) := by
  sorry

/-- Region A1. -/
@[lockstep] theorem stub_rule_rhs_at_ls {pers st rec_name ctor lps rhs us lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.rule_rhs_at pers st rec_name ctor lps rhs us) lst
      (ruleRhsAt (absNIdx rec_name) (absNIdx ctor) (lps.val.map absNIdx) (absEIdx rhs)
        (absLsIdx us)) := by
  sorry

/-- Region A1. -/
@[lockstep] theorem stub_rec_fire_comparands_ls {pers st rl lps us cvj_lps args r_p lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (absLsIdx a.1, absEIdxList a.2))
      (arena.core.rec_fire_comparands pers st rl lps us cvj_lps args r_p) lst
      (recFireComparands (absIRecRule rl) (lps.val.map absNIdx) (absLsIdx us)
        (cvj_lps.val.map absNIdx) (absEIdxList args) (absU r_p)) := by
  sorry

/-- Region A1. -/
@[lockstep] theorem stub_read_name_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.NIdx) :
    LS pers (fun a b => ConRon.Refine.NameWF a ∧ b = ConRon.Refine.absName a)
      (arena.monad.read_name_m pers st h) lst (Arena.readNameM (absNIdx h)) := by
  sorry

/-- Region C1. -/
@[lockstep] theorem stub_def_eq_list_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth xs ys i lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.def_eq_list pers vis st mode lane fu fe depth xs ys i) lst
      (defEqList (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdxListFrom xs i) (absEIdxListFrom ys i)) := by
  sorry

/-- Region C1. -/
@[lockstep] theorem stub_iota_index_ok_ls {f : Nat} (hk : KnotRel f)
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
  sorry

/-! ## `projCert` / `projCertAt` -/

@[lockstep] theorem proj_cert_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth lic c us args lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.proj_cert pers vis st mode lane fu fe depth lic c us args) lst
      (projCert (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) lic
        (absNIdx c) (absLsIdx us) (absEIdxList args)) := by
  rw [arena.core.proj_cert, projCert]
  lockstep_c2

@[lockstep] theorem proj_cert_at_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth verified lic c us args lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.proj_cert_at pers vis st mode lane fu fe depth verified lic c us args) lst
      (projCertAt (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        verified lic (absNIdx c) (absLsIdx us) (absEIdxList args)) := by
  rw [arena.core.proj_cert_at, projCertAt]
  lockstep_c2

/-! ## The literal conversions -/

attribute [local lockstep_simp] ConRon.Refine.absLiteral

@[lockstep] theorem lit_major_to_ctor_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.lit_major_to_ctor pers vis st mode lane fu fe depth h) lst
      (litMajorToCtor (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h)) := by
  rw [arena.core.lit_major_to_ctor, litMajorToCtor]
  lockstep_c2

@[lockstep] theorem proj_lit_to_ctor_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.proj_lit_to_ctor pers vis st mode lane fu fe depth h) lst
      (projLitToCtor (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h)) := by
  rw [arena.core.proj_lit_to_ctor, projLitToCtor]
  lockstep_c2

/-! ## `etaFabArgsE` -/

@[lockstep] theorem eta_fab_args_e_ls {pers vis st fe lfe t ust targs major nF lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = absEIdxList a)
      (arena.core.eta_fab_args_e pers vis st fe t ust targs major nF) lst
      (etaFabArgsE lfe (absNIdx t) (absLsIdx ust) (absEIdxList targs) (absEIdx major)
        (absU nF)) := by
  rw [arena.core.eta_fab_args_e, etaFabArgsE]
  lockstep_c2

/-! ## `majorToCtor` -/

attribute [lockstep_inline] arena.core.major_to_ctor_certs arena.core.iota_certs_fam
  arena.core.major_to_ctor_k arena.core.major_to_ctor_eta_certs arena.core.major_to_ctor_eta
  arena.core.major_to_ctor_eta_build arena.core.major_to_ctor_and
  arena.core.major_to_ctor_and_build arena.core.major_to_ctor_at

section majorToCtor

theorem absIRecRule_ctor (r : arena.env.IRecRule) : (absIRecRule r).ctor = absNIdx r.ctor := rfl
theorem absIRecRule_k (r : arena.env.IRecRule) : (absIRecRule r).k = r.k := rfl
theorem absIRecRule_eta (r : arena.env.IRecRule) : (absIRecRule r).eta = r.eta := rfl

attribute [local lockstep_simp] absIRecRule_ctor absIRecRule_k absIRecRule_eta

set_option maxHeartbeats 0 in
@[lockstep] theorem major_to_ctor_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth recName rules major lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.major_to_ctor pers vis st mode lane fu fe depth recName rules major) lst
      (majorToCtor (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absNIdx recName) (rules.val.map absIRecRule) (absEIdx major)) := by
  rw [arena.core.major_to_ctor, majorToCtor.eq_def]
  have hlenv : (alloc.vec.Vec.len rules).val = rules.val.length := alloc.vec.Vec.len_val _
  generalize hL : rules.val.map absIRecRule = L
  rcases L with _ | ⟨x, _ | ⟨y, zs⟩⟩
  · have h0 : rules.val.length = 0 := by simpa using congrArg List.length hL
    show LS _ _ _ _ _
    lockstep_c2
  · obtain ⟨r0, hr0, rfl⟩ := List.map_eq_singleton_iff.mp hL
    have h1 : rules.val.length = 1 := by simp [hr0]
    have hr0' : absIRecRule r0
        = absIRecRule (rules.val[(0#usize : Std.Usize).val]'(by simp; omega)) := by
      simp [hr0]
    rw [hr0']
    show LS _ _ _ _ _
    lockstep_c2
  · have h2 : 2 ≤ rules.val.length := by
      have := congrArg List.length hL; simp at this; omega
    show LS _ _ _ _ _
    lockstep_c2

end majorToCtor

/-! ## `prepareMajor` -/

set_option maxHeartbeats 0 in
@[lockstep] theorem prepare_major_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth recName rules major lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.prepare_major pers vis st mode lane fu fe depth recName rules major) lst
      (prepareMajor (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absNIdx recName) (rules.val.map absIRecRule) (absEIdx major)) := by
  rw [arena.core.prepare_major, prepareMajor]
  lockstep_c2

/-! ## `iotaRecAt` / `iotaRec` -/

section iota

theorem absIRecRule_ctor' (r : arena.env.IRecRule) : (absIRecRule r).ctor = absNIdx r.ctor := rfl
theorem absIRecRule_nfields (r : arena.env.IRecRule) : (absIRecRule r).nfields = r.nfields.val := rfl
theorem absIRecRule_ctorParams (r : arena.env.IRecRule) :
    (absIRecRule r).ctorParams = r.ctor_params.val := rfl
theorem absIRecRule_fire (r : arena.env.IRecRule) :
    (absIRecRule r).fire = absIRecRuleFire r.fire := rfl
theorem absIRecRule_rhs (r : arena.env.IRecRule) : (absIRecRule r).rhs = absEIdx r.rhs := rfl

attribute [local lockstep_simp] absIRecRule_ctor' absIRecRule_nfields absIRecRule_ctorParams
  absIRecRule_fire absIRecRule_rhs absIRecRuleFire

attribute [lockstep_inline] arena.core.iota_rec_major arena.core.iota_rec_fire
  arena.core.iota_rec_params arena.core.iota_rec_certs arena.core.iota_rec_fam
  arena.core.iota_rec_reduct

/-- `iotaRecAt`'s one `liftFueled` site, with its message fixed (a free
`String` argument is a goal no side tactic closes). -/
@[lockstep] theorem lift_fueled_level_ls {pers st lst} (o : Option Bool)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst
      (liftFueled "level comparison" o) :=
  stub_lift_fueled_ls "level comparison" o hrel hinv

set_option maxHeartbeats 0 in
@[lockstep] theorem iota_rec_at_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth hd sargs n lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.iota_rec_at pers vis st mode lane fu fe depth hd sargs n) lst
      (iotaRecAt (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx hd) (absEIdxArr sargs) (absSz n)) := by
  rw [arena.core.iota_rec_at, iotaRecAt]
  lockstep_c2

@[lockstep] theorem iota_rec_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.iota_rec pers vis st mode lane fu fe depth e) lst
      (iotaRec (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx e)) := by
  rw [arena.core.iota_rec, iotaRec]
  lockstep_c2

end iota

end ConRon.Refine2.Lockstep
