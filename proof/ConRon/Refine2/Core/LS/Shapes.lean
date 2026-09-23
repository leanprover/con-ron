/-
# `ConRon.Refine2.Core.LS.Shapes` — region A2: the shape helpers and the small loops

Task #97-P5-Core round 5, region A2.  The Theorem-2 lockstep lemmas of the
small `arena::core` helpers — the spine readers (`get_app_spine`,
`head_and_args`), the stuck-tag test, the binder-datum helpers, the
telescope rebuilds (`infer_lams_out`, `infer_pis_out`), the projection-slot
walks (`tower_slots_all`, `rec_slots_all`, `and_rescue_slots`), the
fabricated projections (`eta_projs`) and the scope/shape guards — each
against its twin in `Arena/Core.lean`, by `lockstep_core`.

A Rust READ (`Result (Result α CheckError)`, no state) is stated in `LSR`
form and proved through `LSR.of_LS`, which turns it into an `LS` goal about
`m >>= fun o => ok (o, st)` so that `lockstep_core` can zip it.  A pure Rust
helper whose twin is a pure function is stated in `LSP` form.
-/
import ConRon.Refine2.Core.LS.PrimsA2

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PA2

/-! ## Glue: a Rust read as a state-threading computation -/

/-! ### A local `lockstep_core` variant (region A2's tactic gap workaround)

`Result`'s bind is an `ITree` bind, so `ok v >>= k` is NOT definitionally
`k v` for the kernel: `lockstep_core`'s `coreMove` feeds an `ok v` bind to its
continuation by `replaceTargetDefEq`, which the elaborator accepts and the
kernel then rejects ("application type mismatch").  And `lockstep`'s `errArm`
closes a read's error arm by `exact errArm_ok`, which needs the arm to BE
`ok (.Err e, st)`, not `ok (.Err e) >>= k`.  `lockstep_a2` handles both by
REWRITING (`bind_tc_ok`) before `lockstep_core_step` sees the goal. -/

theorem LS.rust_ok_bind {γ α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {v : γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R (k v) lst x) :
    LS pers R (ok v >>= k) lst x := by
  rw [bind_tc_ok]; exact h

theorem LSP.rust_ok_bind {γ α : Type} {v : γ} {k : γ → Result α} {Q : α → Prop}
    (h : LSP (k v) Q) : LSP (ok v >>= k) Q := by
  rw [bind_tc_ok]; exact h

theorem errArm_of_eq {γ : Type} {e : kernel.core_types.CheckError} {st : arena.monad.AState}
    {m : Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    (h : m = ok (.Err e, st)) : ErrArm m e := by
  subst h; exact errArm_ok

/-- A Rust read in tail position: `f >>= fun o => ok (o, st)`. -/
theorem LSR.tail_ls {α β : Type} {pers : arena.store.PersTier} {R₁ R : α → β → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x' x : AM β}
    (hf : LSR pers R₁ f st lst x') (hx : x' = x) (hR : ∀ a b, R₁ a b → R a b) :
    LS pers R (f >>= fun o => ok (o, st)) lst x := by
  subst hx
  intro o st' hm
  obtain ⟨r, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h2)
  have h := hf r h1
  cases r with
  | Err e => exact h
  | Ok a =>
    obtain ⟨b, lst', h1, h2, h3, h4⟩ := h
    exact ⟨b, lst', h1, hR _ _ h2, h3, h4⟩

open Lean Meta Elab Tactic in
/-- The two moves above, tried before `lockstep_core_step`. -/
elab "lockstep_a2_step" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some rp := rustPos ty | throwError "a2: not a judgement"
  let m := (ty.getArg! rp).headBeta
  unless m.isAppOfArity ``Bind.bind 6 do throwError "a2: not a bind"
  let f ← headNorm (m.getArg! 4)
  if f.isAppOfArity ``Result.ok 2 then
    let gs ← applyRule g (if rp == 4 then ``LS.rust_ok_bind else ``LSP.rust_ok_bind)
    let rest ← normAll [← pick gs `h]
    setGoals (rest ++ others)
    return
  -- a pattern `let (x, y) := p` in bind position (`uncurry`): split the tuple
  if f.isAppOfArity ``Aeneas.Std.uncurry 5 then
    if let .fvar fv := f.appArg! then
      let subs ← g.cases fv
      let rest ← normAll (subs.toList.map (·.mvarId))
      setGoals (rest ++ others)
      return
  if let some mapp ← matchMatcherApp? f then
    for d in mapp.discrs do
      let d ← instantiateMVars d
      for fv in (Lean.collectFVars {} d).fvarIds do
        if (← whnfR (← fv.getType)).isAppOf ``Prod then
          let subs ← g.cases fv
          let rest ← normAll (subs.toList.map (·.mvarId))
          setGoals (rest ++ others)
          return
  if rp == 4 then
    match ← classify (← inferType f).appArg! with
    | .read =>
      let s ← saveState
      try
        let gs ← applyRule g ``LSR.tail_ls
        specCore (← pick gs `hf)
        runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
        runClosed (← pick gs `hR)
          (evalT `(tactic| (intro _ _ h; first | exact h | (subst h; rfl) | lockstep_side)))
        setGoals others
        return
      catch _ => s.restore
      let gs ← applyRule g ``LSR.bind
      specCore (← pick gs `hf)
      runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
      runClosed (← pick gs `he) (evalT `(tactic| (intro _; apply errArm_of_eq; (first | rfl | (simp only [bind_tc_ok]; done) | (simp only [bind_tc_ok]; rfl)))))
      let rest ← cont (← pick gs `hk) [`a, `b, `lst1, `hR, `hrel, `hinv] (some `hR)
      setGoals ((← normAll rest) ++ others)
      return
    | _ => pure ()
  throwError "a2: no move"

/-- `lockstep_core` with region A2's two rewriting moves first. -/
macro "lockstep_a2" : tactic =>
  `(tactic| repeat' (first | lockstep_a2_step | lockstep_core_step))

theorem LSR.of_LS {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : LS pers R (m >>= fun o => ok (o, st)) lst x) : LSR pers R m st lst x := by
  intro o hm
  exact h o st (by rw [hm, bind_tc_ok])

/-! ## Pure helpers -/

@[lockstep] theorem pw_written_ls (pw : kernel.prop_when.PropWhen) :
    LSP (arena.core.pw_written pw) (fun b => b = pwWritten (ConRon.Refine.absPropWhen pw)) := by
  intro b h
  rw [arena.core.pw_written] at h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [pwWritten, ← ConRon.Refine.PropWhen.is_never_refines hc, ← Result.ok_injective h]
  cases c <;> rfl

@[lockstep] theorem annot_binder_meta_ls (pw : Option kernel.prop_when.PropWhen)
    (mb : kernel.expr.BinderMeta) :
    LSP (arena.core.annot_binder_meta pw mb)
      (fun r => ConRon.Refine.absBinderMeta r =
        annotBinderMeta (pw.map ConRon.Refine.absPropWhen) (ConRon.Refine.absBinderMeta mb)) := by
  intro r h
  unfold arena.core.annot_binder_meta at h
  cases pw with
  | none =>
    obtain rfl := ConRon.Refine.Expr.binder_meta_dup_eq h
    rfl
  | some p =>
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hb' := pw_written_ls _ b hb
    simp only [Option.map_some, annotBinderMeta, ConRon.Refine.absBinderMeta]
    split at h
    · rename_i hc
      obtain rfl := ConRon.Refine.Expr.binder_meta_dup_eq h
      rw [← hb', hc]; rfl
    · rename_i hc
      rw [binder_meta_ls p r h]
      simp only [Bool.not_eq_true] at hc
      rw [← hb', hc]; rfl

@[lockstep] theorem whnf_core_stuck_tag_ls (e : arena.handle.EIdx) :
    LSP (arena.core.whnf_core_stuck_tag e) (fun b => b = whnfCoreStuckTag (absEIdx e)) := by
  intro b h
  rw [arena.core.whnf_core_stuck_tag] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have htag := eidx_tag_abs ht
  simp only [whnfCoreStuckTag, htag, absU32_beq_app, absU32_beq_proj, absU32_beq_letE,
    absU32_beq_bvar]
  split_ifs at h <;> simp_all

/-! ## Reads -/

@[lockstep] theorem defeq_peel_done_ls {pers st mism mism_lam lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = a) (arena.core.defeq_peel_done mism mism_lam) st lst
      (defeqPeelDone mism mism_lam) := by
  apply LSR.of_LS
  rw [arena.core.defeq_peel_done, defeqPeelDone]
  lockstep_a2

theorem get_app_spine_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx) (k : Std.Usize),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = (absEIdx a.1, absEIdxArr a.2.1, absEIdxArr a.2.2))
        (arena.core.get_app_spine_go pers st fuel h k) st lst
        (getAppSpineGo n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h k hn hrel hinv
    apply LSR.of_LS
    rw [arena.core.get_app_spine_go, getAppSpineGo]
    lockstep_a2
  | succ m ih =>
    intro pers st lst fuel h k hn hrel hinv
    apply LSR.of_LS
    rw [arena.core.get_app_spine_go, getAppSpineGo]
    lockstep_a2

@[lockstep] theorem get_app_spine_go_ls {pers st fuel h k lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (absEIdx a.1, absEIdxArr a.2.1, absEIdxArr a.2.2))
      (arena.core.get_app_spine_go pers st fuel h k) st lst
      (getAppSpineGo (absU fuel) (absEIdx h)) :=
  get_app_spine_go_aux _ fuel h k rfl hrel hinv

@[lockstep] theorem get_app_spine_ls {pers st fuel h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (absEIdx a.1, absEIdxArr a.2.1, absEIdxArr a.2.2))
      (arena.core.get_app_spine pers st fuel h) st lst
      (getAppSpine (absU fuel) (absEIdx h)) := by
  rw [arena.core.get_app_spine, getAppSpine]
  exact get_app_spine_go_ls hrel hinv

@[lockstep] theorem head_and_args_ls {pers st v lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (absEIdx a.1, absEIdxArr a.2))
      (arena.core.head_and_args pers st v) st lst
      (headAndArgs (absEIdx v)) := by
  apply LSR.of_LS
  rw [arena.core.head_and_args, headAndArgs]
  lockstep_a2

/-! ## Straight-line state-threading helpers -/

section
attribute [local lockstep_inline] arena.core.intern_app

@[lockstep] theorem intern_app_rebuilt_ls {pers st h same f a lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.intern_app_rebuilt pers st h same f a) lst
      (internAppRebuilt (absEIdx h) same (absEIdx f) (absEIdx a)) := by
  rw [arena.core.intern_app_rebuilt, internAppRebuilt]
  lockstep_a2

end

/-! ## Guards and small state-threading helpers -/

@[lockstep] theorem defeq_no_fvars_ls {pers st a b lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.defeq_no_fvars pers st a b) lst
      (defeqNoFvars (absEIdx a) (absEIdx b)) := by
  rw [arena.core.defeq_no_fvars, defeqNoFvars]
  lockstep_a2

@[lockstep] theorem fab_scope_ok_ls {pers st depth fab major lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.fab_scope_ok pers st depth fab major) lst
      (fabScopeOk (absU depth) (absEIdx fab) (absEIdx major)) := by
  rw [arena.core.fab_scope_ok, fabScopeOk]
  lockstep_a2

@[lockstep] theorem infer_lam_result_ls {pers st ty bt depth mb lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.infer_lam_result pers st ty bt depth mb) lst
      (inferLamResult (absEIdx ty) (absEIdx bt) (absU depth) (ConRon.Refine.absBinderMeta mb)) := by
  rw [arena.core.infer_lam_result, inferLamResult]
  lockstep_a2

theorem decide_u64_eq (a b : Std.U64) : decide (a = b) = (a.val == b.val) := by
  by_cases h : a = b
  · subst h; simp
  · have : a.val ≠ b.val := fun hc => h (UScalar.eq_of_val_eq hc)
    simp [h, this]

section
attribute [local lockstep_simp] decide_u64_eq ExprOps.absEIdxList List.length_map
  alloc.vec.Vec.len_val

@[lockstep] theorem eta_ctor_shape_ls {pers vis st fe lfe a lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.eta_ctor_shape pers vis st fe a) lst
      (etaCtorShape lfe (absEIdx a)) := by
  rw [arena.core.eta_ctor_shape, etaCtorShape]
  lockstep_a2

end

theorem pi_residual_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (e : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize),
      ExprOpsHyp pers →
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = Option.map absEIdx a) (arena.core.pi_residual pers st e args i) lst
        (piResidual (absEIdx e) (absEIdxListFrom args i)) := by
  induction n with
  | zero =>
    intro pers st lst e args i hx hn hrel hinv
    rw [arena.core.pi_residual, listFrom_nil args i (by omega), piResidual]
    lockstep_a2
  | succ k ih =>
    intro pers st lst e args i hx hn hrel hinv
    rw [arena.core.pi_residual, listFrom_cons args i (by omega), piResidual]
    lockstep_a2

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

/-- Region A1's `IProjEntry.fireOk`. -/
@[lockstep] theorem stub_proj_entry_fire_ok_ls {pers st entry us lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.proj_entry_fire_ok pers st entry us) lst
      ((absIProjEntry entry).fireOk (absLsIdx us)) := by
  sorry

/-! ## The projection-slot walks -/

section slots
attribute [local lockstep_simp] Option.map_none Option.map_some Option.isSome_none
  Option.isSome_some absIProjEntry

theorem tower_slots_all_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {vis : Std.U64} {st : arena.monad.AState}
      {fe : arena.env.IFEnv} {lfe : IFEnv} {lst : AState}
      (t : arena.handle.NIdx) (nn j : Std.U64),
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      LS pers (fun a b => b = a) (arena.core.tower_slots_all_go pers vis st fe t nn j) lst
        (towerSlotsAllGo lfe (absNIdx t) n (absU j)) := by
  induction n with
  | zero =>
    intro pers vis st fe lfe lst t nn j hn hrel hinv hctx
    rw [arena.core.tower_slots_all_go, towerSlotsAllGo]
    lockstep_a2
  | succ m ih =>
    intro pers vis st fe lfe lst t nn j hn hrel hinv hctx
    rw [arena.core.tower_slots_all_go, towerSlotsAllGo]
    lockstep_a2

@[lockstep] theorem tower_slots_all_go_ls {pers vis st fe lfe t n j lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.tower_slots_all_go pers vis st fe t n j) lst
      (towerSlotsAllGo lfe (absNIdx t) (absU n) (absU j)) :=
  tower_slots_all_go_aux _ t n j rfl hrel hinv hctx

@[lockstep] theorem tower_slots_all_ls {pers vis st fe lfe t n_f lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.tower_slots_all pers vis st fe t n_f) lst
      (towerSlotsAll lfe (absNIdx t) (absU n_f)) := by
  rw [arena.core.tower_slots_all, towerSlotsAll]
  lockstep_a2

theorem rec_slots_all_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {vis : Std.U64} {st : arena.monad.AState}
      {fe : arena.env.IFEnv} {lfe : IFEnv} {lst : AState}
      (t : arena.handle.NIdx) (nn j : Std.U64),
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      LS pers (fun a b => b = a) (arena.core.rec_slots_all_go pers vis st fe t nn j) lst
        (recSlotsAllGo lfe (absNIdx t) n (absU j)) := by
  induction n with
  | zero =>
    intro pers vis st fe lfe lst t nn j hn hrel hinv hctx
    rw [arena.core.rec_slots_all_go, recSlotsAllGo]
    lockstep_a2
  | succ m ih =>
    intro pers vis st fe lfe lst t nn j hn hrel hinv hctx
    rw [arena.core.rec_slots_all_go, recSlotsAllGo]
    lockstep_a2

@[lockstep] theorem rec_slots_all_go_ls {pers vis st fe lfe t n j lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.rec_slots_all_go pers vis st fe t n j) lst
      (recSlotsAllGo lfe (absNIdx t) (absU n) (absU j)) :=
  rec_slots_all_go_aux _ t n j rfl hrel hinv hctx

@[lockstep] theorem rec_slots_all_ls {pers vis st fe lfe t n_f lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.rec_slots_all pers vis st fe t n_f) lst
      (recSlotsAll lfe (absNIdx t) (absU n_f)) := by
  rw [arena.core.rec_slots_all, recSlotsAll]
  lockstep_a2

end slots

section projs
attribute [local lockstep_simp] absEIdxList

theorem proj_nodes_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (t : arena.handle.NIdx) (b : arena.handle.EIdx) (nn j : Std.U64),
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxList a) (arena.core.proj_nodes_go pers st t b nn j) lst
        (projNodesGo (absNIdx t) (absEIdx b) n (absU j)) := by
  induction n with
  | zero =>
    intro pers st lst t b nn j hn hrel hinv
    rw [arena.core.proj_nodes_go, projNodesGo]
    lockstep_a2
    all_goals trace_state
    all_goals sorry
  | succ m ih =>
    intro pers st lst t b nn j hn hrel hinv
    rw [arena.core.proj_nodes_go, projNodesGo]
    lockstep_a2
    all_goals trace_state
    all_goals sorry

@[lockstep] theorem proj_nodes_go_ls {pers st t b n j lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxList a) (arena.core.proj_nodes_go pers st t b n j) lst
      (projNodesGo (absNIdx t) (absEIdx b) (absU n) (absU j)) :=
  proj_nodes_go_aux _ t b n j rfl hrel hinv

theorem proj_apps_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (t : arena.handle.NIdx) (us : arena.handle.LsIdx) (targs : alloc.vec.Vec arena.handle.EIdx)
      (b : arena.handle.EIdx) (nn j : Std.U64),
      ExprOpsHyp pers → nn.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxList a)
        (arena.core.proj_apps_go pers st t us targs b nn j) lst
        (projAppsGo (absNIdx t) (absLsIdx us) (absEIdxList targs) (absEIdx b) n (absU j)) := by
  induction n with
  | zero =>
    intro pers st lst t us targs b nn j hx hn hrel hinv
    rw [arena.core.proj_apps_go, projAppsGo]
    lockstep_a2
    all_goals trace_state
    all_goals sorry
  | succ m ih =>
    intro pers st lst t us targs b nn j hx hn hrel hinv
    rw [arena.core.proj_apps_go, projAppsGo]
    lockstep_a2
    all_goals trace_state
    all_goals sorry

@[lockstep] theorem proj_apps_go_ls {pers st t us targs b n j lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxList a)
      (arena.core.proj_apps_go pers st t us targs b n j) lst
      (projAppsGo (absNIdx t) (absLsIdx us) (absEIdxList targs) (absEIdx b) (absU n) (absU j)) :=
  proj_apps_go_aux _ t us targs b n j hx rfl hrel hinv

@[lockstep] theorem eta_projs_ls {pers vis st fe lfe t us targs b n_f lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = absEIdxList a)
      (arena.core.eta_projs pers vis st fe t us targs b n_f) lst
      (etaProjs lfe (absNIdx t) (absLsIdx us) (absEIdxList targs) (absEIdx b) (absU n_f)) := by
  rw [arena.core.eta_projs, etaProjs]
  lockstep_a2
  all_goals trace_state
  all_goals sorry

end projs

end ConRon.Refine2.Lockstep
