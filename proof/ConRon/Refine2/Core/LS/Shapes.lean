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
import ConRon.Refine2.Core.LS.Leaves

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PA2

/-! ## Pure helpers -/

@[lockstep] theorem pw_written_ls (pw : kernel.prop_when.PropWhen) :
    LSP (arena.core.pw_written pw) (fun b => b = pwWritten (ConRon.Refine.absPropWhen pw)) := by
  intro b h
  rw [arena.core.pw_written] at h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [pwWritten, ← ConRon.Refine.PropWhen.is_never_refines hc, ← Result.ok_injective h]
  cases c <;> rfl

theorem annot_binder_meta_spec (pw : Option kernel.prop_when.PropWhen)
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

/-- `annot_binder_meta`'s answer is well formed when its inputs are: it is
either `mb` or `{ pw := p }` (a representation fact about the Rust inputs). -/
theorem annot_binder_meta_wf (pw : Option kernel.prop_when.PropWhen)
    (mb : kernel.expr.BinderMeta) :
    LSP (arena.core.annot_binder_meta pw mb)
      (fun m => ConRon.Refine.PropWhenWF mb.pw →
        (∀ p, pw = some p → ConRon.Refine.PropWhenWF p) → ConRon.Refine.PropWhenWF m.pw) := by
  intro r h hmb hpw
  unfold arena.core.annot_binder_meta at h
  cases pw with
  | none =>
    obtain rfl := ConRon.Refine.Expr.binder_meta_dup_eq h
    exact hmb
  | some p =>
    obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    split at h
    · obtain rfl := ConRon.Refine.Expr.binder_meta_dup_eq h
      exact hmb
    · rw [binder_meta_ls p r h]
      exact hpw p rfl

/-- `annot_binder_meta` in the `TwinEq` form the zip rewrites the twin with
(region G's statement): the twin's `annotBinderMeta` of the abstracted
arguments IS the abstraction of the port's answer; and the answer's datum is
well formed when the inputs' are. -/
@[lockstep] theorem annot_binder_meta_ls (pw : Option kernel.prop_when.PropWhen)
    (mb : kernel.expr.BinderMeta) :
    LSP (arena.core.annot_binder_meta pw mb)
      (fun m => TwinEq (annotBinderMeta (ExprOps.absPwOpt pw) (ConRon.Refine.absBinderMeta mb))
        (ConRon.Refine.absBinderMeta m) ∧
        (ConRon.Refine.PropWhenWF mb.pw →
          (∀ p, pw = some p → ConRon.Refine.PropWhenWF p) → ConRon.Refine.PropWhenWF m.pw)) :=
  fun r h => ⟨(annot_binder_meta_spec pw mb r h).symm, annot_binder_meta_wf pw mb r h⟩

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
  lockstep

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
    lockstep
  | succ m ih =>
    intro pers st lst fuel h k hn hrel hinv
    apply LSR.of_LS
    rw [arena.core.get_app_spine_go, getAppSpineGo]
    lockstep

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
  lockstep

/-! ## Straight-line state-threading helpers -/

section
attribute [local lockstep_inline] arena.core.intern_app

@[lockstep] theorem intern_app_rebuilt_ls {pers st h same f a lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.intern_app_rebuilt pers st h same f a) lst
      (internAppRebuilt (absEIdx h) same (absEIdx f) (absEIdx a)) := by
  rw [arena.core.intern_app_rebuilt, internAppRebuilt]
  lockstep

end

/-! ## Guards and small state-threading helpers -/

@[lockstep] theorem defeq_no_fvars_ls {pers st a b lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.defeq_no_fvars pers st a b) lst
      (defeqNoFvars (absEIdx a) (absEIdx b)) := by
  rw [arena.core.defeq_no_fvars, defeqNoFvars]
  lockstep

@[lockstep] theorem fab_scope_ok_ls {pers st depth fab major lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.fab_scope_ok pers st depth fab major) lst
      (fabScopeOk (absU depth) (absEIdx fab) (absEIdx major)) := by
  rw [arena.core.fab_scope_ok, fabScopeOk]
  lockstep

@[lockstep] theorem infer_lam_result_ls {pers st ty bt depth mb lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hmb : ConRon.Refine.PropWhenWF mb.pw) :
    LS pers (fun a b => b = absEIdx a) (arena.core.infer_lam_result pers st ty bt depth mb) lst
      (inferLamResult (absEIdx ty) (absEIdx bt) (absU depth) (ConRon.Refine.absBinderMeta mb)) := by
  rw [arena.core.infer_lam_result, inferLamResult]
  lockstep

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
  lockstep

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
    lockstep
  | succ k ih =>
    intro pers st lst e args i hx hn hrel hinv
    rw [arena.core.pi_residual, listFrom_cons args i (by omega), piResidual]
    lockstep

@[lockstep] theorem pi_residual_ls {pers st e args i lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = Option.map absEIdx a) (arena.core.pi_residual pers st e args i) lst
      (piResidual (absEIdx e) (absEIdxListFrom args i)) :=
  pi_residual_aux _ e args i hx rfl hrel hinv

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

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
    lockstep
  | succ m ih =>
    intro pers vis st fe lfe lst t nn j hn hrel hinv hctx
    rw [arena.core.tower_slots_all_go, towerSlotsAllGo]
    lockstep

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
  lockstep

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
    lockstep
  | succ m ih =>
    intro pers vis st fe lfe lst t nn j hn hrel hinv hctx
    rw [arena.core.rec_slots_all_go, recSlotsAllGo]
    lockstep

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
  lockstep

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
    lockstep
  | succ m ih =>
    intro pers st lst t b nn j hn hrel hinv
    rw [arena.core.proj_nodes_go, projNodesGo]
    lockstep

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
    lockstep
  | succ m ih =>
    intro pers st lst t us targs b nn j hx hn hrel hinv
    rw [arena.core.proj_apps_go, projAppsGo]
    lockstep

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
  lockstep

end projs

section rescue

theorem u64_val_beq_two (x : Std.U64) : (x.val == 2) = decide (x = 2#u64) := by
  by_cases h : x = 2#u64
  · subst h; rfl
  · have : x.val ≠ 2 := fun hc => h (UScalar.eq_of_val_eq (by rw [hc]; rfl))
    simp [h, this]

theorem u64_val_beq (x y : Std.U64) : (x.val == y.val) = decide (x = y) :=
  (decide_u64_eq x y).symm

attribute [local lockstep_simp] Option.map_none Option.map_some absIProjEntry u64_val_beq_two
  u64_val_beq

theorem and_rescue_slots_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {vis : Std.U64} {st : arena.monad.AState}
      {fe : arena.env.IFEnv} {lfe : IFEnv} {lst : AState}
      (an ctor : arena.handle.NIdx) (n_p : Std.U64) (ust : arena.handle.LsIdx) (nn j : Std.U64),
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      LS pers (fun a b => b = a)
        (arena.core.and_rescue_slots_go pers vis st fe an ctor n_p ust nn j) lst
        (andRescueSlotsGo lfe (absNIdx an) (absNIdx ctor) (absU n_p) (absLsIdx ust) n (absU j)) := by
  induction n with
  | zero =>
    intro pers vis st fe lfe lst an ctor n_p ust nn j hn hrel hinv hctx
    rw [arena.core.and_rescue_slots_go, andRescueSlotsGo]
    lockstep
  | succ m ih =>
    intro pers vis st fe lfe lst an ctor n_p ust nn j hn hrel hinv hctx
    rw [arena.core.and_rescue_slots_go, andRescueSlotsGo]
    lockstep

@[lockstep] theorem and_rescue_slots_go_ls {pers vis st fe lfe an ctor n_p ust n j lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a)
      (arena.core.and_rescue_slots_go pers vis st fe an ctor n_p ust n j) lst
      (andRescueSlotsGo lfe (absNIdx an) (absNIdx ctor) (absU n_p) (absLsIdx ust) (absU n)
        (absU j)) :=
  and_rescue_slots_go_aux _ an ctor n_p ust n j rfl hrel hinv hctx

@[lockstep] theorem and_rescue_slots_ls {pers vis st fe lfe ctor n_p ust lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a)
      (arena.core.and_rescue_slots pers vis st fe ctor n_p ust) lst
      (andRescueSlots lfe (absNIdx ctor) (absU n_p) (absLsIdx ust)) := by
  rw [arena.core.and_rescue_slots, andRescueSlots]
  lockstep

end rescue

/-! ## The telescope rebuilds -/

section tele

/-- `prop_when::beq` at a stack entry's datum (the ∀-membership form of the
`PropWhenWF` premise). -/
@[lockstep] theorem prop_when_beq_lam_stk_ls {l : List (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {i : Nat} {hi : i < l.length} {b : kernel.prop_when.PropWhen}
    (hl : ∀ x ∈ l, ConRon.Refine.PropWhenWF x.2.pw) (hb : ConRon.Refine.PropWhenWF b) :
    LSP (kernel.prop_when.beq (l[i]'hi).2.pw b)
      (fun c => c = (ConRon.Refine.absPropWhen (l[i]'hi).2.pw == ConRon.Refine.absPropWhen b)) :=
  PA2.prop_when_beq_ls (hl _ (List.getElem_mem hi)) hb

@[lockstep] theorem prop_when_beq_pi_stk_ls {l : List (arena.handle.LIdx × kernel.prop_when.PropWhen)}
    {i : Nat} {hi : i < l.length} {a : kernel.prop_when.PropWhen}
    (hl : ∀ x ∈ l, ConRon.Refine.PropWhenWF x.2) (ha : ConRon.Refine.PropWhenWF a) :
    LSP (kernel.prop_when.beq a (l[i]'hi).2)
      (fun c => c = (ConRon.Refine.absPropWhen a == ConRon.Refine.absPropWhen (l[i]'hi).2)) :=
  PA2.prop_when_beq_ls ha (hl _ (List.getElem_mem hi))

theorem getElem!_map_toArray {α β : Type} [Inhabited β] (f : α → β) {l : List α} {i : Nat}
    (hi : i < l.length) (k : Nat) (hk : k = i) : (l.map f).toArray[k]! = f l[i] := by
  subst hk
  simp [hi]

open Lean Meta Elab Tactic in
/-- The twin reads a stack by `stk[k]!` where the Rust reads `stk[i]` under a
bound `i < len`: rewrite the twin's read to the Rust's, `k = i` by `omega`. -/
elab "a2_idx" : tactic => withMainContext do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.isAppOfArity ``LT.lt 4 && (t.getArg! 3).isAppOfArity ``List.length 2 do continue
    let l := (t.getArg! 3).getArg! 1
    let i := t.getArg! 2
    let occ? := tgt.find? fun e =>
      e.isAppOf ``GetElem?.getElem! && e.getAppNumArgs ≥ 2 &&
        (let xs := e.getArg! (e.getAppNumArgs - 2)
         xs.isAppOfArity ``List.toArray 2 && (xs.getArg! 1).isAppOfArity ``List.map 4 &&
           (xs.getArg! 1).getArg! 3 == l)
    let some occ := occ? | continue
    let xs := occ.getArg! (occ.getAppNumArgs - 2)
    let f := (xs.getArg! 1).getArg! 2
    let k := occ.getArg! (occ.getAppNumArgs - 1)
    let hk ← mkFreshExprMVar (← mkEq k i)
    let rest ← runOn hk.mvarId! (evalT `(tactic| first
      | ((try simp only [lockstep_simp]); omega)
      | (simp only [lockstep_simp] at *; omega)))
    unless rest.isEmpty do throwError "a2_idx: index"
    let pf ← mkAppM ``getElem!_map_toArray #[f, d.toExpr, k, hk]
    let r ← g.rewrite tgt pf
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    setGoals (g' :: r.mvarIds ++ others)
    return
  throwError "a2_idx: no stack read"

attribute [local lockstep_simp] ConRon.Refine.absBinderMeta

/-- `lockstep` with the stack-read rewrite `a2_idx` FIRST: the tactic now splits
an undecided twin `if` (task #97-T2-TACTIC round 2), so the twin's `stk[k]!`
must be in the Rust's spelling before its test is reached. -/
macro "lockstep_a2_stk" : tactic =>
  `(tactic| repeat' (first | a2_idx | lockstep_step))

theorem infer_lams_out_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (mode : kernel.env.CheckMode) (d : Std.U64)
      (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
      (nn : Std.Usize) (cur : arena.handle.EIdx) (prev_pw : kernel.prop_when.PropWhen),
      ExprOpsHyp pers →
      (∀ x ∈ stk.val, ConRon.Refine.PropWhenWF x.2.pw) → ConRon.Refine.PropWhenWF prev_pw →
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_lams_out pers st mode d stk nn cur prev_pw) lst
        (inferLamsOut (ConRon.Refine.absMode mode) (absU d)
          (stk.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).toArray n
          (absEIdx cur) (ConRon.Refine.absPropWhen prev_pw)) := by
  induction n with
  | zero =>
    intro pers st lst mode d stk nn cur prev_pw hx hstk hpw hn hrel hinv
    rw [arena.core.infer_lams_out, inferLamsOut]
    lockstep_a2_stk
  | succ m ih =>
    intro pers st lst mode d stk nn cur prev_pw hx hstk hpw hn hrel hinv
    rw [arena.core.infer_lams_out, inferLamsOut]
    lockstep_a2_stk
    -- glue: the recursive call, whose datum premise is a stack entry's
    all_goals
      refine LS.tail (ih _ _ _ _ _ _ hx hstk (hstk _ (List.getElem_mem ‹_›))
        (by simp only [lockstep_simp] at *; omega) hrel hinv) ?_ (fun _ _ h => h)
      simp only [ConRon.Refine.absBinderMeta]
      congr 1

theorem infer_pis_out_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (mode : kernel.env.CheckMode)
      (stk : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen))
      (nn : Std.Usize) (v : arena.handle.LIdx) (pv : kernel.prop_when.PropWhen),
      (∀ x ∈ stk.val, ConRon.Refine.PropWhenWF x.2) → ConRon.Refine.PropWhenWF pv →
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absLIdx a)
        (arena.core.infer_pis_out pers st mode stk nn v pv) lst
        (inferPisOut (ConRon.Refine.absMode mode)
          (stk.val.map fun p => (absLIdx p.1, ConRon.Refine.absPropWhen p.2)).toArray n
          (absLIdx v) (ConRon.Refine.absPropWhen pv)) := by
  induction n with
  | zero =>
    intro pers st lst mode stk nn v pv hstk hpw hn hrel hinv
    rw [arena.core.infer_pis_out, inferPisOut]
    lockstep_a2_stk
  | succ m ih =>
    intro pers st lst mode stk nn v pv hstk hpw hn hrel hinv
    rw [arena.core.infer_pis_out, inferPisOut]
    lockstep_a2_stk

@[lockstep] theorem infer_lams_out_ls {pers st mode d stk n cur prev_pw lst}
    (hx : ExprOpsHyp pers)
    (hstk : ∀ x ∈ stk.val, ConRon.Refine.PropWhenWF x.2.pw)
    (hpw : ConRon.Refine.PropWhenWF prev_pw)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_lams_out pers st mode d stk n cur prev_pw) lst
      (inferLamsOut (ConRon.Refine.absMode mode) (absU d)
        (stk.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).toArray (absSz n)
        (absEIdx cur) (ConRon.Refine.absPropWhen prev_pw)) :=
  infer_lams_out_aux _ mode d stk n cur prev_pw hx hstk hpw rfl hrel hinv

@[lockstep] theorem infer_pis_out_ls {pers st mode stk n v pv lst}
    (hstk : ∀ x ∈ stk.val, ConRon.Refine.PropWhenWF x.2)
    (hpw : ConRon.Refine.PropWhenWF pv)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdx a)
      (arena.core.infer_pis_out pers st mode stk n v pv) lst
      (inferPisOut (ConRon.Refine.absMode mode)
        (stk.val.map fun p => (absLIdx p.1, ConRon.Refine.absPropWhen p.2)).toArray (absSz n)
        (absLIdx v) (ConRon.Refine.absPropWhen pv)) :=
  infer_pis_out_aux _ mode stk n v pv hstk hpw rfl hrel hinv

end tele

/-! ## The axiom census -/

#print axioms get_app_spine_ls
#print axioms head_and_args_ls
#print axioms intern_app_rebuilt_ls
#print axioms defeq_peel_done_ls
#print axioms pw_written_ls
#print axioms annot_binder_meta_ls
#print axioms annot_binder_meta_spec
#print axioms annot_binder_meta_wf
#print axioms whnf_core_stuck_tag_ls
#print axioms defeq_no_fvars_ls
#print axioms fab_scope_ok_ls
#print axioms infer_lam_result_ls
#print axioms eta_ctor_shape_ls
#print axioms pi_residual_ls
#print axioms tower_slots_all_ls
#print axioms rec_slots_all_ls
#print axioms eta_projs_ls
#print axioms and_rescue_slots_ls
#print axioms infer_lams_out_ls
#print axioms infer_pis_out_ls

end ConRon.Refine2.Lockstep
