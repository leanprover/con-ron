/-
# `ConRon.Bridge.Core.Arms.WhnfCore` — Theorem 1 for `whnfCoreBody`

DESIGN §8.2, task #97s's **rule 8**: one step lemma per exit of the PURE
function.  The twin's `whnfCoreBody` is (con-leche's task #342 R2) the
CACHED tier's loop (`Cached/CoreC.lean whnfCoreStepI` / `whnfCoreLoopI`):
`whnfCoreStep` RETURNS the term to continue with (`WhnfStep.cont`) and
`whnfCoreLoop` iterates it on its own step budget, under official
`whnf_core`'s memo policy (con-leche's task #572).  con-leche's pure mirror of
a step is `Verify/BetaSpine.lean`'s `whnfCoreStepW`, and
`whnfCore_of_stepW_cont` / `_done` carry a step's outcome to the chained
`whnfCore` at some knot fuel.  So:

| piece | twin | pure side |
|---|---|---|
| one step | `whnfCoreStep` | `whnfCoreStepW` at `pureFns .verified eager env F` (`whnfCoreStep_spec`) |
| the stuck arm | `whnfStuck` | the `.app` exit, read by `whnfAppW_stuck` (`whnfStuck_spec`) |
| the loop | `whnfCoreLoop` | `whnfCore` itself (`whnfCoreLoop_spec`, induction on the budget; the memo policy's pending keys are `PendH`) |
| the body | `whnfCoreBody` | `whnfCore` (`whnfCoreBody_spec`) |

The step's exits: the six values are `.done` themselves; `.app` is the
batched spine (`Walks/BetaSpine.lean`'s `whnfApp_carry`); `.proj` is the
scrutinee's reduction then `reduceProjCore` (fired field `.cont`, stuck node
`.done`); `.letE` is ζ (`.cont`, con-leche's task #342 S0); `.bvar` throws.
-/
module

import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.ProjCore
public import ConRon.Bridge.Core.Walks.BetaSpine
import ConRon.Bridge.Core.Walks.Spine
public import ConLeche.Verify.Cached.DiscC4
import ConRon.Bridge.Core.Walks.Iota
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool} {env : Env} {fe : IFEnv}

/-! ## 1. The scrutinee of the `.proj` exit -/

/-- con-leche: ConLeche/Kernel/Core.lean:967 whnfCoreBody — the
scrutinee's reduction, in the clause's mode, at the pure knot. -/
abbrev projScrut (mode : CheckMode) (eager : Bool) (env : Env) (c : Bool) (F d : Nat)
    (pe : Expr) : CheckM Expr :=
  if c then ConLeche.whnfCore mode eager env F d pe true
  else ConLeche.whnf mode eager env F d pe

/-- con-leche: ConLeche/Verify/Mono.lean:120 whnfCore_mono — the scrutinee's
reduction is fuel-monotone in either mode. -/
theorem projScrut_mono {c : Bool} {F F' d : Nat} {pe r : Expr} (hle : F ≤ F')
    (h : projScrut mode eager env c F d pe = .ok r) :
    projScrut mode eager env c F' d pe = .ok r := by
  cases c
  · exact ConLeche.whnf_mono hle h
  · exact ConLeche.whnfCore_mono hle h

/-! ## 2. The pure step at its exits -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:328 whnfCoreStepW — at the pure
knot. -/
abbrev mStep (mode : CheckMode) (eager : Bool) (env : Env) (c : Bool) (F d : Nat) (e : Expr) :
    CheckM ConLeche.WhnfStep :=
  ConLeche.whnfCoreStepW mode (ConLeche.pureFns mode eager env F) env c d e

/-- con-leche: ConLeche/Verify/BetaSpine.lean:458 whnfCoreStepW_atF — fuel
monotonicity of the step. -/
theorem mStep_mono {c : Bool} {F F' d : Nat} {e : Expr} {r : ConLeche.WhnfStep}
    (hle : F ≤ F') (h : mStep mode eager env c F d e = .ok r) :
    mStep mode eager env c F' d e = .ok r := by
  simp only [mStep] at h ⊢
  rw [← ConLeche.whnfCoreStepW_atF] at h ⊢
  exact (ConLeche.whnfCoreStepW mode (ConLeche.fueledFns mode eager env) env c d
    e).property hle h

/-- con-leche: ConLeche/Verify/BetaSpine.lean:328 whnfCoreStepW — the `.app`
exit: the spine head's normal form, then the batched walk. -/
theorem mStep_app {c : Bool} {F d : Nat} {f a V : Expr} {r : ConLeche.WhnfStep}
    (hv : ConLeche.whnfCore mode eager env F d (Expr.app f a).getAppFn c = .ok V)
    (hw : mWA mode eager env F d V (Expr.app f a).getAppArgs = .ok r) :
    mStep mode eager env c F d (.app f a) = .ok r := by
  have hv' : (ConLeche.pureFns mode eager env F).whnfCore c d (Expr.app f a).getAppFn
      = .ok V := hv
  simp only [mStep, ConLeche.whnfCoreStepW, hv', bind, Except.bind]
  exact hw

/-- con-leche: ConLeche/Verify/BetaSpine.lean:328 whnfCoreStepW — the `.proj`
exit, the rule does not fire: the node itself, done (con-leche's task #323:
its scrutinee as it was). -/
theorem mStep_proj_none {c : Bool} {F d i : Nat} {sn : Name} {pe c' : Expr}
    (hs : projScrut mode eager env c F d pe = .ok c')
    (hr : ConLeche.reduceProjCoreFueled mode eager env F d sn i c' = .ok none) :
    mStep mode eager env c F d (.proj sn i pe) = .ok (.done (.proj sn i pe)) := by
  simp only [ConLeche.reduceProjCoreFueled] at hr
  cases c <;>
    simp only [projScrut, ite_true, Bool.false_eq_true, ite_false] at hs <;>
    simp only [mStep, ConLeche.whnfCoreStepW, ConLeche.whnf_def,
      ConLeche.whnfCore_def, ite_true, Bool.false_eq_true, ite_false, hs, hr,
      bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:328 whnfCoreStepW — the `.proj`
exit, the rule fires: the selected field is the term to continue with. -/
theorem mStep_proj_some {c : Bool} {F d i : Nat} {sn : Name} {pe c' m : Expr}
    (hs : projScrut mode eager env c F d pe = .ok c')
    (hr : ConLeche.reduceProjCoreFueled mode eager env F d sn i c' = .ok (some m)) :
    mStep mode eager env c F d (.proj sn i pe) = .ok (.cont m) := by
  simp only [ConLeche.reduceProjCoreFueled] at hr
  cases c <;>
    simp only [projScrut, ite_true, Bool.false_eq_true, ite_false] at hs <;>
    simp only [mStep, ConLeche.whnfCoreStepW, ConLeche.whnf_def,
      ConLeche.whnfCore_def, ite_true, Bool.false_eq_true, ite_false, hs, hr,
      bind, Except.bind, pure, Except.pure]

/-! ## 2b. The stuck spine (con-leche's task #556 P-A, #577)

A spine whose head is its own head normal form and not a λ is answered by
`whnfStuck`: the ι step once, at the head's target prefix, and otherwise the
input.  The mirror's `.app` exit normalizes the head (to itself) and runs
`whnfAppW` over the arguments; con-leche's `whnfAppW_stuck`
(`Verify/Cached/DiscC4.lean`) reads that loop the stuck arm's way. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:180-184 isStuckHeadC — the twin's
tag test reads the kind of the denoted head. -/
theorem isStuckHeadC_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {H : Expr}
    (hd : denoteE st h = some H) (ht : isStuckHead h = true) :
    ConLeche.Cached.isStuckHeadC H = true := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  have htag := EStore.tagOf_of_view hv
  simp only [isStuckHead] at ht
  cases v with
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hd; rfl
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hd; rfl
  | const n us => obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hd; rfl
  | forallE ty b => obtain ⟨et, eb, rfl, _, _⟩ := denote_forallE_inv hwf hv hd; rfl
  | lit l => rw [denote_lit_inv hwf hv hd]; rfl
  | bvar i => rw [htag] at ht; simp [ENodeView.tagOf, ETag.bvar, ETag.sort, ETag.fvar,
      ETag.forallE, ETag.const, ETag.lit] at ht
  | app f a => rw [htag] at ht; simp [ENodeView.tagOf, ETag.app, ETag.sort, ETag.fvar,
      ETag.forallE, ETag.const, ETag.lit] at ht
  | lam ty b => rw [htag] at ht; simp [ENodeView.tagOf, ETag.lam, ETag.sort, ETag.fvar,
      ETag.forallE, ETag.const, ETag.lit] at ht
  | letE ty w b => rw [htag] at ht; simp [ENodeView.tagOf, ETag.letE, ETag.sort, ETag.fvar,
      ETag.forallE, ETag.const, ETag.lit] at ht
  | proj n i sub => rw [htag] at ht; simp [ENodeView.tagOf, ETag.proj, ETag.sort, ETag.fvar,
      ETag.forallE, ETag.const, ETag.lit] at ht

/-- con-leche: ConLeche/Cached/CoreC.lean:186-198 iotaTargetF — **THEOREM 1
for `iotaTarget`**: read-only, and the answer is con-leche's target of the
denoted head. -/
theorem iotaTarget_spec (s₀ : AState) (h : EIdx) (H : Expr)
    (hok : CheckOK eager env fe s₀) (hd : denoteE s₀.store h = some H) :
    ⦃fun s => s = s₀⦄ iotaTarget fe h
    ⦃fun o s' => s' = s₀ ∧ o = ConLeche.Cached.iotaTargetF (ConLeche.mkFEnv env) H; ⊤⦄ := by
  have hwf := hok.state.wf
  unfold iotaTarget
  by_cases htag : (h.tag == ETag.const) = true
  · rw [ite_eq_left htag]
    refine triple_seq (viewConst_spec s₀ h) ?_
    rintro oc s1 ⟨hs1, hoc⟩
    subst s1
    cases oc with
    | none => exact triple_failDanglingE
    | some cu =>
      obtain ⟨c, us⟩ := cu
      have hv := view_of_viewConst_tag htag hoc.symm
      obtain ⟨cn, ls, rfl, hcn, hls⟩ := denote_const_inv hwf hv hd
      dsimp only
      split
      next icv mI rP isK rules hfc =>
        obtain ⟨dcv, drules, hdcv, hdr, hfind⟩ := env_rec_of_index hok hcn hfc
        obtain ⟨_, hlps, _⟩ := denoteCV_inv hdcv
        have hlenlps := denoteNList_len hlps
        refine triple_seq (viewLsLen_spec s₀ us) ?_
        rintro ol s2 ⟨hs2, hol⟩
        subst s2
        rw [viewLen_of_denoteLs hls] at hol
        subst hol
        dsimp only
        have htgt : ConLeche.Cached.iotaTargetF (ConLeche.mkFEnv env) (.const cn ls) =
            if ls.length = dcv.levelParams.length then some (mI + 1) else none := by
          simp [ConLeche.Cached.iotaTargetF, ConLeche.mkFEnv_find?, hfind]
        rw [htgt, ← hlenlps]
        split <;> vcgen <;> subst_vars <;> simp_all
      next hnot =>
        have hnr := env_not_rec_of_index hok hcn hnot
        vcgen
        subst_vars
        refine ⟨rfl, ?_⟩
        simp only [ConLeche.Cached.iotaTargetF, ConLeche.mkFEnv_find?]
        all_goals
          split <;> first
            | rfl
            | (rename_i cv mI rP isK rules hf; exact absurd hf (hnr cv mI rP isK rules))
  · rw [ite_eq_right htag]
    vcgen
    subst_vars
    refine ⟨rfl, ?_⟩
    obtain ⟨w, hw⟩ := denoteE_view hd
    have hnc := denote_not_const hwf hw hd (by
      intro c us hcu; subst hcu
      exact htag (by rw [EStore.tagOf_of_view hw]; rfl))
    unfold ConLeche.Cached.iotaTargetF
    split
    · next c us => exact absurd rfl (hnc c us)
    · rfl

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfAppW_stuck — **the
spine loop at a stuck head**, at the pure knot: the ι step at its target
prefix, and otherwise the spine itself. -/
theorem mWA_stuck {F d : Nat} {H : Expr} (hh : ConLeche.Cached.isStuckHeadC H = true)
    (L : List Expr) :
    mWA .verified eager env F d H L =
      match ConLeche.Cached.iotaTargetF (ConLeche.mkFEnv env) H with
      | some k =>
        if k ≤ L.length then
          ConLeche.iotaRecFueled .verified eager env F d (Expr.mkAppN H (L.take k)) >>=
            fun o => (ConLeche.Cached.whnfStuckTail H L k o).val F
        else .ok (.done (Expr.mkAppN H L))
      | none => .ok (.done (Expr.mkAppN H L)) := by
  simp only [mWA]
  rw [← ConLeche.whnfAppW_atF, ConLeche.Cached.whnfAppW_stuck hh]
  cases ConLeche.Cached.iotaTargetF (ConLeche.mkFEnv env) H with
  | none => rfl
  | some k =>
    dsimp only
    split
    · simp only [ConLeche.FueledM.atF_bind, ConLeche.iotaRec_atF]
    · rfl

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean Runs.whnfCore_stuckHead —
the mirror's `.app` exit at a stuck head: the head is its own head normal
form, and the spine loop runs on it. -/
theorem mStep_stuck {c : Bool} {F d : Nat} {f a : Expr}
    (hh : ConLeche.Cached.isStuckHeadC (Expr.app f a).getAppFn = true) :
    mStep .verified eager env c (F + 1) d (.app f a) =
      mWA .verified eager env (F + 1) d (Expr.app f a).getAppFn (Expr.app f a).getAppArgs := by
  have hv : ConLeche.whnfCore .verified eager env (F + 1) d (Expr.app f a).getAppFn c
      = .ok (Expr.app f a).getAppFn := by
    apply whnfCore_of_stuck
    revert hh
    cases (Expr.app f a).getAppFn <;> intro hh <;>
      first
        | (simp; done)
        | exact nomatch hh
  have hv' : (ConLeche.pureFns .verified eager env (F + 1)).whnfCore c d
      (Expr.app f a).getAppFn = .ok (Expr.app f a).getAppFn := hv
  simp only [mStep, ConLeche.whnfCoreStepW, hv', bind, Except.bind]

/-- con-leche: none — `iotaRecAt` reads its argument vector only through the
prefix it fires at. -/
theorem iotaRecAt_take (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (hd : EIdx) (sargs : Array EIdx) (n : Nat) :
    iotaRecAt mode r fe depth hd sargs n = iotaRecAt mode r fe depth hd (takeEidx sargs n) n := by
  have hcopy : takeEidx (takeEidx sargs n) n = takeEidx sargs n := by
    apply Array.toList_inj.mp
    simp [ExprOps.takeEidx_toList, List.take_take]
  unfold iotaRecAt
  rw [hcopy]

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfStuckC_spec —
**THEOREM 1 for `whnfStuck`**: the stuck arm denotes the mirror's `.app`
exit at some fuel. -/
theorem whnfStuck_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (c : Bool)
    (s₀ : AState) (d : Nat) (h i : EIdx) (f a : Expr)
    (hok : CheckOK eager env fe s₀) (hden : denoteE s₀.store i = some (.app f a))
    (hdh : denoteE s₀.store h = some (Expr.app f a).getAppFn)
    (hh : ConLeche.Cached.isStuckHeadC (Expr.app f a).getAppFn = true)
    (hw : Expr.WScoped d (.app f a)) :
    ⦃fun s => s = s₀⦄
      whnfStuck .verified (coreKnot .verified eager fe id fuel) fe d h i
    ⦃fun r s' => StepPost eager env fe d s₀
        (fun F => mStep .verified eager env c F d (.app f a)) r s'; ⊤⦄ := by
  have hwf := hok.state.wf
  have hmk : Expr.mkAppN (Expr.app f a).getAppFn (Expr.app f a).getAppArgs = .app f a :=
    Expr.mkAppN_getApp _
  have hwL : ∀ x ∈ (Expr.app f a).getAppArgs, Expr.WScoped d x := Expr.WScoped.getAppArgs hw
  have hwH : Expr.WScoped d (Expr.app f a).getAppFn := Expr.WScoped.getAppFn hw
  have hnapp : ∀ g b, (Expr.app f a).getAppFn ≠ .app g b := getAppFn_not_app _
  unfold whnfStuck
  refine triple_seq (iotaTarget_spec s₀ h _ hok hdh) ?_
  rintro o s1 ⟨hs1, ho⟩
  subst s1
  -- the input itself, done
  have hdone : ∀ (P : Prop), (mWA .verified eager env (0 + 1) d (Expr.app f a).getAppFn
      (Expr.app f a).getAppArgs = .ok (.done (.app f a))) →
      StepPost eager env fe d s₀ (fun F => mStep .verified eager env c F d (.app f a))
        (.done i) s₀ := by
    intro _ hm
    exact ⟨hok, Ext.refl _, rfl, .done (.app f a), by simp [denoteStep, hden], hw, 0 + 1,
      by show mStep .verified eager env c (0 + 1) d (.app f a) = _
         rw [mStep_stuck hh]; exact hm⟩
  cases o with
  | none =>
    vcgen
    subst_vars
    refine hdone True ?_
    show mWA .verified eager env (0 + 1) d (Expr.app f a).getAppFn (Expr.app f a).getAppArgs = _
    rw [mWA_stuck hh, ← ho, hmk]
  | some k =>
    dsimp only
    refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ i hok.state
      (by rw [hden]; rfl)) ?_
    rintro as s2 ⟨hs2, has⟩
    subst s2
    have hdas := has _ hden
    have hlen : (Expr.app f a).getAppArgs.length = as.length := denoteEList_len hdas
    by_cases hk : k ≤ as.toArray.size
    · rw [ite_eq_left hk, iotaRecAt_take]
      have hks : (takeEidx as.toArray k).size = k := by
        have := congrArg List.length (ExprOps.takeEidx_toList as.toArray k)
        simp only [Array.length_toList, List.length_take] at this
        simp at hk
        rw [this]; omega
      have hdk : Frontend.denoteEList s₀.store (takeEidx as.toArray k).toList =
          some ((Expr.app f a).getAppArgs.take k) := by
        rw [ExprOps.takeEidx_toList, List.toList_toArray]
        exact ExprOps.denoteEList_take k _ _ hdas
      have hwk : Expr.WScoped d (Expr.mkAppN (Expr.app f a).getAppFn
          ((Expr.app f a).getAppArgs.take k)) :=
        Expr.WScoped.mkAppN hwH (fun x hx => hwL x (List.mem_of_mem_take hx))
      refine triple_seq (iotaRecAt_spec henv hsim s₀ d h (takeEidx as.toArray k) k
        _ _ hok hdh hnapp hks.symm hdk hwk) ?_
      rintro step s3 ⟨hok3, hx3, hp3, ov, hov, hwov, F1, hF1⟩
      have hkL : k ≤ (Expr.app f a).getAppArgs.length := by
        rw [hlen]; simpa using hk
      cases step with
      | none =>
        simp only [denoteEO, Option.some.injEq] at hov
        subst hov
        vcgen
        subst_vars
        refine ⟨hok3, hx3, hp3, .done (.app f a), by simp [denoteStep, denote_ext hden hx3],
          hw, F1 + 1, ?_⟩
        show mStep .verified eager env c (F1 + 1) d (.app f a) = _
        rw [mStep_stuck hh, mWA_stuck hh, ← ho]
        dsimp only
        rw [ite_eq_left hkL, show ConLeche.iotaRecFueled .verified eager env (F1 + 1) d _ = _ from
          ConLeche.iotaRec_mono (Nat.le_succ F1) hF1]
        simp only [bind, Except.bind, ConLeche.Cached.whnfStuckTail, hmk]
        rfl
      | some e2 =>
        simp only [denoteEO, Option.map_eq_some_iff] at hov
        obtain ⟨E2, hdE2, rfl⟩ := hov
        have hwE2 := hwov E2 rfl
        dsimp only
        have hrest : Frontend.denoteEList s3.store (as.toArray.toList.drop k) =
            some ((Expr.app f a).getAppArgs.drop k) := by
          rw [List.toList_toArray]
          exact denoteEList_ext' hx3 (ExprOps.denoteEList_drop k _ _ hdas)
        refine triple_seq (ExprOps.mkAppNFrom_spec _ s3 e2 as.toArray k rfl
          hok3.state (by rw [hdE2]; rfl) (by rw [hrest]; rfl)) ?_
        rintro r s4 ⟨hst4, hx4, _, hc4, hp4, hrel⟩
        have hpost : StepPost eager env fe d s₀
            (fun F => mStep .verified eager env c F d (.app f a)) (.cont r) s4 := by
          refine ⟨hok3.mono hst4 hx4 hc4 hp4, hx3.trans hx4, by rw [hp4, hp3],
            .cont (Expr.mkAppN E2 ((Expr.app f a).getAppArgs.drop k)),
            by simp [denoteStep, hrel _ _ hdE2 hrest],
            Expr.WScoped.mkAppN hwE2 (fun x hx => hwL x (List.mem_of_mem_drop hx)),
            F1 + 1, ?_⟩
          show mStep .verified eager env c (F1 + 1) d (.app f a) = _
          rw [mStep_stuck hh, mWA_stuck hh, ← ho]
          dsimp only
          rw [ite_eq_left hkL, show ConLeche.iotaRecFueled .verified eager env (F1 + 1) d _ = _ from
            ConLeche.iotaRec_mono (Nat.le_succ F1) hF1]
          rfl
        vcgen
        subst_vars
        exact hpost
    · rw [ite_eq_right hk]
      vcgen
      subst_vars
      refine hdone True ?_
      have hkL : ¬ k ≤ (Expr.app f a).getAppArgs.length := by
        rw [hlen]; simpa using hk
      show mWA .verified eager env (0 + 1) d (Expr.app f a).getAppFn (Expr.app f a).getAppArgs = _
      rw [mWA_stuck hh, ← ho]
      dsimp only
      rw [ite_eq_right hkL, hmk]

/-! ## 3. Theorem 1 for one step -/

/-- con-leche: ConLeche/Cached/CoreC.lean:768-804 whnfCoreStepI —
**THEOREM 1 for `whnfCoreStep`**: the twin's step denotes the mirror's
outcome at some fuel. -/
theorem whnfCoreStep_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (c : Bool)
    (s₀ : AState) (d : Nat) (h i : EIdx) (e : Expr)
    (hok : CheckOK eager env fe s₀) (hden : denoteE s₀.store i = some e)
    (hdh : denoteE s₀.store h = some e.getAppFn)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄
      whnfCoreStep .verified (coreKnot .verified eager fe id fuel) fe c d h i
    ⦃fun r s' => StepPost eager env fe d s₀ (fun F => mStep .verified eager env c F d e)
        r s'; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  unfold whnfCoreStep
  refine view_bind_triple hv ?_
  -- a value answers itself
  have hval : ∀ (e0 : Expr), e = e0 →
      mStep .verified eager env c 0 d e0 = .ok (.done e0) →
      ⦃fun s => s = s₀⦄ (pure (ConRon.Arena.WhnfStep.done i) : AM _)
      ⦃fun r s' => StepPost eager env fe d s₀ (fun F => mStep .verified eager env c F d e)
          r s'; ⊤⦄ := by
    intro e0 he0 hst
    subst he0
    vcgen
    subst_vars
    exact ⟨hok, Ext.refl _, rfl, .done e, by simp [denoteStep, hden], hw, 0, hst⟩
  cases v with
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hden
    exact hval _ rfl rfl
  | sort u =>
    obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hden
    exact hval _ rfl rfl
  | const n us =>
    obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hden
    exact hval _ rfl rfl
  | lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    exact hval _ rfl rfl
  | lam ty b =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_lam_inv hwf hv hden
    exact hval _ rfl rfl
  | forallE ty b =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_forallE_inv hwf hv hden
    exact hval _ rfl rfl
  | bvar k => exact triple_fail
  | letE ty w b =>
    obtain ⟨et, ew, eb, rfl, _, hdw, hdb⟩ := denote_letE_inv hwf hv hden
    have hws : Expr.WScoped d ew ∧ Expr.WScoped d eb := by
      simp only [Expr.WScoped] at hw; exact ⟨hw.2.1, hw.2.2⟩
    dsimp only
    refine triple_seq (instantiate1Fast_ok_spec s₀ b w eb ew hok hdb hdw) ?_
    rintro e' s1 ⟨hok1, hx1, hp1, hde'⟩
    vcgen
    subst_vars
    exact ⟨hok1, hx1, hp1, .cont (eb.instantiate1 ew),
      by simp [denoteStep, hde'],
      Expr.WScoped.instantiate1_gen hws.1 0 hws.2, 0, rfl⟩
  | proj sn k pe =>
    obtain ⟨nm, es, rfl, hsn, hpe⟩ := denote_proj_inv hwf hv hden
    have hwes : Expr.WScoped d es := by simpa [Expr.WScoped] using hw
    dsimp only
    unfold whnfCoreStepProj
    have h1 : ⦃fun s => s = s₀⦄
        (if c then (coreKnot .verified eager fe id fuel).whnfCore true d pe
          else (coreKnot .verified eager fe id fuel).whnf d pe)
        ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
            s'.pins = s₀.pins ∧
            SimEOp (fun F => projScrut .verified eager env c F d es) d s'.store r; ⊤⦄ := by
      cases c
      · simp only [Bool.false_eq_true, ite_false]
        exact hsim.whnf s₀ d pe es hok hpe hwes
      · simp only [ite_true]
        exact hsim.whnfCore s₀ d pe es hok hpe hwes
    rw [ite_bind_fold]
    refine triple_seq h1 ?_
    rintro e0 s1 ⟨hok1, hx1, hp1, v0, hv0, hwv0, F1, hF1⟩
    refine triple_seq (reduceProjCore_spec henv hsim s1 d sn k e0 nm v0 hok1
      (denoteN_ext hsn hx1) hv0 hwv0) ?_
    rintro o s2 ⟨hok2, hx2, hp2, ov, hov, hwov, F2, hF2⟩
    have hx02 : Ext s₀.store s2.store := hx1.trans hx2
    have hp02 : s2.pins = s₀.pins := hp2.trans hp1
    have hs' := projScrut_mono (Nat.le_max_left F1 F2) hF1
    have hr' := ConLeche.reduceProjCore_mono (env := env) (mi := .verified)
      (Nat.le_max_right F1 F2) hF2
    cases o with
    | none =>
      simp only [denoteEO, Option.some.injEq] at hov
      subst hov
      vcgen
      subst_vars
      exact ⟨hok2, hx02, hp02, .done (.proj nm k es),
        by simp [denoteStep, denote_ext hden hx02], hw, max F1 F2,
        mStep_proj_none hs' hr'⟩
    | some m =>
      simp only [denoteEO, Option.map_eq_some_iff] at hov
      obtain ⟨M, hdM, rfl⟩ := hov
      vcgen
      subst_vars
      exact ⟨hok2, hx02, hp02, .cont M, by simp [denoteStep, hdM], hwov M rfl,
        max F1 F2, mStep_proj_some hs' hr'⟩
  | app f a =>
    dsimp only
    obtain ⟨ef, ea, rfl, _, _⟩ := denote_app_inv hwf hv hden
    -- the spine head, read by the loop
    by_cases hst : isStuckHead h = true
    · rw [ite_eq_left hst]
      exact whnfStuck_spec henv hsim c s₀ d h i ef ea hok hden hdh
        (isStuckHeadC_of_tag hwf hdh hst) hw
    rw [ite_eq_right hst]
    unfold whnfCoreStepApp
    -- the spine, in one read
    refine triple_seq (getAppSpine_spec coreWalkFuel s₀ i _ hok.state hden) ?_
    rintro sp s1 ⟨hs1, hsp1, hsp2, hsp3, hsp4⟩
    subst s1
    -- the head's normal form
    refine triple_seq (hsim.whnfCore s₀ d sp.1 _ hok hsp1
      (Expr.WScoped.getAppFn hw)) ?_
    rintro vh s2 ⟨hok2, hx2, hp2, Vh, hdv, hwv, F0, hF0⟩
    -- the reduct's own spine
    refine triple_seq (headAndArgs_spec s2 vh Vh hok2.state hdv) ?_
    rintro hv' s3 ⟨hs3, hh1, hh2⟩
    subst s3
    have hctx : SpineCtx d sp.2.1 sp.2.2 (Expr.app ef ea).getAppFn (Expr.app ef ea).getAppArgs s2.store :=
      ⟨denoteEList_ext' hx2 hsp2, Expr.WScoped.getAppArgs hw, hsp3,
        fun j hj => denote_ext (hsp4 j hj) hx2⟩
    have hsame : (vh == sp.1) = true →
        Vh = Expr.mkAppN (Expr.app ef ea).getAppFn ((Expr.app ef ea).getAppArgs.take 0) := by
      intro hb
      have heq : vh = sp.1 := beq_iff_eq.mp hb
      rw [heq, denote_ext hsp1 hx2] at hdv
      simpa [Expr.mkAppN] using (Option.some.inj hdv).symm
    refine triple_mono (whnfApp_carry henv hsim d sp.2.1 sp.2.2
      (Expr.app ef ea).getAppFn (Expr.app ef ea).getAppArgs _ vh hv'.1 hv'.2
      (vh == sp.1) 0 s2 Vh rfl hok2 hctx hdv hwv hh1 hh2 hsame) ?_
    rintro r s' ⟨hck, hx, hp, R, hdR, hwR, F, hF⟩
    refine ⟨hck, hx2.trans hx, by rw [hp, hp2], R, hdR, hwR, max F0 F, ?_⟩
    exact mStep_app (ConLeche.whnfCore_mono (Nat.le_max_left _ _) hF0)
      (mWA_mono (Nat.le_max_right _ _) (by simpa using hF))

/-! ## 4. The loop and its memo policy (con-leche's task #572)

The loop looks every key up in the mode's memo, and stores the keys of a
chain at its end; its answer is stated against the chained `whnfCore`
directly (con-leche's `whnfCoreLoopC_spec`).  A continuing step carries the
answer back (`whnfCore_of_mStep_cont`, con-leche's `whnfCore_of_stepW_cont`),
an answering one is the answer (`whnfCore_of_mStep_done`), a hit is the
cache invariant's row.  The keys waiting for the answer satisfy `PendH`:
each answers what the current term answers (con-leche's `PendOK`). -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean whnfCore_of_stepW_cont — a
continuing step: the term answers what its continuation answers. -/
theorem whnfCore_of_mStep_cont {c : Bool} {d F G : Nat} {E E' V : Expr}
    (hs : mStep .verified eager env c F d E = .ok (.cont E'))
    (hk : ConLeche.whnfCore .verified eager env G d E' c = .ok V) :
    ∃ M, ConLeche.whnfCore .verified eager env M d E c = .ok V :=
  ConLeche.whnfCore_of_stepW_cont (by rw [ConLeche.whnfCoreStepW_atF]; exact hs) hk

/-- con-leche: ConLeche/Verify/BetaSpine.lean whnfCore_of_stepW_done — an
answering step: its answer is the term's. -/
theorem whnfCore_of_mStep_done {c : Bool} {d F : Nat} {E V : Expr}
    (hs : mStep .verified eager env c F d E = .ok (.done V)) :
    ∃ M, ConLeche.whnfCore .verified eager env M d E c = .ok V :=
  ConLeche.whnfCore_of_stepW_done (by rw [ConLeche.whnfCoreStepW_atF]; exact hs)

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfCoreStepW_cheap — a
step the two modes take alike is the same step in the cheap mode. -/
theorem mStep_cheap {c : Bool} {F d : Nat} {E : Expr}
    (h : ConLeche.Cached.whnfCoreCheapSafeC E.getAppFn E = true) :
    mStep .verified eager env true F d E = mStep .verified eager env c F d E := by
  simp only [mStep]
  rw [← ConLeche.whnfCoreStepW_atF, ← ConLeche.whnfCoreStepW_atF,
    ConLeche.Cached.whnfCoreStepW_cheap h]

/-- con-leche: ConLeche/Cached/CoreC.lean:275-282 whnfCoreCheapSafeC — the
twin's tag test reads the denoted step's kind. -/
theorem whnfCoreCheapSafeC_of_tag {st : EStore} (hwf : StoreWF st) {h i : EIdx} {E : Expr}
    (hd : denoteE st i = some E) (hh : denoteE st h = some E.getAppFn)
    (hs : whnfCoreCheapSafe h i = true) :
    ConLeche.Cached.whnfCoreCheapSafeC E.getAppFn E = true := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  have htag := EStore.tagOf_of_view hv
  simp only [whnfCoreCheapSafe] at hs
  cases v with
  | app f a =>
    obtain ⟨ef, ea, rfl, _, _⟩ := denote_app_inv hwf hv hd
    rw [htag] at hs
    simp only [ENodeView.tagOf, ETag.app] at hs
    simp only [ConLeche.Cached.whnfCoreCheapSafeC]
    by_cases hl : (h.tag == ETag.lam) = true
    · obtain ⟨_, _, Ty, Body, _, hlam, _, _⟩ := viewBind_of_lam_tag hwf (by simpa using hl) hh
      rw [hlam]
    · rw [ite_eq_right hl] at hs
      have hst := isStuckHeadC_of_tag hwf hh hs
      revert hst
      cases (Expr.app ef ea).getAppFn <;> intro hst <;> first | rfl | exact hst
  | letE ty w b =>
    obtain ⟨et, ew, eb, rfl, _, _, _⟩ := denote_letE_inv hwf hv hd
    rfl
  | _ => rw [htag] at hs; simp [ENodeView.tagOf, ETag.app, ETag.letE, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.lit, ETag.proj] at hs

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean PendOK — **the keys
pending in the loop**: each denotes a well-scoped key that answers, in mode
`c`, what `E` answers. -/
@[expose] def PendH (eager : Bool) (env : Env) (c : Bool) (d : Nat) (st : EStore)
    (pend : Array EIdx) (E : Expr) : Prop :=
  ∀ k ∈ pend.toList, ∃ K, denoteE st k = some K ∧ Expr.WScoped d K ∧
    ∀ V F, ConLeche.whnfCore .verified eager env F d E c = .ok V →
      ∃ G, ConLeche.whnfCore .verified eager env G d K c = .ok V

theorem PendH.nil {c : Bool} {d : Nat} {st : EStore} {E : Expr} :
    PendH eager env c d st #[] E := by
  intro k hk; simp at hk

theorem PendH.ext {c : Bool} {d : Nat} {st st' : EStore} {pend : Array EIdx} {E : Expr}
    (h : PendH eager env c d st pend E) (hx : Ext st st') : PendH eager env c d st' pend E := by
  intro k hk
  obtain ⟨K, hK, hw, hans⟩ := h k hk
  exact ⟨K, denote_ext hK hx, hw, hans⟩

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean PendOK.self — the term
joins its pending keys. -/
theorem PendH.pushKey (b : Bool) {c : Bool} {d : Nat} {st : EStore} {pend : Array EIdx}
    {i : EIdx} {E : Expr} (h : PendH eager env c d st pend E)
    (hd : denoteE st i = some E) (hw : Expr.WScoped d E) :
    PendH eager env c d st (pushKey b i pend) E := by
  unfold ConRon.Arena.pushKey
  split
  · intro k hk
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | rfl
    · exact h k hk
    · exact ⟨E, hd, hw, fun V F hF => ⟨F, hF⟩⟩
  · exact h

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean PendOK.cont — past a
continuing step, the keys answer what the continuation answers. -/
theorem PendH.cont {c : Bool} {d F : Nat} {st : EStore} {pend : Array EIdx} {E E' : Expr}
    (h : PendH eager env c d st pend E)
    (hs : mStep .verified eager env c F d E = .ok (.cont E')) :
    PendH eager env c d st pend E' := by
  intro k hk
  obtain ⟨K, hK, hw, hans⟩ := h k hk
  refine ⟨K, hK, hw, fun V G hG => ?_⟩
  obtain ⟨M, hM⟩ := whnfCore_of_mStep_cont hs hG
  exact hans V M hM

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean PendOK.pushCheap — the
cheap keys past a step: kept (the term joining them) past a step the two
modes take alike, dropped past any other. -/
theorem PendH.pushCheapKey (b : Bool) {c : Bool} {d F : Nat} {st : EStore}
    {pendC : Array EIdx} {i h : EIdx} {E E' : Expr} (hwf : StoreWF st)
    (hp : PendH eager env true d st pendC E)
    (hd : denoteE st i = some E) (hh : denoteE st h = some E.getAppFn) (hw : Expr.WScoped d E)
    (hs : mStep .verified eager env c F d E = .ok (.cont E')) :
    PendH eager env true d st (pushCheapKey (whnfCoreCheapSafe h i) b i pendC) E' := by
  unfold ConRon.Arena.pushCheapKey
  split
  · rename_i hsafe
    have hsc := whnfCoreCheapSafeC_of_tag hwf hd hh hsafe
    rw [← mStep_cheap hsc] at hs
    exact (hp.pushKey b hd hw).cont hs
  · exact PendH.nil

/-- con-leche: none — **the keys a store writes**: each denotes a
well-scoped key that `V` answers in mode `c`. -/
@[expose] def KeysAns (eager : Bool) (env : Env) (c : Bool) (d : Nat) (st : EStore)
    (pend : Array EIdx) (V : Expr) : Prop :=
  ∀ k ∈ pend.toList, ∃ K, denoteE st k = some K ∧ Expr.WScoped d K ∧
    ∃ F, ConLeche.whnfCore .verified eager env F d K c = .ok V

theorem KeysAns.nil {c : Bool} {d : Nat} {st : EStore} {V : Expr} :
    KeysAns eager env c d st #[] V := by
  intro k hk; simp at hk

theorem PendH.keysAns {c : Bool} {d F : Nat} {st : EStore} {pend : Array EIdx} {E V : Expr}
    (h : PendH eager env c d st pend E)
    (hV : ConLeche.whnfCore .verified eager env F d E c = .ok V) :
    KeysAns eager env c d st pend V := by
  intro k hk
  obtain ⟨K, hK, hw, hans⟩ := h k hk
  exact ⟨K, hK, hw, hans V F hV⟩

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean CSOK.chainStored —
**THEOREM 1 for `whnfCoreStoreKeys`**: the stored keys are backed rows. -/
theorem whnfCoreStoreKeys_spec (henv : ConLeche.EnvWF env) (d : Nat) (v : EIdx) (V : Expr)
    (pend : Array EIdx) :
    ∀ (n i : Nat) (s₀ : AState), pend.size - i = n → CheckOK eager env fe s₀ →
      denoteE s₀.store v = some V → Expr.WScoped d V →
      KeysAns eager env false d s₀.store pend V →
      ⦃fun s => s = s₀⦄ whnfCoreStoreKeys pend i v
      ⦃fun _ s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins; ⊤⦄
  | 0, i, s₀, hn, hok, _, _, _ => by
    rw [whnfCoreStoreKeys, dite_eq_right (by omega)]
    vcgen
    subst_vars
    exact ⟨hok, rfl, rfl⟩
  | n + 1, i, s₀, hn, hok, hv, hwV, hk => by
    have hi : i < pend.size := by omega
    rw [whnfCoreStoreKeys, dite_eq_left hi]
    refine triple_seq (whnfCoreSet_spec s₀ pend[i] v) ?_
    rintro _ s1 rfl
    obtain ⟨K, hK, hwK, F, hF⟩ := hk pend[i] (Array.getElem_mem_toList hi)
    have hok1 := CheckOK.insertWhnfCoreAt henv hok hK hwK ⟨V, hv, hwV, F, hF⟩
    exact whnfCoreStoreKeys_spec henv d v V pend n (i + 1) _ (by omega) hok1 hv hwV hk

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean CSOK.chainStored —
**THEOREM 1 for `whnfCoreStoreCheapKeys`**. -/
theorem whnfCoreStoreCheapKeys_spec (henv : ConLeche.EnvWF env) (d : Nat) (v : EIdx)
    (V : Expr) (pendC : Array EIdx) :
    ∀ (n i : Nat) (s₀ : AState), pendC.size - i = n → CheckOK eager env fe s₀ →
      denoteE s₀.store v = some V → Expr.WScoped d V →
      KeysAns eager env true d s₀.store pendC V →
      ⦃fun s => s = s₀⦄ whnfCoreStoreCheapKeys pendC i v
      ⦃fun _ s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins; ⊤⦄
  | 0, i, s₀, hn, hok, _, _, _ => by
    rw [whnfCoreStoreCheapKeys, dite_eq_right (by omega)]
    vcgen
    subst_vars
    exact ⟨hok, rfl, rfl⟩
  | n + 1, i, s₀, hn, hok, hv, hwV, hk => by
    have hi : i < pendC.size := by omega
    rw [whnfCoreStoreCheapKeys, dite_eq_left hi]
    refine triple_seq (whnfCoreCheapSet_spec s₀ pendC[i] v) ?_
    rintro _ s1 rfl
    obtain ⟨K, hK, hwK, F, hF⟩ := hk pendC[i] (Array.getElem_mem_toList hi)
    have hok1 := CheckOK.insertWhnfCoreCheapAt henv hok hK hwK ⟨V, hv, hwV, F, hF⟩
    exact whnfCoreStoreCheapKeys_spec henv d v V pendC n (i + 1) _ (by omega) hok1 hv hwV hk

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean CSOK.chainStored —
**THEOREM 1 for `whnfCoreStoreChain`**: the full mode's keys and cheap keys
are backed rows; the cheap mode stores nothing. -/
theorem whnfCoreStoreChain_spec (henv : ConLeche.EnvWF env) (c : Bool) (d : Nat)
    (pend pendC : Array EIdx) (v : EIdx) (V : Expr) (s₀ : AState)
    (hok : CheckOK eager env fe s₀) (hv : denoteE s₀.store v = some V)
    (hwV : Expr.WScoped d V)
    (hk : c = false → KeysAns eager env false d s₀.store pend V)
    (hkc : c = false → KeysAns eager env true d s₀.store pendC V) :
    ⦃fun s => s = s₀⦄ whnfCoreStoreChain c pend pendC v
    ⦃fun _ s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins; ⊤⦄ := by
  unfold whnfCoreStoreChain
  cases c with
  | true =>
    simp only [ite_true]
    vcgen
    subst_vars
    exact ⟨hok, rfl, rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    split
    · vcgen
      subst_vars
      exact ⟨hok, rfl, rfl⟩
    · refine triple_seq (whnfCoreStoreKeys_spec henv d v V pend _ 0 s₀ rfl hok hv hwV
        (hk rfl)) ?_
      rintro _ s1 ⟨hok1, hs1, hp1⟩
      refine triple_mono (whnfCoreStoreCheapKeys_spec henv d v V pendC _ 0 s1 rfl hok1
        (by rw [hs1]; exact hv) hwV (by rw [hs1]; exact hkc rfl)) ?_
      rintro _ s2 ⟨hok2, hs2, hp2⟩
      exact ⟨hok2, hs2.trans hs1, hp2.trans hp1⟩

/-- con-leche: ConLeche/Cached/CoreC.lean:314-316 whnfCoreLookupI — the
lookup reads the mode's table. -/
theorem whnfCoreLookup_spec (c : Bool) (s₀ : AState) (i : EIdx) :
    ⦃fun s => s = s₀⦄ whnfCoreLookup c i
    ⦃fun o s' => s' = s₀ ∧
        o = (if c then s₀.caches.whnfCoreCheapC[i]? else s₀.caches.whnfCoreC[i]?); ⊤⦄ := by
  unfold whnfCoreLookup
  cases c <;> (vcgen; subst_vars) <;> simp_all

/-- con-leche: none — the hit, in either mode, from the state invariant. -/
theorem CheckOK.whnfCoreHitAt (henv : ConLeche.EnvWF env) {c : Bool} {s : AState}
    {i j : EIdx} {d : Nat} {e : Expr} (hok : CheckOK eager env fe s)
    (hx : (if c then s.caches.whnfCoreCheapC[i]? else s.caches.whnfCoreC[i]?) = some j)
    (hden : denoteE s.store i = some e) (hw : Expr.WScoped d e) :
    SimE (fun F d e => ConLeche.whnfCore .verified eager env F d e c) d e s.store j := by
  cases c
  · exact CheckOK.whnfCoreHit henv hok (by simpa using hx) hden hw
  · exact CheckOK.whnfCoreCheapHit henv hok (by simpa using hx) hden hw

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfCoreLoopC_spec —
**THEOREM 1 for `whnfCoreLoop`**, by induction on the step budget: the twin's
loop answers the chained `whnfCore` of its term, its pending keys being backed
by it, and leaves the memo invariant in place. -/
theorem whnfCoreLoop_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (c : Bool) (d : Nat) :
    ∀ (n : Nat) (s₀ : AState) (i : EIdx) (E : Expr) (pend pendC : Array EIdx),
      CheckOK eager env fe s₀ → denoteE s₀.store i = some E →
      Expr.WScoped d E →
      PendH eager env c d s₀.store pend E → PendH eager env true d s₀.store pendC E →
      ⦃fun s => s = s₀⦄
        whnfCoreLoop .verified (coreKnot .verified eager fe id fuel) fe c d n i pend pendC
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          SimE (fun F d e => ConLeche.whnfCore .verified eager env F d e c) d E s'.store r; ⊤⦄
  | 0, s₀, i, E, pend, pendC, _, _, _, _, _ => by
    rw [whnfCoreLoop]; exact triple_fail
  | n + 1, s₀, i, E, pend, pendC, hok, hden, hw, hp, hpc => by
    have hwf := hok.state.wf
    rw [whnfCoreLoop]
    by_cases hst : whnfCoreStuckTag i = true
    · -- an easy case: its own answer in both modes
      rw [ite_eq_left hst]
      have hstk := denote_stuck_of_whnfCoreStuckTag hwf hden hst
      have hE : ∀ c', ConLeche.whnfCore .verified eager env 1 d E c' = .ok E :=
        fun _ => whnfCore_of_stuck hstk 0 d
      refine triple_seq (whnfCoreStoreChain_spec henv c d pend pendC i E s₀ hok hden hw
        (fun hc => by subst hc; exact hp.keysAns (hE false))
        (fun _ => hpc.keysAns (hE true))) ?_
      rintro _ s1 ⟨hok1, hs1, hp1⟩
      vcgen
      subst_vars
      exact ⟨hok1, by rw [hs1]; exact Ext.refl _, hp1, E, by rw [hs1]; exact hden, hw, 1,
        hE c⟩
    · rw [ite_eq_right hst]
      refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ i hok.state
        (by rw [hden]; rfl)) ?_
      rintro hh s1 ⟨hs1, hrelh⟩
      subst s1
      have hdh := hrelh E hden
      -- the lookup, at a key only
      have hlk : ⦃fun s => s = s₀⦄
          (whnfCoreLookupAt (whnfCoreKey hh i) c i)
          ⦃fun o s' => s' = s₀ ∧ ∀ x, o = some x →
            (if c then s₀.caches.whnfCoreCheapC[i]? else s₀.caches.whnfCoreC[i]?) = some x;
            ⊤⦄ := by
        unfold whnfCoreLookupAt
        split
        · exact triple_mono (whnfCoreLookup_spec c s₀ i)
            (fun o s' ⟨h1, h2⟩ => ⟨h1, fun x hx => by rw [← h2, hx]⟩)
        · vcgen
          subst_vars
          simp
      dsimp only
      refine triple_seq hlk ?_
      rintro hit s2 ⟨hs2, hhit⟩
      subst s2
      cases hit with
      | some x =>
        -- a hit ends the chain; its keys get the hit's answer
        obtain ⟨X, hdX, hwX, FX, hFX⟩ := CheckOK.whnfCoreHitAt henv hok (hhit x rfl) hden hw
        dsimp only
        refine triple_seq (whnfCoreStoreChain_spec henv c d pend #[] x X s₀ hok hdX hwX
          (fun hc => by subst hc; exact hp.keysAns hFX) (fun _ => KeysAns.nil)) ?_
        rintro _ s3 ⟨hok3, hs3, hp3⟩
        vcgen
        subst_vars
        exact ⟨hok3, by rw [hs3]; exact Ext.refl _, hp3, X, by rw [hs3]; exact hdX, hwX,
          FX, hFX⟩
      | none =>
        dsimp only
        refine triple_seq (whnfCoreStep_spec henv hsim c s₀ d hh i E hok hden hdh hw) ?_
        rintro st s3 ⟨hok3, hx3, hp3, R, hdR, hwR, F1, hF1⟩
        have hden3 := denote_ext hden hx3
        have hdh3 := denote_ext hdh hx3
        cases st with
        | done v =>
          simp only [denoteStep, Option.map_eq_some_iff] at hdR
          obtain ⟨V, hdV, rfl⟩ := hdR
          obtain ⟨M, hM⟩ := whnfCore_of_mStep_done hF1
          dsimp only
          refine triple_seq (whnfCoreStoreChain_spec henv c d _ _ v V s3 hok3 hdV hwR
            (fun hc => by subst hc; exact ((hp.ext hx3).pushKey _ hden3 hw).keysAns hM)
            (fun _ => ?_)) ?_
          · unfold ConRon.Arena.pushCheapKey
            split
            · rename_i hsafe
              have hsc := whnfCoreCheapSafeC_of_tag hok3.state.wf hden3 hdh3 hsafe
              have hF1c : mStep .verified eager env c F1 d E = .ok (.done V) := hF1
              rw [← mStep_cheap hsc] at hF1c
              obtain ⟨M', hM'⟩ := whnfCore_of_mStep_done hF1c
              exact ((hpc.ext hx3).pushKey _ hden3 hw).keysAns hM'
            · exact KeysAns.nil
          rintro _ s4 ⟨hok4, hs4, hp4⟩
          vcgen
          subst_vars
          exact ⟨hok4, by rw [hs4]; exact hx3, by rw [hp4, hp3], V,
            by rw [hs4]; exact hdV, hwR, M, hM⟩
        | cont e' =>
          simp only [denoteStep, Option.map_eq_some_iff] at hdR
          obtain ⟨E', hdE', rfl⟩ := hdR
          dsimp only
          refine triple_mono (whnfCoreLoop_spec henv hsim c d n s3 e' E' _ _ hok3 hdE' hwR
            (((hp.ext hx3).pushKey _ hden3 hw).cont hF1)
            ((hpc.ext hx3).pushCheapKey _ hok3.state.wf hden3 hdh3 hw hF1)) ?_
          rintro r s' ⟨hck, hx, hp', v, hdv, hwv, F2, hF2⟩
          obtain ⟨M, hM⟩ := whnfCore_of_mStep_cont hF1 hF2
          exact ⟨hck, hx3.trans hx, by rw [hp', hp3], v, hdv, hwv, M, hM⟩

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfCoreBodyC_spec —
**THEOREM 1 for `whnfCoreBody`**: the loop at its own budget, with no key
pending. -/
theorem whnfCoreBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (c : Bool) :
    BodySpec eager env fe (whnfCoreBody .verified (coreKnot .verified eager fe id fuel) fe c)
      (fun F d e => ConLeche.whnfCore .verified eager env F d e c) := by
  intro s₀ d i e hok hden hw
  unfold ConRon.Arena.whnfCoreBody
  exact whnfCoreLoop_spec henv hsim c d _ s₀ i e #[] #[] hok hden hw PendH.nil PendH.nil

section Census

#print axioms mStep_proj_none
#print axioms mStep_proj_some
#print axioms whnfCoreStep_spec
#print axioms whnfStuck_spec
#print axioms whnfCoreStoreChain_spec
#print axioms whnfCoreLoop_spec
#print axioms whnfCoreBody_spec

end Census

end ConRon.Bridge.Core
