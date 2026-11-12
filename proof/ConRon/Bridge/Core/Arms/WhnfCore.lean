/-
# `ConRon.Bridge.Core.Arms.WhnfCore` — Theorem 1 for `whnfCoreBody`

DESIGN §8.2, task #97s's **rule 8**: one step lemma per exit of the PURE
function.  The twin's `whnfCoreBody` is (con-leche's task #342 R2) the
CACHED tier's loop (`Cached/CoreC.lean:768-822 whnfCoreStepI` /
`whnfCoreLoopI`): `whnfCoreStep` RETURNS the term to continue with
(`WhnfStep.cont`) and `whnfCoreLoop` iterates it on its own step budget.
con-leche's pure mirrors are `Verify/BetaSpine.lean`'s `whnfCoreStepW` /
`whnfCoreLoopM`, and `whnfCoreLoop_sound_body` reproduces a successful mirror
run by the chained `whnfCoreBody` at some knot fuel.  So:

| piece | twin | pure side |
|---|---|---|
| one step | `whnfCoreStep` | `whnfCoreStepW` at `pureFns .verified eager env F` (`whnfCoreStep_spec`) |
| the loop | `whnfCoreLoop` | `whnfCoreLoopM` (`whnfCoreLoop_spec`, induction on the budget) |
| the body | `whnfCoreBody` | `whnfCore` (`whnfCoreBody_spec`, over `whnfCore_of_loopM`) |

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
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool} {env : Env}

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

/-- con-leche: ConLeche/Verify/BetaSpine.lean:470 whnfCoreLoopM_atF — fuel
monotonicity of the loop mirror. -/
theorem loopM_mono {c : Bool} {d n F F' : Nat} (hle : F ≤ F') {e v : Expr}
    (h : ConLeche.whnfCoreLoopM mode (ConLeche.pureFns mode eager env F) env c d n e
      = .ok v) :
    ConLeche.whnfCoreLoopM mode (ConLeche.pureFns mode eager env F') env c d n e
      = .ok v := by
  rw [← ConLeche.whnfCoreLoopM_atF] at h ⊢
  exact (ConLeche.whnfCoreLoopM mode (ConLeche.fueledFns mode eager env) env c d n
    e).property hle h

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1097 whnfCoreLoop_sound_body —
**the loop mirror is the chained head normalization**: a successful
`whnfCoreLoopM` run at some fuel is a `whnfCore` run at some fuel. -/
theorem whnfCore_of_loopM {c : Bool} {d n F : Nat} {e v : Expr}
    (h : ConLeche.whnfCoreLoopM mode (ConLeche.pureFns mode eager env F) env c d n e
      = .ok v) :
    ∃ F', ConLeche.whnfCore mode eager env F' d e c = .ok v := by
  rw [← ConLeche.whnfCoreLoopM_atF] at h
  obtain ⟨F', hF'⟩ := ConLeche.whnfCoreLoop_sound_body d e v n F h
  refine ⟨F' + 1, ?_⟩
  rw [ConLeche.whnfCore_succ, ← ConLeche.whnfCoreBody_atF]
  exact hF'

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
        split <;> (vcgen; subst_vars; simp_all)
      next hnot =>
        have hnr := env_not_rec_of_index hok hcn hnot
        vcgen
        subst_vars
        refine ⟨rfl, ?_⟩
        simp only [ConLeche.Cached.iotaTargetF, ConLeche.mkFEnv_find?]
        split
        · next cv mI rP isK rules hf => exact absurd hf (hnr cv mI rP isK rules)
        · rfl
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
  split
  · split
    · simp only [ConLeche.FueledM.atF_bind, ConLeche.iotaRec_atF]
    · rfl
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
        | exact absurd hh (by simp [ConLeche.Cached.isStuckHeadC])
        | simp
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
    simp [ExprOps.takeEidx_toList]
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
  rintro o s1 ⟨rfl, ho⟩
  -- the input itself, done
  have hdone : ∀ (P : Prop), (mWA .verified eager env 1 d (Expr.app f a).getAppFn
      (Expr.app f a).getAppArgs = .ok (.done (.app f a))) →
      StepPost eager env fe d s₀ (fun F => mStep .verified eager env c F d (.app f a))
        (.done i) s₀ := by
    intro _ hm
    exact ⟨hok, Ext.refl _, rfl, .done (.app f a), by simp [denoteStep, hden], hw, 1,
      by rw [mStep_stuck hh]; exact hm⟩
  cases o with
  | none =>
    vcgen
    subst_vars
    refine hdone True ?_
    rw [mWA_stuck hh, ← ho, hmk]
  | some k =>
    dsimp only
    refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ i hok.state
      (by rw [hden]; rfl)) ?_
    rintro as s2 ⟨rfl, has⟩
    have hdas := has _ hden
    have hlen : (Expr.app f a).getAppArgs.length = as.length := denoteEList_len hdas
    by_cases hk : k ≤ as.toArray.size
    · rw [if_pos hk, iotaRecAt_take]
      have hks : (takeEidx as.toArray k).size = k := by
        have := congrArg List.length (ExprOps.takeEidx_toList as.toArray k)
        simp only [Array.length_toList, List.length_take, Array.toList_toArray] at this
        simp at hk
        rw [this]; omega
      have hdk : Frontend.denoteEList s₀.store (takeEidx as.toArray k).toList =
          some ((Expr.app f a).getAppArgs.take k) := by
        rw [ExprOps.takeEidx_toList, Array.toList_toArray]
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
        rw [mStep_stuck hh, mWA_stuck hh, ← ho]
        dsimp only
        rw [if_pos hkL, ConLeche.iotaRec_mono (by omega) hF1]
        simp only [bind, Except.bind, ConLeche.Cached.whnfStuckTail, hmk]
        rfl
      | some e2 =>
        simp only [denoteEO, Option.map_eq_some_iff] at hov
        obtain ⟨E2, hdE2, rfl⟩ := hov
        have hwE2 := hwov E2 rfl
        dsimp only
        have hrest : Frontend.denoteEList s3.store (as.toArray.toList.drop k) =
            some ((Expr.app f a).getAppArgs.drop k) := by
          rw [Array.toList_toArray]
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
          dsimp only
          rw [mStep_stuck hh, mWA_stuck hh, ← ho]
          dsimp only
          rw [if_pos hkL, ConLeche.iotaRec_mono (by omega) hF1]
          rfl
        vcgen
        subst_vars
        exact hpost
    · rw [if_neg hk]
      vcgen
      subst_vars
      refine hdone True ?_
      have hkL : ¬ k ≤ (Expr.app f a).getAppArgs.length := by
        rw [hlen]; simpa using hk
      rw [mWA_stuck hh, ← ho]
      dsimp only
      rw [if_neg hkL, hmk]

/-! ## 3. Theorem 1 for one step -/

/-- con-leche: ConLeche/Cached/CoreC.lean:768-804 whnfCoreStepI —
**THEOREM 1 for `whnfCoreStep`**: the twin's step denotes the mirror's
outcome at some fuel. -/
theorem whnfCoreStep_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (c : Bool)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK eager env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄
      whnfCoreStep .verified (coreKnot .verified eager fe id fuel) fe c d i
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
    -- the spine head, read once
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ i hok.state
      (by rw [hden]; rfl)) ?_
    rintro hh s0 ⟨rfl, hrelh⟩
    have hdh := hrelh _ hden
    by_cases hst : isStuckHead hh = true
    · rw [if_pos hst]
      exact whnfStuck_spec henv hsim c s₀ d hh i ef ea hok hden hdh
        (isStuckHeadC_of_tag hwf hdh hst) hw
    rw [if_neg hst]
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

/-! ## 4. The loop and the body -/

/-- con-leche: ConLeche/Cached/CoreC.lean:806-817 whnfCoreLoopI — **THEOREM 1
for `whnfCoreLoop`**, by induction on the step budget: the twin's loop
denotes the mirror loop `whnfCoreLoopM` at some fuel. -/
theorem whnfCoreLoop_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (c : Bool) (d : Nat) :
    ∀ (n : Nat) (s₀ : AState) (i : EIdx) (e : Expr),
      CheckOK eager env fe s₀ → denoteE s₀.store i = some e →
      Expr.WScoped d e →
      ⦃fun s => s = s₀⦄
        whnfCoreLoop .verified (coreKnot .verified eager fe id fuel) fe c d n i
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          Expr.WScoped d v ∧ ∃ F, ConLeche.whnfCoreLoopM .verified
            (ConLeche.pureFns .verified eager env F) env c d n e = .ok v; ⊤⦄
  | 0, s₀, i, e, _, _, _ => by
    rw [whnfCoreLoop]; exact triple_fail
  | n + 1, s₀, i, e, hok, hden, hw => by
    rw [whnfCoreLoop]
    refine triple_seq (whnfCoreStep_spec henv hsim c s₀ d i e hok hden hw) ?_
    rintro st s1 ⟨hok1, hx1, hp1, R, hdR, hwR, F1, hF1⟩
    cases st with
    | done v =>
      simp only [denoteStep, Option.map_eq_some_iff] at hdR
      obtain ⟨V, hdV, rfl⟩ := hdR
      vcgen
      subst_vars
      refine ⟨hok1, hx1, hp1, V, hdV, hwR, F1, ?_⟩
      simp only [ConLeche.whnfCoreLoopM]
      rw [show ConLeche.whnfCoreStepW .verified (ConLeche.pureFns .verified eager env F1) env c d e
        = .ok (.done V) from hF1]
      rfl
    | cont e' =>
      simp only [denoteStep, Option.map_eq_some_iff] at hdR
      obtain ⟨E', hdE', rfl⟩ := hdR
      dsimp only
      refine triple_mono (whnfCoreLoop_spec henv hsim c d n s1 e' E' hok1 hdE'
        hwR) ?_
      rintro r s' ⟨hck, hx, hp, v, hdv, hwv, F2, hF2⟩
      refine ⟨hck, hx1.trans hx, by rw [hp, hp1], v, hdv, hwv, max F1 F2, ?_⟩
      simp only [ConLeche.whnfCoreLoopM]
      rw [show ConLeche.whnfCoreStepW .verified (ConLeche.pureFns .verified eager env (max F1 F2))
          env c d e = .ok (.cont E') from mStep_mono (Nat.le_max_left _ _) hF1]
      exact loopM_mono (Nat.le_max_right _ _) hF2

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfCoreBodyC_sim —
**THEOREM 1 for `whnfCoreBody`**, at a knot record one fuel level down: the
loop at its own budget, and con-leche's `whnfCoreLoop_sound_body` for the
chained side. -/
theorem whnfCoreBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (c : Bool) :
    BodySpec eager env fe (whnfCoreBody .verified (coreKnot .verified eager fe id fuel) fe c)
      (fun F d e => ConLeche.whnfCore .verified eager env F d e c) := by
  intro s₀ d i e hok hden hw
  unfold ConRon.Arena.whnfCoreBody
  refine triple_mono (whnfCoreLoop_spec henv hsim c d _ s₀ i e hok hden hw) ?_
  rintro r s' ⟨hck, hx, hp, v, hdv, hwv, F, hF⟩
  exact ⟨hck, hx, hp, v, hdv, hwv, whnfCore_of_loopM hF⟩

section Census

#print axioms whnfCore_of_loopM
#print axioms mStep_proj_none
#print axioms mStep_proj_some
#print axioms whnfCoreStep_spec
#print axioms whnfCoreLoop_spec
#print axioms whnfCoreBody_spec

end Census

end ConRon.Bridge.Core
