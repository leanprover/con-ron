/-
# `ConRon.Bridge.Core.Arms.WhnfCore` — Theorem 1 for `whnfCoreBody`

DESIGN §8.2, task #97s's **rule 8**: one step lemma per exit of the PURE
function.  Since con-leche's task #342 R2 the twin's `whnfCoreBody` is the
CACHED tier's loop (`Cached/CoreC.lean:768-822 whnfCoreStepI` /
`whnfCoreLoopI`): `whnfCoreStep` RETURNS the term to continue with
(`WhnfStep.cont`) and `whnfCoreLoop` iterates it on its own step budget.
con-leche's pure mirrors are `Verify/BetaSpine.lean`'s `whnfCoreStepW` /
`whnfCoreLoopM`, and `whnfCoreLoop_sound_body` reproduces a successful mirror
run by the chained `whnfCoreBody` at some knot fuel.  So:

| piece | twin | pure side |
|---|---|---|
| one step | `whnfCoreStep` | `whnfCoreStepW` at `pureFns mode env F` (`whnfCoreStep_spec`) |
| the loop | `whnfCoreLoop` | `whnfCoreLoopM` (`whnfCoreLoop_spec`, induction on the budget) |
| the body | `whnfCoreBody` | `whnfCore` (`whnfCoreBody_spec`, over `whnfCore_of_loopM`) |

The step's exits: the six values are `.done` themselves; `.app` is the
batched spine (`Walks/BetaSpine.lean`'s `whnfApp_carry`); `.proj` is the
scrutinee's reduction then `reduceProjCore` (fired field `.cont`, stuck node
`.done`); `.letE` is ζ (`.cont`, con-leche's task #342 S0); `.bvar` throws.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.Owed
import ConRon.Bridge.Core.Walks.Iota
import ConRon.Bridge.Core.Walks.ProjCore
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Walks.BetaSpine

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env}

/-! ## 1. The scrutinee of the `.proj` exit -/

/-- con-leche: ConLeche/Kernel/Core.lean:967 whnfCoreBody — the
scrutinee's reduction, in the clause's mode, at the pure knot. -/
abbrev projScrut (mode : CheckMode) (env : Env) (c : Bool) (F d : Nat)
    (pe : Expr) : CheckM Expr :=
  if c then ConLeche.whnfCore mode env F d pe true
  else ConLeche.whnf mode env F d pe

/-- con-leche: ConLeche/Verify/Mono.lean:120 whnfCore_mono — the scrutinee's
reduction is fuel-monotone in either mode. -/
theorem projScrut_mono {c : Bool} {F F' d : Nat} {pe r : Expr} (hle : F ≤ F')
    (h : projScrut mode env c F d pe = .ok r) :
    projScrut mode env c F' d pe = .ok r := by
  cases c
  · exact ConLeche.whnf_mono hle h
  · exact ConLeche.whnfCore_mono hle h

/-! ## 2. The pure step at its exits -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:328 whnfCoreStepW — at the pure
knot. -/
abbrev mStep (mode : CheckMode) (env : Env) (c : Bool) (F d : Nat) (e : Expr) :
    CheckM ConLeche.WhnfStep :=
  ConLeche.whnfCoreStepW mode (ConLeche.pureFns mode env F) env c d e

/-- con-leche: ConLeche/Verify/BetaSpine.lean:458 whnfCoreStepW_atF — fuel
monotonicity of the step. -/
theorem mStep_mono {c : Bool} {F F' d : Nat} {e : Expr} {r : ConLeche.WhnfStep}
    (hle : F ≤ F') (h : mStep mode env c F d e = .ok r) :
    mStep mode env c F' d e = .ok r := by
  simp only [mStep] at h ⊢
  rw [← ConLeche.whnfCoreStepW_atF] at h ⊢
  exact (ConLeche.whnfCoreStepW mode (ConLeche.fueledFns mode env) env c d
    e).property hle h

/-- con-leche: ConLeche/Verify/BetaSpine.lean:470 whnfCoreLoopM_atF — fuel
monotonicity of the loop mirror. -/
theorem loopM_mono {c : Bool} {d n F F' : Nat} (hle : F ≤ F') {e v : Expr}
    (h : ConLeche.whnfCoreLoopM mode (ConLeche.pureFns mode env F) env c d n e
      = .ok v) :
    ConLeche.whnfCoreLoopM mode (ConLeche.pureFns mode env F') env c d n e
      = .ok v := by
  rw [← ConLeche.whnfCoreLoopM_atF] at h ⊢
  exact (ConLeche.whnfCoreLoopM mode (ConLeche.fueledFns mode env) env c d n
    e).property hle h

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1097 whnfCoreLoop_sound_body —
**the loop mirror is the chained head normalization**: a successful
`whnfCoreLoopM` run at some fuel is a `whnfCore` run at some fuel. -/
theorem whnfCore_of_loopM {c : Bool} {d n F : Nat} {e v : Expr}
    (h : ConLeche.whnfCoreLoopM mode (ConLeche.pureFns mode env F) env c d n e
      = .ok v) :
    ∃ F', ConLeche.whnfCore mode env F' d e c = .ok v := by
  rw [← ConLeche.whnfCoreLoopM_atF] at h
  obtain ⟨F', hF'⟩ := ConLeche.whnfCoreLoop_sound_body d e v n F h
  refine ⟨F' + 1, ?_⟩
  rw [ConLeche.whnfCore_succ, ← ConLeche.whnfCoreBody_atF]
  exact hF'

/-- con-leche: ConLeche/Verify/BetaSpine.lean:328 whnfCoreStepW — the `.app`
exit: the spine head's normal form, then the batched walk. -/
theorem mStep_app {c : Bool} {F d : Nat} {f a V : Expr} {r : ConLeche.WhnfStep}
    (hv : ConLeche.whnfCore mode env F d (Expr.app f a).getAppFn c = .ok V)
    (hw : mWA mode env F d V (Expr.app f a).getAppArgs = .ok r) :
    mStep mode env c F d (.app f a) = .ok r := by
  have hv' : (ConLeche.pureFns mode env F).whnfCore c d (Expr.app f a).getAppFn
      = .ok V := hv
  simp only [mStep, ConLeche.whnfCoreStepW, hv', bind, Except.bind]
  exact hw

/-- con-leche: ConLeche/Verify/BetaSpine.lean:328 whnfCoreStepW — the `.proj`
exit, the rule does not fire: the node itself, done (con-leche's task #323:
its scrutinee as it was). -/
theorem mStep_proj_none {c : Bool} {F d i : Nat} {sn : Name} {pe c' : Expr}
    (hs : projScrut mode env c F d pe = .ok c')
    (hr : ConLeche.reduceProjCoreFueled mode env F d sn i c' = .ok none) :
    mStep mode env c F d (.proj sn i pe) = .ok (.done (.proj sn i pe)) := by
  simp only [ConLeche.reduceProjCoreFueled] at hr
  cases c <;>
    simp only [projScrut, ite_true, Bool.false_eq_true, ite_false] at hs <;>
    simp only [mStep, ConLeche.whnfCoreStepW, ConLeche.whnf_def,
      ConLeche.whnfCore_def, ite_true, Bool.false_eq_true, ite_false, hs, hr,
      bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:328 whnfCoreStepW — the `.proj`
exit, the rule fires: the selected field is the term to continue with. -/
theorem mStep_proj_some {c : Bool} {F d i : Nat} {sn : Name} {pe c' m : Expr}
    (hs : projScrut mode env c F d pe = .ok c')
    (hr : ConLeche.reduceProjCoreFueled mode env F d sn i c' = .ok (some m)) :
    mStep mode env c F d (.proj sn i pe) = .ok (.cont m) := by
  simp only [ConLeche.reduceProjCoreFueled] at hr
  cases c <;>
    simp only [projScrut, ite_true, Bool.false_eq_true, ite_false] at hs <;>
    simp only [mStep, ConLeche.whnfCoreStepW, ConLeche.whnf_def,
      ConLeche.whnfCore_def, ite_true, Bool.false_eq_true, ite_false, hs, hr,
      bind, Except.bind, pure, Except.pure]

/-! ## 3. Theorem 1 for one step -/

/-- con-leche: ConLeche/Cached/CoreC.lean:768-804 whnfCoreStepI —
**THEOREM 1 for `whnfCoreStep`**: the twin's step denotes the mirror's
outcome at some fuel. -/
theorem whnfCoreStep_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (c : Bool)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄
      whnfCoreStep mode (coreKnot mode fe id fuel) fe c d i
    ⦃fun r s' => StepPost mode env fe d s₀ (fun F => mStep mode env c F d e)
        r s'; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  unfold whnfCoreStep
  refine view_bind_triple hv ?_
  -- a value answers itself
  have hval : ∀ (e0 : Expr), e = e0 →
      mStep mode env c 0 d e0 = .ok (.done e0) →
      ⦃fun s => s = s₀⦄ (pure (ConRon.Arena.WhnfStep.done i) : AM _)
      ⦃fun r s' => StepPost mode env fe d s₀ (fun F => mStep mode env c F d e)
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
        (if c then (coreKnot mode fe id fuel).whnfCore true d pe
          else (coreKnot mode fe id fuel).whnf d pe)
        ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
            s'.pins = s₀.pins ∧
            SimEOp (fun F => projScrut mode env c F d es) d s'.store r; ⊤⦄ := by
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
    have hr' := ConLeche.reduceProjCore_mono (env := env) (mi := mode)
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
    -- the spine, in one read
    refine triple_seq (getAppSpine_spec coreWalkFuel s₀ i e hok.state hden) ?_
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
    have hctx : SpineCtx d sp.2.1 sp.2.2 e.getAppFn e.getAppArgs s2.store :=
      ⟨denoteEList_ext' hx2 hsp2, Expr.WScoped.getAppArgs hw, hsp3,
        fun j hj => denote_ext (hsp4 j hj) hx2⟩
    have hsame : (vh == sp.1) = true →
        Vh = Expr.mkAppN e.getAppFn (e.getAppArgs.take 0) := by
      intro hb
      have heq : vh = sp.1 := beq_iff_eq.mp hb
      rw [heq, denote_ext hsp1 hx2] at hdv
      simpa [Expr.mkAppN] using (Option.some.inj hdv).symm
    have hden' := hden
    obtain ⟨ef, ea, rfl, _, _⟩ := denote_app_inv hwf hv hden'
    refine triple_mono (whnfApp_carry henv hμ hsim d sp.2.1 sp.2.2
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
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (c : Bool) (d : Nat) :
    ∀ (n : Nat) (s₀ : AState) (i : EIdx) (e : Expr),
      CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
      Expr.WScoped d e →
      ⦃fun s => s = s₀⦄
        whnfCoreLoop mode (coreKnot mode fe id fuel) fe c d n i
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          Expr.WScoped d v ∧ ∃ F, ConLeche.whnfCoreLoopM mode
            (ConLeche.pureFns mode env F) env c d n e = .ok v; ⊤⦄
  | 0, s₀, i, e, _, _, _ => by
    rw [whnfCoreLoop]; exact triple_fail
  | n + 1, s₀, i, e, hok, hden, hw => by
    rw [whnfCoreLoop]
    refine triple_seq (whnfCoreStep_spec henv hμ hsim c s₀ d i e hok hden hw) ?_
    rintro st s1 ⟨hok1, hx1, hp1, R, hdR, hwR, F1, hF1⟩
    cases st with
    | done v =>
      simp only [denoteStep, Option.map_eq_some_iff] at hdR
      obtain ⟨V, hdV, rfl⟩ := hdR
      vcgen
      subst_vars
      refine ⟨hok1, hx1, hp1, V, hdV, hwR, F1, ?_⟩
      simp only [ConLeche.whnfCoreLoopM]
      rw [show ConLeche.whnfCoreStepW mode (ConLeche.pureFns mode env F1) env c d e
        = .ok (.done V) from hF1]
      rfl
    | cont e' =>
      simp only [denoteStep, Option.map_eq_some_iff] at hdR
      obtain ⟨E', hdE', rfl⟩ := hdR
      dsimp only
      refine triple_mono (whnfCoreLoop_spec henv hμ hsim c d n s1 e' E' hok1 hdE'
        hwR) ?_
      rintro r s' ⟨hck, hx, hp, v, hdv, hwv, F2, hF2⟩
      refine ⟨hck, hx1.trans hx, by rw [hp, hp1], v, hdv, hwv, max F1 F2, ?_⟩
      simp only [ConLeche.whnfCoreLoopM]
      rw [show ConLeche.whnfCoreStepW mode (ConLeche.pureFns mode env (max F1 F2))
          env c d e = .ok (.cont E') from mStep_mono (Nat.le_max_left _ _) hF1]
      exact loopM_mono (Nat.le_max_right _ _) hF2

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfCoreBodyC_sim —
**THEOREM 1 for `whnfCoreBody`**, at a knot record one fuel level down: the
loop at its own budget, and con-leche's `whnfCoreLoop_sound_body` for the
chained side. -/
theorem whnfCoreBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (c : Bool) :
    BodySpec mode env fe (whnfCoreBody mode (coreKnot mode fe id fuel) fe c)
      (fun F d e => ConLeche.whnfCore mode env F d e c) := by
  intro s₀ d i e hok hden hw
  unfold ConRon.Arena.whnfCoreBody
  refine triple_mono (whnfCoreLoop_spec henv hμ hsim c d _ s₀ i e hok hden hw) ?_
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
