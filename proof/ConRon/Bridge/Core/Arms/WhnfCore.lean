/-
# `ConRon.Bridge.Core.Arms.WhnfCore` — Theorem 1 for `whnfCoreBody`

DESIGN §8.2, task #97s's **rule 8**: *one step lemma per clause of the PURE
function, not per constructor of the subject*.  This module is that inventory
for `ConLeche/Kernel/Core.lean:1012-1089 whnfCoreBody` — nine exits over four
clauses — followed by the body theorem (`whnfCoreBody_spec`) the knot's
`whnfCore` wrapper consumes.

## The exits

| clause | exit | lemma |
|---|---|---|
| the six values | `pure e` | `Bridge/Core/Memo.lean`'s `whnfCore_of_stuck` |
| `.app` | the β gate fires | `whnfCore_app_beta_gate` |
| `.app` | the argument certificate succeeds | `whnfCore_app_beta_cert` |
| `.app` | the certificate fails — stuck redex | `whnfCore_app_stuck` |
| `.app` | ι fires | `whnfCore_app_iota` |
| `.app` | ι declines — stuck application | `whnfCore_app_iota_none` |
| `.proj` | `reduceProjCore` fires: the field, head-normalised | `whnfCore_proj_fire` |
| `.proj` | `reduceProjCore` declines: the node itself | `whnfCore_proj_stuck` |
| `.letE` / `.bvar` | `throw` | nothing to prove (`; ⊤`) |

## The two deviations the twin carries at this body

1. **The batched β spine** (task #97-P6-9).  The twin's `.app` clause is
   `getAppSpine` + `whnfApp` + `betaPeel`, con-leche's own CACHED-tier
   clause, where the pure body re-enters the knot per argument.  The
   identification is con-leche's, not ours: `Verify/BetaSpine.lean`'s
   `whnfApp_sound` / `whnfApp_ksound` / `betaPeel_ksound` /
   `whnfCoreStepM_sound` prove the batched walk equals the chain over
   `Expr.instantiateList_cons`, and the arena's job is only to carry the
   denotation across.  `whnfCoreBody_app_batched` below is the statement of
   that carry.
2. **The stuck-tag probe** (task #97-P6-7's lever 2), which is the wrapper's
   and is closed in `Bridge/Core/Memo.lean`.

## Status

The step lemmas are CLOSED, and so is `whnfCoreBody_spec` (it was the
module's one `sorry`; the note at its site keeps round 3's inventory).  Nothing here
depends on the arm split (the coordinator's ruling after task #97-P3-0): a
pure step lemma is about con-leche's body, which is not split, and the twin's
side enters only at `whnfCoreBody_spec`.
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

/-! ## 2. The `.proj` clause's two exits

con-leche 8afe1815 split the clause: the scrutinee is reduced (by `whnf`, or
by the cheap `whnfCore` in the cheap mode), then the projection rule is
`reduceProjCore`, whose own five exits are `Walks/ProjCore.lean`'s.  So the
clause has two exits here: the rule does not fire (the input itself), or it
fires and the field is head-normalised in the same mode. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1072 whnfCoreBody — the
scrutinee's reduction, in the clause's mode, at the pure knot. -/
abbrev projScrut (mode : CheckMode) (env : Env) (c : Bool) (F d : Nat)
    (pe : Expr) : CheckM Expr :=
  if c then ConLeche.whnfCore mode env F d pe true
  else ConLeche.whnf mode env F d pe

/-- con-leche: ConLeche/Verify/Mono.lean:143 whnfCore_mono — the scrutinee's
reduction is fuel-monotone in either mode. -/
theorem projScrut_mono {c : Bool} {F F' d : Nat} {pe r : Expr} (hle : F ≤ F')
    (h : projScrut mode env c F d pe = .ok r) :
    projScrut mode env c F' d pe = .ok r := by
  cases c
  · exact ConLeche.whnf_mono hle h
  · exact ConLeche.whnfCore_mono hle h

/-- con-leche: ConLeche/Kernel/Core.lean:1072-1075 whnfCoreBody — **the rule
does not fire**: the projection is stuck and answers itself (con-leche's task
#323: its scrutinee as it was, not the reduced one). -/
theorem whnfCore_proj_stuck {c : Bool} {F d i : Nat} {sn : Name}
    {pe c' : Expr}
    (hs : projScrut mode env c F d pe = .ok c')
    (hr : ConLeche.reduceProjCoreFueled mode env F d sn i c' = .ok none) :
    ConLeche.whnfCore mode env (F + 1) d (.proj sn i pe) c =
      .ok (.proj sn i pe) := by
  simp only [ConLeche.reduceProjCoreFueled] at hr
  rw [ConLeche.whnfCore_succ]
  cases c <;>
    simp only [projScrut, ite_true, Bool.false_eq_true, ite_false] at hs <;>
    simp only [ConLeche.whnfCoreBody, ConLeche.whnf_def, ConLeche.whnfCore_def,
      ite_true, Bool.false_eq_true, ite_false, hs, hr, bind, Except.bind, pure,
      Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1072-1074 whnfCoreBody — **the rule
fires**: the selected field is head-normalised in the clause's mode. -/
theorem whnfCore_proj_fire {c : Bool} {F d i : Nat} {sn : Name}
    {pe c' m res : Expr}
    (hs : projScrut mode env c F d pe = .ok c')
    (hr : ConLeche.reduceProjCoreFueled mode env F d sn i c' = .ok (some m))
    (hk : ConLeche.whnfCore mode env F d m c = .ok res) :
    ConLeche.whnfCore mode env (F + 1) d (.proj sn i pe) c = .ok res := by
  simp only [ConLeche.reduceProjCoreFueled] at hr
  rw [ConLeche.whnfCore_succ]
  cases c <;>
    simp only [projScrut, ite_true, Bool.false_eq_true, ite_false] at hs <;>
    simp only [ConLeche.whnfCoreBody, ConLeche.whnf_def, ConLeche.whnfCore_def,
      ite_true, Bool.false_eq_true, ite_false, hs, hr, bind, Except.bind] <;>
    exact hk

/-! ## 3. The batched `.app` clause's identification

The twin does NOT run con-leche's `.app` clause: since task #97-P6-9 it runs
con-leche's **cached-tier** clause, the whole argument vector through one
`instantiateList` walk.  The ruling before DESIGN §8.7 licenses the move ("the
multi-substitution walk is fair game between the pure tier and the interned
tier, because con-leche itself makes that move between its PURE and its CACHED
tier") and names the debt: *the bridge owes the same equation con-leche's own
cached tier proves*.

It is proved, and it is con-leche's: `Verify/BetaSpine.lean`'s
`whnfApp_sound` (line 900), `whnfApp_ksound` (927), `betaPeel_ksound` (1017)
and `whnfCoreStepM_sound` (1095), over `Expr.instantiateList_cons`
(`Verify/InstList.lean`).  What this library owes is the *carry*: the twin's
handle-level walk denotes con-leche's `Expr`-level batched walk, which is the
`ExprOps` tier's `instantiateList` spec plus the spine lemmas of
`Bridge/ExprOps/Spine.lean`. -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1095 whnfCoreStepM_sound —
the batched `.app` clause's identification with the chained one.

**PROVED** (task #97-P3-Core round 6) over `Walks/BetaSpine.lean`: the
spine read (`getAppSpine_spec`), the head's normal form (`KnotSpec.whnfCore`),
`headAndArgs_spec`, then `spine_carry` — the twin's `whnfApp`/`betaPeel`
denote con-leche's pure mirrors at `pureFns mode env F` — and con-leche's
own `whnfApp_sound` for the chained side.  It inherited `sorryAx` only through
`iotaRecAt_spec` (`Walks/BetaSpine.lean` §2, the ι tower's entry point),
which is closed since; nothing under it is open now (task #97-MILESTONE).

**One added precondition, `hμ : mode.verifiedChecks = true`** (the body
theorem already has it): the twin's β site reads `CheckMode.betaSkip`, which
skips the per-redex certificate WHOLESALE at `.trusted` (`!mode.certs`),
where con-leche's spec (and its mirror) run it — so at the trusted mode a
redex whose certificate fails is stuck in the spec and reduced by the twin.
`betaSkip_eq_fires` is the two reads' agreement under `certs`, con-leche's
`certs_of_verifiedChecks` (`Verify/BetaGate.lean:126`). -/
theorem whnfCoreBody_app_batched {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (c : Bool)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : (i.tag == ETag.app) = true) :
    ⦃fun s => s = s₀⦄
      whnfCoreBody mode (coreKnot mode fe id fuel) fe c d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (fun F d e => ConLeche.whnfCore mode env F d e c) d e
          s'.store r; ⊤⦄ := by
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case app f a =>
    dsimp only
    -- stage 1: the spine, in one read
    refine triple_seq (getAppSpine_spec coreWalkFuel s₀ i e hok.state hden) ?_
    rintro sp s1 ⟨hs1, hsp1, hsp2, hsp3, hsp4⟩
    subst s1
    -- stage 2: the head's normal form
    refine triple_seq (hsim.whnfCore s₀ d sp.1 _ hok hsp1
      (Expr.WScoped.getAppFn hw)) ?_
    rintro vh s2 ⟨hok2, hx2, hp2, Vh, hdv, hwv, F0, hF0⟩
    -- stage 3: the reduct's own spine
    refine triple_seq (headAndArgs_spec s2 vh Vh hok2.state hdv) ?_
    rintro hv' s3 ⟨hs3, hh1, hh2⟩
    subst s3
    -- stage 4: the batched walk, carried
    have hctx : SpineCtx d sp.2.1 sp.2.2 e.getAppFn e.getAppArgs s2.store :=
      ⟨denoteEList_ext' hx2 hsp2, Expr.WScoped.getAppArgs hw, hsp3,
        fun j hj => denote_ext (hsp4 j hj) hx2⟩
    have hsame : (vh == sp.1) = true →
        Vh = Expr.mkAppN e.getAppFn (e.getAppArgs.take 0) := by
      intro hb
      have heq : vh = sp.1 := beq_iff_eq.mp hb
      rw [heq, denote_ext hsp1 hx2] at hdv
      simpa [Expr.mkAppN] using (Option.some.inj hdv).symm
    refine triple_mono ((spine_carry henv hμ hsim d sp.2.1 sp.2.2 e.getAppFn
      e.getAppArgs (sp.2.1.size - 0)).1 vh hv'.1 hv'.2 (vh == sp.1) 0 s2 Vh
      rfl hok2 hctx hdv hwv hh1 hh2 hsame) ?_
    rintro r s' ⟨hck, hx, hp, v', hdv', hwv', F, hF⟩
    refine ⟨hck, hx2.trans hx, by rw [hp, hp2], v', hdv', hwv', ?_⟩
    -- the chained side: con-leche's own identification
    obtain ⟨F', hF'⟩ := ConLeche.whnfApp_sound e.getAppArgs e.getAppFn Vh v'
      F0 F hF0 (by simpa using hF)
    rw [Expr.mkAppN_getApp] at hF'
    exact ⟨F', hF'⟩
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-! ## 4. The body theorem, skeletonised (task #97-P3-Core round 5)

`whnfCoreBody_spec` is proved from THREE children, one per group of the
twin's `view` dispatch, each a triple at the same body under a tag
hypothesis: the batched `.app` clause (`whnfCoreBody_app_batched` above), the
`.proj` clause (`whnfCoreBody_proj`, below), and every other tag
(`whnfCoreBody_leaf`: the six values answer themselves, `.letE`/`.bvar`
throw).  The parent is a case split on the tag and nothing else, so the
body closed when its three children did (all three are proved). -/

/-- con-leche: ConLeche/Kernel/Core.lean:1028-1033 whnfCoreBody — **the leaf
clauses**: at a tag that is neither `.app` nor `.proj`, the six values answer
themselves and `.letE`/`.bvar` throw. -/
theorem whnfCoreBody_leaf {fe : IFEnv} {fuel : Nat} (c : Bool)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (hna : i.tag ≠ ETag.app) (hnp : i.tag ≠ ETag.proj) :
    ⦃fun s => s = s₀⦄
      whnfCoreBody mode (coreKnot mode fe id fuel) fe c d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (fun F d e => ConLeche.whnfCore mode env F d e c) d e
          s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  -- the value arms answer the handle itself
  have hval : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l) ∨
      (∃ t b m, e = .lam t b m) ∨ (∃ t b m, e = .forallE t b m) →
      SimE (fun F d e => ConLeche.whnfCore mode env F d e c) d e s₀.store i :=
    fun hs => ⟨e, hden, hw, 1, whnfCore_of_stuck hs 0 d⟩
  refine view_bind_triple hv ?_
  cases v with
  | app f a => exact absurd htg hna
  | proj n k sub => exact absurd htg hnp
  | letE ty w b => vcgen
  | bvar k => vcgen
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hden
    vcgen; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inl ⟨k, t', rfl⟩)⟩
  | sort u =>
    obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hden
    vcgen; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inl ⟨l, rfl⟩))⟩
  | const n us =>
    obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hden
    vcgen; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inr (Or.inl ⟨nm, ls, rfl⟩)))⟩
  | lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    vcgen; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, rfl⟩))))⟩
  | lam ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_lam_inv hwf hv hden
    vcgen; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨et, eb, m, rfl⟩)))))⟩
  | forallE ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_forallE_inv hwf hv hden
    vcgen; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨et, eb, m, rfl⟩)))))⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1062-1075 whnfCoreBody — **the
`.proj` clause**: reduce the scrutinee (by `whnf`, or by the cheap `whnfCore`
in the cheap mode), run the projection rule (`reduceProjCore_spec`,
`Walks/ProjCore.lean`), and head-normalise a fired field in the same mode;
when the rule does not fire, the node itself. -/
theorem whnfCoreBody_proj {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel) (c : Bool)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : i.tag = ETag.proj) :
    ⦃fun s => s = s₀⦄
      whnfCoreBody mode (coreKnot mode fe id fuel) fe c d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (fun F d e => ConLeche.whnfCore mode env F d e c) d e
          s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  cases v
  case proj sn k pe =>
    obtain ⟨nm, es, rfl, hsn, hpe⟩ := denote_proj_inv hwf hv hden
    have hwes : Expr.WScoped d es := by simpa [Expr.WScoped] using hw
    refine view_bind_triple hv ?_
    dsimp only
    -- stage 1: the scrutinee, in the clause's mode
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
    -- stage 2: the projection rule
    refine triple_seq (reduceProjCore_spec henv hsim s1 d sn k e0 nm v0 hok1
      (denoteN_ext hsn hx1) hv0 hwv0) ?_
    rintro o s2 ⟨hok2, hx2, hp2, ov, hov, hwov, F2, hF2⟩
    have hx02 : Ext s₀.store s2.store := hx1.trans hx2
    have hp02 : s2.pins = s₀.pins := hp2.trans hp1
    have hs' := projScrut_mono (Nat.le_max_left F1 F2) hF1
    have hr' := reduceProjCoreFueled_mono (Nat.le_max_right F1 F2) hF2
    cases o with
    | none =>
      -- the rule does not fire: the node itself
      simp only [denoteEO, Option.some.injEq] at hov
      subst hov
      dsimp only
      vcgen; subst_vars
      exact ⟨hok2, hx02, hp02, .proj nm k es, denote_ext hden hx02, hw,
        max F1 F2 + 1, whnfCore_proj_stuck hs' hr'⟩
    | some m =>
      -- the rule FIRES: head-normalise the selected field
      simp only [denoteEO, Option.map_eq_some_iff] at hov
      obtain ⟨M, hdM, rfl⟩ := hov
      dsimp only
      refine triple_mono (hsim.whnfCore s2 d m M hok2 hdM (hwov M rfl)) ?_
      rintro r s3 ⟨hok3, hx3, hp3, w, hw3, hww, F3, hF3⟩
      refine ⟨hok3, hx02.trans hx3, hp3.trans hp02, w, hw3, hww,
        max (max F1 F2) F3 + 1, ?_⟩
      exact whnfCore_proj_fire
        (projScrut_mono (Nat.le_max_left _ _) hs')
        (reduceProjCoreFueled_mono (Nat.le_max_left _ _) hr')
        (ConLeche.whnfCore_mono (Nat.le_max_right _ _) hF3)
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

/-! ## 5. The body theorem -/

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfCoreBodyC_sim —
**THEOREM 1 for `whnfCoreBody`**, at a knot record one fuel level down.

**PROVED from its three children** (round 5): a case split on the tag over
`whnfCoreBody_app_batched` (closed since), `whnfCoreBody_proj` (proved, over the
walk `projLitToCtor_spec`, closed too) and `whnfCoreBody_leaf` (CLOSED).  The note
below is round 3's inventory, kept for its reasons:

* the `.app` arm is `whnfCoreBody_app_batched` above (the batched spine's
  carry, which waits on `ExprOps.instantiateList_spec`);
* the `.proj` arm needs `projLitToCtor`, `projCertAt` and `iotaRec` as callee
  rules — three walks of `Arena/Core.lean` that are NOT knot slots and
  therefore need their own `BodySpec`-shaped theorems, which this round did
  not write;
* the `.letE` and `.bvar` arms are free (`; ⊤` claims nothing of a `fail`);
* the six value arms are `whnfCore_of_stuck`, closed.

The step lemmas above are what the arms consume once the twin's arms are
split (the coordinator's ruling after task #97-P3-0): each becomes one
`exact` in a `next =>` block, in `ExprOps/Inst1.lean`'s shape. -/
theorem whnfCoreBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (c : Bool) :
    BodySpec mode env fe (whnfCoreBody mode (coreKnot mode fe id fuel) fe c)
      (fun F d e => ConLeche.whnfCore mode env F d e c) := by
  intro s₀ d i e hok hden hw
  by_cases ha : i.tag = ETag.app
  · exact whnfCoreBody_app_batched henv hμ hsim c s₀ d i e hok hden hw
      (by simp [ha])
  by_cases hp : i.tag = ETag.proj
  · exact whnfCoreBody_proj henv hsim c s₀ d i e hok hden hw hp
  exact whnfCoreBody_leaf c s₀ d i e hok hden hw ha hp

section Census

#print axioms whnfCore_proj_stuck
#print axioms whnfCore_proj_fire
#print axioms whnfCoreBody_leaf
/-! No `sorryAx` expected: `whnfCoreBody_app_batched` read it only through
`Walks/BetaSpine.lean`'s `iotaRecAt_spec` (round 6), which is closed since. -/
#print axioms whnfCoreBody_app_batched
#print axioms whnfCoreBody_proj
#print axioms whnfCoreBody_spec

end Census

end ConRon.Bridge.Core
