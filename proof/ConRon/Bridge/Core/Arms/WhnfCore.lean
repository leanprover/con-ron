/-
# `ConRon.Bridge.Core.Arms.WhnfCore` — Theorem 1 for `whnfCoreBody`

DESIGN §8.2, task #97s's **rule 8**: *one step lemma per clause of the PURE
function, not per constructor of the subject*.  This module is that inventory
for `ConLeche/Kernel/Core.lean:968-1052 whnfCoreBody` — twelve exits over four
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
| `.proj` | the table fires and the certificate succeeds | `whnfCore_proj_fire` |
| `.proj` | the table fires, certificate fails | `whnfCore_proj_cert_false` |
| `.proj` | the guards fail | `whnfCore_proj_guard` |
| `.proj` | the scrutinee's head is not a constant | `whnfCore_proj_head` |
| `.proj` | no table entry | `whnfCore_proj_none` |
| `.letE` / `.bvar` | `throw` | nothing to prove (`⇓?`) |

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

The step lemmas are CLOSED; `whnfCoreBody_spec` is **`sorry`** — see the note
at its site and DESIGN §8's task section for what is missing.  Nothing here
depends on the arm split (the coordinator's ruling after task #97-P3-0): a
pure step lemma is about con-leche's body, which is not split, and the twin's
side enters only at `whnfCoreBody_spec`.
-/
import ConRon.Bridge.Core.Memo

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The `.app` clause's five exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:977-1000 whnfCoreBody — the β arm
with the **gate firing** (con-leche's task #161): the validated annotation
says the binder is never a proposition, so no argument certificate runs. -/
theorem whnfCore_app_beta_gate {F d : Nat} {f a ty body res : Expr}
    {mb : BinderMeta}
    (hf : ConLeche.whnfCore mode env F d f = .ok (.lam ty body mb))
    (hg : ConLeche.betaGateFires mode mb.pw = true)
    (hr : ConLeche.whnfCore mode env F d (body.instantiate1 a) = .ok res) :
    ConLeche.whnfCore mode env (F + 1) d (.app f a) = .ok res := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnfCore_def, hf, hg, bind,
    Except.bind, if_true]
  exact hr

/-- con-leche: ConLeche/Kernel/Core.lean:977-1000 whnfCoreBody — the β arm
with the **argument certificate**: the argument's io-grade type is defeq to
the binder's domain, so the redex reduces. -/
theorem whnfCore_app_beta_cert {F d : Nat} {f a ty body ta res : Expr}
    {mb : BinderMeta}
    (hf : ConLeche.whnfCore mode env F d f = .ok (.lam ty body mb))
    (hg : ConLeche.betaGateFires mode mb.pw = false)
    (hta : ConLeche.inferTypeIO mode env F d a = .ok ta)
    (hde : ConLeche.isDefEqCore mode env F d ta ty = .ok true)
    (hr : ConLeche.whnfCore mode env F d (body.instantiate1 a) = .ok res) :
    ConLeche.whnfCore mode env (F + 1) d (.app f a) = .ok res := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnfCore_def,
    ConLeche.inferTypeIO_def, ConLeche.defeq_def, hf, hg, hta, hde, bind,
    Except.bind, if_false, Bool.false_eq_true, if_true]
  exact hr

/-- con-leche: ConLeche/Kernel/Core.lean:997-1000 whnfCoreBody — the β arm
whose certificate FAILS: the redex stays stuck, which is sound and
unreachable for well-typed input. -/
theorem whnfCore_app_stuck {F d : Nat} {f a ty body ta : Expr}
    {mb : BinderMeta}
    (hf : ConLeche.whnfCore mode env F d f = .ok (.lam ty body mb))
    (hg : ConLeche.betaGateFires mode mb.pw = false)
    (hta : ConLeche.inferTypeIO mode env F d a = .ok ta)
    (hde : ConLeche.isDefEqCore mode env F d ta ty = .ok false) :
    ConLeche.whnfCore mode env (F + 1) d (.app f a) =
      .ok (.app (.lam ty body mb) a) := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnfCore_def,
    ConLeche.inferTypeIO_def, ConLeche.defeq_def, hf, hg, hta, hde, bind,
    Except.bind, if_false, Bool.false_eq_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1001-1004 whnfCoreBody — the ι arm:
the head is not a λ and the recursor rule **fires**. -/
theorem whnfCore_app_iota {F d : Nat} {f a f' e'' res : Expr}
    (hf : ConLeche.whnfCore mode env F d f = .ok f')
    (hne : ∀ ty body mb, f' ≠ .lam ty body mb)
    (hi : ConLeche.iotaRec mode (ConLeche.pureFns mode env F) env d
      (.app f' a) = .ok (some e''))
    (hr : ConLeche.whnfCore mode env F d e'' = .ok res) :
    ConLeche.whnfCore mode env (F + 1) d (.app f a) = .ok res := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnfCore_def, hf, bind,
    Except.bind]
  cases f'
  case lam ty b m => exact absurd rfl (hne ty b m)
  all_goals
    simp only [hi, bind, Except.bind, ConLeche.whnfCore_def]
    exact hr

/-- con-leche: ConLeche/Kernel/Core.lean:1001-1004 whnfCoreBody — the ι arm
that **declines**: the application is stuck at its normalized head. -/
theorem whnfCore_app_iota_none {F d : Nat} {f a f' : Expr}
    (hf : ConLeche.whnfCore mode env F d f = .ok f')
    (hne : ∀ ty body mb, f' ≠ .lam ty body mb)
    (hi : ConLeche.iotaRec mode (ConLeche.pureFns mode env F) env d
      (.app f' a) = .ok none) :
    ConLeche.whnfCore mode env (F + 1) d (.app f a) = .ok (.app f' a) := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnfCore_def, hf, bind,
    Except.bind]
  cases f'
  case lam ty b m => exact absurd rfl (hne ty b m)
  all_goals simp only [hi, bind, Except.bind, pure, Except.pure]

/-! ## 2. The `.proj` clause's five exits

All five run the same prefix — `r.whnf depth pe` then `projLitToCtor` — so
each lemma takes that prefix's two answers as hypotheses and differs only in
what the table and the certificate say. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1005-1037 whnfCoreBody — **no table
entry**: the projection stays stuck at the reduced scrutinee. -/
theorem whnfCore_proj_none {F d i : Nat} {sn : Name} {pe e0 e' : Expr}
    (hw : ConLeche.whnf mode env F d pe = .ok e0)
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d e0
      = .ok e')
    (ht : env.findProj? sn i = none) :
    ConLeche.whnfCore mode env (F + 1) d (.proj sn i pe) =
      .ok (.proj sn i e') := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnf_def, hw, hl, ht, bind,
    Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1035 whnfCoreBody — the table
fires, the guards hold and **the certificate succeeds**: the projection
selects its field and head-normalizes it. -/
theorem whnfCore_proj_fire {F d i : Nat} {sn : Name} {pe e0 e' res : Expr}
    {entry : ProjEntry} {c : Name} {us : List Level}
    (hw : ConLeche.whnf mode env F d pe = .ok e0)
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d e0
      = .ok e')
    (ht : env.findProj? sn i = some entry)
    (hh : e'.getAppFn = .const c us)
    (hg : c = entry.ctor ∧ i < entry.numFields ∧
      e'.getAppArgs.length = entry.numParams + entry.numFields ∧
      us.length = entry.levelParams.length ∧ entry.fireOk us = true)
    (hcert : ConLeche.projCertAt (ConLeche.pureFns mode env F) env d
      mode.verifiedChecks mode.betaGate c us e'.getAppArgs = .ok true)
    (hr : ConLeche.whnfCore mode env F d
      (e'.getAppArgs.getD (entry.numParams + i) (.bvar 0)) = .ok res) :
    ConLeche.whnfCore mode env (F + 1) d (.proj sn i pe) = .ok res := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnf_def, ConLeche.whnfCore_def,
    hw, hl, ht, hh, bind, Except.bind]
  rw [if_pos hg, hcert]
  simp only [bind, Except.bind, if_true]
  exact hr

/-- con-leche: ConLeche/Kernel/Core.lean:1032-1035 whnfCoreBody — the table
fires and **the certificate fails**: stuck, at the reduced scrutinee. -/
theorem whnfCore_proj_cert_false {F d i : Nat} {sn : Name} {pe e0 e' : Expr}
    {entry : ProjEntry} {c : Name} {us : List Level}
    (hw : ConLeche.whnf mode env F d pe = .ok e0)
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d e0
      = .ok e')
    (ht : env.findProj? sn i = some entry)
    (hh : e'.getAppFn = .const c us)
    (hg : c = entry.ctor ∧ i < entry.numFields ∧
      e'.getAppArgs.length = entry.numParams + entry.numFields ∧
      us.length = entry.levelParams.length ∧ entry.fireOk us = true)
    (hcert : ConLeche.projCertAt (ConLeche.pureFns mode env F) env d
      mode.verifiedChecks mode.betaGate c us e'.getAppArgs = .ok false) :
    ConLeche.whnfCore mode env (F + 1) d (.proj sn i pe) =
      .ok (.proj sn i e') := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnf_def, hw, hl, ht, hh, bind,
    Except.bind]
  rw [if_pos hg, hcert]
  simp only [bind, Except.bind, Bool.false_eq_true, if_false, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1034 whnfCoreBody — the table fires
but **a guard fails** (wrong constructor, index out of range, arity mismatch,
level-arity mismatch, or the possibly-`Prop` fence): stuck. -/
theorem whnfCore_proj_guard {F d i : Nat} {sn : Name} {pe e0 e' : Expr}
    {entry : ProjEntry} {c : Name} {us : List Level}
    (hw : ConLeche.whnf mode env F d pe = .ok e0)
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d e0
      = .ok e')
    (ht : env.findProj? sn i = some entry)
    (hh : e'.getAppFn = .const c us)
    (hg : ¬ (c = entry.ctor ∧ i < entry.numFields ∧
      e'.getAppArgs.length = entry.numParams + entry.numFields ∧
      us.length = entry.levelParams.length ∧ entry.fireOk us = true)) :
    ConLeche.whnfCore mode env (F + 1) d (.proj sn i pe) =
      .ok (.proj sn i e') := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnf_def, hw, hl, ht, hh, bind,
    Except.bind]
  rw [if_neg hg]
  simp only [pure, Except.pure]

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
**OPEN** (task #97-P3-Core): the batched `.app` clause's identification with
the chained one.  The `Expr`-level half is con-leche's (cited above); what is
owed here is the denotation carry for `getAppSpine`, `headAndArgs`,
`whnfApp` and `betaPeel`, whose `ExprOps`-tier callee rules are
`Bridge/ExprOps/Spine.lean`'s and whose `instantiateList` rule is
`Bridge/ExprOps/Inst1.lean`'s — the latter still `sorry` at its
`instantiateList_spec` (task #97-P3-0's open list). -/
theorem whnfCoreBody_app_batched {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : (i.tag == ETag.app) = true) :
    ⦃fun s => ⌜s = s₀⌝⦄
      whnfCoreBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnfCore mode env) d e s'.store r⌝⦄ := by
  sorry

/-! ## 4. The body theorem, skeletonised (task #97-P3-Core round 5)

`whnfCoreBody_spec` is proved from THREE children, one per group of the
twin's `view` dispatch, each a triple at the same body under a tag
hypothesis: the batched `.app` clause (`whnfCoreBody_app_batched` above), the
`.proj` clause (`whnfCoreBody_proj`, below), and every other tag
(`whnfCoreBody_leaf`: the six values answer themselves, `.letE`/`.bvar`
throw).  The parent is a case split on the tag and nothing else, so the
`sorry`s the Core tier owes at this body are exactly the children's. -/

/-- con-leche: ConLeche/Kernel/Core.lean:968-975 whnfCoreBody — **the leaf
clauses**: at a tag that is neither `.app` nor `.proj`, the six values answer
themselves and `.letE`/`.bvar` throw. -/
theorem whnfCoreBody_leaf {fe : IFEnv} {fuel : Nat}
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (hna : i.tag ≠ ETag.app) (hnp : i.tag ≠ ETag.proj) :
    ⦃fun s => ⌜s = s₀⌝⦄
      whnfCoreBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnfCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  -- the value arms answer the handle itself
  have hval : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l) ∨
      (∃ t b m, e = .lam t b m) ∨ (∃ t b m, e = .forallE t b m) →
      SimE (ConLeche.whnfCore mode env) d e s₀.store i :=
    fun hs => ⟨e, hden, hw, 1, whnfCore_of_stuck hs 0 d⟩
  refine view_bind_triple hv ?_
  cases v with
  | app f a => exact absurd htg hna
  | proj n k sub => exact absurd htg hnp
  | letE ty w b => mvcgen; exact fun h => h.elim
  | bvar k => mvcgen; exact fun h => h.elim
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inl ⟨k, t', rfl⟩)⟩
  | sort u =>
    obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inl ⟨l, rfl⟩))⟩
  | const n us =>
    obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inr (Or.inl ⟨nm, ls, rfl⟩)))⟩
  | lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, rfl⟩))))⟩
  | lam ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_lam_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨et, eb, m, rfl⟩)))))⟩
  | forallE ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_forallE_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hval (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨et, eb, m, rfl⟩)))))⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1005-1037 whnfCoreBody — **the
`.proj` clause**: normalise the scrutinee, expand a string literal, consult
the projection table, and fire behind the guards and the certificate.

**OPEN**.  Callee rules: `KnotSpec.whnf'`, `projLitToCtor_spec`
(`Walks/Owed.lean`, open), `getAppFn`/`getAppArgs` (`ExprOps` tier),
`IProjEntry.fireOk_spec` and `projCertAt_spec` (`Walks/Proj.lean`, closed),
`KnotSpec.whnfCore'`; pure side `whnfCore_proj_{none,fire,cert_false,guard}`
above plus the non-constant-head exit. -/
theorem whnfCoreBody_proj {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : i.tag = ETag.proj) :
    ⦃fun s => ⌜s = s₀⌝⦄
      whnfCoreBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnfCore mode env) d e s'.store r⌝⦄ := by
  sorry

/-! ## 5. The body theorem -/

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfCoreBodyC_sim —
**THEOREM 1 for `whnfCoreBody`**, at a knot record one fuel level down.

**OPEN** (task #97-P3-Core).  What is missing, arm by arm:

* the `.app` arm is `whnfCoreBody_app_batched` above (the batched spine's
  carry, which waits on `ExprOps.instantiateList_spec`);
* the `.proj` arm needs `projLitToCtor`, `projCertAt` and `iotaRec` as callee
  rules — three walks of `Arena/Core.lean` that are NOT knot slots and
  therefore need their own `BodySpec`-shaped theorems, which this round did
  not write;
* the `.letE` and `.bvar` arms are free (`⇓?` claims nothing of a `fail`);
* the six value arms are `whnfCore_of_stuck`, closed.

The step lemmas above are what the arms consume once the twin's arms are
split (the coordinator's ruling after task #97-P3-0): each becomes one
`exact` in a `next =>` block, in `ExprOps/Inst1.lean`'s shape. -/
theorem whnfCoreBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe (whnfCoreBody mode (coreKnot mode fe id fuel) fe)
      (ConLeche.whnfCore mode env) := by
  intro s₀ d i e hok hden hw
  by_cases ha : i.tag = ETag.app
  · exact whnfCoreBody_app_batched henv hsim s₀ d i e hok hden hw
      (by simp [ha])
  by_cases hp : i.tag = ETag.proj
  · exact whnfCoreBody_proj henv hsim s₀ d i e hok hden hw hp
  exact whnfCoreBody_leaf s₀ d i e hok hden hw ha hp

end ConRon.Bridge.Core
