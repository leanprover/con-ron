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
import ConRon.Bridge.Core.Walks.Owed
import ConRon.Bridge.Core.Walks.ProjLit
import ConRon.Bridge.Core.Walks.Proj

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

/-- con-leche: ConLeche/Kernel/Core.lean:1005-1037 whnfCoreBody — the table
fires but **the scrutinee's head is not a constant**: stuck. -/
theorem whnfCore_proj_head {F d i : Nat} {sn : Name} {pe e0 e' : Expr}
    {entry : ProjEntry}
    (hw : ConLeche.whnf mode env F d pe = .ok e0)
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d e0
      = .ok e')
    (ht : env.findProj? sn i = some entry)
    (hh : ∀ c us, e'.getAppFn ≠ .const c us) :
    ConLeche.whnfCore mode env (F + 1) d (.proj sn i pe) =
      .ok (.proj sn i e') := by
  rw [ConLeche.whnfCore_succ]
  simp only [ConLeche.whnfCoreBody, ConLeche.whnf_def, hw, hl, ht, bind,
    Except.bind]
  first
    | rfl
    | (split
       · rename_i c us heq; exact absurd heq (hh c us)
       · rfl)

/-- con-leche: none — an in-range `getD` is the element, whatever the
default (the twin's default is an interned `.bvar 0` handle, con-leche's the
term `.bvar 0`). -/
theorem getD_of_lt {α : Type} {l : List α} {i : Nat} {a : α}
    (h : i < l.length) : l.getD i a = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ### The `.proj` clause's callee rules in ANSWER shape

Round 3's rule: a walk whose subject is another walk's answer must not take
that answer's denotation as an explicit argument.  In the `.proj` clause the
scrutinee of `projLitToCtor` is `whnf`'s answer, the table entry of `fireOk`
is `findProj?`'s, and the constructor, levels and arguments of `projCertAt`
are read off `projLitToCtor`'s answer — so each gets its primed form here,
four lines over the published one. -/

/-- con-leche: none — `projLitToCtor_spec` in answer shape. -/
theorem projLitToCtor_spec' {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (s₀ : AState) (d : Nat) (h : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hdw : ∃ x, denoteE s₀.store h = some x ∧ Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projLitToCtor (coreKnot mode fe id fuel) fe d h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ x, denoteE s₀.store h = some x →
          SimEOp (fun F => ConLeche.projLitToCtorFueled mode env F d x) d
            s'.store r⌝⦄ := by
  obtain ⟨x, hx, hw⟩ := hdw
  have hs := projLitToCtor_spec hsim s₀ d h x hok hx hw
  mvcgen [hs]
  intro hck hxt hp hr
  refine ⟨hck, hxt, hp, fun x' hx' => ?_⟩
  obtain rfl := Option.some.inj (hx.symm.trans hx')
  exact hr

/-- con-leche: none — `IProjEntry.fireOk_spec` in answer shape. -/
theorem IProjEntry.fireOk_spec' {fe : IFEnv} (s₀ : AState)
    (entry : IProjEntry) (us : LsIdx) (hok : CheckOK mode env fe s₀)
    (hpre : ∃ p ls, denoteProjEntry s₀.store entry = some p ∧
      denoteLs s₀.store.lss us = some ls) :
    ⦃fun s => ⌜s = s₀⌝⦄ entry.fireOk us
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        ∀ p ls, denoteProjEntry s₀.store entry = some p →
          denoteLs s₀.store.lss us = some ls → b = p.fireOk ls⌝⦄ := by
  obtain ⟨p, ls, hp, hls⟩ := hpre
  have hs := IProjEntry.fireOk_spec s₀ entry us p ls hok hp hls
  mvcgen [hs]
  intro hck hst hpn hb
  refine ⟨hck, hst, hpn, fun p' ls' hp' hls' => ?_⟩
  obtain rfl := Option.some.inj (hp.symm.trans hp')
  obtain rfl := Option.some.inj (hls.symm.trans hls')
  exact hb

/-- con-leche: none — `projCertAt_spec` in answer shape. -/
theorem projCertAt_spec' {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (henv : ConLeche.EnvWF env)
    (s₀ : AState) (d : Nat) (verified lic : Bool) (c : NIdx) (us : LsIdx)
    (args : List EIdx) (hok : CheckOK mode env fe s₀)
    (hpre : ∃ cn ls xs, denoteN s₀.store.ns c = some cn ∧
      denoteLs s₀.store.lss us = some ls ∧
      Frontend.denoteEList s₀.store args = some xs ∧
      ∀ x ∈ xs, Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projCertAt (coreKnot mode fe id fuel) fe d verified lic c
        us args
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ cn ls xs, denoteN s₀.store.ns c = some cn →
          denoteLs s₀.store.lss us = some ls →
          Frontend.denoteEList s₀.store args = some xs →
          SimBOp
            (fun F => ConLeche.projCertAtFueled mode env F d verified lic cn
              ls xs) b⌝⦄ := by
  obtain ⟨cn, ls, xs, hc, hus, hxs, hw⟩ := hpre
  have hs := projCertAt_spec hsim henv s₀ d verified lic c us args cn ls xs
    hok hc hus hxs hw
  mvcgen [hs]
  intro hck hxt hp hb
  refine ⟨hck, hxt, hp, fun cn' ls' xs' hc' hus' hxs' => ?_⟩
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  obtain rfl := Option.some.inj (hus.symm.trans hus')
  obtain rfl := Option.some.inj (hxs.symm.trans hxs')
  exact hb

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

**PROVED** (round 5), in eleven stages chained by `triple_seq`
(`Memo.lean`), each stage's facts introduced by name: `KnotSpec.whnf`,
`projLitToCtor_spec`, `IFEnv.findProj?_spec`, `getAppFn_spec`, the head's
`view`, `getAppArgs_spec`, `viewLsLen`, `IProjEntry.fireOk_spec`, the guard,
`internE (.bvar 0)`, `projCertAt_spec`, `KnotSpec.whnfCore`; the five exits
are `whnfCore_proj_{none,head,guard,cert_false,fire}` above.  **Sorry-free**
since `projLitToCtor_spec` closed (`Walks/ProjLit.lean`, same round).  Every callee is applied at a subject whose
denotation the previous stage NAMED, so the published (explicit-argument)
forms serve and the primed forms above are for `mvcgen`-driven callers. -/
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
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  cases v
  case proj sn k pe =>
    obtain ⟨nm, es, rfl, hsn, hpe⟩ := denote_proj_inv hwf hv hden
    have hwes : Expr.WScoped d es := by simpa [Expr.WScoped] using hw
    refine view_bind_triple hv ?_
    dsimp only
    -- stage 1: the scrutinee's head normal form
    refine triple_seq (hsim.whnf s₀ d pe es hok hpe hwes) ?_
    rintro e0 s1 ⟨hok1, hx1, hp1, v0, hv0, hwv0, F1, hF1⟩
    -- stage 2: the string-literal expansion
    refine triple_seq (projLitToCtor_spec hsim s1 d e0 v0 hok1 hv0 hwv0) ?_
    rintro e' s2 ⟨hok2, hx2, hp2, v', hv', hwv', F2, hF2⟩
    have hsn2 : denoteN s2.store.ns sn = some nm := denoteN_ext hsn (hx1.trans hx2)
    -- the stuck exit, shared by four of the five exits: rebuild the node
    have hstuck : ∀ (s : AState), CheckOK mode env fe s →
        Ext s₀.store s.store → s.pins = s₀.pins →
        denoteE s.store e' = some v' → denoteN s.store.ns sn = some nm →
        (∃ F, ConLeche.whnfCore mode env F d (.proj nm k es) =
          .ok (.proj nm k v')) →
        ⦃fun s' => ⌜s' = s⌝⦄ internE (.proj sn k e')
        ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
            s'.pins = s₀.pins ∧
            SimE (ConLeche.whnfCore mode env) d (.proj nm k es) s'.store r⌝⦄ := by
      intro s hs hxs hps hes hns hF
      have hvw : s.store.ViewOK (.proj sn k e') :=
        viewOK_proj (nview_isSome_of_denote hns) (by rw [hes]; rfl)
      refine triple_mono (internE_spec s _ hs.state.wf hvw) ?_
      rintro r s' ⟨hwf', hx', _hbm, _hl, _hsc, _hm, hc', hp', _hview, hden'⟩
      refine ⟨hs.mono ⟨hwf'⟩ hx' hc' hp', hxs.trans hx', hp'.trans hps,
        .proj nm k v', ?_, by simpa [Expr.WScoped] using hwv', hF⟩
      rw [hden']
      simp only [denoteEView, denoteN_ext hns hx', denote_ext hes hx', opt2]
    -- stage 3: the table
    refine triple_seq (IFEnv.findProj?_spec s2 sn k nm hok2 hsn2) ?_
    rintro oe s3 ⟨hok3, hx3, _hm3, _hc3, hp3, hsome, hnone⟩
    have hv'3 := denote_ext hv' hx3
    have hsn3 := denoteN_ext hsn2 hx3
    have hx03 : Ext s₀.store s3.store := hx1.trans (hx2.trans hx3)
    have hp03 : s3.pins = s₀.pins := hp3.trans (hp2.trans hp1)
    have hwhnf : ConLeche.whnf mode env (max F1 F2) d es = .ok v0 :=
      ConLeche.whnf_mono (Nat.le_max_left _ _) hF1
    have hplc : ConLeche.projLitToCtor (ConLeche.pureFns mode env (max F1 F2))
        env d v0 = .ok v' :=
      projLitToCtorFueled_mono (Nat.le_max_right _ _) hF2
    cases oe with
    | none =>
      exact hstuck s3 hok3 hx03 hp03 hv'3 hsn3
        ⟨max F1 F2 + 1, whnfCore_proj_none hwhnf hplc (hnone rfl)⟩
    | some entry =>
      obtain ⟨pe', hpd, hfp⟩ := hsome entry rfl
      have hwf3 := hok3.state.wf
      obtain ⟨rk3, hrk3⟩ := hok3.state.wf
      -- stage 4: the head of the expanded scrutinee
      refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s3 e' hok3.state
        (by rw [hv'3]; rfl)) ?_
      rintro hd s4 ⟨hs4, hrelF⟩
      subst s4
      have hdd : denoteE s3.store hd = some v'.getAppFn := hrelF v' hv'3
      obtain ⟨vh, hvh⟩ := denoteE_view hdd
      refine view_bind_triple hvh ?_
      cases vh
      case const c us =>
        obtain ⟨cn, ls, hgf, hcn, hus⟩ := denote_const_inv hwf3 hvh hdd
        dsimp only
        -- stage 5: the spine's arguments
        refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s3 e'
          hok3.state (by rw [hv'3]; rfl)) ?_
        rintro args s5 ⟨hs5, hrelA⟩
        subst s5
        have hargs : Frontend.denoteEList s3.store args = some v'.getAppArgs :=
          hrelA v' hv'3
        -- stage 6: the level list's length
        refine triple_seq (viewLsLen_spec s3 us) ?_
        rintro ol s6 ⟨hs6, hol⟩
        subst s6
        rw [viewLen_of_denoteLs hus] at hol
        subst hol
        dsimp only
        -- stage 7: the possibly-`Prop` fence
        obtain ⟨hsnp, hlps, hctor, _hbody, _hfs, _hss, _hidx, hnp, hnf, _hoff⟩ :=
          denoteProjEntry_inv hpd
        refine triple_seq (IProjEntry.fireOk_spec s3 entry us pe' ls hok3 hpd
          hus) ?_
        rintro fok s7 ⟨hok7, hst7, hp7, hfok⟩
        subst hfok
        have hc_iff : c = entry.ctor ↔ cn = pe'.ctor := by
          constructor
          · rintro rfl; exact Option.some.inj (hcn.symm.trans hctor)
          · rintro rfl; exact denoteN_inj hrk3.nsWF hcn hctor
        have hlen_a : args.length = v'.getAppArgs.length :=
          (denoteEList_len hargs).symm
        have hlen_l : ls.length = pe'.levelParams.length ↔
            ls.length = entry.levelParams.length := by
          rw [← denoteNList_len hlps]
        have hguard : (c = entry.ctor ∧ k < entry.numFields ∧
            args.length = entry.numParams + entry.numFields ∧
            ls.length = entry.levelParams.length ∧ pe'.fireOk ls = true) ↔
            (cn = pe'.ctor ∧ k < pe'.numFields ∧
            v'.getAppArgs.length = pe'.numParams + pe'.numFields ∧
            ls.length = pe'.levelParams.length ∧ pe'.fireOk ls = true) := by
          rw [hc_iff, hlen_a, hnp, hnf, hlen_l]
        split
        next hg =>
          obtain ⟨hcE, hkF, hlenA, _hlenL, _hfire⟩ := hg
          have hgP := hguard.mp ⟨hcE, hkF, hlenA, _hlenL, _hfire⟩
          subst hcE
          have hst : s7.store = s3.store := hst7
          have hx07 : Ext s₀.store s7.store := by rw [hst]; exact hx03
          have hp07 : s7.pins = s₀.pins := hp7.trans hp03
          -- stage 8: the `getD` default
          refine triple_seq (internE_spec s7 (.bvar 0) hok7.state.wf viewOK_bvar) ?_
          rintro b0 s8 ⟨hwf8, hx8, _hbm8, _hl8, _hsc8, _hm8, hc8, hp8, _hv8, _hd8⟩
          have hok8 : CheckOK mode env fe s8 := hok7.mono ⟨hwf8⟩ hx8 hc8 hp8
          have hx38 : Ext s3.store s8.store := by rw [← hst]; exact hx8
          -- the argument the rule selects, in range on both sides
          have hj : entry.numParams + k < args.length := by omega
          have hj' : pe'.numParams + k < v'.getAppArgs.length := by
            rw [← hlen_a, hnp]; exact hj
          have hwargs : ∀ x ∈ v'.getAppArgs, Expr.WScoped d x :=
            Expr.WScoped.getAppArgs hwv'
          have harg3 : denoteE s3.store (args.getD (entry.numParams + k) b0) =
              some (v'.getAppArgs.getD (pe'.numParams + k) (.bvar 0)) := by
            have hj'' : entry.numParams + k < v'.getAppArgs.length := by
              rw [← hlen_a]; exact hj
            have e1 : args.getD (entry.numParams + k) b0 =
                args.getD (entry.numParams + k) default := by
              rw [getD_of_lt hj, getD_of_lt hj]
            have e2 : v'.getAppArgs.getD (entry.numParams + k) (.bvar 0) =
                v'.getAppArgs.getD (entry.numParams + k) default := by
              rw [getD_of_lt hj'', getD_of_lt hj'']
            rw [hnp, e1, e2]
            exact denoteEList_getD hargs hj
          have hwarg : Expr.WScoped d
              (v'.getAppArgs.getD (pe'.numParams + k) (.bvar 0)) := by
            rw [getD_of_lt hj']
            exact hwargs _ (List.getElem_mem _)
          -- stage 9: the certificate
          refine triple_seq (projCertAt_spec hsim henv s8 d mode.verifiedChecks
            mode.betaGate entry.ctor us args cn ls v'.getAppArgs hok8
            (denoteN_ext hcn hx38) (denoteLs_ext hus hx38)
            (denoteEList_ext hx38 _ _ hargs) hwargs) ?_
          rintro cert s9 ⟨hok9, hx9, hp9, F3, hF3⟩
          have hx09 : Ext s₀.store s9.store := hx07.trans (hx8.trans hx9)
          have hp09 : s9.pins = s₀.pins := hp9.trans (hp8.trans hp07)
          cases cert
          · -- the certificate fails: stuck
            exact hstuck s9 hok9 hx09 hp09
              (denote_ext hv'3 (hx38.trans hx9))
              (denoteN_ext hsn3 (hx38.trans hx9))
              ⟨max (max F1 F2) F3 + 1, whnfCore_proj_cert_false
                (ConLeche.whnf_mono (Nat.le_max_left _ _) hwhnf)
                (projLitToCtorFueled_mono (Nat.le_max_left _ _) hplc) hfp hgf
                hgP (projCertAtFueled_mono (Nat.le_max_right _ _) hF3)⟩
          · -- the rule FIRES: head-normalise the selected field
            refine triple_mono (hsim.whnfCore s9 d _ _ hok9
              (denote_ext harg3 (hx38.trans hx9)) hwarg) ?_
            rintro r s10 ⟨hok10, hx10, hp10, w, hw10, hww, F4, hF4⟩
            refine ⟨hok10, hx09.trans hx10, hp10.trans hp09, w, hw10, hww,
              max (max F1 F2) (max F3 F4) + 1, ?_⟩
            exact whnfCore_proj_fire
              (ConLeche.whnf_mono (Nat.le_max_left _ _) hwhnf)
              (projLitToCtorFueled_mono (Nat.le_max_left _ _) hplc) hfp hgf hgP
              (projCertAtFueled_mono (Nat.le_trans (Nat.le_max_left F3 F4)
                (Nat.le_max_right _ _)) hF3)
              (ConLeche.whnfCore_mono (Nat.le_trans (Nat.le_max_right F3 F4)
                (Nat.le_max_right _ _)) hF4)
        next hg =>
          -- a guard fails: stuck
          have hst : s7.store = s3.store := hst7
          exact hstuck s7 hok7 (by rw [hst]; exact hx03) (hp7.trans hp03)
            (by rw [hst]; exact hv'3) (by rw [hst]; exact hsn3)
            ⟨max F1 F2 + 1, whnfCore_proj_guard hwhnf hplc hfp hgf
              (fun h => hg (hguard.mpr h))⟩
      -- the head is not a constant: stuck
      all_goals
        dsimp only
        exact hstuck s3 hok3 hx03 hp03 hv'3 hsn3
          ⟨max F1 F2 + 1, whnfCore_proj_head hwhnf hplc hfp
            (denote_not_const hwf3 hvh hdd (by intro c us h; cases h))⟩
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
`whnfCoreBody_app_batched` (OPEN), `whnfCoreBody_proj` (proved, over the
walk `projLitToCtor_spec`, closed too) and `whnfCoreBody_leaf` (CLOSED).  The note
below is round 3's inventory, kept for its reasons:

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

section Census

#print axioms whnfCore_proj_head
#print axioms getD_of_lt
#print axioms projLitToCtor_spec'
#print axioms IProjEntry.fireOk_spec'
#print axioms projCertAt_spec'
#print axioms whnfCoreBody_leaf
/-! `sorryAx` expected only through `whnfCoreBody_app_batched`, under the
body theorem. -/
#print axioms whnfCoreBody_proj
#print axioms whnfCoreBody_spec

end Census

end ConRon.Bridge.Core
