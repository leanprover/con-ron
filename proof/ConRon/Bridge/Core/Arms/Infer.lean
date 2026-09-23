/-
# `ConRon.Bridge.Core.Arms.Infer` — Theorem 1 for `inferBody`

DESIGN §8.2, rule 8's inventory for `ConLeche/Kernel/Core.lean:1112-1274
inferBody`.  Eleven SUCCESS exits over ten clauses; the failing exits need no
lemma, because a twin failure makes Theorem 1's `⇓?` postcondition vacuous and
a twin SUCCESS is what each success lemma is the licence for.

| clause | exit | lemma |
|---|---|---|
| `.sort u` | `Sort (u+1)` | `infer_sort` |
| `.fvar idx ty` | in scope | `infer_fvar` |
| `.const n us` | stored, not a tower entry, level arity matches | `infer_const` |
| `.lit (.natVal _)` | the `Nat` basis is installed | `infer_natLit` |
| `.lit (.strVal _)` | the `String` basis is installed | `infer_strLit` |
| `.forallE` | domain and codomain sorts, the datum validated | `infer_forallE` |
| `.lam` | the CHAIN rule (con-leche's task #161) | `infer_lam_chain` |
| `.lam` | the innermost binder's codomain-sort leaf (task #152) | `infer_lam_leaf` |
| `.lam` | the trusted lane, which runs neither | `infer_lam_trusted` |
| `.app` | the per-argument certificate succeeds | `infer_app` |
| `.proj` | the table entry, at a `Prop` and at a non-`Prop` structure | `infer_proj_prop`, `infer_proj_nonprop` |

## The deviations the twin carries at this body

1. **The binder-telescope loops** (task #97-P6-12): the twin's `.lam` and
   `.forallE` clauses are `inferLams`/`inferPis`, con-leche's own CACHED-tier
   `inferLamsI`/`inferPisI`, which peel and open the whole chain in one walk.
   The identification is con-leche's — `Verify/Cached/BinderLoopC.lean` and
   `Verify/BinderLoop.lean` — and what this library owes is the denotation
   carry, `inferBody_binders_batched` below.
2. **The batched application spine** (task #97-P6-9): `inferSpine`/`inferApp`
   in place of the per-argument chain, identified by
   `Verify/BetaSpine.lean`'s `inferSpine_*` family
   (`inferBody_app_batched` below).
3. `env : Env` is `fe : IFEnv` throughout (task #97c's deviation 1), which
   `Bridge/StateOK.lean`'s `IFEnvOK` absorbs with no clause of its own here.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Walks.Frame
import ConRon.Bridge.Core.Walks.StrLit

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The five leaf clauses -/

/-- con-leche: ConLeche/Kernel/Core.lean:1115 inferBody — a sort's type is the
next sort. -/
theorem infer_sort {F d : Nat} {u : Level} :
    ConLeche.inferTypeCore mode env (F + 1) d (.sort u) =
      .ok (.sort (.succ u)) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1116-1125 inferBody — a free
variable's type is the one its node carries (DESIGN §8.3, "Free variables":
this is what makes every handle-keyed cache sound). -/
theorem infer_fvar {F d idx : Nat} {ty : Expr} (h : idx < d) :
    ConLeche.inferTypeCore mode env (F + 1) d (.fvar idx ty) = .ok ty := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, if_pos h, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1126-1137 inferBody — a stored
constant's type at its universe instantiation. -/
theorem infer_const {F d : Nat} {n : Name} {us : List Level}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (ht : ci.isTowerEntry = false)
    (hl : us.length = ci.toConstantVal.levelParams.length) :
    ConLeche.inferTypeCore mode env (F + 1) d (.const n us) =
      .ok (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, hf, ht, hl, bind, Except.bind, pure,
    Except.pure]
  simp

/-- con-leche: ConLeche/Kernel/Core.lean:1138-1140 inferBody — a `Nat`
literal types as `Nat`, once the basis declarations are pinned. -/
theorem infer_natLit {F d n : Nat} (h : ConLeche.natLitSupported env = true) :
    ConLeche.inferTypeCore mode env (F + 1) d (.lit (.natVal n)) =
      .ok (.const ConLeche.natName []) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, h, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1141-1147 inferBody — a string
literal types as `String`. -/
theorem infer_strLit {F d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    ConLeche.inferTypeCore mode env (F + 1) d (.lit (.strVal s)) =
      .ok (.const ConLeche.stringName []) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, h, if_true, pure, Except.pure]

/-! ## 2. The two binder clauses -/

/-- con-leche: ConLeche/Kernel/Core.lean:1148-1164 inferBody — **the
∀-formation rule**: the codomain sort is inferred from the OPENED body and
the node's prop-ness datum is validated against it at the verified modes
(con-leche's task #161). -/
theorem infer_forallE {F d : Nat} {ty body bt : Expr} {mb : BinderMeta}
    {tty : Expr} {u v : Level}
    (hty : ConLeche.inferTypeCore mode env F d ty = .ok tty)
    (hw : ConLeche.whnf mode env F d tty = .ok (.sort u))
    (hb : ConLeche.inferTypeCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : ConLeche.ensureSortCore mode env F (d + 1) bt = .ok v)
    (hz : mode.verifiedChecks = true → (Level.zeronessOf v == mb.pw) = true) :
    ConLeche.inferTypeCore mode env (F + 1) d (.forallE ty body mb) =
      .ok (.sort (.imax u v)) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ConLeche.infer_def, ConLeche.whnf_def,
    ConLeche.ensureSort_def, hty, hw, hb, hv, bind, Except.bind]
  cases hm : mode.verifiedChecks with
  | false => simp [pure, Except.pure]
  | true => simp only [hz hm, pure, Except.pure]; simp

/-- con-leche: ConLeche/Kernel/Core.lean:1165-1215 inferBody — the λ clause's
**chain rule** (con-leche's task #161): an outer binder's codomain is the
inner λ's own ∀-type, so the datum is compared with the neighbour's and no
inference runs. -/
theorem infer_lam_chain {F d : Nat} {ty body bt tty : Expr} {mb : BinderMeta}
    {u : Level} {pwI : PropWhen}
    (hty : ConLeche.inferTypeCore mode env F d ty = .ok tty)
    (hw : ConLeche.whnf mode env F d tty = .ok (.sort u))
    (hb : ConLeche.inferTypeCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : mode.verifiedChecks = true) (hpw : body.lamPw = some pwI)
    (hz : (mb.pw == pwI) = true) :
    ConLeche.inferTypeCore mode env (F + 1) d (.lam ty body mb) =
      .ok (.forallE ty (bt.abstract1 d) mb) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ConLeche.infer_def, ConLeche.whnf_def,
    hty, hw, hb, hv, hpw, hz, bind, Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1205-1214 inferBody — the λ clause's
**innermost binder** (con-leche's task #152): the codomain sort is computed
from the body's inferred type at the io grade and the datum validated against
it. -/
theorem infer_lam_leaf {F d : Nat} {ty body bt tty btt : Expr}
    {mb : BinderMeta} {u vb : Level}
    (hty : ConLeche.inferTypeCore mode env F d ty = .ok tty)
    (hw : ConLeche.whnf mode env F d tty = .ok (.sort u))
    (hb : ConLeche.inferTypeCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : mode.verifiedChecks = true) (hpw : body.lamPw = none)
    (hbtt : ConLeche.inferTypeIO mode env F (d + 1) bt = .ok btt)
    (hvb : ConLeche.ensureSortCore mode env F (d + 1) btt = .ok vb)
    (hz : (Level.zeronessOf vb == mb.pw) = true) :
    ConLeche.inferTypeCore mode env (F + 1) d (.lam ty body mb) =
      .ok (.forallE ty (bt.abstract1 d) mb) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ConLeche.infer_def, ConLeche.whnf_def,
    ConLeche.inferTypeIO_def, ConLeche.ensureSort_def, hty, hw, hb, hv, hpw,
    hbtt, hvb, hz, bind, Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1165-1215 inferBody — the λ clause
at a mode that runs no TT-lane check: the reference kernel's `infer_lambda`,
verbatim. -/
theorem infer_lam_trusted {F d : Nat} {ty body bt tty : Expr}
    {mb : BinderMeta} {u : Level}
    (hty : ConLeche.inferTypeCore mode env F d ty = .ok tty)
    (hw : ConLeche.whnf mode env F d tty = .ok (.sort u))
    (hb : ConLeche.inferTypeCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : mode.verifiedChecks = false) :
    ConLeche.inferTypeCore mode env (F + 1) d (.lam ty body mb) =
      .ok (.forallE ty (bt.abstract1 d) mb) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ConLeche.infer_def, ConLeche.whnf_def,
    hty, hw, hb, hv, bind, Except.bind, Bool.false_eq_true, if_false, pure,
    Except.pure]

/-! ## 3. The application clause -/

/-- con-leche: ConLeche/Kernel/Core.lean:1216-1228 inferBody — the
application rule with its **per-argument certificate** (con-leche's task #100
de-gating: it runs unconditionally at the full grade). -/
theorem infer_app {F d : Nat} {f a tf ty body ta : Expr} {mt : BinderMeta}
    (hf : ConLeche.inferTypeCore mode env F d f = .ok tf)
    (hw : ConLeche.whnf mode env F d tf = .ok (.forallE ty body mt))
    (hta : ConLeche.inferTypeCore mode env F d a = .ok ta)
    (hde : ConLeche.isDefEqCore mode env F d ta ty = .ok true) :
    ConLeche.inferTypeCore mode env (F + 1) d (.app f a) =
      .ok (body.instantiate1 a) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ConLeche.infer_def, ConLeche.whnf_def,
    ConLeche.defeq_def, hf, hw, hta, hde, bind, Except.bind, pure,
    Except.pure]
  simp

/-! ## 4. The projection clause

Two success exits, and the guard that separates them is con-leche's task #175
W4c/O4 fence: at a `Prop`-declared structure the field's sort must itself be
`Prop` at this instantiation. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1229-1262 inferBody — the
projection at a **non-`Prop`** structure: the fence does not apply. -/
theorem infer_proj_nonprop {F d i : Nat} {sn T : Name} {pe te tpe : Expr}
    {us : List Level} {entry : ProjEntry}
    (hpe : ConLeche.inferTypeCore mode env F d pe = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hg : T = sn ∧ te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length)
    (hp : ¬ (Level.isEquiv entry.structSort .zero == some true)) :
    ConLeche.inferTypeCore mode env (F + 1) d (.proj sn i pe) =
      .ok (entry.typeAt us te.getAppArgs pe) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ConLeche.infer_def, ConLeche.whnf_def,
    hpe, hw, hh, ht, bind, Except.bind]
  rw [if_pos hg]
  simp only [if_neg hp, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1248-1259 inferBody — the projection
at a **`Prop`** structure, where the field's own sort must be `Prop` too. -/
theorem infer_proj_prop {F d i : Nat} {sn T : Name} {pe te tpe : Expr}
    {us : List Level} {entry : ProjEntry}
    (hpe : ConLeche.inferTypeCore mode env F d pe = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hg : T = sn ∧ te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length)
    (hp : (Level.isEquiv entry.structSort .zero == some true))
    (hf : (Level.isEquiv
      (Level.subst entry.levelParams us entry.fieldSort) .zero
        == some true)) :
    ConLeche.inferTypeCore mode env (F + 1) d (.proj sn i pe) =
      .ok (entry.typeAt us te.getAppArgs pe) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ConLeche.infer_def, ConLeche.whnf_def,
    hpe, hw, hh, ht, bind, Except.bind]
  rw [if_pos hg]
  simp only [if_pos hp, hf, pure, Except.pure]
  simp

/-! ## 5. The two batched clauses' identification, and the body theorem -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1288-1373 inferSpine_* —
**OPEN** (task #97-P3-Core): the twin's `.app` clause is `inferSpine`/
`inferApp`, con-leche's own cached-tier clause (task #97-P6-9), against the
chained `infer_app` above.  The `Expr`-level identification is con-leche's;
what is owed is the denotation carry. -/
theorem inferBody_app_batched {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : (i.tag == ETag.app) = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ inferApp mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean — **OPEN** (task
#97-P3-Core): the twin's `.lam`/`.forallE` clauses are `inferLams`/`inferPis`
(task #97-P6-12), con-leche's own cached-tier telescope loops, against the
chained `infer_lam_*`/`infer_forallE` above.  con-leche's own identification
is `Verify/BinderLoop.lean` plus its cached port; what is owed is the
denotation carry, including `inferPisOut`'s THREADED zero-ness datum
(con-leche's task #272), which is the one place the twin computes something
the chained clause recomputes per binder. -/
theorem inferBody_binders_batched {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : ETag.isBind i.tag = true) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  sorry


/-! ### The dispatch's children (task #97-P3-Core round 5)

`inferBody_spec` below is a case split on the tag and nothing else: one
child per group of the twin's `view` dispatch, each a triple at the same
body under its tag hypothesis.  The two batched clauses above are two of
them (`inferBody_app` reaches `inferBody_app_batched` through the dispatch);
the other four are here. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1216-1228 inferBody — **the `.app`
clause**, at the body: the dispatch hands the node to `inferApp`, whose
carry is `inferBody_app_batched`.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves) as a dispatch: its
own proof is sorry-free, and its census line shows `sorryAx` only through
`inferBody_app_batched`, the real content, which stays open. -/
theorem inferBody_app {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.app) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case app f a =>
    exact inferBody_app_batched henv hsim s₀ d i e hok hden hw (by simp [htag])
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1126-1137 inferBody — **the `.const`
clause**: the index lookup, the tower-entry and level-arity guards, and the
stored type through `constTyAt` (`Walks/Cached.lean`'s `constTyAt_spec'`,
CLOSED); pure side `infer_const`.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem inferBody_const {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.const) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case const n us =>
    obtain ⟨nm, ls, rfl, hn, hus⟩ := denote_const_inv hwf hv hden
    dsimp only
    cases hf : fe.find? n with
    | none =>
      mvcgen [ConRon.Arena.unknownConstError, ConRon.Arena.pinSorryAx]
      all_goals (bridge_peel; subst_vars)
      all_goals first
        | exact hok.pins
        | exact hok.caches.readN
        | exact fun h => h.elim
    | some ci =>
      obtain ⟨nm', c, hn', hci, hfind⟩ := hok.ienv.hit n ci hf
      obtain rfl := Option.some.inj (hn.symm.trans hn')
      cases ht : ci.isTowerEntry
      · obtain ⟨hct, cv, hcv_eq, hcv⟩ := denoteCI_nonTower hci ht
        have hname : denoteN s₀.store.ns cv.name = some nm := by
          rw [denoteCV_name hcv]; exact congrArg some (env_find_name hfind)
        have hlp := denoteNList_len (denoteCV_inv hcv).2.1
        have hcta := constTyAt_spec' (mode := mode) (env := env) (fe := fe)
          s₀ cv us hok ⟨nm, ls, c, hname, hus, hfind, hcv⟩
        simp only [hcv_eq, Bool.false_eq_true, if_false]
        mvcgen [hcta]
        all_goals (bridge_peel; subst_vars)
        all_goals first
          | exact hok.pins
          | exact hok.caches.readN
          | exact fun h => h.elim
          | rfl
          | skip
        rename_i _ usl hlen s₁ r s₂ hview
        intro hck hx hp hd
        have hlen' : usl.length = cv.levelParams.length := by simpa using hlen
        have hl : ls.length = c.toConstantVal.levelParams.length := by
          rw [← view_len_of_denoteLs hus hview, hlen', hlp]
        exact ⟨hck, hx, hp, _, hd nm ls c hname hus hfind,
          Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfind ls),
          1, infer_const hfind hct hl⟩
      · mvcgen
        all_goals (bridge_peel; subst_vars)
        all_goals first
          | exact hok.caches.readN
          | exact fun h => h.elim
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1138-1147 inferBody — **the two
literal clauses**: `natLitSupported_spec` (`Walks/Nat.lean`, CLOSED) and
`strLitSupported_spec` (`Walks/StrLit.lean`, CLOSED), then `constE_spec`;
pure side `infer_natLit`/`infer_strLit`.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem inferBody_lit {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lit) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  have hce := fun (s : AState) (n : NIdx) =>
    constE_spec' (mode := mode) (env := env) (fe := fe) s n
  cases v
  case lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    cases l with
    | natVal n =>
      have hn := natLitSupported_spec (mode := mode) (env := env) (fe := fe)
        s₀ hok
      mvcgen [hn, ConRon.Arena.pinNat, hce]
      all_goals (bridge_peel; subst_vars)
      all_goals first
        | exact fun h => h.elim
        | (apply CheckOK.pins; assumption)
        | (intro s hs _; subst hs; assumption)
        | (intro s hs hp; subst hs; exact ⟨_, hp _ rfl⟩)
        | (rename_i s2 r1 s1 r0 s0 hsup ck_s1 hpin x_s2_s1 p_s1_s2
           intro hck hx hp hd
           exact ⟨hck, x_s2_s1.trans hx, hp.trans p_s1_s2, _, hd _ (hpin _ rfl),
             by unfold Expr.WScoped; trivial, 1, infer_natLit hsup.symm⟩)
    | strVal str =>
      have hn := strLitSupported_spec (mode := mode) (env := env) (fe := fe)
        s₀ hok
      mvcgen [hn, ConRon.Arena.pinString, hce]
      all_goals (bridge_peel; subst_vars)
      all_goals first
        | exact fun h => h.elim
        | (apply CheckOK.pins; assumption)
        | (intro s hs _; subst hs; assumption)
        | (intro s hs hp; subst hs; exact ⟨_, hp _ rfl⟩)
        | (rename_i s2 r1 s1 r0 s0 hsup ck_s1 hpin x_s2_s1 p_s1_s2
           intro hck hx hp hd
           exact ⟨hck, x_s2_s1.trans hx, hp.trans p_s1_s2, _, hd _ (hpin _ rfl),
             by unfold Expr.WScoped; trivial, 1, infer_strLit hsup.symm⟩)
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1229-1264 inferBody — **the `.proj`
clause**: `KnotSpec.infer`, `KnotSpec.whnf'`, `getAppFn`/`getAppArgs`,
`IFEnv.findProj?_spec`, `lvlEq?_spec`, the three readbacks and
`IProjEntry.typeAt_spec` (`Walks/Proj.lean`, CLOSED); pure side
`infer_proj_prop`/`infer_proj_nonprop`.

**CLOSED** (round 5), staged by `triple_seq` (`Memo.lean`): every
callee is applied at a subject whose denotation the previous stage NAMED,
and every callee rule it needs was already closed. -/
theorem inferBody_proj {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.proj) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  cases v
  case proj sn k pe =>
    obtain ⟨nm, es, rfl, hsn, hpe⟩ := denote_proj_inv hwf hv hden
    have hwes : Expr.WScoped d es := by simpa [Expr.WScoped] using hw
    refine view_bind_triple hv ?_
    dsimp only
    -- stage 1: the subject's type
    refine triple_seq (hsim.infer s₀ d pe es hok hpe hwes) ?_
    rintro t1 s1 ⟨hok1, hx1, hp1, vt, hvt, hwvt, F1, hF1⟩
    -- stage 2: its head normal form
    refine triple_seq (hsim.whnf s1 d t1 vt hok1 hvt hwvt) ?_
    rintro te s2 ⟨hok2, hx2, hp2, vte, hvte, hwvte, F2, hF2⟩
    have hx02 : Ext s₀.store s2.store := hx1.trans hx2
    have hp02 : s2.pins = s₀.pins := hp2.trans hp1
    have hwf2 := hok2.state.wf
    obtain ⟨rk2, hrk2⟩ := hok2.state.wf
    -- stage 3: its head
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s2 te hok2.state
      (by rw [hvte]; rfl)) ?_
    rintro hd s3 ⟨hs3, hrelF⟩
    subst s3
    have hdd : denoteE s2.store hd = some vte.getAppFn := hrelF vte hvte
    obtain ⟨vh, hvh⟩ := denoteE_view hdd
    refine view_bind_triple hvh ?_
    cases vh
    case const T us =>
      obtain ⟨Tn, ls, hgf, hTn, hus⟩ := denote_const_inv hwf2 hvh hdd
      dsimp only
      -- stage 4: the table
      refine triple_seq (IFEnv.findProj?_spec s2 T k Tn hok2 hTn) ?_
      rintro oe s4 ⟨hok4, hx4, _hm4, _hc4, hp4, hsome, _hnone⟩
      cases oe with
      | none => exact triple_fail
      | some entry =>
        obtain ⟨p, hpd, hfp⟩ := hsome entry rfl
        dsimp only
        have hvte4 := denote_ext hvte hx4
        have hx04 : Ext s₀.store s4.store := hx02.trans hx4
        have hp04 : s4.pins = s₀.pins := hp4.trans hp02
        -- stage 5: the type's arguments
        refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s4 te
          hok4.state (by rw [hvte4]; rfl)) ?_
        rintro targs s5 ⟨hs5, hrelA⟩
        subst s5
        have hargs : Frontend.denoteEList s4.store targs = some vte.getAppArgs :=
          hrelA vte hvte4
        have hus4 := denoteLs_ext hus hx4
        -- stage 6: the level list's length
        refine triple_seq (viewLsLen_spec s4 us) ?_
        rintro ol s6 ⟨hs6, hol⟩
        subst s6
        rw [viewLen_of_denoteLs hus4] at hol
        subst hol
        dsimp only
        obtain ⟨_hsnp, hlps, _hctor, _hbody, hfs, hss, _hidx, hnp, _hnf, _hoff⟩ :=
          denoteProjEntry_inv hpd
        split
        next hg =>
          obtain ⟨hT, hlenA, hlenL⟩ := hg
          have hTnm : Tn = nm := by
            have h1 := denoteN_ext hsn (hx02.trans hx4)
            have h2 := denoteN_ext hTn hx4
            rw [hT] at h2
            exact Option.some.inj (h2.symm.trans h1)
          have hlen' : vte.getAppArgs.length = p.numParams := by
            rw [denoteEList_len hargs, hlenA, hnp]
          have hlenL' : ls.length = p.levelParams.length := by
            rw [hlenL, denoteNList_len hlps]
          have hgP : Tn = nm ∧ vte.getAppArgs.length = p.numParams ∧
              ls.length = p.levelParams.length := ⟨hTnm, hlen', hlenL'⟩
          have hwhnf : ConLeche.whnf mode env (max F1 F2) d vt = .ok vte :=
            ConLeche.whnf_mono (Nat.le_max_right _ _) hF2
          have hinf : ConLeche.inferTypeCore mode env (max F1 F2) d es =
              .ok vt :=
            ConLeche.inferTypeCore_mono (Nat.le_max_left _ _) hF1
          have hwty : Expr.WScoped d (p.typeAt ls vte.getAppArgs es) :=
            ConLeche.projEntry_typeAt_WScoped henv hfp ls hlen'
              (Expr.WScoped.getAppArgs hwvte) hwes
          -- the answer, at any state the fence leaves behind
          have hfin : ∀ (s : AState), CheckOK mode env fe s →
              s.store = s4.store → s.pins = s₀.pins →
              (∃ F, ConLeche.inferTypeCore mode env F d (.proj nm k es) =
                .ok (p.typeAt ls vte.getAppArgs es)) →
              ⦃fun s' => ⌜s' = s⌝⦄ entry.typeAt us targs pe
              ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
                  s'.pins = s₀.pins ∧
                  SimE (ConLeche.inferTypeCore mode env) d (.proj nm k es)
                    s'.store r⌝⦄ := by
            intro s hs hst hps hF
            refine triple_mono (IProjEntry.typeAt_spec s entry us targs pe p ls
              vte.getAppArgs es hs (by rw [hst]; exact hpd)
              (by rw [hst]; exact hus4) (by rw [hst]; exact hargs)
              (by rw [hst]; exact denote_ext hpe hx04)) ?_
            rintro r s' ⟨hok', hx', hp', hd'⟩
            exact ⟨hok', by rw [hst] at hx'; exact hx04.trans hx',
              hp'.trans hps, _, hd', hwty, hF⟩
          -- stage 7: the possibly-`Prop` fence
          refine triple_seq (pinZeroLevel_spec s4 hok4.pins) ?_
          rintro z s7 ⟨hs7, hz⟩
          subst s7
          refine triple_seq (lvlEq?_spec s4 entry.structSort z hok4) ?_
          rintro rq s8 ⟨hok8, hst8, hp8, lu, lv, hlu, hlv, hrq⟩
          rw [hss] at hlu
          rw [hz] at hlv
          obtain rfl : lu = p.structSort := (Option.some.inj hlu).symm
          obtain rfl : lv = Level.zero := (Option.some.inj hlv).symm
          subst hrq
          split
          next hprop =>
            -- a `Prop` structure: the field's sort must be `Prop` too
            refine triple_seq (readNamesM_spec s8 entry.levelParams
              hok8.caches.readN) ?_
            rintro ks s9 ⟨hst9, hm9, hp9, hc9, hks, hN9⟩
            have hok9 := CheckOK.ofReadbackFrame hok8
              (ReadbackFrame.ofReadN hst9 hm9 hp9 hc9 hN9)
            refine triple_seq (readLevelsM_spec s9 us hok9.caches.readLs) ?_
            rintro vs s10 ⟨hst10, hm10, hp10, hc10, hvs, hLs10⟩
            have hok10 := CheckOK.ofReadbackFrame hok9
              (ReadbackFrame.ofReadLs hst10 hm10 hp10 hc10 hLs10)
            refine triple_seq (readLevelM_spec s10 entry.fieldSort
              hok10.caches.readL) ?_
            rintro fs s11 ⟨hst11, hm11, hp11, hc11, hfs11, hL11⟩
            have hok11 := CheckOK.ofReadbackFrame hok10
              (ReadbackFrame.ofReadL hst11 hm11 hp11 hc11 hL11)
            have hst411 : s11.store = s4.store :=
              hst11.trans (hst10.trans (hst9.trans hst8))
            rw [hst8, hlps] at hks
            rw [hst9, hst8, hus4] at hvs
            rw [hst10, hst9, hst8, hfs] at hfs11
            obtain rfl : ks = p.levelParams := (Option.some.inj hks).symm
            obtain rfl : vs = ls := (Option.some.inj hvs).symm
            obtain rfl : fs = p.fieldSort := (Option.some.inj hfs11).symm
            split
            next => exact triple_fail
            next hfield =>
              exact hfin s11 hok11 hst411
                (hp11.trans (hp10.trans (hp9.trans (hp8.trans hp04))))
                ⟨max F1 F2 + 1, infer_proj_prop hinf hwhnf hgf hfp hgP
                  (by simpa using hprop) (by simpa using hfield)⟩
          next hprop =>
            exact hfin s8 hok8 hst8 (hp8.trans hp04)
              ⟨max F1 F2 + 1, infer_proj_nonprop hinf hwhnf hgf hfp hgP
                (by simpa using hprop)⟩
        next => exact triple_fail
    all_goals (dsimp only; exact triple_fail)
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

#print axioms inferBody_proj

/-- con-leche: ConLeche/Kernel/Core.lean:1115-1125 inferBody — **the leaf
clauses**: `.sort` (one level intern and one node intern), `.fvar` (the
scope check), and the two throws (`.letE`, `.bvar`).
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem inferBody_leaf {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (hna : i.tag ≠ ETag.app) (hnp : i.tag ≠ ETag.proj)
    (hnb : ETag.isBind i.tag = false) (hnc : i.tag ≠ ETag.const)
    (hnl : i.tag ≠ ETag.lit) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v with
  | app f a => exact absurd htg hna
  | lit l => exact absurd htg hnl
  | const n us => exact absurd htg hnc
  | proj n k sub => exact absurd htg hnp
  | lam ty b m =>
    rw [htg] at hnb; simp [ENodeView.tagOf, ETag.isBind] at hnb
  | forallE ty b m =>
    rw [htg] at hnb; simp [ENodeView.tagOf, ETag.isBind] at hnb
  | letE ty w b => mvcgen; exact fun h => h.elim
  | bvar k => mvcgen; exact fun h => h.elim
  | fvar k t =>
    obtain ⟨t', rfl, ht⟩ := denote_fvar_inv hwf hv hden
    have hk : k < d := by unfold Expr.WScoped at hw; exact hw.1
    have hwt : Expr.WScoped d t' := by
      unfold Expr.WScoped at hw; exact Expr.WScoped.mono (Nat.le_of_lt hk) hw.2
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, ht, hwt, 1, infer_fvar hk⟩
  | sort u =>
    obtain ⟨l, rfl, hl⟩ := denote_sort_inv hwf hv hden
    mvcgen [internLNode_spec, internE_spec]
    all_goals (bridge_peel; subst_vars)
    case vc1.hwf => exact hwf
    case vc2.hv =>
      exact ⟨fun c hc => by
        simp [LNodeView.lchildren] at hc; subst hc
        exact lview_isSome_of_denote hl,
        fun c hc => by simp [LNodeView.nchildren] at hc⟩
    case vc3.sort.post.success.post.success =>
      rename_i s₁ r₁ s₂ r₂ s₃ _ hx1 _ _ _ _ hc1 hp1 _ hd1
      intro hwf2 hx2 _ _ hc2 hp2 _ _ _ hd2
      refine ⟨hok.mono ⟨hwf2⟩ (hx1.trans hx2) (hc2.trans hc1) (hp2.trans hp1),
        hx1.trans hx2, hp2.trans hp1, .sort (.succ l), ?_,
        by unfold Expr.WScoped; trivial, 1, infer_sort⟩
      have hs1 : denoteL s₂.store.ls r₁ = some (Level.succ l) := by
        rw [hd1]; simp [denoteLView, denoteL_ext hl hx1]
      rw [hd2]; simp [denoteEView, denoteL_ext hs1 hx2]
    case vc4 => intro s h _ _ _ _ _ _ _ _ _; exact h
    case vc5 =>
      intro s _ _ _ _ _ _ _ _ hview _
      exact viewOK_sort (by rw [hview]; rfl)

/-- con-leche: ConLeche/Verify/Cached/DiscC5.lean inferBodyC_sim — **THEOREM 1
for `inferBody`**.

**OPEN** (task #97-P3-Core).  What is missing: the two batched clauses above,
and the `.proj` arm's callee rules (`IProjEntry.typeAt`, `lvlEq?`, the three
memoised readbacks), which are `Arena/Core.lean` walks that are not knot slots
and need `BodySpec`-shaped theorems of their own.  The nine leaf/binder/app
step lemmas above are closed and are what the split arms consume. -/
theorem inferBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe (inferBody mode (coreKnot mode fe id fuel) fe)
      (ConLeche.inferTypeCore mode env) := by
  intro s₀ d i e hok hden hw
  by_cases ha : i.tag = ETag.app
  · exact inferBody_app henv hμ hsim s₀ d i e hok hden hw ha
  by_cases hp : i.tag = ETag.proj
  · exact inferBody_proj henv hμ hsim s₀ d i e hok hden hw hp
  by_cases hb : ETag.isBind i.tag = true
  · exact inferBody_binders_batched henv hsim s₀ d i e hok hden hw hb
  by_cases hc : i.tag = ETag.const
  · exact inferBody_const henv hμ hsim s₀ d i e hok hden hw hc
  by_cases hl : i.tag = ETag.lit
  · exact inferBody_lit henv hμ hsim s₀ d i e hok hden hw hl
  exact inferBody_leaf henv hμ hsim s₀ d i e hok hden hw ha hp
    (Bool.eq_false_iff.mpr hb) hc hl

/-! ## The axiom census of the closed children (task #97-P3-Core round 5,
sub-lane Leaves) -/

section Census

-- `sorryAx` here is `inferBody_app_batched`'s, inherited through the dispatch
#print axioms inferBody_app
#print axioms inferBody_const
#print axioms inferBody_lit
#print axioms inferBody_leaf

end Census

end ConRon.Bridge.Core
