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
carry is `inferBody_app_batched`. -/
theorem inferBody_app {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
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
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1126-1137 inferBody — **the `.const`
clause**: the index lookup, the tower-entry and level-arity guards, and the
stored type through `constTyAt` (`Walks/Cached.lean`'s `constTyAt_spec'`,
CLOSED); pure side `infer_const`. -/
theorem inferBody_const {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.const) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1138-1147 inferBody — **the two
literal clauses**: `natLitSupported_spec` (`Walks/Nat.lean`, CLOSED) and
`strLitSupported` (OPEN — no bridge spec yet), then `constE_spec`; pure side
`infer_natLit`/`infer_strLit`. -/
theorem inferBody_lit {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lit) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBody mode (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1229-1264 inferBody — **the `.proj`
clause**: `KnotSpec.infer`, `KnotSpec.whnf'`, `getAppFn`/`getAppArgs`,
`IFEnv.findProj?_spec`, `lvlEq?_spec`, the three readbacks and
`IProjEntry.typeAt_spec` (`Walks/Proj.lean`, CLOSED); pure side
`infer_proj_prop`/`infer_proj_nonprop`. -/
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
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1115-1125 inferBody — **the leaf
clauses**: `.sort` (one level intern and one node intern), `.fvar` (the
scope check), and the two throws (`.letE`, `.bvar`). -/
theorem inferBody_leaf {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
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
  sorry

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

end ConRon.Bridge.Core
