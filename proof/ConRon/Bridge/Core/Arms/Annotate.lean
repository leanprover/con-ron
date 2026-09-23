/-
# `ConRon.Bridge.Core.Arms.Annotate` — Theorem 1 for `annotateBody`

DESIGN §8.2, rule 8's inventory for `ConLeche/Kernel/Core.lean:1805-1915
annotateBody` — the one pass that meets raw stream input, and therefore the
one pass whose `.letE` clause runs the official `infer_let` triple and returns
the ζ reduct (con-leche's task #217).

| clause | exit | lemma |
|---|---|---|
| `.bvar` | itself | `annot_bvar` |
| `.fvar` | in scope, itself | `annot_fvar` |
| `.sort` / `.const` | itself | `annot_sort`, `annot_const` |
| `.lit (.natVal _)` | the `Nat` basis is installed | `annot_natLit` |
| `.lit (.strVal _)` | the `String` basis is installed | `annot_strLit` |
| `.app` | structural | `annot_app` |
| `.forallE` | the node carries a real datum | `annot_forallE_written` |
| `.forallE` | the datum is computed (`annotPwPi`) | `annot_forallE_computed` |
| `.lam` | the node carries a real datum | `annot_lam_written` |
| `.lam` | the datum is computed (`annotPwLam`) | `annot_lam_computed` |
| `.letE` | the `infer_let` triple, then the ζ reduct | `annot_letE` |
| `.proj` | the table entry and the two name/arity premises | `annot_proj` |

## The deviations the twin carries at this body

1. **The binder-telescope loops** (task #97-P6-11): the twin's `.forallE`
   clause and its bvar-closed `.lam` clause are `annotatePis`/`annotateLams`,
   con-leche's own CACHED-tier `annotatePisI`/`annotateLamsI` with
   `annotateBindersOut`'s outward rebuild.  The single-binder clause survives
   as `annotateBinder`, con-leche's λ residual, entered zero times on `Init`.
   con-leche's identification is `Verify/BinderLoop.lean` and its cached port;
   the carry is `annotateBody_binders_batched` below.
2. **The EXECUTED `abstractRange`** (the same task): the rebuild calls
   `abstractRangeFast`, whose spec is `Bridge/ExprOps/Owed.lean`'s (still
   `sorry` — task #97-P3-0's open list) and whose identification with the
   spec descent is `Bridge/ExprOps/Abs.lean`'s.
3. `internRebuiltApp` at the `.app` clause (task #97-P6-7's lever 4), whose
   `@[spec]` theorem is `Bridge/Specs.lean`'s `internRebuiltApp_spec` and
   which claims exactly `RelE`'s `.self` when the children did not move.
-/
import ConRon.Bridge.Core.Memo

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The six leaf clauses -/

/-- con-leche: ConLeche/Kernel/Core.lean:1808 annotateBody. -/
theorem annot_bvar {F d i : Nat} :
    ConLeche.annotateCore mode env (F + 1) d (.bvar i) = .ok (.bvar i) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1809-1814 annotateBody — the leaf
scope check, which is where a dangling free variable in RAW input is
rejected (at depth 0, any `fvar` fails). -/
theorem annot_fvar {F d idx : Nat} {ty : Expr} (h : idx < d) :
    ConLeche.annotateCore mode env (F + 1) d (.fvar idx ty) =
      .ok (.fvar idx ty) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, if_pos h, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1815 annotateBody. -/
theorem annot_sort {F d : Nat} {u : Level} :
    ConLeche.annotateCore mode env (F + 1) d (.sort u) = .ok (.sort u) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1816 annotateBody. -/
theorem annot_const {F d : Nat} {n : Name} {us : List Level} :
    ConLeche.annotateCore mode env (F + 1) d (.const n us) =
      .ok (.const n us) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1817-1821 annotateBody — a literal
is well formed exactly when its type's declarations are stored. -/
theorem annot_natLit {F d n : Nat}
    (h : ConLeche.natLitSupported env = true) :
    ConLeche.annotateCore mode env (F + 1) d (.lit (.natVal n)) =
      .ok (.lit (.natVal n)) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, h, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1822-1827 annotateBody. -/
theorem annot_strLit {F d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    ConLeche.annotateCore mode env (F + 1) d (.lit (.strVal s)) =
      .ok (.lit (.strVal s)) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, h, if_true, pure, Except.pure]

/-! ## 2. The application clause -/

/-- con-leche: ConLeche/Kernel/Core.lean:1828-1835 annotateBody — structural:
the application rule's checks are the driver's inference sweep's (con-leche's
task #100 stage 6). -/
theorem annot_app {F d : Nat} {f a f' a' : Expr}
    (hf : ConLeche.annotateCore mode env F d f = .ok f')
    (ha : ConLeche.annotateCore mode env F d a = .ok a') :
    ConLeche.annotateCore mode env (F + 1) d (.app f a) = .ok (.app f' a') := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hf, ha, bind,
    Except.bind, pure, Except.pure]

/-! ## 3. The two binder clauses

Each has two exits: the node already carries a real input annotation (which
validation judges and the pass never overwrites — con-leche's
`pwWritten`/`annotBinderMeta`), or the datum is computed from the annotated
body. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1836-1845 annotateBody — the ∀
clause at a node that **already carries** a datum. -/
theorem annot_forallE_written {F d : Nat} {ty body ty' body' : Expr}
    {mb : BinderMeta}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (hb : ConLeche.annotateCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty')) = .ok body')
    (hw : ConLeche.pwWritten mb.pw = true) :
    ConLeche.annotateCore mode env (F + 1) d (.forallE ty body mb) =
      .ok (.forallE ty' (body'.abstract1 d) ⟨mb.pw⟩) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hty, hb, hw, bind,
    Except.bind, Bool.not_eq_true', Bool.true_eq_false, if_false, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1836-1845 annotateBody — the ∀
clause whose datum is **computed** by `annotPwPi` from the annotated body. -/
theorem annot_forallE_computed {F d : Nat} {ty body ty' body' : Expr}
    {mb : BinderMeta} {pw : PropWhen}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (hb : ConLeche.annotateCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty')) = .ok body')
    (hw : ConLeche.pwWritten mb.pw = false)
    (hpw : ConLeche.annotPwPi (ConLeche.pureFns mode env F) env (d + 1) body'
      = .ok pw) :
    ConLeche.annotateCore mode env (F + 1) d (.forallE ty body mb) =
      .ok (.forallE ty' (body'.abstract1 d) ⟨pw⟩) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hty, hb, hw, hpw,
    bind, Except.bind, Bool.not_eq_true', if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1846-1853 annotateBody — the λ
clause at a node that **already carries** a datum. -/
theorem annot_lam_written {F d : Nat} {ty body ty' body' : Expr}
    {mb : BinderMeta}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (hb : ConLeche.annotateCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty')) = .ok body')
    (hw : ConLeche.pwWritten mb.pw = true) :
    ConLeche.annotateCore mode env (F + 1) d (.lam ty body mb) =
      .ok (.lam ty' (body'.abstract1 d) ⟨mb.pw⟩) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hty, hb, hw, bind,
    Except.bind, Bool.not_eq_true', Bool.true_eq_false, if_false, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1846-1853 annotateBody — the λ
clause whose datum is **computed** by `annotPwLam`. -/
theorem annot_lam_computed {F d : Nat} {ty body ty' body' : Expr}
    {mb : BinderMeta} {pw : PropWhen}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (hb : ConLeche.annotateCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty')) = .ok body')
    (hw : ConLeche.pwWritten mb.pw = false)
    (hpw : ConLeche.annotPwLam (ConLeche.pureFns mode env F) env (d + 1) body'
      = .ok pw) :
    ConLeche.annotateCore mode env (F + 1) d (.lam ty body mb) =
      .ok (.lam ty' (body'.abstract1 d) ⟨pw⟩) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hty, hb, hw, hpw,
    bind, Except.bind, Bool.not_eq_true', if_true, pure, Except.pure]

/-! ## 4. The `let` clause — the one place the official `infer_let` triple
runs

con-leche's task #217: this clause returns the ζ REDUCT, so every term the
checker stores is let-free and `inferBody`'s and `whnfCoreBody`'s `.letE` arms
are unreachable by construction.  Dropping the triple as redundant with
`inferBody`'s own `.letE` clause was con-leche's task #161 item C2, and it was
wrong — the witness is in that clause's doc comment. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1854-1886 annotateBody — the `let`
clause: `ensureSort (infer ty')`, `infer v'`, `defeq tv ty'`, then annotate
the ζ reduct. -/
theorem annot_letE {F d : Nat} {ty v b ty' v' tty tv res : Expr} {u : Level}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (htty : ConLeche.inferTypeCore mode env F d ty' = .ok tty)
    (hs : ConLeche.ensureSortCore mode env F d tty = .ok u)
    (hv : ConLeche.annotateCore mode env F d v = .ok v')
    (htv : ConLeche.inferTypeCore mode env F d v' = .ok tv)
    (hde : ConLeche.isDefEqCore mode env F d tv ty' = .ok true)
    (hr : ConLeche.annotateCore mode env F d (b.instantiate1 v) = .ok res) :
    ConLeche.annotateCore mode env (F + 1) d (.letE ty v b) = .ok res := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, ConLeche.infer_def,
    ConLeche.ensureSort_def, ConLeche.defeq_def, hty, htty, hs, hv, htv, hde,
    bind, Except.bind]
  simpa using hr

/-! ## 5. The projection clause -/

/-- con-leche: ConLeche/Kernel/Core.lean:1887-1915 annotateBody — the
projection rule, run HERE and nowhere else: the node's own structure name is
official's `infer_proj` premise (con-leche's task #271, its issue #7), and the
display name is normalized to the type's head so that reduction's table lookup
is complete on annotated terms. -/
theorem annot_proj {F d i : Nat} {sn T : Name} {pe e' te tpe : Expr}
    {us : List Level} {entry : ProjEntry}
    (hpe : ConLeche.annotateCore mode env F d pe = .ok e')
    (hipe : ConLeche.inferTypeIO mode env F d e' = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hn : T = sn)
    (ha : te.getAppArgs.length = entry.numParams) :
    ConLeche.annotateCore mode env (F + 1) d (.proj sn i pe) =
      .ok (.proj T i e') := by
  subst hn
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, ConLeche.whnf_def,
    ConLeche.inferTypeIO_def, hpe, hipe, hw, hh, ht, ha, bind, Except.bind,
    pure, Except.pure]
  simp

/-! ## 6. The batched clause's identification, and the body theorem -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean — **OPEN** (task
#97-P3-Core): the twin's binder clauses are `annotatePis`/`annotateLams`
(task #97-P6-11), con-leche's own cached-tier telescope loops with
`annotateBindersOut`'s outward rebuild, against the chained
`annot_forallE_*`/`annot_lam_*` above.  What is owed is the denotation carry,
and it needs `Bridge/ExprOps/Owed.lean`'s `abstractRangeFast_spec` — still
`sorry` (task #97-P3-0's open list) — because the rebuild is the EXECUTED
`abstractRange` and not the spec descent. -/
theorem annotateBody_binders_batched {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : ETag.isBind i.tag = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  sorry


/-! ### The dispatch's children (task #97-P3-Core round 5)

`annotateBody_spec` below is a case split on the tag: one child per group of
the twin's `view` dispatch, each a triple at the same body under its tag
hypothesis; the batched binder clause above is one of them. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1828-1834 annotateBody — **the
`.app` clause**: two `KnotSpec.annotate` calls and the rebuilt node
(`internRebuiltApp`, task #97-P6-7's upward cutoff); pure side `annot_app`. -/
theorem annotateBody_app {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.app) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1817-1827 annotateBody — **the two
literal clauses**: `natLitSupported_spec` (CLOSED) and `strLitSupported`
(OPEN); pure side `annot_natLit`/`annot_strLit`. -/
theorem annotateBody_lit {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lit) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1852-1881 annotateBody — **the `.letE`
clause** (con-leche's task #217): `KnotSpec.annotate`, `ensureSort`,
`KnotSpec.infer`, `KnotSpec.defeq'`, `instantiate1Fast`; pure side
`annot_letE`. -/
theorem annotateBody_letE {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.letE) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1882-1900 annotateBody — **the `.proj`
clause**: `KnotSpec.annotate`, `KnotSpec.inferIO'`, `KnotSpec.whnf'`,
`getAppFn`/`getAppArgs`, `IFEnv.findProj?_spec`; pure side `annot_proj`. -/
theorem annotateBody_proj {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.proj) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1808-1816 annotateBody — **the leaf
clauses**: `.bvar`, `.fvar` (the scope check), `.sort` and `.const` answer
themselves; pure side `annot_bvar`/`_fvar`/`_sort`/`_const`. -/
theorem annotateBody_leaf {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (hna : i.tag ≠ ETag.app) (hnl : i.tag ≠ ETag.lit)
    (hnb : ETag.isBind i.tag = false) (hne : i.tag ≠ ETag.letE)
    (hnp : i.tag ≠ ETag.proj) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v with
  | app f a => exact absurd htg hna
  | lit l => exact absurd htg hnl
  | letE ty w b => exact absurd htg hne
  | proj n k sub => exact absurd htg hnp
  | lam ty b m =>
    rw [htg] at hnb; simp [ENodeView.tagOf, ETag.isBind] at hnb
  | forallE ty b m =>
    rw [htg] at hnb; simp [ENodeView.tagOf, ETag.isBind] at hnb
  | bvar k =>
    obtain rfl := denote_bvar_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, hden, hw, 1, annot_bvar⟩
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hden
    have hk : k < d := by unfold Expr.WScoped at hw; exact hw.1
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, hden, hw, 1, annot_fvar hk⟩
  | sort u =>
    obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, hden, hw, 1, annot_sort⟩
  | const n us =>
    obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, hden, hw, 1, annot_const⟩

/-- con-leche: ConLeche/Verify/Cached/DiscC6.lean annotateBodyC_sim —
**THEOREM 1 for `annotateBody`**.

**OPEN** (task #97-P3-Core).  What is missing: the batched binder clause
above, the `.proj` arm's callee rules, and `annotPwPi`/`annotPwLam` — two
`Arena/Core.lean` walks that read the head symbol before falling back to
inference and that need `BodySpec`-shaped theorems of their own.  The twelve
step lemmas above are closed. -/
theorem annotateBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe (annotateBody (coreKnot mode fe id fuel) fe)
      (ConLeche.annotateCore mode env) := by
  intro s₀ d i e hok hden hw
  by_cases ha : i.tag = ETag.app
  · exact annotateBody_app henv hμ hsim s₀ d i e hok hden hw ha
  by_cases hb : ETag.isBind i.tag = true
  · exact annotateBody_binders_batched henv hsim s₀ d i e hok hden hw hb
  by_cases hl : i.tag = ETag.lit
  · exact annotateBody_lit henv hμ hsim s₀ d i e hok hden hw hl
  by_cases he : i.tag = ETag.letE
  · exact annotateBody_letE henv hμ hsim s₀ d i e hok hden hw he
  by_cases hp : i.tag = ETag.proj
  · exact annotateBody_proj henv hμ hsim s₀ d i e hok hden hw hp
  exact annotateBody_leaf henv hμ hsim s₀ d i e hok hden hw ha hl
    (Bool.eq_false_iff.mpr hb) he hp

end ConRon.Bridge.Core
