/-
# `ConRon.Bridge.Core.Arms.InferIO` — Theorem 1 for `inferBodyIO`

DESIGN §8.2, rule 8's inventory for `ConLeche/Kernel/Core.lean:1276-1404
inferBodyIO` — **the io grade** (con-leche's task #170/#172 B4).  The body is
`inferBody` with two clauses changed, and those two are the only lemmas that
differ from `Bridge/Core/Arms/Infer.lean`'s:

| clause | exit | lemma |
|---|---|---|
| `.lam` | **no domain-sort run** (official's `infer_lambda` at `infer_only`) | `inferIO_lam_chain`, `inferIO_lam_leaf`, `inferIO_lam_trusted` |
| `.app` | **the licensed arm**: the ∀'s datum is `never`, so no certificate | `inferIO_app_licensed` |
| `.app` | the unlicensed arm: the certificate runs, as at the full grade | `inferIO_app_cert` |

Everything else (`.sort`, `.fvar`, `.const`, the two literals, `.forallE`,
`.proj`, the two throws) is byte-identical to `inferBody`'s, and the io
lemmas for those clauses are the same proofs at `inferTypeIO`; the four that
this round states are below, the rest are listed in DESIGN §8's task section.

## Why the statements are at `betaGate = true`

The knot's io slot selects the grade once per level: at `mode.betaGate = false`
the slot IS full inference (`ConLeche.inferTypeIO_off`), so the io lemmas are
`Infer.lean`'s verbatim and there is nothing to state.  The bridge is stated
at `.verified`, where the bit is on — which is also where the twin's
`mode.ioGate` agrees with it (task #97c's smaller deviation 4).

## The grade propagates through the RECORD, not through a flag

`inferBodyIO` recurses through `r.infer`, and the knot hands it
`CoreFns.ioView (coreKnot … fuel)` — the record whose `infer` slot is the io
slot.  So every `r.infer` below is `ConLeche.inferTypeIO mode env F`, which
is what the hypotheses say.  This is official's `infer_type_core` passing
`infer_only` down, without a textual twin.
-/
import ConRon.Bridge.Core.Arms.Infer

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The λ clause: no domain-sort run -/

/-- con-leche: ConLeche/Kernel/Core.lean:1328-1349 inferBodyIO — the io λ
clause's **chain rule**.  Note what is NOT here: `inferBody`'s
`r.whnf (← r.infer ty)` domain-sort run.  Official's `infer_lambda` skips it
at `infer_only`, and the P row never consumed it. -/
theorem inferIO_lam_chain {F d : Nat} {ty body bt : Expr} {mb : BinderMeta}
    {pwI : PropWhen} (hg : mode.betaGate = true)
    (hb : ConLeche.inferTypeIO mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : mode.verifiedChecks = true) (hpw : body.lamPw = some pwI)
    (hz : (mb.pw == pwI) = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lam ty body mb) =
      .ok (.forallE ty (bt.abstract1 d) mb) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    hb, hv, hpw, hz, bind, Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1348 inferBodyIO — the io λ
clause's **innermost binder**: the codomain-sort validation stays (it is what
makes the λ datum trustworthy), and at this grade its own inference is the io
one too. -/
theorem inferIO_lam_leaf {F d : Nat} {ty body bt btt : Expr}
    {mb : BinderMeta} {vb : Level} (hg : mode.betaGate = true)
    (hb : ConLeche.inferTypeIO mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : mode.verifiedChecks = true) (hpw : body.lamPw = none)
    (hbtt : ConLeche.inferTypeIO mode env F (d + 1) bt = .ok btt)
    (hvb : ConLeche.whnf mode env F (d + 1) btt = .ok (.sort vb))
    (hz : (Level.zeronessOf vb == mb.pw) = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lam ty body mb) =
      .ok (.forallE ty (bt.abstract1 d) mb) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.ensureSort, ConLeche.whnf_def, hb, hv, hpw, hbtt, hvb, hz, bind,
    Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1328-1349 inferBodyIO — the io λ
clause at a mode that runs no TT-lane check. -/
theorem inferIO_lam_trusted {F d : Nat} {ty body bt : Expr}
    {mb : BinderMeta} (hg : mode.betaGate = true)
    (hb : ConLeche.inferTypeIO mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : mode.verifiedChecks = false) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lam ty body mb) =
      .ok (.forallE ty (bt.abstract1 d) mb) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    hb, hv, bind, Except.bind, Bool.false_eq_true, if_false, pure,
    Except.pure]

/-! ## 2. The application clause: **the io site** -/

/-- con-leche: ConLeche/Kernel/Core.lean:1350-1373 inferBodyIO — **the io
site**: at a ∀ whose validated datum is `never` the per-argument certificate
is dead weight (the premise-form io claim derives the membership from the
subject's own `WellDenoted` app slot), so it is skipped.  The READ IS THE
DATUM ALONE — con-leche's licence ruling of 2026-09-06 — which is why no
`mode` conjunct appears. -/
theorem inferIO_app_licensed {F d : Nat} {f a tf ty body : Expr}
    {mt : BinderMeta} (hg : mode.betaGate = true)
    (hf : ConLeche.inferTypeIO mode env F d f = .ok tf)
    (hw : ConLeche.whnf mode env F d tf = .ok (.forallE ty body mt))
    (hlic : mt.pw.isNever = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.app f a) =
      .ok (body.instantiate1 a) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.whnf_def, hf, hw, hlic, bind, Except.bind, pure, Except.pure]
  simp

/-- con-leche: ConLeche/Kernel/Core.lean:1368-1372 inferBodyIO — the
application clause at a **possibly-zero** datum: the certificate runs
unconditionally.  The squash regime's membership is model-class-wide
unrecoverable, and that fence is absolute. -/
theorem inferIO_app_cert {F d : Nat} {f a tf ty body ta : Expr}
    {mt : BinderMeta} (hg : mode.betaGate = true)
    (hf : ConLeche.inferTypeIO mode env F d f = .ok tf)
    (hw : ConLeche.whnf mode env F d tf = .ok (.forallE ty body mt))
    (hlic : mt.pw.isNever = false)
    (hta : ConLeche.inferTypeIO mode env F d a = .ok ta)
    (hde : ConLeche.isDefEqCore mode env F d ta ty = .ok true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.app f a) =
      .ok (body.instantiate1 a) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.whnf_def, ConLeche.defeq_def, hf, hw, hlic, hta, hde, bind,
    Except.bind, Bool.false_eq_true, if_false, pure, Except.pure]
  simp

/-! ## 3. The body theorem -/


/-! ### The leaf clauses at the io grade (task #97-P3-Core round 5)

`inferBodyIO`'s `.sort`/`.fvar`/`.const`/literal clauses are `inferBody`'s
verbatim, so at either value of the gate bit the io entry answers what
`Infer.lean`'s `infer_*` lemmas say.  Stated once here, at any mode. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1295 inferBodyIO — a sort's type is
the next sort, at the io grade. -/
theorem inferIO_sort {F d : Nat} {u : Level} :
    ConLeche.inferTypeIO mode env (F + 1) d (.sort u) =
      .ok (.sort (.succ u)) := by
  rw [ConLeche.inferTypeIO_succ]; split <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1296-1298 inferBodyIO — the scope
check, at the io grade. -/
theorem inferIO_fvar {F d idx : Nat} {ty : Expr} (h : idx < d) :
    ConLeche.inferTypeIO mode env (F + 1) d (.fvar idx ty) = .ok ty := by
  rw [ConLeche.inferTypeIO_succ]
  split <;> simp only [ConLeche.inferBodyIO, ConLeche.inferBody, if_pos h,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1299-1310 inferBodyIO — a stored
constant's type at its universe instantiation, at the io grade. -/
theorem inferIO_const {F d : Nat} {n : Name} {us : List Level}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (ht : ci.isTowerEntry = false)
    (hl : us.length = ci.toConstantVal.levelParams.length) :
    ConLeche.inferTypeIO mode env (F + 1) d (.const n us) =
      .ok (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) := by
  rw [ConLeche.inferTypeIO_succ]
  split <;> simp only [ConLeche.inferBodyIO, ConLeche.inferBody, hf, ht, hl,
    bind, Except.bind, pure, Except.pure] <;> simp

/-- con-leche: ConLeche/Kernel/Core.lean:1311-1313 inferBodyIO — a `Nat`
literal types as `Nat`, at the io grade. -/
theorem inferIO_natLit {F d n : Nat}
    (h : ConLeche.natLitSupported env = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lit (.natVal n)) =
      .ok (.const ConLeche.natName []) := by
  rw [ConLeche.inferTypeIO_succ]
  split <;> simp only [ConLeche.inferBodyIO, ConLeche.inferBody, h, if_true,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1314-1317 inferBodyIO — a string
literal types as `String`, at the io grade. -/
theorem inferIO_strLit {F d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lit (.strVal s)) =
      .ok (.const ConLeche.stringName []) := by
  rw [ConLeche.inferTypeIO_succ]
  split <;> simp only [ConLeche.inferBodyIO, ConLeche.inferBody, h, if_true,
    pure, Except.pure]

/-! ### The dispatch's children (task #97-P3-Core round 5)

`inferBodyIO_spec` below is a case split on the tag: one child per group of
the twin's `view` dispatch.  The io lane keeps CHAINED binder clauses, so
`.forallE` and `.lam` are two children here where `Infer.lean` has one
batched one. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1350-1373 inferBodyIO — **the io
`.app` clause**: the batched `inferAppIOAt`/`inferSpineIO` (task #97-P6-9)
against the chained `inferIO_app_licensed`/`inferIO_app_cert`. -/
theorem inferBodyIO_app {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hg : mode.betaGate = true)     (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.app) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1318-1327 inferBodyIO — **the `.forallE`
clause**, chained: `KnotSpec.infer`, `KnotSpec.whnf'`, `instantiate1Fast`,
`ensureSort`, `readLevelM`; pure side `Infer.lean`'s `infer_forallE` at the
io grade. -/
theorem inferBodyIO_forallE {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hg : mode.betaGate = true)     (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.forallE) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1328-1349 inferBodyIO — **the `.lam`
clause**, chained and with no domain-sort run: `instantiate1Fast`,
`KnotSpec.infer`, `lamPw`, `ensureSort`, `inferLamResult`; pure side
`inferIO_lam_chain`/`_leaf`/`_trusted`. -/
theorem inferBodyIO_lam {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hg : mode.betaGate = true)     (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lam) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1299-1310 inferBodyIO — **the `.const`
clause**, `inferBody`'s verbatim at the io grade.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem inferBodyIO_const {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hg : mode.betaGate = true)     (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.const) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
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
        have hvl := viewLen_of_denoteLs hus
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
        rename_i _ usl hlen s₁ r s₂ hvl'
        intro hck hx hp hd
        have hlen' : usl = cv.levelParams.length := by simpa using hlen
        have hl : ls.length = c.toConstantVal.levelParams.length := by
          rw [hvl] at hvl'; rw [← Option.some.inj hvl', hlen', hlp]
        exact ⟨hck, hx, hp, _, hd nm ls c hname hus hfind,
          Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfind ls),
          1, inferIO_const hfind hct hl⟩
      · mvcgen
        all_goals (bridge_peel; subst_vars)
        all_goals first
          | exact hok.caches.readN
          | exact fun h => h.elim
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1311-1317 inferBodyIO — **the two
literal clauses**, `inferBody`'s verbatim at the io grade.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem inferBodyIO_lit {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hg : mode.betaGate = true)     (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lit) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
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
             by unfold Expr.WScoped; trivial, 1, inferIO_natLit hsup.symm⟩)
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
             by unfold Expr.WScoped; trivial, 1, inferIO_strLit hsup.symm⟩)
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1374-1399 inferBodyIO — **the `.proj`
clause**, `inferBody`'s verbatim at the io grade. -/
theorem inferBodyIO_proj {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hg : mode.betaGate = true)     (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.proj) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1295-1298 inferBodyIO — **the leaf
clauses**: `.sort`, `.fvar`, and the two throws.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem inferBodyIO_leaf {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hg : mode.betaGate = true)     (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (hna : i.tag ≠ ETag.app) (hnp : i.tag ≠ ETag.proj)
    (hnf : i.tag ≠ ETag.forallE) (hnm : i.tag ≠ ETag.lam)
    (hnc : i.tag ≠ ETag.const) (hnl : i.tag ≠ ETag.lit) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v with
  | app f a => exact absurd htg hna
  | lit l => exact absurd htg hnl
  | const n us => exact absurd htg hnc
  | proj n k sub => exact absurd htg hnp
  | lam ty b m => exact absurd htg hnm
  | forallE ty b m => exact absurd htg hnf
  | letE ty w b => mvcgen; exact fun h => h.elim
  | bvar k => mvcgen; exact fun h => h.elim
  | fvar k t =>
    obtain ⟨t', rfl, ht⟩ := denote_fvar_inv hwf hv hden
    have hk : k < d := by unfold Expr.WScoped at hw; exact hw.1
    have hwt : Expr.WScoped d t' := by
      unfold Expr.WScoped at hw; exact Expr.WScoped.mono (Nat.le_of_lt hk) hw.2
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, ht, hwt, 1, inferIO_fvar hk⟩
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
        by unfold Expr.WScoped; trivial, 1, inferIO_sort⟩
      have hs1 : denoteL s₂.store.ls r₁ = some (Level.succ l) := by
        rw [hd1]; simp [denoteLView, denoteL_ext hl hx1]
      rw [hd2]; simp [denoteEView, denoteL_ext hs1 hx2]
    case vc4 => intro s h _ _ _ _ _ _ _ _ _; exact h
    case vc5 =>
      intro s _ _ _ _ _ _ _ _ hview _
      exact viewOK_sort (by rw [hview]; rfl)

/-- con-leche: ConLeche/Verify/Cached/DiscC5.lean inferBodyIOC_sim —
**THEOREM 1 for `inferBodyIO`**.

**OPEN** (task #97-P3-Core), and for the same reasons as `inferBody_spec`:
the twin's io `.app` clause is the batched `inferSpineIO`/`inferAppIOAt`
(task #97-P6-9) and its `.proj` clause needs the same three callee rules.
The io lane keeps CHAINED binder clauses — con-leche's `inferBodyIOI` does
(task #97-P6-12's own note), so `infer_lam_open`/`_cod`/`_result` survive as
this lane's λ clause and the batched-telescope debt of `Infer.lean` does NOT
apply here. -/
theorem inferBodyIO_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hg : mode.betaGate = true) (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe
      (inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe)
      (ConLeche.inferTypeIO mode env) := by
  intro s₀ d i e hok hden hw
  by_cases ha : i.tag = ETag.app
  · exact inferBodyIO_app henv hμ hg hsim s₀ d i e hok hden hw ha
  by_cases hp : i.tag = ETag.proj
  · exact inferBodyIO_proj henv hμ hg hsim s₀ d i e hok hden hw hp
  by_cases hf : i.tag = ETag.forallE
  · exact inferBodyIO_forallE henv hμ hg hsim s₀ d i e hok hden hw hf
  by_cases hm : i.tag = ETag.lam
  · exact inferBodyIO_lam henv hμ hg hsim s₀ d i e hok hden hw hm
  by_cases hc : i.tag = ETag.const
  · exact inferBodyIO_const henv hμ hg hsim s₀ d i e hok hden hw hc
  by_cases hl : i.tag = ETag.lit
  · exact inferBodyIO_lit henv hμ hg hsim s₀ d i e hok hden hw hl
  exact inferBodyIO_leaf henv hμ hg hsim s₀ d i e hok hden hw ha hp hf hm hc hl

/-! ## The axiom census of the closed children (task #97-P3-Core round 5,
sub-lane Leaves) -/

section Census

#print axioms inferIO_sort
#print axioms inferIO_fvar
#print axioms inferIO_const
#print axioms inferIO_natLit
#print axioms inferIO_strLit
#print axioms inferBodyIO_const
#print axioms inferBodyIO_lit
#print axioms inferBodyIO_leaf

end Census

end ConRon.Bridge.Core
