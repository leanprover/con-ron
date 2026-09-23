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
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Walks.Frame
import ConRon.Bridge.Core.Arms.Infer
import ConRon.Bridge.Core.Walks.FvarB
import ConRon.Bridge.ExprOps.Walks

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


/-- con-leche: ConLeche/Kernel/Core.lean:1374-1399 inferBodyIO — the
projection at a **non-`Prop`** structure, at the io grade: `inferBody`'s
clause verbatim, with the subject's type read through the io slot. -/
theorem inferIO_proj_nonprop {F d i : Nat} {sn T : Name} {pe te tpe : Expr}
    {us : List Level} {entry : ProjEntry} (hgate : mode.betaGate = true)
    (hpe : ConLeche.inferTypeIO mode env F d pe = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hg : T = sn ∧ te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length)
    (hp : ¬ (Level.isEquiv entry.structSort .zero == some true)) :
    ConLeche.inferTypeIO mode env (F + 1) d (.proj sn i pe) =
      .ok (entry.typeAt us te.getAppArgs pe) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hgate]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.whnf_def, hpe, hw, hh, ht, bind, Except.bind]
  rw [if_pos hg]
  simp only [if_neg hp, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1374-1399 inferBodyIO — the
projection at a **`Prop`** structure, at the io grade. -/
theorem inferIO_proj_prop {F d i : Nat} {sn T : Name} {pe te tpe : Expr}
    {us : List Level} {entry : ProjEntry} (hgate : mode.betaGate = true)
    (hpe : ConLeche.inferTypeIO mode env F d pe = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hg : T = sn ∧ te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length)
    (hp : (Level.isEquiv entry.structSort .zero == some true))
    (hf : (Level.isEquiv
      (Level.subst entry.levelParams us entry.fieldSort) .zero
        == some true)) :
    ConLeche.inferTypeIO mode env (F + 1) d (.proj sn i pe) =
      .ok (entry.typeAt us te.getAppArgs pe) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hgate]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.whnf_def, hpe, hw, hh, ht, bind, Except.bind]
  rw [if_pos hg]
  simp only [if_pos hp, hf, pure, Except.pure]
  simp
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

/-- con-leche: ConLeche/Kernel/Core.lean:1318-1327 inferBodyIO — **the io
∀-formation rule**: `Infer.lean`'s `infer_forallE` with both inferences at
the io grade (the record `CoreFns.ioView` passes down). -/
theorem inferIO_forallE {F d : Nat} {ty body tty bt : Expr} {mb : BinderMeta}
    {u v : Level} (hg : mode.betaGate = true)
    (hty : ConLeche.inferTypeIO mode env F d ty = .ok tty)
    (hw : ConLeche.whnf mode env F d tty = .ok (.sort u))
    (hb : ConLeche.inferTypeIO mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : ConLeche.whnf mode env F (d + 1) bt = .ok (.sort v))
    (hz : mode.verifiedChecks = true → (Level.zeronessOf v == mb.pw) = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.forallE ty body mb) =
      .ok (.sort (.imax u v)) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.ensureSort, ConLeche.whnf_def, hty, hw, hb, hv, bind, Except.bind]
  cases hm : mode.verifiedChecks with
  | false => simp [pure, Except.pure]
  | true => simp only [hz hm, pure, Except.pure]; simp

/-! ### The dispatch's children (task #97-P3-Core round 5)

`inferBodyIO_spec` below is a case split on the tag: one child per group of
the twin's `view` dispatch.  The io lane keeps CHAINED binder clauses, so
`.forallE` and `.lam` are two children here where `Infer.lean` has one
batched one. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1350-1373 inferBodyIO — **the io
`.app` clause**: the batched `inferAppIOAt`/`inferSpineIO` (task #97-P6-9)
against the chained `inferIO_app_licensed`/`inferIO_app_cert`.
**CLOSED** (task #97-P3-Core round 6): `headAndArgs_app_spec`, the knot's
io slot at the head, the carry `inferSpineIO_go` (`Walks/InferSpine.lean`;
the licence test is the datum alone by `hμ`), then con-leche's
`inferSpineIO_sound` (at `hg`) and `Expr.mkAppN_getApp`. -/
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
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case app f a =>
    dsimp only
    unfold ConRon.Arena.inferAppIOAt
    -- stage 1: the spine's head and argument vector
    refine triple_seq (headAndArgs_app_spec s₀ i e hok.state hden
      (by simp [htag])) ?_
    rintro ⟨hd, args⟩ s1 ⟨hs1, hhd, hargs⟩
    subst s1
    dsimp only at hhd hargs ⊢
    -- stage 2: the head's io-grade type, once
    refine triple_seq (hsim.inferIO s₀ d hd e.getAppFn hok hhd
      (Expr.WScoped.getAppFn hw)) ?_
    rintro tf s2 ⟨hok2, hx2, hp2, th, hth, hwth, F1, hF1⟩
    -- stage 3: the batched io spine, then con-leche's identification
    refine triple_mono (inferSpineIO_go hμ hsim d args _ tf #[] 0 s2 th []
      e.getAppArgs rfl hok2 hth (InstLVec.empty _)
      (by rw [ConLeche.Expr.instantiateList_nil]; exact hwth)
      (by rw [List.drop_zero]; exact denoteEList_ext hx2 _ _ hargs)
      (Expr.WScoped.getAppArgs hw)) ?_
    rintro r s3 ⟨hok3, hx3, hp3, v, hv, hwv, F2, hF2⟩
    refine ⟨hok3, hx2.trans hx3, hp3.trans hp2, v, hv, hwv, ?_⟩
    obtain ⟨F', hF'⟩ := ConLeche.inferSpineIO_sound hg e.getAppArgs e.getAppFn
      th v F1 F2 hF1 hF2
    rw [ConLeche.Expr.mkAppN_getApp] at hF'
    exact ⟨F', hF'⟩
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-! `inferBodyIO_app`: sorry-free (task #97-P3-Core round 6). -/
#print axioms inferBodyIO_app

/-- con-leche: ConLeche/Kernel/Core.lean:1318-1327 inferBodyIO — **the `.forallE`
clause**, chained: `KnotSpec.infer`, `KnotSpec.whnf'`, `instantiate1Fast`,
`ensureSort`, `readLevelM`; pure side `Infer.lean`'s `infer_forallE` at the
io grade.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
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
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case forallE ty b m =>
    obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hv hden
    have hwt : Expr.WScoped d et := by unfold Expr.WScoped at hw; exact hw.1
    have hwb : Expr.WScoped d eb := by unfold Expr.WScoped at hw; exact hw.2
    have hi : ∀ (s : AState) (d' : Nat) (j : EIdx), CheckOK mode env fe s →
        (∃ e, denoteE s.store j = some e ∧ Expr.WScoped d' e) →
        ⦃fun s' => ⌜s' = s⌝⦄ (CoreFnsA.ioView (coreKnot mode fe id fuel)).infer d' j
        ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s.store s'.store ∧
            s'.pins = s.pins ∧ ∀ e, denoteE s.store j = some e →
              SimE (ConLeche.inferTypeIO mode env) d' e s'.store r⌝⦄ :=
      fun s d' j hck hdw => hsim.inferIO' s d' j hck hdw
    have hn : ∀ (s : AState) (d' : Nat) (j : EIdx), CheckOK mode env fe s →
        (∃ e, denoteE s.store j = some e ∧ Expr.WScoped d' e) →
        ⦃fun s' => ⌜s' = s⌝⦄ (CoreFnsA.ioView (coreKnot mode fe id fuel)).whnf d' j
        ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s.store s'.store ∧
            s'.pins = s.pins ∧ ∀ e, denoteE s.store j = some e →
              SimE (ConLeche.whnf mode env) d' e s'.store r⌝⦄ :=
      fun s d' j hck hdw => hsim.whnf' s d' j hck hdw
    have hin := fun (s : AState) (fv : EIdx) (hs : StateOK s)
        (hvs : (denoteE s.store fv).isSome = true)
        (hbs : (denoteE s.store b).isSome = true) =>
      instantiate1Fast_specE coreWalkFuel s b fv 0 hs hvs hbs
    mvcgen [ConRon.Arena.ensureSort, hi, hn, hin]
    all_goals (bridge_peel; subst_vars)
    all_goals clear_tag_hyps
    case vc2.a => exact ⟨et, hdt, hwt⟩
    case vc4.a =>
      rename_i s1 r0 s0 ck_s0 x_s1_s0 p_s0_s1 hse
      exact SimE.exists_denote (hse et hdt)
    case vc6.hv =>
      rename_i s2 r1 s1 r0 u0 s0 ck_s1 x_s2_s1 p_s1_s2 hse ck_s0 v_r0_s0 x_s1_s0
        p_s0_s1 hse_2
      exact viewOK_fvar (by rw [denote_ext hdt (x_s2_s1.trans x_s1_s0)]; rfl)
    case vc8.hvs =>
      rename_i s3 r2 s2 r1 u0 s1 r0 s0 ck_s2 wf_s0 x_s3_s2 x_s1_s0 p_s2_s3 hse _ _
        c_s0_s1 p_s0_s1 _ _ v_r0_s0 d_r0_s0 ck_s1 v_r1_s1 x_s2_s1 p_s1_s2 hse_2
      rw [d_r0_s0]
      simp [denoteEView, denote_ext hdt (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))]
    case vc9.hbs =>
      rename_i s3 r2 s2 r1 u0 s1 r0 s0 ck_s2 wf_s0 x_s3_s2 x_s1_s0 p_s2_s3 hse _ _
        c_s0_s1 p_s0_s1 _ _ v_r0_s0 d_r0_s0 ck_s1 v_r1_s1 x_s2_s1 p_s1_s2 hse_2
      rw [denote_ext hdb (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))]; rfl
    case vc10.a =>
      rename_i s4 r3 s3 r2 u0 s2 r1 s1 r0 s0 ck_s3 wf_s1 sok x_s4_s3 x_s2_s1
        x_s1_s0 p_s3_s4 hse _ c_s0_s1 _ p_s0_s1 c_s1_s2 _ hia p_s1_s2 _ _ v_r1_s1
        d_r1_s1 ck_s2 v_r2_s2 x_s3_s2 p_s2_s3 hse_2
      exact ck_s2.mono sok (x_s2_s1.trans x_s1_s0) (c_s0_s1.trans c_s1_s2)
        (p_s0_s1.trans p_s1_s2)
    case vc11.a =>
      rename_i s4 r3 s3 r2 u0 s2 r1 s1 r0 s0 ck_s3 wf_s1 sok x_s4_s3 x_s2_s1
        x_s1_s0 p_s3_s4 hse _ c_s0_s1 _ p_s0_s1 c_s1_s2 _ hia p_s1_s2 _ _ v_r1_s1
        d_r1_s1 ck_s2 v_r2_s2 x_s3_s2 p_s2_s3 hse_2
      have x41 := x_s4_s3.trans (x_s3_s2.trans x_s2_s1)
      have hfv : denoteE s1.store r1 = some (.fvar d et) := by
        rw [d_r1_s1]; simp [denoteEView, denote_ext hdt x41]
      exact ⟨_, hia _ hfv eb (denote_ext hdb x41),
        Expr.WScoped.instantiate1 hwt 0 hwb⟩
    case vc13.a =>
      rename_i s5 r4 s4 r3 u0 s3 r2 s2 r1 s1 r0 s0 ck_s4 wf_s2 sok ck_s0 x_s5_s4
        x_s3_s2 x_s2_s1 x_s1_s0 p_s4_s5 hse _ c_s1_s2 p_s0_s1 hse_2 _ p_s1_s2
        c_s2_s3 _ hia p_s2_s3 _ _ v_r2_s2 d_r2_s2 ck_s3 v_r3_s3 x_s4_s3 p_s3_s4
        hse_3
      have x52 := x_s5_s4.trans (x_s4_s3.trans x_s3_s2)
      have hfv : denoteE s2.store r2 = some (.fvar d et) := by
        rw [d_r2_s2]; simp [denoteEView, denote_ext hdt x52]
      exact SimE.exists_denote (hse_2 _ (hia _ hfv eb (denote_ext hdb x52)))
    case vc16.hwf =>
      rename_i s7 r6 s6 r5 u1 s5 r4 s4 r3 s3 r2 s2 r1 u0 s1 _ _ r0 s0 hbeq0 ck_s6
        wf_s4 sok ck_s2 hst01 x_s7_s6 x_s5_s4 x_s4_s3 x_s3_s2 _ p_s6_s7 hse _
        c_s3_s4 p_s2_s3 hse_2 p_s0_s1 _ p_s3_s4 _ c_s4_s5 _ hia dl_u0_s1 _ p_s4_s5
        _ _ v_r4_s4 d_r4_s4 ck_s5 v_r5_s5 x_s6_s5 p_s5_s6 hse_3 ck_s1 v_r1_s1
        x_s2_s1 p_s1_s2 hse_4
      rw [hst01]; exact ck_s1.state.wf
    case vc17.hv =>
      rename_i s7 r6 s6 r5 u1 s5 r4 s4 r3 s3 r2 s2 r1 u0 s1 _ _ r0 s0 hbeq0 ck_s6
        wf_s4 sok ck_s2 hst01 x_s7_s6 x_s5_s4 x_s4_s3 x_s3_s2 _ p_s6_s7 hse _
        c_s3_s4 p_s2_s3 hse_2 p_s0_s1 _ p_s3_s4 _ c_s4_s5 _ hia dl_u0_s1 _ p_s4_s5
        _ _ v_r4_s4 d_r4_s4 ck_s5 v_r5_s5 x_s6_s5 p_s5_s6 hse_3 ck_s1 v_r1_s1
        x_s2_s1 p_s1_s2 hse_4
      obtain ⟨T, hT, _⟩ := hse et hdt
      obtain ⟨W, hW, _⟩ := hse_3 T hT
      obtain ⟨U1, rfl, hU1⟩ := denote_sort_inv ck_s5.state.wf v_r5_s5 hW
      have hU1' := denoteL_ext hU1
        (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans x_s2_s1)))
      rw [hst01]
      constructor
      · intro c hc
        simp only [LNodeView.lchildren, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact lview_isSome_of_denote hU1'
        · exact lview_isSome_of_denote dl_u0_s1
      · intro c hc; simp [LNodeView.nchildren] at hc
    case vc18 =>
      rename_i s9 r8 s8 r7 u1 s7 r6 s6 r5 s5 r4 s4 r3 u0 s3 _ hμ2 r2 s2 hbeq0 r1 s1
        r0 s0 ck_s8 wf_s6 sok ck_s4 hst23 wf_s1 x_s9_s8 x_s7_s6 x_s6_s5 x_s5_s4
        hm23 x_s2_s1 p_s8_s9 hse _ c_s5_s6 p_s4_s5 hse_2 p_s2_s3 _ _ p_s5_s6 hc23
        _ c_s6_s7 _ hia dl_u0_s3 hL2 _ p_s6_s7 _ _ c_s1_s2 _ p_s1_s2 v_r6_s6
        d_r6_s6 vl_r1_s1 dl_r1_s1 ck_s7 v_r7_s7 x_s8_s7 p_s7_s8 hse_3 ck_s3
        v_r3_s3 x_s4_s3 p_s3_s4 hse_4
      intro wf_s0 x_s1_s0 _ _ c_s0_s1 p_s0_s1 _ _ _ d_r0_s0
      have ck2 := CheckOK.ofReadbackFrame ck_s3
        (ReadbackFrame.ofReadL hst23 hm23 p_s2_s3 hc23 hL2)
      have x32 : Ext s3.store s2.store := by rw [hst23]; exact Ext.refl _
      have x96 := x_s9_s8.trans (x_s8_s7.trans x_s7_s6)
      have x71 := x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans
        (x32.trans x_s2_s1))))
      refine ⟨ck2.mono ⟨wf_s0⟩ (x_s2_s1.trans x_s1_s0) (c_s0_s1.trans c_s1_s2)
          (p_s0_s1.trans p_s1_s2),
        x_s9_s8.trans (x_s8_s7.trans (x71.trans x_s1_s0)),
        p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans
          (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans p_s8_s9))))))), ?_⟩
      obtain ⟨T, hT, _, F1, hF1⟩ := hse et hdt
      obtain ⟨W, hW, _, F2, hF2⟩ := hse_3 T hT
      obtain ⟨U1, rfl, hU1⟩ := denote_sort_inv ck_s7.state.wf v_r7_s7 hW
      have hfv : denoteE s6.store r6 = some (.fvar d et) := by
        rw [d_r6_s6]; simp [denoteEView, denote_ext hdt x96]
      obtain ⟨TB, hTB, _, F3, hF3⟩ := hse_2 _ (hia _ hfv eb (denote_ext hdb x96))
      obtain ⟨W2, hW2, _, F4, hF4⟩ := hse_4 TB hTB
      obtain ⟨U0, rfl, hU0⟩ := denote_sort_inv ck_s3.state.wf v_r3_s3 hW2
      obtain rfl : r2 = U0 := Option.some.inj (dl_u0_s3.symm.trans hU0)
      have hz : mode.verifiedChecks = true → (r2.zeronessOf == m.pw) = true :=
        fun _ => by simpa using hbeq0
      have hl1 : denoteL s1.store.ls r1 = some (.imax U1 r2) := by
        rw [dl_r1_s1]
        simp [denoteLView, opt2, denoteL_ext hU1 x71,
          denoteL_ext hU0 (x32.trans x_s2_s1)]
      refine ⟨.sort (.imax U1 r2), ?_, by unfold Expr.WScoped; trivial,
        max F1 (max F2 (max F3 F4)) + 1, ?_⟩
      · rw [d_r0_s0]; simp [denoteEView, denoteL_ext hl1 x_s1_s0]
      · exact inferIO_forallE hg
          (ConLeche.inferTypeIO_mono (by omega) hF1)
          (ConLeche.whnf_mono (by omega) hF2)
          (ConLeche.inferTypeIO_mono (by omega) hF3)
          (ConLeche.whnf_mono (by omega) hF4) hz
    case vc19 => intro s hwf _ _ _ _ _ _ _ _ _; exact hwf
    case vc20 =>
      intro s _ _ _ _ _ _ _ _ hview _
      exact viewOK_sort (by rw [hview]; rfl)
    all_goals first
      | assumption
      | exact fun h => h.elim
      | (apply CheckOK.wf'; assumption)
      | (constructor; assumption)
      | (apply CacheOK.readL; apply CheckOK.caches; assumption)
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: none — **a `pure` exit** at a pinned state (`Defeq.lean`'s
`triple_pure_post`, which this module does not import). -/
theorem triple_pure_lam {α : Type} {s₀ : AState} {v : α}
    {Q : α → AState → Prop} (h : Q v s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ (pure v : AM α) ⦃⇓? r s => ⌜Q r s⌝⦄ := by
  mvcgen
  subst_vars; exact h

/-- con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody — the λ
clause's result `.forallE ty (bt.abstract1 depth) mb`, the twin's
`inferLamResult`: `abstract1Fast` (over the Core tier's `fvarBSpec`,
`Walks/FvarB.lean`) then one intern. -/
theorem inferLamResult_spec {fe : IFEnv} (s₀ : AState) (ty bt : EIdx) (d : Nat)
    (m : BinderMeta) (et vbt : Expr) (hok : CheckOK mode env fe s₀)
    (hdt : denoteE s₀.store ty = some et) (hdb : denoteE s₀.store bt = some vbt) :
    ⦃fun s => ⌜s = s₀⌝⦄ inferLamResult ty bt d m
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (.forallE et (vbt.abstract1 d) m)⌝⦄ := by
  unfold inferLamResult
  refine triple_seq (ExprOps.abstract1Fast_spec fvarBSpec coreWalkFuel s₀ bt d 0
    hok.state (by rw [hdb]; rfl)) ?_
  rintro ab s1 ⟨hso1, hx1, _, hc1, hp1, _, hrel⟩
  have hok1 := hok.mono hso1 hx1 hc1 hp1
  have hdab : denoteE s1.store ab = some (vbt.abstract1 d 0) := hrel vbt hdb
  have hdt1 := denote_ext hdt hx1
  refine triple_mono (internE_spec s1 (.forallE ty ab m) hok1.state.wf
    (viewOK_forallE (by rw [hdt1]; rfl) (by rw [hdab]; rfl))) ?_
  rintro r s2 ⟨hwf2, hx2, _, _, _, _, hc2, hp2, _, hd2⟩
  refine ⟨hok1.mono ⟨hwf2⟩ hx2 hc2 hp2, hx1.trans hx2, hp2.trans hp1, ?_⟩
  rw [hd2]
  simp [denoteEView, denote_ext hdt1 hx2, denote_ext hdab hx2]

/-- con-leche: ConLeche/Kernel/Core.lean:1101-1107 ensureSort — the twin's
`ensureSort` through the io record (`CoreFnsA.ioView`, whose `whnf` slot is
the knot's): the answer denotes the level a `whnf` of the subject reached. -/
theorem ensureSort_ioView_spec {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (s₀ : AState) (d : Nat) (j : EIdx)
    (t : Expr) (hok : CheckOK mode env fe s₀)
    (hd : denoteE s₀.store j = some t) (hw : Expr.WScoped d t) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.ensureSort (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d j
    ⦃⇓? u s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ U, denoteL s'.store.ls u = some U ∧
          ∃ F, ConLeche.whnf mode env F d t = .ok (.sort U)⌝⦄ := by
  unfold ConRon.Arena.ensureSort
  have hn : ⦃fun s => ⌜s = s₀⌝⦄
      (CoreFnsA.ioView (coreKnot mode fe id fuel)).whnf d j
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnf mode env) d t s'.store r⌝⦄ :=
    hsim.whnf s₀ d j t hok hd hw
  refine triple_seq hn ?_
  rintro wr s1 ⟨hok1, hx1, hp1, W, hW, _, F, hF⟩
  obtain ⟨vw, hvw⟩ := denoteE_view hW
  refine tag_view_bind_triple hvw ?_
    (fun hne => by cases vw <;> first | rfl | exact absurd rfl hne)
  cases vw
  case sort u =>
    obtain ⟨U, rfl, hU⟩ := denote_sort_inv hok1.state.wf hvw hW
    exact triple_pure_lam ⟨hok1, hx1, hp1, U, hU, F, hF⟩
  all_goals exact triple_fail

/-- con-leche: ConLeche/Kernel/Core.lean:1328-1349 inferBodyIO — **the `.lam`
clause**, chained and with no domain-sort run: `instantiate1Fast`,
`KnotSpec.infer`, `lamPw`, `ensureSort`, `inferLamResult`; pure side
`inferIO_lam_chain`/`_leaf` (the `_trusted` exit is unreachable under `hμ`).
**CLOSED** (task #97-P3-Core round 6, lane `lam`), staged: `internE` of the
free variable, `instantiate1Fast_specE`, the io knot slot, `lamPw_spec`, then
either the chain exit or the leaf's io knot slot, `ensureSort_ioView_spec`
and `readLevelM_spec`; both exits end in `inferLamResult_spec`, whose
`abstract1Fast` needs the Core tier's `fvarBSpec` (`Walks/FvarB.lean`). -/
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
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  unfold ConRon.Arena.inferBodyIO
  refine view_bind_triple hv ?_
  cases v
  case lam ty b m =>
    obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hv hden
    have hwt : Expr.WScoped d et := by unfold Expr.WScoped at hw; exact hw.1
    have hwb : Expr.WScoped d eb := by unfold Expr.WScoped at hw; exact hw.2
    dsimp only
    -- stage 1: the free variable
    refine triple_seq (internE_spec s₀ (.fvar d ty) hwf
      (viewOK_fvar (by rw [hdt]; rfl))) ?_
    rintro fv s1 ⟨hwf1, hx1, _, _, _, _, hc1, hp1, _, hd1⟩
    have hok1 := hok.mono ⟨hwf1⟩ hx1 hc1 hp1
    have hfv : denoteE s1.store fv = some (.fvar d et) := by
      rw [hd1]; simp [denoteEView, denote_ext hdt hx1]
    -- stage 2: open the body
    refine triple_seq (instantiate1Fast_specE coreWalkFuel s1 b fv 0 hok1.state
      (by rw [hfv]; rfl) (by rw [denote_ext hdb hx1]; rfl)) ?_
    rintro ob s2 ⟨hso2, hx2, hc2, hp2, _, hia⟩
    have hok2 := hok1.mono hso2 hx2 hc2 hp2
    have hob : denoteE s2.store ob = some (eb.instantiate1 (.fvar d et) 0) :=
      hia _ hfv eb (denote_ext hdb hx1)
    have hwob : Expr.WScoped (d + 1) (eb.instantiate1 (.fvar d et) 0) :=
      Expr.WScoped.instantiate1 hwt 0 hwb
    have hx02 : Ext s₀.store s2.store := hx1.trans hx2
    -- stage 3: the body's io type
    have hi3 : ⦃fun s => ⌜s = s2⌝⦄
        (CoreFnsA.ioView (coreKnot mode fe id fuel)).infer (d + 1) ob
        ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s2.store s'.store ∧
          s'.pins = s2.pins ∧
          SimE (ConLeche.inferTypeIO mode env) (d + 1)
            (eb.instantiate1 (.fvar d et) 0) s'.store r⌝⦄ :=
      hsim.inferIO s2 (d + 1) ob _ hok2 hob hwob
    refine triple_seq hi3 ?_
    rintro bt s3 ⟨hok3, hx3, hp3, vbt, hvbt, hwvbt, F1, hF1⟩
    have hx03 : Ext s₀.store s3.store := hx02.trans hx3
    have hp03 : s3.pins = s₀.pins := hp3.trans (hp2.trans hp1)
    have hwres : Expr.WScoped d (.forallE et (vbt.abstract1 d) m) := by
      unfold Expr.WScoped; exact ⟨hwt, ConLeche.WScoped.abstract1 0 hwvbt⟩
    rw [if_pos hμ]
    -- stage 4: the body's own binder datum
    refine triple_seq (ExprOps.lamPw_spec s3 b hok3.state
      (by rw [denote_ext hdb hx03]; rfl)) ?_
    rintro pw s4 ⟨hs4, hpw⟩
    subst s4
    have hpw' : pw = eb.lamPw := hpw eb (denote_ext hdb hx03)
    cases pw with
    | some pwI =>
      dsimp only
      split
      · exact triple_fail
      · rename_i hz
        have hz' : (m.pw == pwI) = true := by simpa using hz
        refine triple_mono (inferLamResult_spec s3 ty bt d m et vbt hok3
          (denote_ext hdt hx03) hvbt) ?_
        rintro r s' ⟨hok', hx', hp', hd'⟩
        exact ⟨hok', hx03.trans hx', hp'.trans hp03, _, hd', hwres, F1 + 1,
          inferIO_lam_chain hg hF1 hμ hpw'.symm hz'⟩
    | none =>
      dsimp only
      -- stage 5: the leaf's codomain sort
      have hi5 : ⦃fun s => ⌜s = s3⌝⦄
          (CoreFnsA.ioView (coreKnot mode fe id fuel)).infer (d + 1) bt
          ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s3.store s'.store ∧
            s'.pins = s3.pins ∧
            SimE (ConLeche.inferTypeIO mode env) (d + 1) vbt s'.store r⌝⦄ :=
        hsim.inferIO s3 (d + 1) bt vbt hok3 hvbt hwvbt
      refine triple_seq hi5 ?_
      rintro btt s5 ⟨hok5, hx5, hp5, vbtt, hvbtt, hwvbtt, F2, hF2⟩
      refine triple_seq (ensureSort_ioView_spec hsim s5 (d + 1) btt vbtt hok5
        hvbtt hwvbtt) ?_
      rintro vb s6 ⟨hok6, hx6, hp6, U, hU, F3, hF3⟩
      refine triple_seq (readLevelM_spec s6 vb hok6.caches.readL) ?_
      rintro lvb s7 ⟨hst7, hm7, hp7, hc7, hl7, hL7⟩
      have hok7 := CheckOK.ofReadbackFrame hok6
        (ReadbackFrame.ofReadL hst7 hm7 hp7 hc7 hL7)
      obtain rfl : lvb = U := Option.some.inj (hl7.symm.trans hU)
      have hx37 : Ext s3.store s7.store := by
        rw [hst7]; exact hx5.trans hx6
      split
      · exact triple_fail
      · rename_i hz
        have hz' : (Level.zeronessOf lvb == m.pw) = true := by simpa using hz
        refine triple_mono (inferLamResult_spec s7 ty bt d m et vbt hok7
          (denote_ext hdt (hx03.trans hx37)) (denote_ext hvbt hx37)) ?_
        rintro r s' ⟨hok', hx', hp', hd'⟩
        refine ⟨hok', hx03.trans (hx37.trans hx'),
          hp'.trans (hp7.trans (hp6.trans (hp5.trans hp03))), _, hd', hwres,
          max F1 (max F2 F3) + 1, ?_⟩
        exact inferIO_lam_leaf hg (ConLeche.inferTypeIO_mono (by omega) hF1) hμ
          hpw'.symm (ConLeche.inferTypeIO_mono (by omega) hF2)
          (ConLeche.whnf_mono (by omega) hF3) hz'
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

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
      all_goals clear_tag_hyps
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
        all_goals clear_tag_hyps
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
        all_goals clear_tag_hyps
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
      all_goals clear_tag_hyps
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
      all_goals clear_tag_hyps
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
clause**, `inferBody`'s verbatim at the io grade.

**CLOSED** (round 5), staged by `triple_seq` (`Memo.lean`): every
callee is applied at a subject whose denotation the previous stage NAMED,
and every callee rule it needs was already closed. -/
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
    refine triple_seq (hsim.inferIO s₀ d pe es hok hpe hwes) ?_
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
    refine tag_view_bind_triple hvh ?_
      (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
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
          have hinf : ConLeche.inferTypeIO mode env (max F1 F2) d es =
              .ok vt :=
            ConLeche.inferTypeIO_mono (Nat.le_max_left _ _) hF1
          have hwty : Expr.WScoped d (p.typeAt ls vte.getAppArgs es) :=
            ConLeche.projEntry_typeAt_WScoped henv hfp ls hlen'
              (Expr.WScoped.getAppArgs hwvte) hwes
          -- the answer, at any state the fence leaves behind
          have hfin : ∀ (s : AState), CheckOK mode env fe s →
              s.store = s4.store → s.pins = s₀.pins →
              (∃ F, ConLeche.inferTypeIO mode env F d (.proj nm k es) =
                .ok (p.typeAt ls vte.getAppArgs es)) →
              ⦃fun s' => ⌜s' = s⌝⦄ entry.typeAt us targs pe
              ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
                  s'.pins = s₀.pins ∧
                  SimE (ConLeche.inferTypeIO mode env) d (.proj nm k es)
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
                ⟨max F1 F2 + 1, inferIO_proj_prop hg hinf hwhnf hgf hfp hgP
                  (by simpa using hprop) (by simpa using hfield)⟩
          next hprop =>
            exact hfin s8 hok8 hst8 (hp8.trans hp04)
              ⟨max F1 F2 + 1, inferIO_proj_nonprop hg hinf hwhnf hgf hfp hgP
                (by simpa using hprop)⟩
        next => exact triple_fail
    all_goals (dsimp only; exact triple_fail)
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg


#print axioms inferBodyIO_proj

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
    all_goals clear_tag_hyps
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
#print axioms inferIO_forallE
#print axioms inferBodyIO_forallE
end Census

/-! Lane `lam` (task #97-P3-Core round 6): the `.lam` clause, sorry-free. -/

section CensusLam
#print axioms inferLamResult_spec
#print axioms ensureSort_ioView_spec
#print axioms inferBodyIO_lam
end CensusLam

end ConRon.Bridge.Core
