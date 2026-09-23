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
clause**, `inferBody`'s verbatim at the io grade. -/
theorem inferBodyIO_const {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hg : mode.betaGate = true)     (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.const) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1311-1317 inferBodyIO — **the two
literal clauses**, `inferBody`'s verbatim at the io grade. -/
theorem inferBodyIO_lit {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hg : mode.betaGate = true)     (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lit) :
    ⦃fun s => ⌜s = s₀⌝⦄
      inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
  sorry

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
clauses**: `.sort`, `.fvar`, and the two throws. -/
theorem inferBodyIO_leaf {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hg : mode.betaGate = true)     (hsim : KnotSpec mode env fe fuel)
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
  sorry

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

end ConRon.Bridge.Core
