/-
# `ConRon.Bridge.Checker.Split` — the two folds are one accept

`Arena/Checker.lean` has two folds and its module note says why:

> * **`checkDeclsPure`** is the THEOREM's shape […] one step per record,
>   install and check together.
> * **`installThenCheck`** is what the BINARY runs […] phase A installs every
>   record, annotating its header and its value but not inferring; phase B
>   checks each recorded declaration against the PREFIX VIEW it was installed
>   at.  con-leche proves the two are the same accept
>   (`fullyChecked_checkDecls`).

`Bridge/Checker/Fold.lean` proves Theorem 1 for `checkDeclsPure`.  This module
is what carries it to `installThenCheck`, and it is the history report's
**fine print 5** in full:

> If the foreign core wants the two-phase install-then-check fold rather than
> `checkDeclsPure`'s straight fold, it must additionally re-derive
> `checkDecl_of_split_{defn,thm,opaque}` (`Verify/CheckerSplit.lean`) and the
> prefix-view congruence (`KnotCongr.lean:543`,
> `mkFEnv_find?_visibleBelow`).

Both exist in con-leche at `78ded4b6` and neither has to be re-derived — they
have to be *reached*:

* `ConLeche.checkDecl_of_split_defn` / `_thm` / `_opaque`
  (`Verify/CheckerSplit.lean:319` / `:344` / `:364`) take the install half and
  the check half AT THE SAME ENVIRONMENT and give `checkDecl`'s own run.  So
  the arena's phase A must give con-leche's `installConstantVal` /
  `installValue` at the prefix environment, and its phase B must give
  con-leche's `checkValueGroup` at the SAME one;
* `ConLeche.mkFEnv_find?_visibleBelow` (`Verify/EnvBound.lean:141`) is what
  makes "the same one" true: phase B runs at `fe.restrictTo pc.vis`, whose
  `find?` is `(env.prefixTo pc.vis).find?` — the environment the record was
  installed at — provided the final environment's names are `Nodup`.  That
  side condition is `checkConstantVal`'s duplicate test, accumulated over the
  fold.

## The three-way fuel

`checkDecl_of_split_*` take the two halves at ONE fuel and con-leche raises
each half with `installConstantVal_mono` / `checkValueGroup_mono`
(`Verify/CheckerSplit.lean:233`–`:247`) before combining — `max F₁ F` at
`Verify/Cached/InstalledC.lean:416`.  `Bridge/Checker/Mono.lean`'s
`checkDecl_mono` is the same idea one level up, and the fold here needs both.

## What this module states and what it does not

It states the five bridge theorems of `Arena/CheckerSplit.lean` and
`Arena/Checker.lean`'s phase-A/phase-B pair, and the punchline
`Arena.installThenCheck_bridge`.  It does not restate the model tier: the
punchline lands on `Bridge/Checker/Fold.lean`'s `checkDeclsPure` statement, so
`Bridge/Checker/Capstone.lean` covers both folds with one composition.
-/
import ConRon.Bridge.Checker.Fold
import ConLeche.Verify.EnvBound

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The install half -/

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:64-85 installConstantVal —
the PURE half: nine guards accepted means con-leche's install accepts with the
annotated header. -/
theorem installConstantVal_pure {μ : CheckMode} {F : Nat} {env : Env}
    {c : ConstantVal} {ty : Expr}
    (h1 : env.find? c.name = none)
    (h2 : ConLeche.reservedBasisNames.contains c.name = false)
    (h3 : c.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup c.levelParams = true)
    (h5 : c.type.looseBVarsBounded 0 = true)
    (h6 : c.type.hasFvar = false)
    (h7 : ConLeche.annotateCore μ env F 0 c.type = .ok ty)
    (h8 : ty.allLevelParamsDefined c.levelParams = true)
    (h9 : ty.constsResolve env = true) :
    ConLeche.installConstantVal (ConLeche.fueledOps μ F) env c
      = .ok { c with type := ty } := by
  simp only [ConLeche.installConstantVal, ConLeche.fueledOps, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, Option.isSome_none, Bool.false_eq_true, if_false,
    if_true, bind, Except.bind, pure, Except.pure]


/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:64-85 installConstantVal —
the header's guards and annotation, without the inference.

**PROVED** (task #97-P3-Checker round 4): the same six guards as
`checkConstantVal_bridge` (`Bridge/Checker/Base.lean`) and its annotation,
stopping before the inference and the sort test — con-leche's own
`installConstantVal` is `checkConstantVal` minus exactly those two calls, so
the two proofs are the same nine steps and this one ends at the ninth.  It
was waiting on `allLevelParamsDefined_run` and `constsResolveFFast_run`,
closed in the same round. -/
theorem installConstantVal_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {cv cvA : IConstantVal} {c : ConstantVal} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : installConstantVal μ fe cv s = .ok (cvA, s')) :
    CoreStep μ env fe s s' ∧ ∃ cA F, Frontend.denoteCV s'.store cvA = some cA ∧
      ConLeche.installConstantVal (ConLeche.fueledOps μ F) env c = .ok cA := by
  obtain ⟨hnm, hlps, hty⟩ := denoteCV_inv hcv
  have hknot := hk.knot env fe hok.envWF
  have hck0 : CheckOK μ env fe s := hok.check
  have hnever : ∀ {α β γ : Type} {x : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (x >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  simp only [Arena.installConstantVal] at hrun
  -- 1. the duplicate-declaration guard
  obtain ⟨hdup, r1⟩ := AM.dguard_ok hnever hrun
  replace r1 := AM.pure_bind_ok r1
  have hfind : fe.find? cv.name = none := by
    cases hf : fe.find? cv.name with
    | none => rfl
    | some ci => rw [hf] at hdup; exact absurd rfl hdup
  have hfindP : env.find? c.name = none :=
    IFEnvOK.miss hck0.state hck0.ienv hnm hfind
  -- 2. the reserved-name guard
  obtain ⟨rs, s2, g2r, r2⟩ := AM.bind_ok r1
  obtain ⟨hp2, hrs⟩ := reservedBasisNames_run hck0.state.wf hck0.pins g2r
  have hck2 : CheckOK μ env fe s2 := hck0.mono ⟨hp2.wf⟩ hp2.ext hp2.caches hp2.pins
  have hnm2 : denoteN s2.store.ns cv.name = some c.name := denoteN_ext hnm hp2.ext
  have hlps2 : Frontend.denoteNList s2.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hp2.ext.lss.ls.ns _ _ hlps
  have hty2 : denoteE s2.store cv.type = some c.type := denote_ext hty hp2.ext
  obtain ⟨hres, r3⟩ := AM.dguard_ok hnever r2
  replace r3 := AM.pure_bind_ok r3
  have hresP : ConLeche.reservedBasisNames.contains c.name = false := by
    have hc := denoteNList_contains hck2.state.wf rs reservedBasisNameValues
      (denoteNL_toList rs reservedBasisNameValues hrs) cv.name c.name hnm2
    rw [← reservedBasisNameValues_eq, ← hc]
    cases hb : rs.contains cv.name with
    | false => rfl
    | true => rw [hb] at hres; exact absurd rfl hres
  -- 3. the reserved-projection-name guard
  obtain ⟨b3, s3, g3r, r4⟩ := AM.bind_ok r3
  obtain ⟨hs3, hb3⟩ := isProjFnShape_run hck2.state rfl hnm2 g3r
  obtain ⟨hproj, r5⟩ := AM.dguard_ok hnever r4
  replace r5 := AM.pure_bind_ok r5
  have hprojP : c.name.isProjFnShape = false := by
    rw [← hb3]
    cases hb : b3 with
    | false => rfl
    | true => rw [hb] at hproj; exact absurd rfl hproj
  -- 4. the duplicate-universe-parameter guard
  obtain ⟨hnod, r6⟩ := AM.dunless_ok hnever r5
  replace r6 := AM.pure_bind_ok r6
  have hnodP : ConLeche.Name.nodup c.levelParams = true := by
    rw [← nameNodup_spec hck2.state.wf cv.levelParams c.levelParams hlps2]
    exact hnod
  subst hs3
  -- 5. the loose-bound-variable guard
  obtain ⟨b5, s5, g5r, r7⟩ := AM.bind_ok r6
  obtain ⟨h5st, h5c, h5p, h5r⟩ := AM.of_run (P := fun t => t = s3)
    (Q := fun r t => t.store = s3.store ∧ t.caches = s3.caches ∧
      t.pins = s3.pins ∧ RelV (Expr.looseBVarsBounded 0) s3.store cv.type r)
    rfl g5r (ConRon.Bridge.ExprOps.looseBVarsBoundedFast_spec coreWalkFuel 0 s3
      cv.type hck2.state (by rw [hty2]; rfl))
  obtain ⟨hlbb, r8⟩ := AM.dunless_ok hnever r7
  replace r8 := AM.pure_bind_ok r8
  have hlbbP : c.type.looseBVarsBounded 0 = true := by
    rw [← h5r c.type hty2]; exact hlbb
  have hck5 : CheckOK μ env fe s5 :=
    hck2.mono ⟨by rw [h5st]; exact hck2.state.wf⟩ (by rw [h5st]; exact Ext.refl _)
      h5c h5p
  have hnm5 : denoteN s5.store.ns cv.name = some c.name := by rw [h5st]; exact hnm2
  have hty5 : denoteE s5.store cv.type = some c.type := by rw [h5st]; exact hty2
  have hlps5 : Frontend.denoteNList s5.store.ns cv.levelParams
      = some c.levelParams := by rw [h5st]; exact hlps2
  -- 6. the free-variable guard
  obtain ⟨b6, s6, g6r, r9⟩ := AM.bind_ok r8
  obtain ⟨h6st, h6c, h6p, h6r⟩ := AM.of_run (P := fun t => t = s5)
    (Q := fun r t => t.store = s5.store ∧ t.caches = s5.caches ∧
      t.pins = s5.pins ∧ RelV Expr.hasFvar s5.store cv.type r)
    rfl g6r (ConRon.Bridge.ExprOps.hasFvarFast_spec coreWalkFuel s5 cv.type
      hck5.state (by rw [hty5]; rfl))
  obtain ⟨hfv, r10⟩ := AM.dguard_ok hnever r9
  replace r10 := AM.pure_bind_ok r10
  have hfvP : c.type.hasFvar = false := by
    rw [← h6r c.type hty5]
    cases hb : b6 with
    | false => rfl
    | true => rw [hb] at hfv; exact absurd rfl hfv
  have hck6 : CheckOK μ env fe s6 :=
    hck5.mono ⟨by rw [h6st]; exact hck5.state.wf⟩ (by rw [h6st]; exact Ext.refl _)
      h6c h6p
  have hnm6 : denoteN s6.store.ns cv.name = some c.name := by rw [h6st]; exact hnm5
  have hty6 : denoteE s6.store cv.type = some c.type := by rw [h6st]; exact hty5
  have hlps6 : Frontend.denoteNList s6.store.ns cv.levelParams
      = some c.levelParams := by rw [h6st]; exact hlps5
  have hws : Expr.WScoped 0 c.type := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  have hden6 : denoteFEnv s6.store fe = some env := by
    rw [h6st, h5st]
    exact denoteFEnv_pext (PExt.of_ext hp2.ext) hok.persEnv hok.denote
  -- 7. the annotation
  obtain ⟨type, s7, g7r, r11⟩ := AM.bind_ok r10
  obtain ⟨hck7, hx7, hp7, hsim7⟩ := AM.of_run (P := fun t => t = s6)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s6.store t.store ∧
      t.pins = s6.pins ∧
      Core.SimE (ConLeche.annotateCore μ env) 0 c.type t.store r)
    rfl g7r (hknot.annotate s6 0 cv.type c.type hck6 hty6 hws)
  obtain ⟨v, hv7, hwsv, F7, hF7⟩ := hsim7
  have hnm7 : denoteN s7.store.ns cv.name = some c.name := denoteN_ext hnm6 hx7
  have hlps7 : Frontend.denoteNList s7.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hx7.lss.ls.ns _ _ hlps6
  have hden7 : denoteFEnv s7.store fe = some env :=
    denoteFEnv_pext (PExt.of_ext hx7) hok.persEnv hden6
  -- 8. the undeclared-universe-parameter guard
  obtain ⟨b8, s8, g8r, r12⟩ := AM.bind_ok r11
  obtain ⟨h8st, h8c, h8p, h8r⟩ :=
    allLevelParamsDefined_run hck7.state hlps7 hv7 g8r
  obtain ⟨hlpd, r13⟩ := AM.dunless_ok hnever r12
  replace r13 := AM.pure_bind_ok r13
  have hlpdP : v.allLevelParamsDefined c.levelParams = true := by
    rw [← h8r]; exact hlpd
  have hck8 : CheckOK μ env fe s8 :=
    hck7.mono ⟨by rw [h8st]; exact hck7.state.wf⟩ (by rw [h8st]; exact Ext.refl _)
      h8c h8p
  have hv8 : denoteE s8.store type = some v := by rw [h8st]; exact hv7
  have hnm8 : denoteN s8.store.ns cv.name = some c.name := by rw [h8st]; exact hnm7
  have hlps8 : Frontend.denoteNList s8.store.ns cv.levelParams
      = some c.levelParams := by rw [h8st]; exact hlps7
  have hden8 : denoteFEnv s8.store fe = some env := by rw [h8st]; exact hden7
  -- 9. the unresolved-constant guard
  obtain ⟨b9, s9, g9r, r14⟩ := AM.bind_ok r13
  have hpins8 : s8.pins = s.pins := by rw [h8p, hp7, h6p, h5p, hp2.pins]
  obtain ⟨h9st, h9c, h9p, h9r⟩ :=
    constsResolveFFast_run ⟨hck8, hok.envWF, hok.persPins.mono hpins8,
      hok.persEnv, hok.coh, hden8⟩ hv8 g9r
  obtain ⟨hcr, r15⟩ := AM.dunless_ok
    (AM.Never.bind fun _ => AM.Never.bind fun _ => AM.Never.fail_any) r14
  replace r15 := AM.pure_bind_ok r15
  have hcrP : v.constsResolve env = true := by rw [← h9r]; exact hcr
  have hck9 : CheckOK μ env fe s9 :=
    hck8.mono ⟨by rw [h9st]; exact hck8.state.wf⟩ (by rw [h9st]; exact Ext.refl _)
      h9c h9p
  have hv9 : denoteE s9.store type = some v := by rw [h9st]; exact hv8
  have hnm9 : denoteN s9.store.ns cv.name = some c.name := by rw [h9st]; exact hnm8
  have hlps9 : Frontend.denoteNList s9.store.ns cv.levelParams
      = some c.levelParams := by rw [h9st]; exact hlps8
  -- 10. the answer
  obtain ⟨hcvA, hs'⟩ := AM.pure_ok r15
  subst hcvA
  subst hs'
  have hext : Ext s.store s'.store := by
    refine hp2.ext.trans ?_
    rw [← h5st, ← h6st]
    refine hx7.trans ?_
    rw [← h8st, ← h9st]
    exact Ext.refl _
  have hpins : s'.pins = s.pins := by
    rw [h9p, h8p, hp7, h6p, h5p, hp2.pins]
  refine ⟨⟨hck9, hext, hpins⟩, ⟨{ c with type := v }, F7, ?_, ?_⟩⟩
  · simp only [Frontend.denoteCV, hnm9, hlps9, hv9]
  · exact installConstantVal_pure hfindP hresP hprojP hnodP hlbbP hfvP hF7
      hlpdP hcrP

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:87-100 installValue — the
PURE half: five guards accepted means con-leche's install accepts with the
annotated value. -/
theorem installValue_pure {μ : CheckMode} {F : Nat} {env : Env}
    {c : ConstantVal} {x ty : Expr}
    (h5 : x.looseBVarsBounded 0 = true)
    (h6 : x.hasFvar = false)
    (h7 : ConLeche.annotateCore μ env F 0 x = .ok ty)
    (h8 : ty.allLevelParamsDefined c.levelParams = true)
    (h9 : ty.constsResolve env = true) :
    ConLeche.installValue (ConLeche.fueledOps μ F) env c x = .ok ty := by
  simp only [ConLeche.installValue, ConLeche.fueledOps, h5, h6, h7, h8, h9,
    Bool.false_eq_true, if_false, if_true, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:87-100 installValue — the
value's guards and annotation.

**PROVED** (task #97-P3-Checker round 4): the last five steps of
`installConstantVal_bridge`, at the VALUE rather than the type —
`looseBVarsBoundedFast` and `hasFvarFast` (`Bridge/ExprOps/Walks.lean`),
`KnotSpec.annotate`, `allLevelParamsDefined_run` and
`constsResolveFFast_run`. -/
theorem installValue_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cv : IConstantVal} {c : ConstantVal} {value jv : EIdx} {x : Expr}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : installValue μ fe cv value s = .ok (jv, s')) :
    CoreStep μ env fe s s' ∧ ∃ y F, denoteE s'.store jv = some y ∧
      ConLeche.installValue (ConLeche.fueledOps μ F) env c x = .ok y := by
  obtain ⟨hnm, hlps, -⟩ := denoteCV_inv hcv
  have hknot := hk.knot env fe hok.envWF
  have hck0 : CheckOK μ env fe s := hok.check
  have hnever : ∀ {α β γ : Type} {x : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (x >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  simp only [Arena.installValue] at hrun
  -- 1. the loose-bound-variable guard
  obtain ⟨b5, s5, g5r, r7⟩ := AM.bind_ok hrun
  obtain ⟨h5st, h5c, h5p, h5r⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t.store = s.store ∧ t.caches = s.caches ∧
      t.pins = s.pins ∧ RelV (Expr.looseBVarsBounded 0) s.store value r)
    rfl g5r (ConRon.Bridge.ExprOps.looseBVarsBoundedFast_spec coreWalkFuel 0 s
      value hck0.state (by rw [hv]; rfl))
  obtain ⟨hlbb, r8⟩ := AM.dunless_ok hnever r7
  replace r8 := AM.pure_bind_ok r8
  have hlbbP : x.looseBVarsBounded 0 = true := by
    rw [← h5r x hv]; exact hlbb
  have hck5 : CheckOK μ env fe s5 :=
    hck0.mono ⟨by rw [h5st]; exact hck0.state.wf⟩ (by rw [h5st]; exact Ext.refl _)
      h5c h5p
  have hv5 : denoteE s5.store value = some x := by rw [h5st]; exact hv
  have hlps5 : Frontend.denoteNList s5.store.ns cv.levelParams
      = some c.levelParams := by rw [h5st]; exact hlps
  -- 2. the free-variable guard
  obtain ⟨b6, s6, g6r, r9⟩ := AM.bind_ok r8
  obtain ⟨h6st, h6c, h6p, h6r⟩ := AM.of_run (P := fun t => t = s5)
    (Q := fun r t => t.store = s5.store ∧ t.caches = s5.caches ∧
      t.pins = s5.pins ∧ RelV Expr.hasFvar s5.store value r)
    rfl g6r (ConRon.Bridge.ExprOps.hasFvarFast_spec coreWalkFuel s5 value
      hck5.state (by rw [hv5]; rfl))
  obtain ⟨hfv, r10⟩ := AM.dguard_ok hnever r9
  replace r10 := AM.pure_bind_ok r10
  have hfvP : x.hasFvar = false := by
    rw [← h6r x hv5]
    cases hb : b6 with
    | false => rfl
    | true => rw [hb] at hfv; exact absurd rfl hfv
  have hck6 : CheckOK μ env fe s6 :=
    hck5.mono ⟨by rw [h6st]; exact hck5.state.wf⟩ (by rw [h6st]; exact Ext.refl _)
      h6c h6p
  have hv6 : denoteE s6.store value = some x := by rw [h6st]; exact hv5
  have hlps6 : Frontend.denoteNList s6.store.ns cv.levelParams
      = some c.levelParams := by rw [h6st]; exact hlps5
  have hws : Expr.WScoped 0 x := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  have hden6 : denoteFEnv s6.store fe = some env := by
    rw [h6st, h5st]; exact hok.denote
  -- 3. the annotation
  obtain ⟨jv2, s7, g7r, r11⟩ := AM.bind_ok r10
  obtain ⟨hck7, hx7, hp7, hsim7⟩ := AM.of_run (P := fun t => t = s6)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s6.store t.store ∧
      t.pins = s6.pins ∧
      Core.SimE (ConLeche.annotateCore μ env) 0 x t.store r)
    rfl g7r (hknot.annotate s6 0 value x hck6 hv6 hws)
  obtain ⟨w, hw7, hwsw, F7, hF7⟩ := hsim7
  have hlps7 : Frontend.denoteNList s7.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hx7.lss.ls.ns _ _ hlps6
  have hden7 : denoteFEnv s7.store fe = some env :=
    denoteFEnv_pext (PExt.of_ext hx7) hok.persEnv hden6
  -- 4. the undeclared-universe-parameter guard
  obtain ⟨b8, s8, g8r, r12⟩ := AM.bind_ok r11
  obtain ⟨h8st, h8c, h8p, h8r⟩ :=
    allLevelParamsDefined_run hck7.state hlps7 hw7 g8r
  obtain ⟨hlpd, r13⟩ := AM.dunless_ok hnever r12
  replace r13 := AM.pure_bind_ok r13
  have hlpdP : w.allLevelParamsDefined c.levelParams = true := by
    rw [← h8r]; exact hlpd
  have hck8 : CheckOK μ env fe s8 :=
    hck7.mono ⟨by rw [h8st]; exact hck7.state.wf⟩ (by rw [h8st]; exact Ext.refl _)
      h8c h8p
  have hw8 : denoteE s8.store jv2 = some w := by rw [h8st]; exact hw7
  have hden8 : denoteFEnv s8.store fe = some env := by rw [h8st]; exact hden7
  -- 5. the unresolved-constant guard
  obtain ⟨b9, s9, g9r, r14⟩ := AM.bind_ok r13
  have hpins8 : s8.pins = s.pins := by rw [h8p, hp7, h6p, h5p]
  obtain ⟨h9st, h9c, h9p, h9r⟩ :=
    constsResolveFFast_run ⟨hck8, hok.envWF, hok.persPins.mono hpins8,
      hok.persEnv, hok.coh, hden8⟩ hw8 g9r
  obtain ⟨hcr, r15⟩ := AM.dunless_ok
    (AM.Never.bind fun _ => AM.Never.bind fun _ => AM.Never.fail_any) r14
  replace r15 := AM.pure_bind_ok r15
  have hcrP : w.constsResolve env = true := by rw [← h9r]; exact hcr
  have hck9 : CheckOK μ env fe s9 :=
    hck8.mono ⟨by rw [h9st]; exact hck8.state.wf⟩ (by rw [h9st]; exact Ext.refl _)
      h9c h9p
  have hw9 : denoteE s9.store jv2 = some w := by rw [h9st]; exact hw8
  -- 6. the answer
  obtain ⟨hjv, hs'⟩ := AM.pure_ok r15
  subst hjv
  subst hs'
  have hext : Ext s.store s'.store := by
    rw [← h5st, ← h6st]
    refine hx7.trans ?_
    rw [← h8st, ← h9st]
    exact Ext.refl _
  have hpins : s'.pins = s.pins := by rw [h9p, h8p, hp7, h6p, h5p]
  exact ⟨⟨hck9, hext, hpins⟩, ⟨w, F7, hw9,
    installValue_pure hlbbP hfvP hF7 hlpdP hcrP⟩⟩

/-! ## The check half -/

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:102-119 checkValueGroup —
**the check half of a value declaration**, at the environment the constant was
installed at.

`sorry`: `KnotSpec.infer`, `EnsureSortSpec.ensureSort`, the level
comparison (`lvlEq?` through `CacheOK.lvlEq`), `installValue_bridge` for a
theorem's own value, and `KnotSpec.defeq`.  Task #97-P3-Checker's sorry
list, item 17. -/
theorem checkValueGroup_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {g : Arena.ValueGroup} {gP : ConLeche.ValueGroup}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s)
    (hkind : g.kind = .defn ∧ gP.kind = .defn ∨ g.kind = .thm ∧ gP.kind = .thm ∨
      g.kind = .opaque ∧ gP.kind = .opaque)
    (hcv : Frontend.denoteCV s.store g.cvA = some gP.cvA)
    (hjv : denoteE s.store g.jv = some gP.jv)
    (hrun : checkValueGroup μ fe g s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkValueGroup (ConLeche.fueledOps μ F) env gP = .ok () := by
  sorry

/-! ## The prefix view

con-leche's `mkFEnv_find?_visibleBelow` at the arena's `IFEnv.restrictTo`.
This is the one place the environment INDEX is consulted at something other
than the environment it indexes, and it is why `FoldOK` carries `IFEnvCoh`. -/

/-- con-leche: ConLeche/Verify/EnvBound.lean:243 mkFEnv_find?_visibleBelow —
**the prefix view IS the index of the prefix environment**.  Phase B checks a
pending record against `fe.restrictTo pc.vis`, and this says that view indexes
the environment the record was installed at.

The `Nodup` side condition is con-leche's own and it is the accumulated
duplicate test of `checkConstantVal`; the fold carries it.

**RESTATED** (task #97-P3-Checker round 5, on round 4's finding).  Round 4's
conclusion was

    ∃ envK, denoteFEnv s.store (fe.restrictTo k) = some envK ∧
      envK.find? = (env.prefixTo k).find?

and it is FALSE.  `IFEnv.restrictTo k` is `{ fe with visibleBelow := k }` — a
change to the INDEX's bound and to nothing else — while `denoteFEnv st fe` is
`denoteIEnv st fe.env`, which reads `fe.env.consts` and ignores `idx` and
`visibleBelow` entirely.  So `denoteFEnv s.store (fe.restrictTo k)
= denoteFEnv s.store fe = some env`, `envK = env` is forced, and the second
conjunct degenerates to `env.find? = (env.prefixTo k).find?`, which fails at
`k = 0` and any non-empty `env` (`env.prefixTo 0 = ⟨[]⟩`).

con-leche's own `mkFEnv_find?_visibleBelow` is a statement about `FEnv.find?`,
not about a denotation — *"looking a name up in the full index with the bound
`k` is looking it up in the environment truncated to its first `k` installed
constants"* — and the arena twin of that is a statement about the INDEX.  That
is what stands here now, and it is what the one consumer
(`Arena.checkPending_bridge`, phase B, which calls the core at
`fe.restrictTo pc.vis`) actually needs: the Core tier's hypotheses are
`IFEnvOK`-shaped, not denotation-shaped.

`sorry`: `proj` is immediate (`hk` makes every hit of the restricted view a
hit of `fe`, so `FoldOK`'s own `IFEnvOK.proj` applies), and `hit`/`cover` are
con-leche's `idxBelow_eq` at a DENOTED list — the same `mkIFEnvGo` induction
`IFEnvOK_of_denote` needs, with `denoteN_inj` where con-leche uses name
equality and `Env.prefixTo`'s `drop` where con-leche has `List.find?`.
Task #97-P3-Checker's sorry list, item 20. -/
theorem IFEnvOK_restrictTo {μ : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {k : Nat} (hok : FoldOK μ env fe s)
    (hnd : (env.consts.map (·.name)).Nodup) (hk : k ≤ fe.visibleBelow) :
    IFEnvOK (env.prefixTo k) (fe.restrictTo k) s := by
  sorry

/-! ## Phase A and phase B -/

/-- con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC — **phase
A's step, bracketed**: the four arms, the promotion of what leaves the step,
and the drop.

The conclusion is the install half's, not `checkDecl`'s: a value kind leaves a
`PendingCheck` behind and con-leche's `installConstantVal` / `installValue`
is what ran.  The three non-value arms fall through to `checkDecl` and the
conclusion is `Bridge/Checker/Decl.lean`'s `DeclOut`.

`sorry`: `annotStepGo`'s four arms over `installConstantVal_bridge`,
`installValue_bridge` and `Arena.checkDecl_bridge`, then the bracket —
`promoteVG_spec` and `promoteNew_spec` at ONE memo, then `PExt.dropScratch`.
The bracket is `Arena.checkDeclStep_bridge`'s with one operation more.  Task
#97-P3-Checker's sorry list, item 19. -/
theorem Arena.annotStep_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {i : Nat} {fe fe' : IFEnv} {pend pend' : Array PendingCheck}
    {pd : IDeclaration} {d : Declaration} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hpp : PersPinSets pins) (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.annotStep μ pins i fe pend pd s = .ok ((fe', pend'), s')) :
    ∃ env', FoldOK μ env' fe' s' ∧ PExt s.store s'.store ∧
      Pushed fe fe' ∧ (∀ pc ∈ pend'.toList, PersVG pc.vg) ∧
      (pend'.toList = pend.toList ∨
        ∃ pc, pend'.toList = pend.toList ++ [pc] ∧ pc.pos = i ∧
          pc.vis = fe.visibleBelow) := by
  sorry

/-- con-leche: ConLeche/Cached/Installed.lean:260-274 checkPending — **phase
B's check of one record**, against the prefix view, inside its own bracket.

`sorry`: `IFEnvOK_restrictTo` and `checkValueGroup_bridge`, then the
bracket with nothing to promote (`Arena/Checker.lean`: "Nothing crosses back,
so there is nothing to promote").  Task #97-P3-Checker's sorry list,
item 19. -/
theorem Arena.checkPending_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {pc : PendingCheck} {gP : ConLeche.ValueGroup} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpers : PersVG pc.vg)
    (hnd : (env.consts.map (·.name)).Nodup)
    (hcv : Frontend.denoteCV s.store pc.vg.cvA = some gP.cvA)
    (hjv : denoteE s.store pc.vg.jv = some gP.jv)
    (hrun : Arena.checkPending μ fe pc s = .ok ((), s')) :
    ∃ envK F, FoldOK μ env fe s' ∧ PExt s.store s'.store ∧
      envK.find? = (env.prefixTo pc.vis).find? ∧
      ConLeche.checkValueGroup (ConLeche.fueledOps μ F) envK gP = .ok () := by
  sorry

/-! ## The punchline -/

/-- con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
con-leche: ConLeche/Verify/CheckerSplit.lean:319-380 checkDecl_of_split_*
**THE TWO FOLDS ARE ONE ACCEPT**: what the binary runs implies what the
theorem is about.  With `Bridge/Checker/Fold.lean`'s
`Arena.checkDeclsPure_bridge` this is the second half of DESIGN §8.2's
Theorem 1 — the half the history report's fine print 5 prices — and with
`Bridge/Checker/Capstone.lean` it carries the model to the binary's own fold.

`sorry`: the `InstallRun` induction (con-leche's
`Verify/Cached/InstalledC.lean:456 installRun_model` is the same walk at the
model instead of at `checkDeclsPure`): phase A's records give the install
halves at each prefix environment, `Arena.checkPending_bridge` gives the check
half at the SAME one through `IFEnvOK_restrictTo`, `checkDecl_of_split_*`
combines them into `ConLeche.checkDecl`, and `checkDecl_mono` raises the fuels
to one.  Task #97-P3-Checker's sorry list, item 20 — the largest remaining
item after the seven arms, and the only one that is a *fold* rather than a
*step*. -/
theorem Arena.installThenCheck_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {fe' : IFEnv}
    {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hpp : PersPinSets pins)
    (hok : FoldOK μ Env.empty (mkIFEnv IEnv.empty) s)
    (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hden : denoteDecls s.store ds.toList = some dsP)
    (hrun : Arena.installThenCheck μ pins ds s = .ok (.ok fe', s')) :
    ∃ env' F', denoteFEnv s'.store fe' = some env' ∧
      ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F') pinsP dsP
        = .ok env' := by
  sorry

end ConRon.Bridge
