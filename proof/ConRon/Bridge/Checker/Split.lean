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

**THE STATEMENT WAS UNDER-HYPOTHESISED, and the two `WScoped` clauses are
the repair** (task #97-P3-Checker round 5 — the campaign's seventh statement
defect in this tier, found by taking the proof on).  `checkValueGroup`'s FIRST
operation is `inferTypeCore … 0 g.cvA.type`, and the only route from an arena
core run to con-leche's is `KnotSpec.infer`, whose precondition is
`Expr.WScoped 0` of the DENOTED argument.  Nothing in round 1's hypotheses
delivers it: `FoldOK` speaks about the environment and the store, not about a
pending record's header, and `gP.cvA` is not (as far as this statement says) a
constant of `env`, so `EnvWF`'s `hasFvar = false` clause does not reach it
either.  The same holds of `gP.jv` at the second inference, in the `defn` and
`opaque` arms where the value reaches `inferTypeCore` unannotated.

At depth 0 `WScoped` IS `hasFvar = false` (`Expr.WScoped.of_not_hasFvar`), so
both clauses are free at the one call site: phase A's `installConstantVal` and
`installValue` test exactly that guard, and `annotateCore_WScoped` carries it
to the annotated term.  `Arena.checkPending_bridge` is where they are
discharged.

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
    (hwsty : Expr.WScoped 0 gP.cvA.type) (hwsjv : Expr.WScoped 0 gP.jv)
    (hrun : checkValueGroup μ fe g s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkValueGroup (ConLeche.fueledOps μ F) env gP = .ok () := by
  sorry

/-! ## The prefix view

con-leche's `mkFEnv_find?_visibleBelow` at the arena's `IFEnv.restrictTo`.
This is the one place the environment INDEX is consulted at something other
than the environment it indexes, and it is why `FoldOK` carries `IFEnvCoh`. -/

/-! ### The bound, and the suffix it names

`IFEnv.restrictTo k` keeps the index and lowers the bound; `Env.prefixTo k`
keeps the environment's LAST `k` constants.  These four lemmas are that
correspondence at the arena's index, and they are con-leche's `idxBelow_eq`
(`Verify/EnvBound.lean`) with `List.drop` where con-leche has its own spec
list.  They are stated here because `IFEnvOK_restrictTo` is their only
consumer. -/

/-- con-leche: none — lowering the bound only ever hides: a hit of the
restricted view is a hit of the full one. -/
theorem IFEnv.restrictTo_find?_le {fe : IFEnv} {k : Nat}
    (hk : k ≤ fe.visibleBelow) {n : NIdx} {ci : IConstantInfo}
    (h : (fe.restrictTo k).find? n = some ci) : fe.find? n = some ci := by
  simp only [IFEnv.find?, IFEnv.restrictTo] at h ⊢
  cases hg : fe.idx[n]? with
  | none => rw [hg] at h; simp at h
  | some p =>
    obtain ⟨c0, ci0⟩ := p
    rw [hg] at h
    dsimp only at h ⊢
    by_cases hc : c0 < k
    · rw [if_pos hc] at h
      rw [if_pos (Nat.lt_of_lt_of_le hc hk)]
      exact h
    · rw [if_neg hc] at h; simp at h

/-- con-leche: ConLeche/Verify/EnvBound.lean idxBelow_eq_some — **soundness of
the bound**: what the restricted index finds, the suffix finds too.  The
counter `mkIFEnvGo` hands an entry is the length of the list BEHIND it, so
`c < k` says the entry is within the last `k`. -/
theorem mkIFEnvGo_below : ∀ (cs : List IConstantInfo) (n : NIdx) (k c : Nat)
    (ci : IConstantInfo), (mkIFEnvGo cs).2[n]? = some (c, ci) → c < k →
    (cs.drop (cs.length - k)).find? (fun d => d.name == n) = some ci := by
  intro cs
  induction cs with
  | nil => intro n k c ci h _; simp [mkIFEnvGo] at h
  | cons a as ih =>
    intro n k c ci h hc
    simp only [mkIFEnvGo] at h
    rw [Std.HashMap.getElem?_insert] at h
    by_cases hb : a.name == n
    · rw [if_pos hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [mkIFEnvGo_fst] at hc
      have e0 : (a :: as).length - k = 0 := by simp only [List.length_cons]; omega
      rw [e0, List.drop_zero, List.find?_cons, hb]
    · rw [if_neg hb] at h
      have hbf : (a.name == n) = false := by simpa using hb
      have ihh := ih n k c ci h hc
      by_cases hk : k ≤ as.length
      · have e1 : (a :: as).length - k = (as.length - k) + 1 := by
          simp only [List.length_cons]; omega
        rw [e1, List.drop_succ_cons]
        exact ihh
      · have e2 : (a :: as).length - k = 0 := by simp only [List.length_cons]; omega
        have e3 : as.length - k = 0 := by omega
        rw [e3, List.drop_zero] at ihh
        rw [e2, List.drop_zero, List.find?_cons, hbf]
        exact ihh

/-- con-leche: ConLeche/Verify/EnvBound.lean idxBelow_eq — **completeness of
the bound**, and the one place the `Nodup` side condition is spent: without it
an entry of the suffix could be SHADOWED by an earlier entry with the same
handle, which the index would answer with instead. -/
theorem mkIFEnvGo_below_of : ∀ (cs : List IConstantInfo) (n : NIdx) (k : Nat)
    (ci : IConstantInfo), k ≤ cs.length → (cs.map (·.name)).Nodup →
    (cs.drop (cs.length - k)).find? (fun d => d.name == n) = some ci →
    ∃ c, (mkIFEnvGo cs).2[n]? = some (c, ci) ∧ c < k := by
  intro cs
  induction cs with
  | nil =>
    intro n k ci hk _ h
    simp only [List.length_nil, Nat.le_zero_eq] at hk
    subst hk
    simp at h
  | cons a as ih =>
    intro n k ci hk hnd h
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hna, hnd'⟩ := hnd
    simp only [List.length_cons] at hk
    simp only [mkIFEnvGo]
    rw [Std.HashMap.getElem?_insert]
    by_cases hkk : k ≤ as.length
    · have e1 : (a :: as).length - k = (as.length - k) + 1 := by
        simp only [List.length_cons]; omega
      rw [e1, List.drop_succ_cons] at h
      obtain ⟨c, hc, hck⟩ := ih n k ci hkk hnd' h
      have hcin : ci ∈ as := List.drop_subset _ _ (List.mem_of_find?_eq_some h)
      have hcn : ci.name = n := by simpa using List.find?_some h
      have hb : ¬ (a.name == n) := by
        intro hx
        obtain rfl : a.name = n := by simpa using hx
        exact hna (hcn ▸ List.mem_map_of_mem hcin)
      rw [if_neg hb]
      exact ⟨c, hc, hck⟩
    · have hke : k = as.length + 1 := by omega
      subst hke
      have e0 : (a :: as).length - (as.length + 1) = 0 := by
        simp only [List.length_cons]; omega
      rw [e0, List.drop_zero, List.find?_cons] at h
      by_cases hb : a.name == n
      · rw [hb] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [if_pos hb, mkIFEnvGo_fst]
        exact ⟨as.length, rfl, Nat.lt_succ_self _⟩
      · have hbf : (a.name == n) = false := by simpa using hb
        rw [hbf] at h
        simp only at h
        rw [if_neg hb]
        have hm := mkIFEnvGo_snd as n
        rw [h] at hm
        cases hg : (mkIFEnvGo as).2[n]? with
        | none => rw [hg] at hm; simp at hm
        | some p =>
          obtain ⟨c0, ci0⟩ := p
          rw [hg] at hm
          simp only [Option.map_some, Option.some.injEq] at hm
          subst hm
          exact ⟨c0, rfl,
            Nat.lt_succ_of_lt (mkIFEnvGo_lt as n c0 ci0 hg)⟩

/-- con-leche: none — the readback is elementwise, so a member of the list has
a member of its denotation. -/
theorem denoteCIList_mem {st : EStore} : ∀ (cs : List IConstantInfo)
    (zs : List ConstantInfo), Frontend.denoteCIList st cs = some zs →
    ∀ b ∈ cs, ∃ z ∈ zs, Frontend.denoteCI st b = some z := by
  intro cs
  induction cs with
  | nil => intro zs _ b hb; simp at hb
  | cons a as ih =>
    intro zs hz b hb
    obtain ⟨x, xs, ha, has, rfl⟩ := denoteCIList_cons hz
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, List.mem_cons_self, ha⟩
    · obtain ⟨z, hzm, hzd⟩ := ih xs has b hb
      exact ⟨z, List.mem_cons_of_mem _ hzm, hzd⟩

/-- con-leche: none — the readback is elementwise, so it commutes with
`List.drop`. -/
theorem denoteCIList_drop {st : EStore} : ∀ (m : Nat) (cs : List IConstantInfo)
    (zs : List ConstantInfo), Frontend.denoteCIList st cs = some zs →
    Frontend.denoteCIList st (cs.drop m) = some (zs.drop m) := by
  intro m
  induction m with
  | zero => intro cs zs h; simpa using h
  | succ m ih =>
    intro cs zs h
    cases cs with
    | nil =>
      simp only [Frontend.denoteCIList, Option.some.injEq] at h
      subst h
      simp [Frontend.denoteCIList]
    | cons a as =>
      obtain ⟨x, xs, -, has, rfl⟩ := denoteCIList_cons h
      simp only [List.drop_succ_cons]
      exact ih as xs has

/-- con-leche: none — the readback preserves length. -/
theorem denoteCIList_length {st : EStore} : ∀ (cs : List IConstantInfo)
    (zs : List ConstantInfo), Frontend.denoteCIList st cs = some zs →
    cs.length = zs.length := by
  intro cs
  induction cs with
  | nil =>
    intro zs h
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro zs h
    obtain ⟨x, xs, -, has, rfl⟩ := denoteCIList_cons h
    simp only [List.length_cons, ih xs has]

/-- con-leche: none — **name uniqueness transports to HANDLE uniqueness**:
`denoteN` is injective and each entry's handle denotes its constant's name, so
two entries with the same handle would be two constants with the same name.
This is how `IFEnvOK_restrictTo` spends con-leche's own `Nodup` side
condition on the arena's index. -/
theorem denoteCIList_nodup {st : EStore} (hwf : StoreWF st) :
    ∀ (cs : List IConstantInfo) (zs : List ConstantInfo),
      Frontend.denoteCIList st cs = some zs →
      (∀ t, IConstantInfo.projInfo t ∈ cs → IProjTableOK st t) →
      (zs.map (·.name)).Nodup → (cs.map (·.name)).Nodup := by
  obtain ⟨rk, hrk⟩ := hwf
  intro cs
  induction cs with
  | nil => intro zs _ _ _; simp
  | cons a as ih =>
    intro zs hz hproj hnd
    obtain ⟨x, xs, ha, has, rfl⟩ := denoteCIList_cons hz
    simp only [List.map_cons, List.nodup_cons] at hnd ⊢
    obtain ⟨hxa, hxs⟩ := hnd
    refine ⟨?_, ih xs has (fun t ht => hproj t (List.mem_cons_of_mem _ ht)) hxs⟩
    intro hmem
    obtain ⟨b, hbm, hbn⟩ := List.mem_map.mp hmem
    obtain ⟨z, hzm, hzd⟩ := denoteCIList_mem as xs has b hbm
    have h1 : denoteN st.ns a.name = some x.name :=
      denoteCI_name_of (fun t ht => (hproj t (by simp [ht])).toNamed) ha
    have h2 : denoteN st.ns b.name = some z.name :=
      denoteCI_name_of
        (fun t ht => (hproj t (List.mem_cons_of_mem _ (ht ▸ hbm))).toNamed) hzd
    rw [hbn] at h2
    have hxz : x.name = z.name := Option.some.inj (h1.symm.trans h2)
    exact hxa (hxz ▸ List.mem_map_of_mem hzm)

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

**PROVED** (task #97-P3-Checker round 5, in the same round as the
restatement).  `proj` is immediate: `hk` makes every hit of the restricted
view a hit of `fe` (`IFEnv.restrictTo_find?_le`), so `FoldOK`'s own
`IFEnvOK.proj` applies.  `hit` and `cover` are con-leche's `idxBelow_eq` at a
DENOTED list: `mkIFEnvGo_below` and `mkIFEnvGo_below_of` above turn the
bounded index read into `List.find?` over `cs.drop (cs.length - k)` — the
counter an entry gets is the length of the list BEHIND it, so `c < k` says
exactly "within the last `k`" — and then `Bridge/Checker/Inv.lean`'s
`denoteCIList_find?` applies to the two DROPPED lists, because the readback is
elementwise and so commutes with `List.drop`.

**`hnd` is spent in exactly one place**, `mkIFEnvGo_below_of`: without it an
entry of the suffix could be shadowed by an earlier entry with the same
handle, which the index would answer with instead.  It arrives as con-leche's
own NAME uniqueness and `denoteCIList_nodup` transports it to HANDLE
uniqueness through `denoteN_inj`.

**`hproj` is the tier's standing `.projInfo` hypothesis**, the same one
`IFEnvOK_of_denote`, `installBasisDecl_bridge` and `IConstantInfo.canonEq_run`
take at the same gap (`Frontend.denoteProjTable` drops `tableName`), and the
same debtor discharges it (`projTableOK_of_install`).  It is needed here for
`denoteCIList_find?`'s use of `denoteCI_name_of`. -/
theorem IFEnvOK_restrictTo {μ : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {k : Nat} (hok : FoldOK μ env fe s)
    (hproj : ∀ t, IConstantInfo.projInfo t ∈ fe.env.consts →
      IProjTableOK s.store t)
    (hnd : (env.consts.map (·.name)).Nodup) (hk : k ≤ fe.visibleBelow) :
    IFEnvOK (env.prefixTo k) (fe.restrictTo k) s := by
  have hwf := hok.check.state.wf
  have hd := hok.denote
  simp only [denoteFEnv, denoteIEnv, Option.map_eq_some_iff] at hd
  obtain ⟨zs, hzs, rfl⟩ := hd
  have hidx : fe.idx = (mkIFEnvGo fe.env.consts).2 := congrArg IFEnv.idx hok.coh
  have hvb : fe.visibleBelow = fe.env.consts.length := by
    rw [show fe.visibleBelow = (mkIFEnv fe.env).visibleBelow from
      congrArg IFEnv.visibleBelow hok.coh]
    exact mkIFEnvGo_fst fe.env.consts
  have hk' : k ≤ fe.env.consts.length := hvb ▸ hk
  have hlen : fe.env.consts.length = zs.length := denoteCIList_length _ _ hzs
  have hndH : (fe.env.consts.map (·.name)).Nodup :=
    denoteCIList_nodup hwf _ _ hzs hproj hnd
  obtain ⟨hH, hC⟩ :=
    denoteCIList_find? hwf (fe.env.consts.drop (fe.env.consts.length - k))
      (zs.drop (fe.env.consts.length - k)) (denoteCIList_drop _ _ _ hzs)
      (fun t ht => hproj t (List.drop_subset _ _ ht))
  have hfwd : ∀ (n : NIdx) (ci : IConstantInfo),
      (fe.restrictTo k).find? n = some ci →
      (fe.env.consts.drop (fe.env.consts.length - k)).find?
        (fun d => d.name == n) = some ci := by
    intro n ci hf
    simp only [IFEnv.find?, IFEnv.restrictTo, hidx] at hf
    cases hg : (mkIFEnvGo fe.env.consts).2[n]? with
    | none => rw [hg] at hf; simp at hf
    | some p =>
      obtain ⟨c0, ci0⟩ := p
      rw [hg] at hf
      dsimp only at hf
      by_cases hc : c0 < k
      · rw [if_pos hc] at hf
        obtain rfl : ci0 = ci := Option.some.inj hf
        exact mkIFEnvGo_below _ n k c0 _ hg hc
      · rw [if_neg hc] at hf; simp at hf
  have hbwd : ∀ (n : NIdx) (ci : IConstantInfo),
      (fe.env.consts.drop (fe.env.consts.length - k)).find?
        (fun d => d.name == n) = some ci →
      (fe.restrictTo k).find? n = some ci := by
    intro n ci hf
    obtain ⟨c, hc, hck⟩ := mkIFEnvGo_below_of _ n k ci hk' hndH hf
    simp only [IFEnv.find?, IFEnv.restrictTo, hidx, hc]
    rw [if_pos hck]
  refine ⟨?_, ?_, ?_⟩
  · intro n ci hf
    obtain ⟨nm, c, h1, h2, h3⟩ := hH n ci (hfwd n ci hf)
    refine ⟨nm, c, h1, h2, ?_⟩
    simpa [Env.prefixTo, Env.find?, ← hlen] using h3
  · intro nm c he
    have he' : (zs.drop (fe.env.consts.length - k)).find?
        (fun d => d.name == nm) = some c := by
      simpa [Env.prefixTo, Env.find?, ← hlen] using he
    obtain ⟨n, ci, h1, h2, h3⟩ := hC nm c he'
    exact ⟨n, ci, h1, hbwd n ci h2, h3⟩
  · intro n t hf
    exact hok.check.ienv.proj n t (IFEnv.restrictTo_find?_le hk hf)

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
