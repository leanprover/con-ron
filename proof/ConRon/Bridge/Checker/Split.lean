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
import ConRon.Bridge.Checker.Nodup
import ConRon.Bridge.Promote.Coh

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
    constsResolveFFast_run hck8 hv8 g9r
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

**PROVED** (task #97-P3-Checker round 6), on
`Bridge/Checker/DeclVal.lean`'s `checkThmVal_bridge` machinery: the same
`KnotSpec.infer` / `EnsureSortSpec` / `pinZeroLevel_spec` / `lvlEq?_spec` /
`installValue_bridge` / `KnotSpec.defeq` chain, with the theorem's install
behind the kind test rather than in front of it.  The two branches are joined
into ONE postcondition (`step3` in the proof) before the value's inference
runs, which is round 3's rule — never carry a branch-dependent invariant along
the rest of a do-block.  Task #97-P3-Checker's sorry list, item 17, closed. -/
theorem checkValueGroup_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {g : Arena.ValueGroup} {gP : ConLeche.ValueGroup}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (henv : EnvWF env) (hck : CheckOK μ env fe s)
    (hkind : g.kind = .defn ∧ gP.kind = .defn ∨ g.kind = .thm ∧ gP.kind = .thm ∨
      g.kind = .opaque ∧ gP.kind = .opaque)
    (hcv : Frontend.denoteCV s.store g.cvA = some gP.cvA)
    (hjv : denoteE s.store g.jv = some gP.jv)
    (hwsty : Expr.WScoped 0 gP.cvA.type)
    (hwsjv : gP.kind ≠ .thm → Expr.WScoped 0 gP.jv)
    (hrun : checkValueGroup μ fe g s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkValueGroup (ConLeche.fueledOps μ F) env gP = .ok () := by
  have hknot := hk.knot env fe henv
  have hsortS := hk.sort env fe henv
  have hnever : ∀ {α β γ : Type} {z : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (z >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  have hnever2 : ∀ {α β : Type} {z : AM α} {f : α → Arena.CheckError},
      AM.Never (z >>= fun a => (Arena.fail (f a) : AM β)) :=
    fun {_ _ _ _} => AM.Never.bind fun _ => AM.Never.fail _
  obtain ⟨-, -, hty0⟩ := denoteCV_inv hcv
  have hkeq : (g.kind == Arena.ValueKind.thm) = true ↔
      gP.kind = ConLeche.ValueKind.thm := by
    rcases hkind with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp
  simp only [Arena.checkValueGroup, Arena.zeroLevel] at hrun
  -- 1. the header's inference
  obtain ⟨stype, s1, ga, ra⟩ := AM.bind_ok hrun
  obtain ⟨hcka, hxa, hpa, hsima⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s.store t.store ∧
      t.pins = s.pins ∧
      Core.SimE (ConLeche.inferTypeCore μ env) 0 gP.cvA.type t.store r)
    rfl ga (hknot.infer s 0 g.cvA.type gP.cvA.type hck hty0 hwsty)
  obtain ⟨sty, hsty, hwssty, Fa, hFa⟩ := hsima
  -- 2. the sort
  obtain ⟨u, s2, gb, rb⟩ := AM.bind_ok ra
  obtain ⟨hckb, hxb, hpb, hsimb⟩ := AM.of_run (P := fun t => t = s1)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s1.store t.store ∧
      t.pins = s1.pins ∧ SimL (ConLeche.ensureSortCore μ env) 0 sty t.store r)
    rfl gb (hsortS s1 0 stype sty hcka hsty hwssty)
  obtain ⟨uu, huu, Fb, hFb⟩ := hsimb
  have hext2 : Ext s.store s2.store := hxa.trans hxb
  have hpin2 : s2.pins = s.pins := by rw [hpb, hpa]
  have hcv2 : Frontend.denoteCV s2.store g.cvA = some gP.cvA :=
    denoteCV_ext hcv hext2
  have hjv2 : denoteE s2.store g.jv = some gP.jv := denote_ext hjv hext2
  -- **The kind test copies the tail into both arms**, so the tail is a local
  -- lemma rather than a continuation: the value's inference and the
  -- conversion, at whatever value the arm produced and whatever it knows
  -- about it.  (Round 3's rule, at a branch instead of at a loop.)
  have tail : ∀ (sA : AState) (jvA : EIdx) (y : Expr) (Fc : Nat),
      CheckOK μ env fe sA → Ext s2.store sA.store → sA.pins = s2.pins →
      denoteE sA.store jvA = some y → Expr.WScoped 0 y →
      (gP.kind = ConLeche.ValueKind.thm →
        ConLeche.installValue (ConLeche.fueledOps μ Fc) env gP.cvA gP.jv
          = .ok y) →
      (gP.kind ≠ ConLeche.ValueKind.thm → y = gP.jv) →
      (gP.kind = ConLeche.ValueKind.thm →
        ConLeche.Level.isEquiv uu .zero = some true) →
      (do
        let vtype ← Arena.inferTypeCore μ fe Arena.checkFuel 0 jvA
        unless ← Arena.isDefEqCore μ fe Arena.checkFuel 0 vtype g.cvA.type do
          Arena.fail (.invalid
            s!"type mismatch in {g.kind.word} {← Arena.readName g.cvA.name}"))
        sA = .ok ((), s') →
      CoreStep μ env fe s s' ∧ ∃ F,
        ConLeche.checkValueGroup (ConLeche.fueledOps μ F) env gP = .ok () := by
    intro sA jvA y Fc hckA hxA hpA hyA hwsy hIV3 hEQ3 hLV3 rc
    obtain ⟨vtype, s7, gh, rh⟩ := AM.bind_ok rc
    obtain ⟨hck7, hx7, hp7, hsim7⟩ := AM.of_run (P := fun t => t = sA)
      (Q := fun r t => CheckOK μ env fe t ∧ Ext sA.store t.store ∧
        t.pins = sA.pins ∧
        Core.SimE (ConLeche.inferTypeCore μ env) 0 y t.store r)
      rfl gh (hknot.infer sA 0 jvA y hckA hyA hwsy)
    obtain ⟨vt, hvt7, hwsvt, F2, hF2⟩ := hsim7
    have hcv7 : Frontend.denoteCV s7.store g.cvA = some gP.cvA :=
      denoteCV_ext hcv2 (hxA.trans hx7)
    obtain ⟨-, -, hty7⟩ := denoteCV_inv hcv7
    obtain ⟨b8, s8, gi, ri⟩ := AM.bind_ok rh
    obtain ⟨hck8, hx8, hp8, hsim8⟩ := AM.of_run (P := fun t => t = s7)
      (Q := fun r t => CheckOK μ env fe t ∧ Ext s7.store t.store ∧
        t.pins = s7.pins ∧
        Core.SimV (ConLeche.isDefEqCore μ env) 0 vt gP.cvA.type r)
      rfl gi (hknot.defeq s7 0 vtype g.cvA.type vt gP.cvA.type hck7 hvt7 hty7
        hwsvt hwsty)
    obtain ⟨F3, hF3⟩ := hsim8
    obtain ⟨hb, rj⟩ := AM.dunless_ok hnever2 ri
    obtain ⟨-, rfl⟩ := AM.pure_ok rj
    subst hb
    refine ⟨⟨hck8, hext2.trans (hxA.trans (hx7.trans hx8)),
      by rw [hp8, hp7, hpA, hpin2]⟩,
      max (max Fa Fb) (max Fc (max F2 F3)), ?_⟩
    exact ConLeche.checkValueGroup_of_facts
      (ConLeche.inferTypeCore_mono (by omega) hFa)
      (ConLeche.ensureSortCore_mono (by omega) hFb)
      hLV3
      (fun hq => ConLeche.installValue_mono (by omega) (hIV3 hq))
      hEQ3
      (ConLeche.inferTypeCore_mono (by omega) hF2)
      (ConLeche.isDefEqCore_mono (by omega) hF3)
  -- 3. the value: a theorem installs its own, the other two kinds take the
  -- record's
  rcases AM.ite_ok rb with ⟨hthm, gd⟩ | ⟨hnthm, gd⟩
  · -- the theorem branch: the is-a-proposition test, then the install
    have hthmP : gP.kind = ConLeche.ValueKind.thm := hkeq.mp hthm
    obtain ⟨z, s4, ge, rd⟩ := AM.bind_ok gd
    obtain ⟨hs4, hz⟩ := AM.of_run (P := fun t => t = s2)
      (Q := fun r t => t = s2 ∧ denoteL s2.store.ls r = some .zero)
      rfl ge (pinZeroLevel_spec s2 hckb.pins)
    rw [hs4] at rd
    obtain ⟨o, s5, gf, re⟩ := AM.bind_ok rd
    obtain ⟨hckd, hstd, hpd, lu, lv, hlu, hlv, hod⟩ := AM.of_run
      (P := fun t => t = s2)
      (Q := fun r t => CheckOK μ env fe t ∧ t.store = s2.store ∧
        t.pins = s2.pins ∧ ∃ lu lv, denoteL s2.store.ls u = some lu ∧
          denoteL s2.store.ls z = some lv ∧ r = ConLeche.Level.isEquiv lu lv)
      rfl gf (Core.lvlEq?_spec s2 u z hckb)
    rw [Option.some.inj (hlu.symm.trans huu),
      Option.some.inj (hlv.symm.trans hz)] at hod
    obtain ⟨b6, s6, gg, rf⟩ := AM.bind_ok re
    obtain ⟨bb, rfl⟩ : ∃ bb, o = some bb := by
      cases ho : o with
      | none => rw [ho] at gg; exact absurd gg (AM.Never.fail _ _ _ _)
      | some bb => exact ⟨bb, rfl⟩
    obtain ⟨rfl, rfl⟩ := AM.pure_ok gg
    obtain ⟨hprop, rg⟩ := AM.dunless_ok hnever rf
    replace rg := AM.pure_bind_ok rg
    have heqv : ConLeche.Level.isEquiv uu .zero = some true := by
      rw [← hod, hprop]
    have hext5 : Ext s2.store s6.store := by rw [hstd]; exact Ext.refl _
    obtain ⟨jvA, s7, gIV, rT⟩ := AM.bind_ok rg
    obtain ⟨hstep6, y, Fc, hy6, hIV⟩ := installValue_bridge hμ hk henv hckd
      (denoteCV_ext hcv2 hext5) (denote_ext hjv2 hext5) gIV
    exact tail s7 jvA y Fc hstep6.ok (hext5.trans hstep6.ext)
      (by rw [hstep6.pins, hpd]) hy6
      (ConLeche.Expr.WScoped.of_not_hasFvar (installValue_valueWF hIV).1)
      (fun _ => hIV) (fun hne => absurd hthmP hne) (fun _ => heqv) rT
  · -- the other two kinds: the record's own value, and no test
    have hnthmP : gP.kind ≠ ConLeche.ValueKind.thm := fun hq =>
      hnthm (hkeq.mpr hq)
    exact tail s2 g.jv gP.jv 0 hckb (Ext.refl _) rfl hjv2 (hwsjv hnthmP)
      (fun hq => absurd hq hnthmP) (fun _ => rfl) (fun hq => absurd hq hnthmP)
      (AM.pure_bind_ok gd)

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
    -- **Re-ascribe before rewriting.**  `dsimp only` reduces the restricted
    -- bound in the PROPOSITION (`c0 < k`) but leaves the `Decidable` instance
    -- at `(fe.restrictTo k).visibleBelow`, so neither `rw [if_pos hc]` nor
    -- `simp only [if_pos hc]` matches.  The two are defeq, so a `have` with
    -- the type written out re-elaborates it at the canonical instance and
    -- everything below is ordinary (task #97-P3-Checker round 6; the
    -- fragility surfaced when `Core/Walks/Cached.lean` entered this module's
    -- import closure).
    have hh : (if c0 < k then some ci0 else none) = some ci := h
    by_cases hc : c0 < k
    · rw [if_pos hc] at hh
      rw [if_pos (Nat.lt_of_lt_of_le hc hk)]
      exact hh
    · rw [if_neg hc] at hh; simp at hh

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
  have hvb : fe.visibleBelow = fe.env.consts.length := hok.coh.1
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
    simp only [IFEnv.find?, IFEnv.restrictTo, hok.coh.2 n] at hf
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
    simp only [IFEnv.find?, IFEnv.restrictTo, hok.coh.2 n, hc]
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

/-! ## The two-phase fold, skeletonised (task #97-P3-Checker round 8)

`installThenCheck` is phase A (`annotFold`) then phase B (`checkPendingList`),
and `checkDeclsPure` is ONE fold of `checkDecl`.  The bridge between them is
con-leche's `checkDecl_of_split_*` (`Verify/CheckerSplit.lean`): a separable
value declaration's install halves at `env`, plus its check half at the SAME
`env`, are `checkDecl` at `env`.  The skeleton is therefore

1. **the pure record of phase A**, `PhaseA` — per declaration either a full
   `checkDecl` step, or the install halves (`SplitInstall`) leaving the pair
   `(env, vg)` owed a check — and `PhaseA.foldlM`, which pays every owed
   check and returns `checkDecl`'s fold.  Pure, con-leche only: PROVED;
2. **phase A over handles**, `Arena.annotFold_bridge`, by induction over
   `Arena.annotStep_split` (one step: the four arms and the bracket);
3. **phase B over handles**, `Arena.checkPendingList_bridge`, by induction
   over `Arena.checkPending_prefix` (one record, at the prefix environment);
4. the assembly, `Arena.installThenCheck_bridge`.

`PendRel` is what crosses the seam for one record: the handle record
denotes the pure one, the two scope facts phase B's knot calls need, the
environment it was installed at (`EnvWF`, its length = `pc.vis`, and the
final environment extends it — so `env'.prefixTo pc.vis` IS it,
`Env.prefixTo_of_extends`), and persistence, so that it survives every later
bracket. -/

/-- con-leche: none — two lists related pointwise (core has no
`List.Forall₂`). -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} :
      R a b → ListRel R l l' → ListRel R (a :: l) (b :: l')

theorem ListRel.nil_right {α β : Type} {R : α → β → Prop} {l : List α}
    (h : ListRel R l []) : l = [] := by
  cases h; rfl

/-- con-leche: none — the handle record's kind is the pure record's, in the
disjunctive form `checkValueGroup_bridge` takes (the arena and con-leche each
have their own `ValueKind`). -/
def KindRel (a : Arena.ValueKind) (b : ConLeche.ValueKind) : Prop :=
  a = .defn ∧ b = .defn ∨ a = .thm ∧ b = .thm ∨ a = .opaque ∧ b = .opaque

/-- con-leche: ConLeche/Verify/CheckerSplit.lean:318-397 checkDecl_of_split_* —
the install halves of a separable value declaration, as the three lemmas'
premises: what phase A ran, at `env`, for record `d`, leaving `vg` and the
extended environment `env'`. -/
def SplitInstall (μ : CheckMode) (F : Nat) (env : Env) (d : Declaration)
    (vg : ConLeche.ValueGroup) (env' : Env) : Prop :=
  (∃ cv value hint, d = .defnDecl cv value hint ∧
    (ConLeche.natOpNames.contains cv.name ||
      ConLeche.natDivModNames.contains cv.name) = false ∧
    vg.kind = .defn ∧
    ConLeche.installConstantVal (ConLeche.fueledOps μ F) env cv = .ok vg.cvA ∧
    ConLeche.installValue (ConLeche.fueledOps μ F) env vg.cvA value = .ok vg.jv ∧
    env' = ⟨.defnInfo vg.cvA vg.jv hint :: env.consts⟩) ∨
  (∃ cv value, d = .thmDecl cv value ∧ vg.kind = .thm ∧
    ConLeche.installConstantVal (ConLeche.fueledOps μ F) env cv = .ok vg.cvA ∧
    vg.jv = value ∧
    env' = ⟨.thmInfo vg.cvA value :: env.consts⟩) ∨
  (∃ cv value, d = .opaqueDecl cv value ∧
    ConLeche.reduceOpNames.contains cv.name = false ∧ vg.kind = .opaque ∧
    ConLeche.installConstantVal (ConLeche.fueledOps μ F) env cv = .ok vg.cvA ∧
    ConLeche.installValue (ConLeche.fueledOps μ F) env vg.cvA value = .ok vg.jv ∧
    env' = ⟨.axiomInfo vg.cvA :: env.consts⟩)

/-- con-leche: ConLeche/Cached/Installed.lean:201-209 InstallRun — **the pure
record of an accepting phase A**: each declaration is a full `checkDecl` step
or a split install owing the check of `(env, vg)`, in fold order. -/
inductive PhaseA (μ : CheckMode) (pinsP : List NatOpPinSet) :
    Env → List Declaration → Env → List (Env × ConLeche.ValueGroup) → Prop
  | nil (env : Env) : PhaseA μ pinsP env [] env []
  | full {env env₁ env' : Env} {d : Declaration} {ds : List Declaration}
      {pend : List (Env × ConLeche.ValueGroup)} (F : Nat)
      (h : ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env₁)
      (rest : PhaseA μ pinsP env₁ ds env' pend) :
      PhaseA μ pinsP env (d :: ds) env' pend
  | split {env env₁ env' : Env} {d : Declaration} {ds : List Declaration}
      {pend : List (Env × ConLeche.ValueGroup)} (vg : ConLeche.ValueGroup) (F : Nat)
      (h : SplitInstall μ F env d vg env₁)
      (rest : PhaseA μ pinsP env₁ ds env' pend) :
      PhaseA μ pinsP env (d :: ds) env' ((env, vg) :: pend)

/-- con-leche: ConLeche/Verify/CheckerSplit.lean:318-397 checkDecl_of_split_* —
one split step with its owed check paid is `checkDecl`, at one fuel. -/
theorem SplitInstall.checkDecl {μ : CheckMode} {pinsP : List NatOpPinSet}
    {F : Nat} {env env' : Env} {d : Declaration} {vg : ConLeche.ValueGroup}
    (h : SplitInstall μ F env d vg env')
    (hC : ConLeche.checkValueGroup (ConLeche.fueledOps μ F) env vg = .ok ()) :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env' := by
  rcases h with ⟨cv, value, hint, rfl, hnat, hk, hI, hV, rfl⟩ |
    ⟨cv, value, rfl, hk, hI, hjv, rfl⟩ | ⟨cv, value, rfl, hred, hk, hI, hV, rfl⟩
  · exact ConLeche.checkDecl_of_split_defn hnat hk hI hV hC
  · exact ConLeche.checkDecl_of_split_thm hk hI hjv hC
  · exact ConLeche.checkDecl_of_split_opaque hred hk hI hV hC

theorem SplitInstall.mono {μ : CheckMode} {F F' : Nat} (hle : F ≤ F')
    {env env' : Env} {d : Declaration} {vg : ConLeche.ValueGroup}
    (h : SplitInstall μ F env d vg env') : SplitInstall μ F' env d vg env' := by
  rcases h with ⟨cv, value, hint, h1, h2, h3, h4, h5, h6⟩ |
    ⟨cv, value, h1, h2, h3, h4, h5⟩ | ⟨cv, value, h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨cv, value, hint, h1, h2, h3,
      ConLeche.installConstantVal_mono hle h4, ConLeche.installValue_mono hle h5, h6⟩
  · exact Or.inr (Or.inl ⟨cv, value, h1, h2,
      ConLeche.installConstantVal_mono hle h3, h4, h5⟩)
  · exact Or.inr (Or.inr ⟨cv, value, h1, h2, h3,
      ConLeche.installConstantVal_mono hle h4, ConLeche.installValue_mono hle h5, h6⟩)

/-- con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure — **phase A
with every owed check paid is `checkDecl`'s fold**, at one fuel (and every
larger one).  PROVED: an induction over `PhaseA`, `SplitInstall.checkDecl` at
each split step, the fuels raised to one `max`. -/
theorem PhaseA.foldlM {μ : CheckMode} {pinsP : List NatOpPinSet}
    {env : Env} {ds : List Declaration} {env' : Env}
    {pend : List (Env × ConLeche.ValueGroup)} (h : PhaseA μ pinsP env ds env' pend)
    (hB : ∀ p ∈ pend, ∃ F,
      ConLeche.checkValueGroup (ConLeche.fueledOps μ F) p.1 p.2 = .ok ()) :
    ∃ F, ∀ F', F ≤ F' →
      ds.foldlM (ConLeche.checkDecl μ (ConLeche.fueledOps μ F') pinsP) env
        = .ok env' := by
  induction h with
  | nil env => exact ⟨0, fun _ _ => rfl⟩
  | full F h rest ih =>
    obtain ⟨F₂, h₂⟩ := ih hB
    refine ⟨max F F₂, fun F' hle => ?_⟩
    simp only [List.foldlM, Bind.bind, Except.bind]
    rw [checkDecl_mono (Nat.le_trans (Nat.le_max_left _ _) hle) h]
    exact h₂ F' (Nat.le_trans (Nat.le_max_right _ _) hle)
  | @split env₀ env₁ env' d ds pend vg F h rest ih =>
    obtain ⟨Fc, hC⟩ := hB (env₀, vg) (by simp)
    obtain ⟨F₂, h₂⟩ := ih (fun p hp => hB p (by simp [hp]))
    refine ⟨max (max F Fc) F₂, fun F' hle => ?_⟩
    have hF : F ≤ F' := by omega
    have hFc : Fc ≤ F' := by omega
    simp only [List.foldlM, Bind.bind, Except.bind]
    rw [SplitInstall.checkDecl (h.mono hF) (ConLeche.checkValueGroup_mono hFc hC)]
    exact h₂ F' (by omega)

/-- con-leche: none — **what crosses the install/check seam for one record**,
at the store phase B will read it in and the environment phase A ended at. -/
structure PendRel (st : EStore) (envF : Env) (pc : PendingCheck)
    (p : Env × ConLeche.ValueGroup) : Prop where
  kind : KindRel pc.vg.kind p.2.kind
  cv : Frontend.denoteCV st pc.vg.cvA = some p.2.cvA
  jv : denoteE st pc.vg.jv = some p.2.jv
  wsty : Expr.WScoped 0 p.2.cvA.type
  wsjv : p.2.kind ≠ .thm → Expr.WScoped 0 p.2.jv
  envWF : EnvWF p.1
  vis : pc.vis = p.1.consts.length
  ext : ∃ new, envF.consts = new ++ p.1.consts
  pers : PersVG pc.vg

/-- con-leche: none — a record's relation survives a later bracket (`PExt`,
the record being persistent) and a later extension of the environment. -/
theorem PendRel.mono {st st' : EStore} {envF envF' : Env} {pc : PendingCheck}
    {p : Env × ConLeche.ValueGroup} (h : PendRel st envF pc p)
    (hx : PExt st st') (he : ∃ new, envF'.consts = new ++ envF.consts) :
    PendRel st' envF' pc p where
  kind := h.kind
  cv := denoteCV_pext hx h.pers.cvA h.cv
  jv := hx.expr _ _ h.pers.jv h.jv
  wsty := h.wsty
  wsjv := h.wsjv
  envWF := h.envWF
  vis := h.vis
  ext := by
    obtain ⟨n1, h1⟩ := h.ext
    obtain ⟨n2, h2⟩ := he
    exact ⟨n2 ++ n1, by rw [h2, h1, List.append_assoc]⟩
  pers := h.pers

/-- con-leche: none — the prefix at a record's visibility bound IS the
environment it was installed at. -/
theorem PendRel.prefix {st : EStore} {envF : Env} {pc : PendingCheck}
    {p : Env × ConLeche.ValueGroup} (h : PendRel st envF pc p) :
    envF.prefixTo pc.vis = p.1 := by
  obtain ⟨new, hn⟩ := h.ext
  rw [h.vis]
  exact Env.prefixTo_of_extends hn

/-! `checkDecl_nodup` — the pure fold keeps names unique — is
`Bridge/Checker/Nodup.lean`'s (task #97-P3-Checker round 9: PROVED off
con-leche's `DeclRun`, arm by arm). -/

/-- con-leche: ConLeche/Verify/CheckerSplit.lean installConstantVal_inv — a
split install pushes one constant whose name the environment did not have.

PROVED: `installConstantVal_inv`'s `find?` miss. -/
theorem SplitInstall.nodup {μ : CheckMode} {F : Nat} {env env' : Env}
    {d : Declaration} {vg : ConLeche.ValueGroup}
    (h : SplitInstall μ F env d vg env') (hnd : NodupNames env) :
    NodupNames env' := by
  have key : ∀ {cv cvA : ConstantVal} {c : ConstantInfo},
      ConLeche.installConstantVal (ConLeche.fueledOps μ F) env cv = .ok cvA →
      c.name = cvA.name → NodupNames ⟨c :: env.consts⟩ := by
    intro cv cvA c hI hc
    obtain ⟨hfind, -, -, -, -, -, type', -, -, -, hcvA⟩ :=
      ConLeche.installConstantVal_inv hI
    unfold NodupNames at hnd ⊢
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, hnd⟩
    intro hmem
    obtain ⟨x, hx, hxn⟩ := List.mem_map.mp hmem
    have hne := List.find?_eq_none.mp hfind x hx
    rw [hc, hcvA] at hxn
    simp [hxn] at hne
  rcases h with ⟨cv, value, hint, -, -, -, hI, -, rfl⟩ |
    ⟨cv, value, -, -, hI, -, rfl⟩ | ⟨cv, value, -, -, -, hI, -, rfl⟩
  · exact key hI rfl
  · exact key hI rfl
  · exact key hI rfl

theorem PhaseA.nodup {μ : CheckMode} {pinsP : List NatOpPinSet}
    {env : Env} {ds : List Declaration} {env' : Env}
    {pend : List (Env × ConLeche.ValueGroup)} (h : PhaseA μ pinsP env ds env' pend) :
    NodupNames env → NodupNames env' := by
  induction h with
  | nil => exact id
  | full F h rest ih => exact fun hnd => ih (checkDecl_nodup h hnd)
  | split vg F h rest ih => exact fun hnd => ih (h.nodup hnd)

/-- con-leche: none — two entries of a denoting list that denote the SAME
constant are the same entry, when the denoted names are unique (a constant
occurring at two positions would repeat its name). -/
theorem denoteCIList_inj_nodup {st : EStore} :
    ∀ (cs : List IConstantInfo) (zs : List ConstantInfo),
      Frontend.denoteCIList st cs = some zs → (zs.map (·.name)).Nodup →
      ∀ a ∈ cs, ∀ b ∈ cs, ∀ c, Frontend.denoteCI st a = some c →
        Frontend.denoteCI st b = some c → a = b := by
  intro cs
  induction cs with
  | nil => intro _ _ _ a ha; simp at ha
  | cons x xs ih =>
    intro zs hz hnd a ha b hb c hac hbc
    obtain ⟨z, zs', hx, hxs, rfl⟩ := denoteCIList_cons hz
    simp only [List.map_cons, List.nodup_cons] at hnd
    -- an entry of the tail denotes a constant of the tail, which is not `z`
    have htail : ∀ y ∈ xs, Frontend.denoteCI st y = some z → False := by
      intro y hy hyz
      obtain ⟨w, hw, hwd⟩ := denoteCIList_mem xs zs' hxs y hy
      rw [hyz] at hwd
      obtain rfl := Option.some.inj hwd
      exact hnd.1 (List.mem_map_of_mem hw)
    rcases List.mem_cons.mp ha with ha' | ha' <;>
      rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · rw [ha', hx] at hac; obtain rfl := Option.some.inj hac
      exact (htail b hb' hbc).elim
    · rw [hb', hx] at hbc; obtain rfl := Option.some.inj hbc
      exact (htail a ha' hac).elim
    · exact ih zs' hxs hnd.2 a ha' b hb' c hac hbc

/-- con-leche: ConLeche/Verify/Cached/StreamConsts.lean:641 find?_name_of_mem —
a name-unique environment finds every constant it holds (con-leche's lemma,
restated: its module is not in this tier's import closure). -/
theorem find?_of_mem_nodupNames : ∀ {cs : List ConstantInfo},
    (cs.map (·.name)).Nodup → ∀ {c : ConstantInfo}, c ∈ cs →
      (⟨cs⟩ : Env).find? c.name = some c := by
  intro cs
  induction cs with
  | nil => intro _ c hc; exact absurd hc List.not_mem_nil
  | cons a t ih =>
    intro hnd c hc
    rw [List.map_cons, List.nodup_cons] at hnd
    show (a :: t).find? (·.name == c.name) = some c
    rw [List.find?_cons]
    by_cases hb : (a.name == c.name) = true
    · simp only [hb]
      rcases List.mem_cons.mp hc with rfl | hc'
      · rfl
      · exact absurd (by rw [eq_of_beq hb]; exact List.mem_map.mpr ⟨c, hc', rfl⟩) hnd.1
    · rw [Bool.not_eq_true] at hb
      simp only [hb]
      rcases List.mem_cons.mp hc with rfl | hc'
      · simp at hb
      · exact ih hnd.2 hc'

/-- con-leche: none — **every projection table the fold's index holds is well
shaped**, not only the ones a lookup reaches: under name uniqueness every
entry of the list IS the answer of a lookup (the `cover` clause finds a
handle for its denoted name, and `denoteCIList_inj_nodup` says the entry
found is this one), so `IFEnvOK.proj` reaches it.  This is
`IFEnvOK_restrictTo`'s membership-shaped `hproj`. -/
theorem FoldOK.projMem {μ : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    (hok : FoldOK μ env fe s) (hnd : (env.consts.map (·.name)).Nodup) :
    ∀ t, IConstantInfo.projInfo t ∈ fe.env.consts → IProjTableOK s.store t := by
  intro t ht
  have hd := hok.denote
  simp only [denoteFEnv, denoteIEnv, Option.map_eq_some_iff] at hd
  obtain ⟨zs, hzs, rfl⟩ := hd
  obtain ⟨c, hcm, hcd⟩ := denoteCIList_mem _ zs hzs _ ht
  have hfind : (⟨zs⟩ : Env).find? c.name = some c :=
    find?_of_mem_nodupNames hnd hcm
  obtain ⟨n, ci, -, hf, hci⟩ := hok.check.ienv.cover c.name c hfind
  have hmem := IFEnv.find?_mem hok.coh hf
  obtain rfl := denoteCIList_inj_nodup _ zs hzs hnd ci hmem _ ht c hci hcd
  exact hok.check.ienv.proj n t hf

/-- con-leche: ConLeche/Verify/EnvBound.lean:243 mkFEnv_find?_visibleBelow —
`IFEnvOK_restrictTo` at ANY bound: past the index's size the restriction
hides nothing and the prefix is the whole environment. -/
theorem IFEnvOK_prefix {μ : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    (hok : FoldOK μ env fe s) (hnd : (env.consts.map (·.name)).Nodup) (k : Nat) :
    IFEnvOK (env.prefixTo k) (fe.restrictTo k) s := by
  by_cases hk : k ≤ fe.visibleBelow
  · exact IFEnvOK_restrictTo hok (hok.projMem hnd) hnd hk
  · have hlen : env.consts.length = fe.env.consts.length := by
      have hd := hok.denote
      simp only [denoteFEnv, denoteIEnv, Option.map_eq_some_iff] at hd
      obtain ⟨zs, hzs, rfl⟩ := hd
      exact (denoteCIList_length _ _ hzs).symm
    have hvb : fe.visibleBelow = fe.env.consts.length := hok.coh.1
    have hpre : env.prefixTo k = env := by
      simp only [Env.prefixTo]
      rw [show env.consts.length - k = 0 by omega, List.drop_zero]
    have hfind : ∀ n, (fe.restrictTo k).find? n = fe.find? n := by
      intro n
      simp only [IFEnv.find?, IFEnv.restrictTo]
      cases hg : fe.idx[n]? with
      | none => rfl
      | some p =>
        obtain ⟨c, ci⟩ := p
        have hc : c < fe.env.consts.length :=
          mkIFEnvGo_lt _ n c ci (hok.coh.2 n ▸ hg)
        simp only [if_pos (show c < k by omega), if_pos (show c < fe.visibleBelow by omega)]
    rw [hpre]
    have h := hok.check.ienv
    exact ⟨fun n ci hf => h.hit n ci (by rw [← hfind]; exact hf),
      fun nm c hf => by
        obtain ⟨n, ci, h1, h2, h3⟩ := h.cover nm c hf
        exact ⟨n, ci, h1, by rw [hfind]; exact h2, h3⟩,
      fun n t hf => h.proj n t (by rw [← hfind]; exact hf)⟩

/-! ## The bracket's close, shared

`Arena.annotStep` and `Arena.checkDeclStep` close the same way: the step body
has run in the scratch tier from the boundary `s0` and left an index `fe1`
pushed onto `fe`; `promoteNew` copies the `k` new constants into the
persistent tier and re-indexes, and `dropScratch` takes the tier.  What the
body must hand the close is `BodyOut` — the index facts at the pushed
environment `env'` that the next boundary's `FoldOK` needs and the close
cannot conjure: `EnvWF env'`, the membership-shaped projection clause
`IFEnvOK_of_denote` takes, and `promoteNew_spec`'s `NamesDistinct`. -/

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean PushChain — **what a step
body leaves for the bracket's close**, at the scratch-tier state `s2` it ended
in: the pushed index `fe1` denotes a well-formed `env'`, its stored tables are
well shaped, and the constants it pushed name pairwise different names. -/
structure BodyOut (env' : Env) (fe fe1 : IFEnv) (s2 : AState) : Prop where
  state : StateOK s2
  coh : IFEnvCoh fe1
  pushed : Pushed fe fe1
  denote : denoteFEnv s2.store fe1 = some env'
  envWF : EnvWF env'
  proj : ∀ t, IConstantInfo.projInfo t ∈ fe1.env.consts → IProjTableOK s2.store t
  distinct : NamesDistinct s2.store
    (fe1.env.consts.take (fe1.visibleBelow - fe.visibleBelow))

/-- con-leche: none — distinct names stay distinct across an append. -/
theorem NamesDistinct.mono {st st' : EStore} {cs : List IConstantInfo}
    (h : NamesDistinct st cs) (hx : Ext st st') : NamesDistinct st' cs :=
  List.Pairwise.imp (fun ⟨x, y, h1, h2, h3⟩ =>
    ⟨x, y, denoteN_ext h1 hx, denoteN_ext h2 hx, h3⟩) h

/-- con-leche: none — a stored table's shape survives a `PExt` at a
persistent table (`IFEnvOK.pmono`'s `proj` clause, standing alone). -/
theorem IProjTableOK.pmono {st st' : EStore} {t : IProjTable} (h : IProjTableOK st t)
    (hp : PersProjTable t) (hx : PExt st st') : IProjTableOK st' t := by
  obtain ⟨sn, h1, h2⟩ := h.named
  exact ⟨h.bodies, h.guards, sn, denoteN_pext hx hp.structName h1,
    denoteN_pext hx hp.tableName h2⟩

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**the bracket closes onto a boundary**: from `FoldOK` at the step's opening
boundary `s0` and the body's `BodyOut`, the promotion (`promoteNew_spec`,
`promoteNew_pushed`, `promoteNew_projOK`) and the drop
(`promoteBracket_close`) leave `FoldOK` at the pushed environment.  `m` is
the memo the promotion starts from (`promoteVG`'s, in phase A's split arms);
`hext` is everything between the opening `enterScratch` and the promotion,
which only appended; the body ended at `sb`, and whatever ran between it and
the promotion (`promoteVG`, or nothing) only appended too. -/
theorem bracketClose_foldOK {μ : CheckMode} {env env' : Env} {fe fe1 fe' : IFEnv}
    {s0 sb s2 s3 : AState} {m m' : PMemo} {fuel : Nat}
    (hok : FoldOK μ env fe s0) (hb : BodyOut env' fe fe1 sb)
    (hxb : Ext sb.store s2.store)
    (hwf2 : StoreWF' s2.store) (hm : PMemoOK m s2.store)
    (hext : Ext s0.store.enableScratch s2.store) (hpins : s2.pins = s0.pins)
    (hrun : promoteNew m fuel (fe1.visibleBelow - fe.visibleBelow) fe1 s2
      = .ok ((m', fe'), s3)) :
    FoldOK μ env' fe'
        ({ store := s3.store.dropScratch, memos := s3.memos, caches := Caches.empty,
           pins := s3.pins } : AState) ∧
      PExt s0.store s3.store.dropScratch ∧ Pushed fe fe' ∧
      PMemoOK m' s3.store ∧ Ext s2.store s3.store ∧ s3.pins = s0.pins ∧
      StoreWF' s3.store := by
  obtain ⟨hwf3, hx23, hm3, hp3, hcoh3, hd3, -, hfr⟩ :=
    promoteNew_spec hwf2 hm hok.coh hok.persEnv hb.coh hb.pushed rfl (hb.distinct.mono hxb)
      (denoteFEnv_mono hxb hb.denote) hrun
  have hpush := promoteNew_pushed hok.coh hb.coh hb.pushed rfl hrun
  have hproj3 := promoteNew_projOK hwf2 hm (fun t ht => (hb.proj t ht).mono hxb) hrun
  obtain ⟨-, hwf4, hx04, hx34⟩ :=
    promoteBracket_close hok.check.state.wf hwf3 (hext.trans hx23)
  have hpins3 : s3.pins = s0.pins := by rw [hfr.pins, hpins]
  have hd4 : denoteFEnv s3.store.dropScratch fe' = some env' :=
    denoteFEnv_pext hx34 hp3 hd3
  refine ⟨?_, hx04, hpush, hm3, hx23, hpins3, hwf3⟩
  exact
    { check :=
        { state := ⟨hwf4⟩
          caches := CacheOK.of_empty rfl
          pins := hok.check.pins.pmono hok.persPins hx04 hpins3
          ienv := IFEnvOK_of_denote (μ := μ) ⟨hwf4⟩ hcoh3
            (fun t ht => (hproj3 t ht).pmono (hp3.env _ ht) hx34) hd4 }
      envWF := hb.envWF
      persPins := hok.persPins.mono hpins3
      persEnv := hp3
      coh := hcoh3
      denote := hd4 }

/-- con-leche: none — a push onto a denoting index extends the denoted
environment by the pushed constants' denotations. -/
theorem envExt_of_pushed {st : EStore} {fe fe1 : IFEnv} {env env' : Env}
    (hd : denoteFEnv st fe = some env) (hd1 : denoteFEnv st fe1 = some env')
    (hp : Pushed fe fe1) : ∃ new, env'.consts = new ++ env.consts := by
  obtain ⟨newI, hn⟩ := hp
  simp only [denoteFEnv, denoteIEnv, Option.map_eq_some_iff] at hd hd1
  obtain ⟨zs, hzs, rfl⟩ := hd
  obtain ⟨zs1, hzs1, rfl⟩ := hd1
  rw [hn] at hzs1
  obtain ⟨za, zb, -, hzb, rfl⟩ := denoteCIList_append _ _ zs1 hzs1
  rw [hzs] at hzb
  obtain rfl := Option.some.inj hzb
  exact ⟨za, rfl⟩

/-- con-leche: none — the bracket's opening (`flushCaches`, `enterScratch`)
keeps the boundary invariant: the caches are empty, the store is the same up
to the (empty) scratch tier, and everything `FoldOK` names is persistent. -/
theorem FoldOK.enter {μ : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    (hok : FoldOK μ env fe s) :
    FoldOK μ env fe
      ({ store := s.store.enableScratch, memos := Memos.empty,
         caches := Caches.empty, pins := s.pins } : AState) := by
  have hwf := hok.check.state.wf
  have hx : PExt s.store s.store.enableScratch := PExt.enterScratch hwf
  exact
    { check :=
        { state := ⟨(EStore.enableScratch_spec hwf).1⟩
          caches := CacheOK.of_empty rfl
          pins := hok.check.pins.pmono hok.persPins hx rfl
          ienv := hok.check.ienv.pmono hok.persEnv hx }
      envWF := hok.envWF
      persPins := hok.persPins.mono rfl
      persEnv := hok.persEnv
      coh := hok.coh
      denote := denoteFEnv_pext hx hok.persEnv hok.denote }

/-- con-leche: ConLeche/Verify/CheckerSplit.lean:30 installConstantVal_inv —
**the four type clauses of an INSTALLED header** (`checkConstantVal_typeWF`'s
argument at the install half, which skips the inference). -/
theorem installConstantVal_typeWF {μ : CheckMode} {F : Nat} {env : Env}
    {cv cvA : ConstantVal}
    (h : ConLeche.installConstantVal (ConLeche.fueledOps μ F) env cv = .ok cvA) :
    CVTypeWF env cvA := by
  obtain ⟨-, -, -, -, hlbt, hitf, type', hann, htp, htr, rfl⟩ :=
    ConLeche.installConstantVal_inv h
  exact { fvar := ConLeche.Expr.not_hasFvar_of_fvarsBelow_zero
            ((ConLeche.annotateCore_WScoped F cv.type hann
              (ConLeche.Expr.WScoped.of_not_hasFvar hitf)).fvarsBelow)
          lvls := htp
          res := htr
          bnd := ConLeche.annotateCore_looseBVars F cv.type hann hlbt }

/-- con-leche: none — a denoting list whose denoted names are unique names
pairwise different names, handle by handle (`denoteCI_name_of` at every
entry, which needs the tables' name clause). -/
theorem namesDistinct_of_denote {st : EStore} :
    ∀ (l : List IConstantInfo) (zs : List ConstantInfo),
      Frontend.denoteCIList st l = some zs → (zs.map (·.name)).Nodup →
      (∀ t, IConstantInfo.projInfo t ∈ l → IProjNamed st t) → NamesDistinct st l := by
  intro l
  induction l with
  | nil => intro _ _ _ _; exact List.Pairwise.nil
  | cons a as ih =>
    intro zs hz hnd hproj
    obtain ⟨x, xs, ha, has, rfl⟩ := denoteCIList_cons hz
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine List.pairwise_cons.mpr ⟨?_, ih xs has hnd.2
      (fun t ht => hproj t (List.mem_cons_of_mem _ ht))⟩
    intro b hb
    obtain ⟨z, hzm, hzd⟩ := denoteCIList_mem as xs has b hb
    refine ⟨x.name, z.name,
      denoteCI_name_of (fun t ht => hproj t (by simp [ht])) ha,
      denoteCI_name_of (fun t ht => hproj t (List.mem_cons_of_mem _ (ht ▸ hb))) hzd, ?_⟩
    intro he
    exact hnd.1 (he ▸ List.mem_map_of_mem hzm)

/-- con-leche: none — **the full `checkDecl` arm's pushed environment is well
formed, and every projection table of the pushed index is well shaped**.

PROVED (task #97-P3-Checker round 10), from `DeclOut`'s two round-10 clauses
(the coordinator's ruling on round 9's finding): `envWF` at the one
denotation, and `proj`, whose old tables are the incoming index's —
`FoldOK.projMem` under name uniqueness, carried across the arm's `Ext`.  The
arms prove the two clauses off their pure run (`DeclCore.out`,
`Bridge/Checker/Arms.lean`), except the unpinned inductive route, which is
`IndSpec.wf` (`Bridge/Checker/Hyp.lean`), owed by the Inductives tier. -/
theorem Arena.checkDecl_wfProj {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env env' : Env}
    {fe fe' : IFEnv} {pd : IDeclaration} {d : Declaration} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s) (hnd : NodupNames env)
    (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.checkDecl μ pins fe pd s = .ok (fe', s'))
    (hden : denoteFEnv s'.store fe' = some env') :
    EnvWF env' ∧
      ∀ t, IConstantInfo.projInfo t ∈ fe'.env.consts → IProjTableOK s'.store t := by
  have hout := Arena.checkDecl_bridge hμ hk hind hok hpins hd hrun
  refine ⟨hout.envWF env' hden, fun t ht => ?_⟩
  rcases hout.proj t ht with hold | hnew
  · exact (hok.projMem hnd t hold).mono hout.ext
  · exact hnew

/-- con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC (the
`checkDeclStepC` arm) — **the full arm of the step body**: `Arena.checkDecl`'s
`DeclOut`, `Arena.checkDecl_wfProj`'s two clauses, and the pushed names'
distinctness from the pure fold's (`checkDecl_nodup`). -/
theorem Arena.annotStepGo_full {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe1 : IFEnv} {pd : IDeclaration} {d : Declaration} {s1 s2 : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s1) (hnd : NodupNames env)
    (hpins : PinsDenote s1.store pins pinsP)
    (hd : Frontend.denoteDecl s1.store pd = some d)
    (hrun : Arena.checkDecl μ pins fe pd s1 = .ok (fe1, s2)) :
    ∃ env', BodyOut env' fe fe1 s2 ∧ Ext s1.store s2.store ∧ s2.pins = s1.pins ∧
      ∃ F, ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env' := by
  have hout := Arena.checkDecl_bridge hμ hk hind hok hpins hd hrun
  obtain ⟨env', F, hden, hF⟩ := hout.run
  obtain ⟨hwf', hproj⟩ := Arena.checkDecl_wfProj hμ hk hind hok hnd hpins hd hrun hden
  refine ⟨env', ⟨hout.state, hout.coh, hout.pushed, hden, hwf', hproj, ?_⟩, hout.ext,
    hout.pins, F, hF⟩
  -- the pushed constants: the `k` newest, denoting the pure step's new ones
  obtain ⟨newI, hn⟩ := hout.pushed
  have hk' : fe1.visibleBelow - fe.visibleBelow = newI.length := by
    rw [hout.coh.1, hok.coh.1, hn, List.length_append]; omega
  rw [hk', hn, List.take_left' rfl]
  have hnd' : NodupNames env' := checkDecl_nodup hF hnd
  have hden1 := hden
  simp only [denoteFEnv, denoteIEnv, Option.map_eq_some_iff] at hden1
  obtain ⟨zs, hzs, rfl⟩ := hden1
  rw [hn] at hzs
  obtain ⟨za, zb, hza, -, rfl⟩ := denoteCIList_append _ _ zs hzs
  have hndza : (za.map (·.name)).Nodup := by
    have : ((za ++ zb).map (·.name)).Nodup := hnd'
    rw [List.map_append] at this
    exact this.sublist (List.sublist_append_left _ _)
  exact namesDistinct_of_denote newI za hza hndza
    (fun t ht => (hproj t (by rw [hn]; exact List.mem_append_left _ ht)).toNamed)

/-- con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC — **phase A's
step body, unbracketed**: `annotStepGo`'s four arms, from the state the
bracket's opening left, deliver what the close needs (`BodyOut`) and the
pure half the fold rebuilds `checkDecl` from — a full `checkDecl` step, or a
split install owing the value group it returns.

PROVED (task #97-P3-Checker round 9) for the three split arms
(`installConstantVal_bridge`, `installValue_bridge`, `StepOK`'s push lemmas at
one pushed constant) and, for every other arm, from `Arena.annotStepGo_full`,
whose `Arena.checkDecl_wfProj` is the open child. -/
theorem Arena.annotStepGo_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe1 : IFEnv} {vg? : Option Arena.ValueGroup}
    {pd : IDeclaration} {d : Declaration} {s1 s2 : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s1) (hnd : NodupNames env)
    (hpins : PinsDenote s1.store pins pinsP)
    (hd : Frontend.denoteDecl s1.store pd = some d)
    (hrun : Arena.annotStepGo μ pins fe pd s1 = .ok ((fe1, vg?), s2)) :
    ∃ env', BodyOut env' fe fe1 s2 ∧ Ext s1.store s2.store ∧ s2.pins = s1.pins ∧
      ((vg? = none ∧ ∃ F,
          ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env') ∨
        ∃ vg gP F, vg? = some vg ∧ SplitInstall μ F env d gP env' ∧
          KindRel vg.kind gP.kind ∧
          Frontend.denoteCV s2.store vg.cvA = some gP.cvA ∧
          denoteE s2.store vg.jv = some gP.jv ∧
          Expr.WScoped 0 gP.cvA.type ∧ (gP.kind ≠ .thm → Expr.WScoped 0 gP.jv)) := by
  -- the full arm, whichever record reaches it
  have full : ∀ {sA : AState}, sA = s1 →
      ((Arena.checkDecl μ pins fe pd >>= fun fe' =>
        (pure (fe', (none : Option Arena.ValueGroup)) : AM (IFEnv × Option Arena.ValueGroup)))
        : AM (IFEnv × Option Arena.ValueGroup)) sA = .ok ((fe1, vg?), s2) →
      ∃ env', BodyOut env' fe fe1 s2 ∧ Ext s1.store s2.store ∧ s2.pins = s1.pins ∧
        ((vg? = none ∧ ∃ F,
            ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env') ∨
          ∃ vg gP F, vg? = some vg ∧ SplitInstall μ F env d gP env' ∧
            KindRel vg.kind gP.kind ∧
            Frontend.denoteCV s2.store vg.cvA = some gP.cvA ∧
            denoteE s2.store vg.jv = some gP.jv ∧
            Expr.WScoped 0 gP.cvA.type ∧ (gP.kind ≠ .thm → Expr.WScoped 0 gP.jv)) := by
    intro sA hsA h
    subst hsA
    obtain ⟨feA, sB, gA, rA⟩ := AM.bind_ok h
    obtain ⟨hv, rfl⟩ := AM.pure_ok rA
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨env', hb, hx, hp, F, hF⟩ :=
      Arena.annotStepGo_full hμ hk hind hok hnd hpins hd gA
    exact ⟨env', hb, hx, hp, Or.inl ⟨rfl, F, hF⟩⟩
  -- a split arm's shared tail: one pushed value-kind constant
  have split : ∀ {ci : IConstantInfo} {c : ConstantInfo}, (∀ t, ci ≠ .projInfo t) →
      StateOK s2 → Ext s1.store s2.store →
      Frontend.denoteCI s2.store ci = some c → ConstWF ⟨c :: env.consts⟩ c →
      BodyOut ⟨c :: env.consts⟩ fe (fe.push ci) s2 := by
    intro ci c hnp hst hx hci hcw
    have hso := (hok.toStepOK.mono hx).push hst hnp hci hcw
    refine ⟨hst, hso.coh, Pushed.push fe ci, hso.denote, hso.envWF, ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with h | h
      · exact absurd h.symm (hnp t)
      · exact (hok.projMem hnd t h).mono hx
    · show NamesDistinct s2.store ((ci :: fe.env.consts).take (fe.visibleBelow + 1 - fe.visibleBelow))
      rw [show fe.visibleBelow + 1 - fe.visibleBelow = 1 by omega]
      exact List.pairwise_singleton _ _
  cases pd with
  | defnDecl cv value hint =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s1.store cv with
    | none => rw [hcv] at hd; simp at hd
    | some c =>
    cases hv : denoteE s1.store value with
    | none => rw [hcv, hv] at hd; simp at hd
    | some x =>
    rw [hcv, hv] at hd
    simp only [Option.some.injEq] at hd
    subst hd
    simp only [Arena.annotStepGo] at hrun
    obtain ⟨ns, t1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨e1, hns⟩ := natOpNames_run hok.check.pins g1
    rw [e1] at r1
    obtain ⟨ds, t2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨e2, hds⟩ := natDivModNames_run hok.check.pins g2
    rw [e2] at r2
    have hwf1 := hok.check.state.wf
    obtain ⟨hnm, -, -⟩ := denoteCV_inv hcv
    have hcN := denoteNList_contains hwf1 ns _ (denoteNL_toList ns _ hns) cv.name c.name hnm
    have hcD := denoteNList_contains hwf1 ds _ (denoteNL_toList ds _ hds) cv.name c.name hnm
    split at r2
    · exact full rfl r2
    · rename_i hnat
      obtain ⟨cvA, sa, ga, ra⟩ := AM.bind_ok r2
      obtain ⟨hsa, cA, F1, hcA, hI⟩ := installConstantVal_bridge hμ hk hok hcv ga
      have hoka := hok.ofCore hsa
      obtain ⟨jv, sb, gb, rb⟩ := AM.bind_ok ra
      obtain ⟨hsb, y, F2, hy, hV⟩ := installValue_bridge hμ hk hoka.envWF hoka.check hcA
        (denote_ext hv hsa.ext) gb
      obtain ⟨hvv, rfl⟩ := AM.pure_ok rb
      simp only [Prod.mk.injEq] at hvv
      obtain ⟨rfl, rfl⟩ := hvv
      have hx12 : Ext s1.store s2.store := hsa.ext.trans hsb.ext
      have hcA2 : Frontend.denoteCV s2.store cvA = some cA := denoteCV_ext hcA hsb.ext
      have htw := installConstantVal_typeWF hI
      obtain ⟨gf, gl, gr, gb'⟩ := installValue_valueWF hV
      have hci : Frontend.denoteCI s2.store (.defnInfo cvA jv hint)
          = some (.defnInfo cA y hint) := by
        simp only [Frontend.denoteCI, hcA2, hy]
      have hnatP : (ConLeche.natOpNames.contains c.name ||
          ConLeche.natDivModNames.contains c.name) = false := by
        rw [← hcN, ← hcD]; simpa using hnat
      refine ⟨_, split (fun t h => IConstantInfo.noConfusion h) hsb.ok.state hx12 hci
          (constWF_defnInfo htw.cons gf gl (ConLeche.Expr.constsResolve_mono gr) gb'),
        hx12, by rw [hsb.pins, hsa.pins],
        Or.inr ⟨_, ⟨.defn, cA, y⟩, max F1 F2, rfl, Or.inl ⟨c, x, hint, rfl, hnatP, rfl,
          ConLeche.installConstantVal_mono (Nat.le_max_left _ _) hI,
          ConLeche.installValue_mono (Nat.le_max_right _ _) hV, rfl⟩,
          Or.inl ⟨rfl, rfl⟩, hcA2, hy, ConLeche.Expr.WScoped.of_not_hasFvar htw.fvar,
          fun _ => ConLeche.Expr.WScoped.of_not_hasFvar gf⟩⟩
  | thmDecl cv value =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s1.store cv with
    | none => rw [hcv] at hd; simp at hd
    | some c =>
    cases hv : denoteE s1.store value with
    | none => rw [hcv, hv] at hd; simp at hd
    | some x =>
    rw [hcv, hv] at hd
    simp only [Option.some.injEq] at hd
    subst hd
    simp only [Arena.annotStepGo] at hrun
    obtain ⟨cvA, sa, ga, ra⟩ := AM.bind_ok hrun
    obtain ⟨hsa, cA, F1, hcA, hI⟩ := installConstantVal_bridge hμ hk hok hcv ga
    obtain ⟨hvv, rfl⟩ := AM.pure_ok ra
    simp only [Prod.mk.injEq] at hvv
    obtain ⟨rfl, rfl⟩ := hvv
    have hx2 : denoteE s2.store value = some x := denote_ext hv hsa.ext
    have htw := installConstantVal_typeWF hI
    have hci : Frontend.denoteCI s2.store (.thmInfo cvA value)
        = some (.thmInfo cA x) := by
      simp only [Frontend.denoteCI, hcA, hx2]
    refine ⟨_, split (fun t h => IConstantInfo.noConfusion h) hsa.ok.state hsa.ext hci
        (constWF_thmInfo htw.cons),
      hsa.ext, hsa.pins,
      Or.inr ⟨_, ⟨.thm, cA, x⟩, F1, rfl, Or.inr (Or.inl ⟨c, x, rfl, rfl, hI, rfl, rfl⟩),
        Or.inr (Or.inl ⟨rfl, rfl⟩), hcA, hx2,
        ConLeche.Expr.WScoped.of_not_hasFvar htw.fvar, fun h => absurd rfl h⟩⟩
  | opaqueDecl cv value =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s1.store cv with
    | none => rw [hcv] at hd; simp at hd
    | some c =>
    cases hv : denoteE s1.store value with
    | none => rw [hcv, hv] at hd; simp at hd
    | some x =>
    rw [hcv, hv] at hd
    simp only [Option.some.injEq] at hd
    subst hd
    simp only [Arena.annotStepGo] at hrun
    obtain ⟨ns, t1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨e1, hns⟩ := reduceOpNames_run hok.check.pins g1
    rw [e1] at r1
    have hwf1 := hok.check.state.wf
    obtain ⟨hnm, -, -⟩ := denoteCV_inv hcv
    have hcR := denoteNList_contains hwf1 ns _ (denoteNL_toList ns _ hns) cv.name c.name hnm
    split at r1
    · exact full rfl r1
    · rename_i hred
      obtain ⟨cvA, sa, ga, ra⟩ := AM.bind_ok r1
      obtain ⟨hsa, cA, F1, hcA, hI⟩ := installConstantVal_bridge hμ hk hok hcv ga
      have hoka := hok.ofCore hsa
      obtain ⟨jv, sb, gb, rb⟩ := AM.bind_ok ra
      obtain ⟨hsb, y, F2, hy, hV⟩ := installValue_bridge hμ hk hoka.envWF hoka.check hcA
        (denote_ext hv hsa.ext) gb
      obtain ⟨hvv, rfl⟩ := AM.pure_ok rb
      simp only [Prod.mk.injEq] at hvv
      obtain ⟨rfl, rfl⟩ := hvv
      have hx12 : Ext s1.store s2.store := hsa.ext.trans hsb.ext
      have hcA2 : Frontend.denoteCV s2.store cvA = some cA := denoteCV_ext hcA hsb.ext
      have htw := installConstantVal_typeWF hI
      obtain ⟨gf, -, -, -⟩ := installValue_valueWF hV
      have hci : Frontend.denoteCI s2.store (.axiomInfo cvA) = some (.axiomInfo cA) := by
        simp only [Frontend.denoteCI, hcA2, Option.map_some]
      have hredP : ConLeche.reduceOpNames.contains c.name = false := by
        rw [← hcR]; simpa using hred
      refine ⟨_, split (fun t h => IConstantInfo.noConfusion h) hsb.ok.state hx12 hci
          (constWF_axiomInfo htw.cons),
        hx12, by rw [hsb.pins, hsa.pins],
        Or.inr ⟨_, ⟨.opaque, cA, y⟩, max F1 F2, rfl, Or.inr (Or.inr ⟨c, x, rfl, hredP, rfl,
          ConLeche.installConstantVal_mono (Nat.le_max_left _ _) hI,
          ConLeche.installValue_mono (Nat.le_max_right _ _) hV, rfl⟩),
          Or.inr (Or.inr ⟨rfl, rfl⟩), hcA2, hy, ConLeche.Expr.WScoped.of_not_hasFvar htw.fvar,
          fun _ => ConLeche.Expr.WScoped.of_not_hasFvar gf⟩⟩
  | axiomDecl cv => exact full rfl hrun
  | basisDecl kind => exact full rfl hrun
  | quotDecl k cv => exact full rfl hrun
  | indDecl block nP => exact full rfl hrun

/-- con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC — **phase A's
step with the pure half it ran**: `Arena.annotStep_bridge`'s conclusion plus
what the fold needs to rebuild `checkDecl` — a full step's `checkDecl` at
`env`, or a split step's `SplitInstall` at `env` with the record's
`PendRel` — and the two frame facts phase B reads (the caches are empty after
the bracket's `dropScratch`; the environment only grows).

**SKELETONISED** (task #97-P3-Checker round 9): the bracket is PROVED —
`FoldOK.enter` for the opening, `promoteVG_spec` for the split arms' record,
and `bracketClose_foldOK` (`promoteNew_spec`, `promoteNew_pushed`,
`promoteNew_projOK`, `promoteBracket_close`) for the close — around ONE child,
`Arena.annotStepGo_bridge`, the step body.

**The statement gained `hnd : NodupNames env`** (a precondition repair, round
9): the close's `IFEnvOK_of_denote` needs every stored table of the pushed
index well shaped, and `FoldOK` states that only for tables a LOOKUP reaches;
under name uniqueness the two agree (`FoldOK.projMem`).  The fold has it
(`PhaseA.nodup` from the empty environment, carried by
`Arena.annotFold_bridge`).  **And `hpd : PersDecl pd`**: the record must be
persistent for its denotation to survive the opening `enterScratch` —
`Arena.checkDeclStep_bridge`'s repair of the same kind; the fold carries it
(`Arena.annotFold_bridge`'s `hpd`). -/
theorem Arena.annotStep_split {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {i : Nat} {fe fe' : IFEnv} {pend pend' : Array PendingCheck}
    {pd : IDeclaration} {d : Declaration} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s) (hnd : NodupNames env)
    (hpins : PinsDenote s.store pins pinsP)
    (hpp : PersPinSets pins) (hpend : ∀ pc ∈ pend.toList, PersVG pc.vg)
    (hpd : PersDecl pd) (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.annotStep μ pins i fe pend pd s = .ok ((fe', pend'), s')) :
    ∃ env', FoldOK μ env' fe' s' ∧ PExt s.store s'.store ∧
      Pushed fe fe' ∧ (∀ pc ∈ pend'.toList, PersVG pc.vg) ∧
      s'.caches = Caches.empty ∧ (∃ new, env'.consts = new ++ env.consts) ∧
      ((pend'.toList = pend.toList ∧ ∃ F,
          ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env') ∨
        ∃ pc gP F, pend'.toList = pend.toList ++ [pc] ∧ pc.pos = i ∧
          pc.vis = fe.visibleBelow ∧ SplitInstall μ F env d gP env' ∧
          PendRel s'.store env' pc (env, gP)) := by
  have hwf := hok.check.state.wf
  have hx1 : PExt s.store s.store.enableScratch := PExt.enterScratch hwf
  simp only [Arena.annotStep] at hrun
  obtain ⟨u0, s0, g0, r0⟩ := AM.bind_ok hrun
  rw [flushCaches_run] at g0
  simp only [Except.ok.injEq, Prod.mk.injEq] at g0
  obtain ⟨-, rfl⟩ := g0
  obtain ⟨u1, s1, g1, r1⟩ := AM.bind_ok r0
  rw [enterScratch_run] at g1
  simp only [Except.ok.injEq, Prod.mk.injEq] at g1
  obtain ⟨-, rfl⟩ := g1
  obtain ⟨⟨fe1, vg?⟩, s2, g2, r2⟩ := AM.bind_ok r1
  have hok1 := hok.enter
  obtain ⟨env', hb, hx12, hp12, hcase⟩ :=
    Arena.annotStepGo_bridge hμ hk hind hok1 hnd (PinsDenote.pmono hx1 _ _ hpp hpins)
      (denoteDecl_pext hx1 hpd hd) g2
  have hdenv := hok.denote
  have hnew : ∃ new, env'.consts = new ++ env.consts :=
    envExt_of_pushed (fe := fe) (fe1 := fe1)
      (denoteFEnv_mono hx12 (denoteFEnv_pext hx1 hok.persEnv hdenv)) hb.denote hb.pushed
  rcases hcase with ⟨rfl, F, hF⟩ | ⟨vg, gP, F, rfl, hsplit, hkind, hcv, hjv, hwsty, hwsjv⟩
  · -- a full step: promote the pushed constants, drop
    simp only at r2
    obtain ⟨⟨m', fe2⟩, s3, g3, r3⟩ := AM.bind_ok r2
    obtain ⟨u4, s4, g4, r4⟩ := AM.bind_ok r3
    rw [dropScratch_run] at g4
    simp only [Except.ok.injEq, Prod.mk.injEq] at g4
    obtain ⟨-, rfl⟩ := g4
    obtain ⟨hv, rfl⟩ := AM.pure_ok r4
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨hfold, hx04, hpush, -, -, -, -⟩ :=
      bracketClose_foldOK (s0 := s) (hok := hok)
        hb (Ext.refl _) (StoreWF'.of_wf hb.state.wf) (PMemoOK.empty _) hx12 hp12 g3
    exact ⟨env', hfold, hx04, hpush, hpend, rfl, hnew, Or.inl ⟨rfl, F, hF⟩⟩
  · -- a split step: promote the record, then the pushed constant, drop
    simp only at r2
    obtain ⟨⟨m, vg'⟩, s2', g2', r2'⟩ := AM.bind_ok r2
    obtain ⟨hwf2', hx22', hm2', hpvg, hkd, hcv', hjv', hfr2⟩ :=
      promoteVG_spec (StoreWF'.of_wf hb.state.wf) (PMemoOK.empty _) hcv hjv g2'
    obtain ⟨⟨m', fe2⟩, s3, g3, r3⟩ := AM.bind_ok r2'
    obtain ⟨u4, s4, g4, r4⟩ := AM.bind_ok r3
    rw [dropScratch_run] at g4
    simp only [Except.ok.injEq, Prod.mk.injEq] at g4
    obtain ⟨-, rfl⟩ := g4
    obtain ⟨hv, rfl⟩ := AM.pure_ok r4
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨hfold, hx04, hpush, -, hx2'3, hpins3, hwf3⟩ :=
      bracketClose_foldOK (s0 := s) (hok := hok)
        hb hx22' hwf2' hm2' (hx12.trans hx22') (by rw [hfr2.pins, hp12]) g3
    have hx34 : PExt s3.store s3.store.dropScratch := PExt.dropScratch' hwf3
    have hx2'4 : PExt s2'.store s3.store.dropScratch := (PExt.of_ext hx2'3).trans hx34
    have hvis : fe.visibleBelow = env.consts.length := by
      rw [hok.coh.1]
      simp only [denoteFEnv, denoteIEnv, Option.map_eq_some_iff] at hdenv
      obtain ⟨zs, hzs, rfl⟩ := hdenv
      exact denoteCIList_length _ _ hzs
    refine ⟨env', hfold, hx04, hpush, ?_, rfl, hnew,
      Or.inr ⟨⟨vg', i, fe.visibleBelow⟩, gP, F, Array.toList_push, rfl, rfl, hsplit, ?_⟩⟩
    · intro pc hpc
      rw [Array.toList_push] at hpc
      rcases List.mem_append.mp hpc with hpc | hpc
      · exact hpend pc hpc
      · rw [List.mem_singleton] at hpc; subst hpc; exact hpvg
    · exact
        { kind := by rw [hkd]; exact hkind
          cv := denoteCV_pext hx2'4 hpvg.cvA hcv'
          jv := hx2'4.expr _ _ hpvg.jv hjv'
          wsty := hwsty
          wsjv := hwsjv
          envWF := hok.envWF
          vis := hvis
          ext := hnew
          pers := hpvg }

/-- con-leche: none — every related record is persistent. -/
theorem PendRel.listRel_pers {st : EStore} {envF : Env} :
    ∀ {l : List PendingCheck} {l' : List (Env × ConLeche.ValueGroup)},
      ListRel (PendRel st envF) l l' → ∀ pc ∈ l, PersVG pc.vg
  | [], [], .nil => fun _ h => absurd h (by simp)
  | _ :: _, _ :: _, .cons h hs => by
    intro pc hpc
    rcases List.mem_cons.mp hpc with rfl | hpc
    · exact h.pers
    · exact PendRel.listRel_pers hs pc hpc

/-- con-leche: none — the relation survives a later bracket, record by
record. -/
theorem PendRel.listRel_mono {st st' : EStore} {envF envF' : Env}
    (hx : PExt st st') (he : ∃ new, envF'.consts = new ++ envF.consts) :
    ∀ {l : List PendingCheck} {l' : List (Env × ConLeche.ValueGroup)},
      ListRel (PendRel st envF) l l' →
      ListRel (PendRel st' envF') l l'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (h.mono hx he) (PendRel.listRel_mono hx he hs)

theorem ListRel.snoc {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {a : α} {b : β},
      ListRel R l l' → R a b → ListRel R (l ++ [a]) (l' ++ [b])
  | [], [], _, _, .nil, h => .cons h .nil
  | _ :: _, _ :: _, _, _, .cons h hs, hab => .cons h (ListRel.snoc hs hab)

/-- con-leche: ConLeche/Cached/Installed.lean:450-455 checkDecls (phase A) —
**phase A over handles**: an accepting `annotFold` is a pure `PhaseA` whose
owed checks are the arena's pending records, related one for one.

PROVED from `Arena.annotStep_split`: an induction over the records, the
relation carried across each bracket by `PendRel.listRel_mono`. -/
theorem Arena.annotFold_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hpp : PersPinSets pins) :
    ∀ (ds : List IDeclaration) (dsP : List Declaration) (env : Env) (i i' : Nat)
      (fe fe' : IFEnv) (pend pend' : Array PendingCheck)
      (pendP : List (Env × ConLeche.ValueGroup)) (s s' : AState),
      FoldOK μ env fe s → NodupNames env → PinsDenote s.store pins pinsP →
      (∀ x ∈ ds, PersDecl x) → denoteDecls s.store ds = some dsP →
      ListRel (PendRel s.store env) pend.toList pendP →
      Arena.annotFold μ pins (i, fe, pend) ds s = .ok (.ok (i', fe', pend'), s') →
      ∃ env' pendP', FoldOK μ env' fe' s' ∧ PExt s.store s'.store ∧
        PhaseA μ pinsP env dsP env' pendP' ∧
        ListRel (PendRel s'.store env') pend'.toList (pendP ++ pendP') ∧
        (ds = [] → s' = s) ∧ (ds ≠ [] → s'.caches = Caches.empty) := by
  intro ds
  induction ds with
  | nil =>
    intro dsP env i i' fe fe' pend pend' pendP s s' hok _ _ _ hden hrel hrun
    simp only [denoteDecls, Option.some.injEq] at hden
    subst hden
    simp only [Arena.annotFold] at hrun
    obtain ⟨he, rfl⟩ := AM.pure_ok hrun
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨env, [], hok, PExt.refl _, .nil env, by simpa using hrel,
      fun _ => rfl, fun h => absurd rfl h⟩
  | cons a as ih =>
    intro dsP env i i' fe fe' pend pend' pendP s s' hok hnd hpins hpd hden hrel hrun
    simp only [denoteDecls] at hden
    cases ha : Frontend.denoteDecl s.store a with
    | none => rw [ha] at hden; simp at hden
    | some x =>
      cases has : denoteDecls s.store as with
      | none => rw [ha, has] at hden; simp at hden
      | some xs =>
        rw [ha, has] at hden
        simp only [Option.some.injEq] at hden
        subst hden
        simp only [Arena.annotFold] at hrun
        obtain ⟨r1, s₁, hstep, htail⟩ := AM.bind_ok hrun
        simp only [Arena.annotDeclStep] at hstep
        cases hA : Arena.annotStep μ pins i fe pend a s with
        | error e =>
          rw [hA] at hstep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          obtain ⟨hbad, -⟩ := AM.pure_ok htail
          exact absurd hbad (by simp)
        | ok v =>
          obtain ⟨⟨fe₁, pend₁⟩, s₁'⟩ := v
          rw [hA] at hstep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
          obtain ⟨h1, h2⟩ := hstep
          subst h1
          subst s₁'
          obtain ⟨env₁, hok₁, hx₁, -, -, hc₁, hext₁, hcase⟩ :=
            Arena.annotStep_split hμ hk hind hok hnd hpins hpp
              (PendRel.listRel_pers hrel) (hpd a (by simp)) ha hA
          have hrel₁ := PendRel.listRel_mono hx₁ hext₁ hrel
          have hpins₁ := PinsDenote.pmono hx₁ _ _ hpp hpins
          have hpd₁ : ∀ c ∈ as, PersDecl c := fun c hc => hpd c (by simp [hc])
          have has₁ := denoteDecls_pext hx₁ as xs hpd₁ has
          rcases hcase with ⟨hpeq, F, hF⟩ | ⟨pc, gP, F, hpeq, -, -, hsplit, hpc⟩
          · have hrelA : ListRel (PendRel s₁.store env₁) pend₁.toList pendP := by
              rw [hpeq]; exact hrel₁
            obtain ⟨env', pendP', hok', hx', hA', hrel', hnil', hc'⟩ :=
              ih xs env₁ (i + 1) i' fe₁ fe' pend₁ pend' pendP s₁ s' hok₁
                (checkDecl_nodup hF hnd) hpins₁ hpd₁ has₁ hrelA htail
            refine ⟨env', pendP', hok', hx₁.trans hx', .full F hF hA', hrel',
              fun h => absurd h (by simp), fun _ => ?_⟩
            by_cases hnil : as = []
            · rw [hnil'  hnil]; exact hc₁
            · exact hc' hnil
          · have hrelA : ListRel (PendRel s₁.store env₁) pend₁.toList
                (pendP ++ [(env, gP)]) := by
              rw [hpeq]; exact ListRel.snoc hrel₁ hpc
            obtain ⟨env', pendP', hok', hx', hA', hrel', hnil', hc'⟩ :=
              ih xs env₁ (i + 1) i' fe₁ fe' pend₁ pend' (pendP ++ [(env, gP)]) s₁ s'
                hok₁ (hsplit.nodup hnd) hpins₁ hpd₁ has₁ hrelA htail
            refine ⟨env', (env, gP) :: pendP', hok', hx₁.trans hx',
              .split gP F hsplit hA', by simpa [List.append_assoc] using hrel',
              fun h => absurd h (by simp), fun _ => ?_⟩
            by_cases hnil : as = []
            · rw [hnil' hnil]; exact hc₁
            · exact hc' hnil

/-- con-leche: ConLeche/Cached/Installed.lean:260-274 checkPending — **phase
B's check of one record, at the prefix environment itself**.  The form the
fold consumes: `checkDecl_of_split_*` needs the check half at the SAME
environment as the install halves, and `Arena.checkPending_bridge`'s
existential `envK` (equal to the prefix only up to `find?`) cannot be fed to
it without a `find?`-congruence of the whole pure core that con-leche does not
state.  It is available here directly: `IFEnvOK_restrictTo` gives the index
invariant AT `env.prefixTo pc.vis`, so the knot is instantiated there.

PROVED (task #97-P3-Checker round 9): `IFEnvOK_prefix` (`IFEnvOK_restrictTo`,
its `hproj` from `FoldOK.projMem` — every stored table IS a lookup's answer
under name uniqueness), carried into the fresh scratch tier by
`IFEnvOK.pmono`, `checkValueGroup_bridge` at the prefix, then the bracket
with nothing to promote — `PExt.enterScratch` / `PExt.dropScratch` and
`FoldOK` across them.

**The statement's `hckK : CacheOK μ (env.prefixTo pc.vis) s` became
`hcE : s.caches = Caches.empty`** (a precondition repair, round 9).
`checkPending` opens with `enterScratch`, which REPLACES the scratch tier by
an empty one and keeps the caches; a cache row valid at `s` whose handles are
scratch handles names nothing — or, once the check interns again, something
else — after it, so `CacheOK` at `s` does not survive the opening and the
theorem was not provable from it.  The call site has the stronger fact: every
`checkPending` follows a `dropScratch` (`checkPendingList_bridge`'s `hc`). -/
theorem Arena.checkPending_prefix {μ : CheckMode} {env : Env}
    {fe : IFEnv} {pc : PendingCheck} {gP : ConLeche.ValueGroup} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpers : PersVG pc.vg)
    (hnd : (env.consts.map (·.name)).Nodup)
    (hcE : s.caches = Caches.empty)
    (henvK : EnvWF (env.prefixTo pc.vis))
    (hkind : KindRel pc.vg.kind gP.kind)
    (hcv : Frontend.denoteCV s.store pc.vg.cvA = some gP.cvA)
    (hjv : denoteE s.store pc.vg.jv = some gP.jv)
    (hwsty : Expr.WScoped 0 gP.cvA.type)
    (hwsjv : gP.kind ≠ .thm → Expr.WScoped 0 gP.jv)
    (hrun : Arena.checkPending μ fe pc s = .ok ((), s')) :
    FoldOK μ env fe s' ∧ PExt s.store s'.store ∧ s'.caches = Caches.empty ∧
      ∃ F, ConLeche.checkValueGroup (ConLeche.fueledOps μ F)
        (env.prefixTo pc.vis) gP = .ok () := by
  have hwf := hok.check.state.wf
  simp only [Arena.checkPending] at hrun
  obtain ⟨u1, s1, g1, r1⟩ := AM.bind_ok hrun
  rw [enterScratch_run] at g1
  simp only [Except.ok.injEq, Prod.mk.injEq] at g1
  obtain ⟨-, rfl⟩ := g1
  obtain ⟨u2, s2, g2, r2⟩ := AM.bind_ok r1
  rw [dropScratch_run] at r2
  simp only [Except.ok.injEq, Prod.mk.injEq] at r2
  obtain ⟨-, rfl⟩ := r2
  -- the opening: the prefix view's invariant, carried into the fresh scratch tier
  have hx1 : PExt s.store s.store.enableScratch := PExt.enterScratch hwf
  have hwf1 := (EStore.enableScratch_spec hwf).1
  have hck1 : CheckOK μ (env.prefixTo pc.vis) (fe.restrictTo pc.vis)
      { store := s.store.enableScratch, memos := Memos.empty, caches := s.caches,
        pins := s.pins } :=
    { state := ⟨hwf1⟩
      caches := CacheOK.of_empty hcE
      pins := hok.check.pins.pmono hok.persPins hx1 rfl
      ienv := (IFEnvOK_prefix hok hnd pc.vis).pmono
        ⟨hok.persEnv.env, hok.persEnv.idx⟩ hx1 }
  -- the check, at the prefix
  obtain ⟨hcs, F, hF⟩ := checkValueGroup_bridge hμ hk henvK hck1 hkind
    (denoteCV_pext hx1 hpers.cvA hcv) (hx1.expr _ _ hpers.jv hjv) hwsty hwsjv g2
  -- the close
  have hwf2 := hcs.ok.state.wf
  have hx : PExt s.store s2.store.dropScratch :=
    (hx1.trans (PExt.of_ext hcs.ext)).trans (PExt.dropScratch hwf2)
  have hpins : s2.pins = s.pins := hcs.pins
  refine ⟨?_, hx, rfl, F, hF⟩
  exact
    { check :=
        { state := ⟨(EStore.dropScratch_spec hwf2).1⟩
          caches := CacheOK.of_empty rfl
          pins := hok.check.pins.pmono hok.persPins hx hpins
          ienv := hok.check.ienv.pmono hok.persEnv hx }
      envWF := hok.envWF
      persPins := hok.persPins.mono hpins
      persEnv := hok.persEnv
      coh := hok.coh
      denote := denoteFEnv_pext hx hok.persEnv hok.denote }

/-- con-leche: ConLeche/Cached/Installed.lean:429-436 checkPendingList —
**phase B over handles**: every owed check of phase A is paid, at the
environment it was owed at.

PROVED from `Arena.checkPending_prefix`: an induction over the records;
each check leaves the caches empty (`dropScratch`), which is the next check's
`CacheOK` at ITS prefix. -/
theorem Arena.checkPendingList_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hnd : NodupNames env) :
    ∀ (pend : List PendingCheck) (pendP : List (Env × ConLeche.ValueGroup))
      (s s' : AState), FoldOK μ env fe s →
      ListRel (PendRel s.store env) pend pendP →
      (pend ≠ [] → s.caches = Caches.empty) →
      Arena.checkPendingList μ fe pend s = .ok (.ok (), s') →
      FoldOK μ env fe s' ∧ PExt s.store s'.store ∧
        ∀ p ∈ pendP, ∃ F,
          ConLeche.checkValueGroup (ConLeche.fueledOps μ F) p.1 p.2 = .ok () := by
  intro pend
  induction pend with
  | nil =>
    intro pendP s s' hok hrel _ hrun
    cases hrel
    simp only [Arena.checkPendingList] at hrun
    obtain ⟨-, rfl⟩ := AM.pure_ok hrun
    exact ⟨hok, PExt.refl _, fun _ h => absurd h (by simp)⟩
  | cons pc rest ih =>
    intro pendP s s' hok hrel hc hrun
    cases hrel with
    | cons hp hrest =>
      rename_i p pendP'
      have hc0 := hc (by simp)
      simp only [Arena.checkPendingList] at hrun
      cases hA : Arena.checkPending μ fe pc s with
      | error e =>
        rw [hA] at hrun
        simp at hrun
      | ok v =>
        obtain ⟨⟨⟩, s₁⟩ := v
        rw [hA] at hrun
        have hpre := hp.prefix
        obtain ⟨hok₁, hx₁, hc₁, F, hF⟩ :=
          Arena.checkPending_prefix hμ hk hok hp.pers hnd
            hc0 (by rw [hpre]; exact hp.envWF) hp.kind hp.cv
            hp.jv hp.wsty hp.wsjv hA
        rw [hpre] at hF
        obtain ⟨hok', hx', hall⟩ :=
          ih pendP' s₁ s' hok₁ (PendRel.listRel_mono hx₁ ⟨[], rfl⟩ hrest)
            (fun _ => hc₁) hrun
        refine ⟨hok', hx₁.trans hx', fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨F, hF⟩
        · exact hall q hq

/-! ## Phase A and phase B -/

/-- con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC — **phase
A's step, bracketed**: the four arms, the promotion of what leaves the step,
and the drop.

The conclusion is the install half's, not `checkDecl`'s: a value kind leaves a
`PendingCheck` behind and con-leche's `installConstantVal` / `installValue`
is what ran.  The three non-value arms fall through to `checkDecl` and the
conclusion is `Bridge/Checker/Decl.lean`'s `DeclOut`.

**The statement gained `hpend`** (task #97-P3-Checker round 8): the
conclusion says every record of `pend'` is persistent, and `pend'` contains
`pend` — so without the same of `pend` it was false at a non-persistent
input.  A missing precondition, free at the one call site (`annotFold`
starts from `#[]` and carries it).  Round 9 added `hnd : NodupNames env` and
`hpd : PersDecl pd`, `Arena.annotStep_split`'s own repairs.

PROVED from `Arena.annotStep_split` (round 8), which carries this conclusion
and the pure half the fold needs; the `sorry` lives there. -/
theorem Arena.annotStep_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {i : Nat} {fe fe' : IFEnv} {pend pend' : Array PendingCheck}
    {pd : IDeclaration} {d : Declaration} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s) (hnd : NodupNames env)
    (hpins : PinsDenote s.store pins pinsP)
    (hpp : PersPinSets pins) (hpend : ∀ pc ∈ pend.toList, PersVG pc.vg)
    (hpd : PersDecl pd) (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.annotStep μ pins i fe pend pd s = .ok ((fe', pend'), s')) :
    ∃ env', FoldOK μ env' fe' s' ∧ PExt s.store s'.store ∧
      Pushed fe fe' ∧ (∀ pc ∈ pend'.toList, PersVG pc.vg) ∧
      (pend'.toList = pend.toList ∨
        ∃ pc, pend'.toList = pend.toList ++ [pc] ∧ pc.pos = i ∧
          pc.vis = fe.visibleBelow) := by
  obtain ⟨env', h1, h2, h3, h4, -, -, hcase⟩ :=
    Arena.annotStep_split hμ hk hind hok hnd hpins hpp hpend hpd hd hrun
  refine ⟨env', h1, h2, h3, h4, ?_⟩
  rcases hcase with ⟨hpeq, -⟩ | ⟨pc, gP, F, hpeq, hpos, hvis, -, -⟩
  · exact Or.inl hpeq
  · exact Or.inr ⟨pc, hpeq, hpos, hvis⟩

/-- con-leche: ConLeche/Cached/Installed.lean:260-274 checkPending — **phase
B's check of one record**, against the prefix view, inside its own bracket.

**The statement gained four clauses** (task #97-P3-Checker round 7, on round
6 §6's finding; the coordinator authorised the repair).  All four are about
the PREFIX environment `envK = env.prefixTo pc.vis` or about the pending
record's own header, and none of them is derivable from `FoldOK μ env fe s`:

| clause | why `FoldOK μ env fe s` does not give it |
|---|---|
| `hckK : CacheOK μ (env.prefixTo pc.vis) s` (round 9: `hcE : s.caches = Caches.empty`, see `Arena.checkPending_prefix`) | `checkPending` opens with `enterScratch`, which does NOT flush the caches — only `dropScratch` does — so the run enters `checkValueGroup` with whatever rows the state holds, and a cache row is **not monotone downward**: a `whnf` that delta-unfolded a constant above the bound is simply wrong at `envK`.  It is TRUE at the call site for a different reason — every `checkPending` follows a `dropScratch` (phase A's last step's, or the previous record's), so `s.caches` is empty — but the statement has to say so |
| `henvK : EnvWF (env.prefixTo pc.vis)` | `ConstWF` asks for `constsResolve` at the environment the constant is stored in, and LOWERING the environment can only break that clause, so `EnvWF env` does not imply it.  It is the install fold's to carry |
| `hwsty : Expr.WScoped 0 gP.cvA.type`, `hwsjv : Expr.WScoped 0 gP.jv` | round 5 §7's two clauses, which `checkValueGroup_bridge` takes and this theorem cannot conjure: phase A's `installConstantVal` / `installValue` tested exactly that guard (`hasFvar = false` at depth 0 IS `WScoped 0`), so they travel in the `PendingCheck`, not in the state |

**Two more repairs** (task #97-P3-Checker round 8), both on the pure
record's side:

* `hkind : pc.vg.kind = gP.kind` was MISSING: nothing tied the handle record's
  kind to the pure one's, and `checkValueGroup` branches on it (a theorem's
  check tests propositionality and annotates the raw value; the other two do
  not), so the conclusion was false at a mismatched pair;
* `hwsjv` is WEAKENED to `gP.kind ≠ .thm → …`: a theorem's pending value is
  its RAW value, which phase A never guards (a theorem installs by statement),
  so the unconditional form is not dischargeable at the fold — and
  `checkValueGroup_bridge` only ever used it on the other two kinds.

PROVED from `Arena.checkPending_prefix` (round 8), which states the check AT
the prefix environment; the `sorry` lives there. -/
theorem Arena.checkPending_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {pc : PendingCheck} {gP : ConLeche.ValueGroup} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpers : PersVG pc.vg)
    (hnd : (env.consts.map (·.name)).Nodup)
    (hcE : s.caches = Caches.empty)
    (henvK : EnvWF (env.prefixTo pc.vis))
    (hkind : KindRel pc.vg.kind gP.kind)
    (hcv : Frontend.denoteCV s.store pc.vg.cvA = some gP.cvA)
    (hjv : denoteE s.store pc.vg.jv = some gP.jv)
    (hwsty : Expr.WScoped 0 gP.cvA.type)
    (hwsjv : gP.kind ≠ .thm → Expr.WScoped 0 gP.jv)
    (hrun : Arena.checkPending μ fe pc s = .ok ((), s')) :
    ∃ envK F, FoldOK μ env fe s' ∧ PExt s.store s'.store ∧
      envK.find? = (env.prefixTo pc.vis).find? ∧
      ConLeche.checkValueGroup (ConLeche.fueledOps μ F) envK gP = .ok () := by
  obtain ⟨h1, h2, -, F, hF⟩ := Arena.checkPending_prefix hμ hk hok hpers hnd hcE
    henvK hkind hcv hjv hwsty hwsjv hrun
  exact ⟨env.prefixTo pc.vis, F, h1, h2, rfl, hF⟩

/-! ## The punchline -/

/-- con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
con-leche: ConLeche/Verify/CheckerSplit.lean:319-380 checkDecl_of_split_*
**THE TWO FOLDS ARE ONE ACCEPT**: what the binary runs implies what the
theorem is about.  With `Bridge/Checker/Fold.lean`'s
`Arena.checkDeclsPure_bridge` this is the second half of DESIGN §8.2's
Theorem 1 — the half the history report's fine print 5 prices — and with
`Bridge/Checker/Capstone.lean` it carries the model to the binary's own fold.

**SKELETONISED** (task #97-P3-Checker round 8): phase A is
`Arena.annotFold_bridge` (PROVED, over the child `Arena.annotStep_split`),
phase B is `Arena.checkPendingList_bridge` (PROVED, over the child
`Arena.checkPending_prefix`), and the two are one accept by `PhaseA.foldlM`
(PROVED: `checkDecl_of_split_*` at each split step, `checkDecl_mono` for the
fuel).  Name uniqueness at the end of phase A — what `IFEnvOK_restrictTo`
needs — is `PhaseA.nodup`, over the child `checkDecl_nodup`.  So the `sorry`s
this theorem reaches in this tier are exactly `Arena.annotStep_split`,
`Arena.checkPending_prefix` and `checkDecl_nodup`. -/
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
  have hnd0 : NodupNames Env.empty := List.nodup_nil
  simp only [Arena.installThenCheck] at hrun
  obtain ⟨r1, s₁, hA, hrest⟩ := AM.bind_ok hrun
  cases r1 with
  | error e =>
    obtain ⟨hbad, -⟩ := AM.pure_ok hrest
    exact absurd hbad (by simp)
  | ok p =>
    obtain ⟨n, fe₁, pend⟩ := p
    obtain ⟨env₁, pendP, hok₁, -, hPA, hrel, hnil, hc₁⟩ :=
      Arena.annotFold_bridge hμ hk hind hpp ds.toList dsP Env.empty 0 n
        (mkIFEnv IEnv.empty) fe₁ #[] pend [] s s₁ hok hnd0 hpins hpd hden .nil hA
    simp only [List.nil_append] at hrel
    obtain ⟨r2, s₂, hB, hrest2⟩ := AM.bind_ok hrest
    cases r2 with
    | error e =>
      obtain ⟨hbad, -⟩ := AM.pure_ok hrest2
      exact absurd hbad (by simp)
    | ok u =>
      obtain ⟨he, hs'⟩ := AM.pure_ok hrest2
      simp only [Except.ok.injEq] at he
      subst he
      subst s'
      have hc : pend.toList ≠ [] → s₁.caches = Caches.empty := by
        intro hne
        by_cases hds : ds.toList = []
        · exfalso
          rw [hds] at hden
          simp only [denoteDecls, Option.some.injEq] at hden
          subst hden
          cases hPA
          exact hne (ListRel.nil_right hrel)
        · exact hc₁ hds
      obtain ⟨hok₂, -, hall⟩ :=
        Arena.checkPendingList_bridge hμ hk (hPA.nodup hnd0) pend.toList pendP s₁ s₂
          hok₁ hrel hc hB
      obtain ⟨F, hF⟩ := hPA.foldlM hall
      exact ⟨env₁, F, hok₂.denote, hF F (Nat.le_refl _)⟩

end ConRon.Bridge
