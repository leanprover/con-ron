/-
# `ConRon.Bridge.Inductives.SumInstall` — Theorem 1 for the direct install's stages

`Arena/Inductives/SumInstall.lean`'s seventeen twins against
`ConLeche/Kernel/Inductives/SumInstall.lean` (and the eight `…F` `abbrev`s of
`SumInstallF.lean`, which are the same functions — task #97d-2's deviation 1).
These are the stages the fixpoint route runs: the former's telescope, the
capability record, the per-field universe bound, the positivity
normalisation, the constructors' stage and the generated rules.

**Mostly CORE grade.**  `whnfTelescope` calls `whnf`, `checkStructFieldSortsI`
calls `inferTypeCore` and `ensureSort`, `normPosDom` calls `whnf`,
`normCtorVal` and `checkSumCtor` call all of them — so their frame is
`CoreStep` and their hypothesis is `CoreSpec`.  Four are pure grade
(`closeTelescope`, `zipFvarDoms`, `consSumCtors`, the two arithmetic readers).

## Two of task #97d-2's five removed higher-order arguments are here

* `checkSumInd`'s `capsOf : InductiveShape → IndCaps` became `isRec : Bool`,
  with `nativeCapsAt` moved one module earlier.  The statement compares the
  twin with con-leche at `capsOf := fun p => ConLeche.nativeCapsAt p isRec`,
  which is that deviation written down.
* `sumRules`' `find? : Name → Option ConstantInfo` became `fe : IFEnv`.  The
  statement compares it at `find? := env.find?`, which is what `IFEnvOK`'s
  `hit`/`cover` pair says the index is.
-/
import ConRon.Bridge.Inductives.StructInstall

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The two arithmetic readers

`InductiveShape.rulePrefix` and `.majorIdx` read only `Nat` fields and the
constructor list's LENGTH, so they are equal on the nose once the shape
relation holds — the tier's second pair of closed results.
`denoteCtors_length` itself MOVED to `Bridge/Inductives/Rel.lean` in round 5:
`NativeParts.lean`'s `nativeRecPinOk_spec` is below this file in the import
chain and needs it. -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:292-294 InductiveShape.rulePrefix
The recursor's rule prefix `nP + 1 + n`. -/
theorem rulePrefix_spec {st : EStore} {p : Arena.InductiveShape}
    {q : ConLeche.InductiveShape} (h : ShapeRel st p q) :
    p.rulePrefix = q.rulePrefix := by
  simp only [Arena.InductiveShape.rulePrefix, ConLeche.InductiveShape.rulePrefix,
    h.nP, denoteCtors_length _ _ h.ctors]

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:295 InductiveShape.majorIdx
The major premise's index. -/
theorem majorIdx_spec {st : EStore} {p : Arena.InductiveShape}
    {q : ConLeche.InductiveShape} (h : ShapeRel st p q) :
    p.majorIdx = q.majorIdx := by
  simp only [Arena.InductiveShape.majorIdx, ConLeche.InductiveShape.majorIdx,
    rulePrefix_spec h, h.nIdx]

/-! ## The former's telescope -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:45-68 whnfTelescope
Peel `n` Π binders, reducing at each step, down to the result `Sort`.

`sorry`: a `Nat` recursion over `CoreSpec.knot`'s `whnf` slot and
`Bridge/Rel.lean`'s `forallE`/`sort` inversions. -/
theorem whnfTelescope_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (i n : Nat) (e : EIdx) (eP : Expr) :
    CSpec μ env fe
      (fun st => denoteE st e = some eP ∧ denoteFEnv st fe = some env)
      (Arena.whnfTelescope μ fe i n e)
      (fun st r => ∃ F bsP sP,
        ConLeche.whnfTelescope (ConLeche.fueledOps μ F) env i n eP
          = .ok (bsP, sP) ∧
        denoteBinders st r.1 = some bsP ∧ denoteL st.ls r.2 = some sP) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:70-78 closeTelescope
Close a body under a telescope, abstracting the free variables as it goes.
PURE grade: `abstract1Fast` and `internE`, no knot.

**CLOSED** (task #97-P3-Ind round 6): a list induction over
`Bridge/ExprOps/Owed.lean`'s `abstract1Fast_spec` — at `Rel.lean`'s
`fvarBSpec`, the `FvarBSpec` hypothesis discharged — and `internForallEE_run`. -/
theorem closeTelescope_spec (bs : List (EIdx × BinderMeta))
    (bsP : List (Expr × BinderMeta)) (i : Nat) (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => denoteBinders st bs = some bsP ∧
        denoteE st body = some bodyP)
      (Arena.closeTelescope bs i body)
      (RE (ConLeche.closeTelescope bsP i bodyP)) := by
  induction bs generalizing bsP i with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    simp only [denoteBinders, Option.some.injEq] at hbs
    subst hbs
    simp only [Arena.closeTelescope] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, hbody⟩
  | cons b bs ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    obtain ⟨dom, bm⟩ := b
    simp only [denoteBinders] at hbs
    cases hdom : denoteE s₀.store dom with
    | none => rw [hdom] at hbs; simp at hbs
    | some domP =>
    cases hrest : denoteBinders s₀.store bs with
    | none => rw [hdom, hrest] at hbs; simp at hbs
    | some rest =>
    rw [hdom, hrest] at hbs
    obtain rfl := (Option.some.inj hbs).symm
    simp only [Arena.closeTelescope] at hrun
    obtain ⟨inner, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hin⟩ := ih rest (i + 1) s₀ s1 inner hok ⟨hrest, hbody⟩ k1
    obtain ⟨cl, s2, k2, z2⟩ := bindOk z1
    obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := AM.of_run (P := fun t => t = s1) rfl k2
      (ExprOps.abstract1Fast_spec fvarBSpec Arena.coreWalkFuel s1 inner i 0 p1.ok
        (by rw [hin]; rfl))
    have p2 : PStep s1 s2 := PStep.of_caches h1 h2 h3 h4 h5
    obtain ⟨p3, hr⟩ := internForallEE_run p2.ok (denote_ext hdom (p1.ext.trans p2.ext))
      (h7 _ hin) z2
    exact ⟨p1.trans (p2.trans p3), hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:80-94 checkSumTele
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
The type former's stage: the telescope checked and the result sort measured.

`sorry`: `whnfTelescope_spec` and `closeTelescope_spec`, plus `CoreSpec.knot`'s
`defeq` slot for the stored type's comparison. -/
theorem checkSumTele_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (cv : IConstantVal) (cvP : ConstantVal)
    (n : Nat) (cvTa₀ : IConstantVal) (cvTa₀P : ConstantVal) :
    CSpec μ env fe
      (fun st => Frontend.denoteCV st cv = some cvP ∧
        Frontend.denoteCV st cvTa₀ = some cvTa₀P ∧
        denoteFEnv st fe = some env)
      (Arena.checkSumTele μ fe cv n cvTa₀)
      (fun st r => ∃ F cvAP sP,
        ConLeche.checkSumTele (ConLeche.fueledOps μ F) env cvP n cvTa₀P
          = .ok (cvAP, sP) ∧
        Frontend.denoteCV st r.1 = some cvAP ∧ denoteL st.ls r.2 = some sP) := by
  sorry

/-! ## The capability record -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:59-98 nativeCapsAt
The capability record the block's shape licenses — eta at a non-`Prop`
structure-like block, unit-likeness at a fieldless constructor, rule K at
official's `is_K_target`.  Twinned in `SumInstall.lean` rather than
`NativeInstall.lean` (task #97d-2's deviation 3: `checkSumInd`'s `capsOf`
became `isRec`, which moves this one module earlier).

**CLOSED** (task #97-P3-Ind round 5), at `PSpecP` — and the grade IS the
round-4 finding, discharged.  The `_` arm of both sides answers the DEFAULT
capability record and the two defaults do not correspond:
`Arena/Env.lean`'s `IIndCaps.etaCtor` defaults to `(default : NIdx)`, the zero
word, where `ConLeche.IndCaps.etaCtor` defaults to `.anonymous`, and
`Frontend.denoteCaps` reads the field UNCONDITIONALLY.  So the `_` arm asks
for `denoteN st.ns (default : NIdx) = some .anonymous`, which round 4 found no
invariant said.  `Bridge/StateOK.lean`'s `PinsOK` now says it (`PinsOK.anon`,
the maintainer's ruling), which is why this statement is `PSpecP` although the
twin reads no pin: it is the ANSWER that needs the pin phase to have run, not
the run.

This was never one `sorry`: `checkSumInd` pushes `.indInfo cvTa caps` with
exactly this record, so at every multi-constructor fixpoint install
`Frontend.denoteCI` of the new row — and with it `denoteFEnv`,
`InstRel.denote` and `FoldOK.denote` — was `none`.

The singleton arm is the shape relation's fields, `readLevel_run` (the twin
does NOT call `lvlEq?`) and `denoteCV_name` at the constructor handle. -/
theorem nativeCapsAt_spec (p : Arena.InductiveShape)
    (q : ConLeche.InductiveShape) (isRec : Bool) :
    PSpecP (fun st => ShapeRel st p q)
      (Arena.nativeCapsAt p isRec) (RCaps (ConLeche.nativeCapsAt q isRec)) := by
  intro s₀ s' r hok hpins hrel hrun
  simp only [Arena.nativeCapsAt] at hrun
  have hct : denoteCtors s₀.store p.ctors = some q.ctors := hrel.ctors
  cases hcs : p.ctors with
  | nil =>
    rw [hcs] at hrun hct
    have hqc : q.ctors = [] := (Option.some.inj hct).symm
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show Frontend.denoteCaps _ _ = _
    simp only [ConLeche.nativeCapsAt, hqc, Frontend.denoteCaps, hpins.anon]
  | cons a as =>
    obtain ⟨cv, nf⟩ := a
    rw [hcs] at hrun hct
    simp only [denoteCtors] at hct
    cases hcv : Frontend.denoteCV s₀.store cv with
    | none => rw [hcv] at hct; simp at hct
    | some cvP =>
      cases has : denoteCtors s₀.store as with
      | none => rw [hcv, has] at hct; simp at hct
      | some restP =>
        rw [hcv, has] at hct
        have hqc : q.ctors = (cvP, nf) :: restP := (Option.some.inj hct).symm
        cases as with
        | nil =>
          simp only [denoteCtors, Option.some.injEq] at has
          subst has
          obtain ⟨l, s1, k1, hz⟩ := bindOk hrun
          obtain ⟨hs1, hl⟩ := readLevel_run k1
          rw [hs1] at hz
          obtain rfl := Option.some.inj (hl.symm.trans hrel.resSort)
          obtain ⟨rfl, rfl⟩ := pureOk hz
          refine ⟨PStep.refl hok, ?_⟩
          show Frontend.denoteCaps _ _ = _
          simp only [ConLeche.nativeCapsAt, hqc, Frontend.denoteCaps,
            denoteCV_name hcv, hrel.nP, hrel.nIdx, hrel.isProp]
        | cons b bs =>
          obtain ⟨cv2, nf2⟩ := b
          simp only [denoteCtors] at has
          cases hcv2 : Frontend.denoteCV s₀.store cv2 with
          | none => rw [hcv2] at has; simp at has
          | some cv2P =>
            cases has2 : denoteCtors s₀.store bs with
            | none => rw [hcv2, has2] at has; simp at has
            | some rest2 =>
              rw [hcv2, has2] at has
              have hrp : restP = (cv2P, nf2) :: rest2 :=
                (Option.some.inj has).symm
              obtain ⟨rfl, rfl⟩ := pureOk hrun
              refine ⟨PStep.refl hok, ?_⟩
              show Frontend.denoteCaps _ _ = _
              simp only [ConLeche.nativeCapsAt, hqc, hrp, Frontend.denoteCaps,
                hpins.anon]

/-! ## The former's install stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:96-112 checkSumInd
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-43 checkSumIndF
The type former checked and installed, and the shape record completed with the
sort its telescope measured.  **Deviation 3's `capsOf`** is instantiated here.

`sorry`: `checkSumTele_spec`, `withSort_spec` (`Bridge/Inductives/SumParts.lean`),
`nativeCapsAt_spec`, and `IFEnv.push`'s two lemmas for the `InstRel`. -/
theorem checkSumInd_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (p : Arena.InductiveShape)
    (q : ConLeche.InductiveShape) (isRec : Bool) :
    CSpec μ env fe
      (fun st => ShapeRel st p q ∧ denoteFEnv st fe = some env)
      (Arena.checkSumInd μ fe p isRec)
      (fun st r => ∃ F envP cvTaP qP,
        ConLeche.checkSumInd (ConLeche.fueledOps μ F) env q
            (fun x => ConLeche.nativeCapsAt x isRec) = .ok (envP, cvTaP, qP) ∧
        InstRel fe (fun e => e = envP) st r.1 ∧
        Frontend.denoteCV st r.2.1 = some cvTaP ∧ ShapeRel st r.2.2 qP) := by
  sorry

/-! ## The fields' universe bound -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:114-139 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:45-61 checkStructFieldSortsIF
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:63-81 checkStructFieldSortsIFA
Each field's sort, checked against the family's — official's
subsingleton-elimination criterion at a one-constructor block.

`sorry`: a `Nat` recursion over `CoreSpec.knot`'s `infer` slot,
`CoreSpec.sort`'s `EnsureSortSpec`, and `Bridge/ExprOps/Leaves.lean`'s
`fvarTypeD`. -/
theorem checkStructFieldSortsI_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (isProp large : Bool) (s : LIdx)
    (sP : Level) (nP : Nat) (fvs idxArgs : List EIdx)
    (fvsP idxArgsP : List Expr) (j : Nat) :
    CSpec μ env fe
      (fun st => denoteL st.ls s = some sP ∧
        Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st idxArgs = some idxArgsP ∧
        denoteFEnv st fe = some env)
      (Arena.checkStructFieldSortsI μ fe isProp large s nP fvs idxArgs j)
      (fun st r => ∃ F ls,
        ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env isProp
          large sP nP fvsP idxArgsP j = .ok ls ∧
        denoteLList st.ls r = some ls) := by
  sorry

/-! ## The positivity normalisation -/

/-- con-leche: none — `normPosDom` is monotone in the fuel of its `whnf`:
`ConLeche.whnf_mono` at every step. -/
theorem normPosDom_mono {μ : CheckMode} {env : Env} {TP : ConLeche.Name}
    {F F' : Nat} (hle : F ≤ F') : ∀ {fuel d : Nat} {e v : Expr},
    ConLeche.normPosDom (ConLeche.fueledOps μ F) env TP d fuel e = .ok v →
    ConLeche.normPosDom (ConLeche.fueledOps μ F') env TP d fuel e = .ok v := by
  intro fuel
  induction fuel with
  | zero =>
    intro d e v h
    simp only [ConLeche.normPosDom] at h
    exact nomatch h
  | succ fuel ih =>
    intro d e v h
    simp only [ConLeche.normPosDom] at h ⊢
    cases hm : e.mentionsConst TP with
    | false => simpa [hm] using h
    | true =>
    simp only [hm, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
    simp only [ConLeche.fueledOps, bind, Except.bind] at h ⊢
    cases hw : ConLeche.whnf μ env F d e with
    | error x => rw [hw] at h; exact nomatch h
    | ok w =>
    rw [hw] at h
    rw [ConLeche.whnf_mono hle hw]
    dsimp only at h ⊢
    cases hm2 : w.mentionsConst TP with
    | false => simpa [hm2] using h
    | true =>
    simp only [hm2, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
    cases w with
    | forallE dom body bm =>
      dsimp only at h ⊢
      cases hdom : dom.mentionsConst TP with
      | true =>
        simp [hdom, throw, throwThe, MonadExceptOf.throw] at h
      | false =>
        simp only [hdom, Bool.false_eq_true, if_false] at h ⊢
        cases hr : ConLeche.normPosDom (ConLeche.fueledOps μ F) env TP (d + 1) fuel
            (body.instantiate1 (.fvar d dom)) with
        | error x => simp only [ConLeche.fueledOps] at hr; rw [hr] at h; exact nomatch h
        | ok b' =>
          simp only [ConLeche.fueledOps] at hr
          rw [hr] at h
          have := ih (by simpa only [ConLeche.fueledOps] using hr)
          simp only [ConLeche.fueledOps] at this
          rw [this]
          exact h
    | _ => exact h

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:141-175 normPosDom
**`normPosDom_spec` with the answer's scope**: the normalised domain is well
scoped at the walk's depth.  This is the form a caller that feeds the answer
into a second knot slot needs (`normFieldDoms`, `normCtorVal`), and the form
the induction needs for its own recursive call; `normPosDom_spec` is it with
the conjunct dropped. -/
theorem normPosDom_run {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T : NIdx)
    (TP : ConLeche.Name) :
    ∀ (fuel d : Nat) (e : EIdx) (eP : Expr), Expr.WScoped d eP →
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧ denoteE st e = some eP ∧
        denoteFEnv st fe = some env)
      (Arena.normPosDom μ fe T d fuel e)
      (fun st r => ∃ F v,
        ConLeche.normPosDom (ConLeche.fueledOps μ F) env TP d fuel eP = .ok v ∧
        denoteE st r = some v ∧ Expr.WScoped d v) := by
  have hknot := hk.knot env fe henv
  intro fuel
  induction fuel with
  | zero =>
    intro d e eP _ s₀ s' r _ _ hrun
    simp only [Arena.normPosDom] at hrun
    exact absurd hrun (fun h => failOk h)
  | succ fuel ih =>
    intro d e eP hws s₀ s' r hok hpre hrun
    obtain ⟨hT, he, hfe⟩ := hpre
    simp only [Arena.normPosDom] at hrun
    obtain ⟨m1, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hm1⟩ := mentionsConst_spec T TP e eP s₀ s1 m1 hok.state ⟨hT, he⟩ k1
    have c1 := p1.toCore hok
    have hm1' : m1 = eP.mentionsConst TP := hm1
    subst hm1'
    cases hm : eP.mentionsConst TP with
    | false =>
      rw [hm] at z1
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨c1, 0, eP, ?_, denote_ext he p1.ext, hws⟩
      simp [ConLeche.normPosDom, hm, pure, Except.pure]
    | true =>
    rw [hm] at z1
    obtain ⟨w, s2, k2, z2⟩ := bindOk z1
    obtain ⟨hok2, hx2, hp2, hsim⟩ := AM.of_run (P := fun u => u = s1)
      (Q := fun r u => CheckOK μ env fe u ∧ Ext s1.store u.store ∧
        u.pins = s1.pins ∧ Core.SimE (ConLeche.whnf μ env) d eP u.store r)
      rfl k2 (hknot.whnf s1 d e eP c1.ok (denote_ext he p1.ext) hws)
    have c2 : CoreStep μ env fe s₀ s2 :=
      c1.trans ⟨hok2, hx2, hp2⟩
    obtain ⟨wP, hwP, hwsw, F1, hF1⟩ := hsim
    obtain ⟨m2, s3, k3, z3⟩ := bindOk z2
    obtain ⟨p3, hm2⟩ := mentionsConst_spec T TP w wP s2 s3 m2 hok2.state
      ⟨denoteN_ext hT c2.ext, hwP⟩ k3
    have hm2' : m2 = wP.mentionsConst TP := hm2
    subst hm2'
    have c3 := c2.trans (p3.toCore hok2)
    have hwP3 : denoteE s3.store w = some wP := denote_ext hwP p3.ext
    cases hmw : wP.mentionsConst TP with
    | false =>
      rw [hmw] at z3
      obtain ⟨rfl, rfl⟩ := pureOk z3
      refine ⟨c3, F1, wP, ?_, hwP3, hwsw⟩
      simp only [ConLeche.normPosDom, hm, Bool.not_true, Bool.false_eq_true, if_false,
        ConLeche.fueledOps, bind, Except.bind, hF1]
      simp [hmw, pure, Except.pure]
    | true =>
    rw [hmw] at z3
    obtain ⟨v, s4, k4, z4⟩ := bindOk z3
    obtain ⟨hs4, hv⟩ := view_run k4
    rw [hs4] at z4
    have hwf3 := c3.ok.state.wf
    have hF1' : ∀ F, F1 ≤ F → ConLeche.whnf μ env F d eP = .ok wP :=
      fun F hle => ConLeche.whnf_mono hle hF1
    cases v
    case forallE dom body bm =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hwf3 hv hwP3
      have hwsdb : Expr.WScoped d domP ∧ Expr.WScoped d bodyP := by
        simp only [Expr.WScoped] at hwsw; exact hwsw
      obtain ⟨hwsd, hwsb⟩ := hwsdb
      dsimp only at z4
      obtain ⟨m3, s5, k5, z5⟩ := bindOk z4
      obtain ⟨p5, hm3⟩ := mentionsConst_spec T TP dom domP s3 s5 m3 c3.ok.state
        ⟨denoteN_ext hT c3.ext, hd⟩ k5
      have hm3' : m3 = domP.mentionsConst TP := hm3
      subst hm3'
      have c5 := c3.trans (p5.toCore c3.ok)
      cases hmd : domP.mentionsConst TP with
      | true =>
        rw [hmd] at z5
        exact absurd z5 (fun h => failOk h)
      | false =>
      rw [hmd] at z5
      obtain ⟨fv, s6, k6, z6⟩ := bindOk z5
      have hd5 : denoteE s5.store dom = some domP := denote_ext hd p5.ext
      obtain ⟨p6, hfv⟩ := internE_run c5.ok.state (viewOK_fvar (by rw [hd5]; rfl)) k6
      have hfv' : denoteE s6.store fv = some (.fvar d domP) := by
        rw [hfv]; simp [denoteEView, denote_ext hd5 p6.ext]
      have c6 := c5.trans (p6.toCore c5.ok)
      obtain ⟨op, s7, k7, z7⟩ := bindOk z6
      have hb6 : denoteE s6.store body = some bodyP := denote_ext hb (p5.ext.trans p6.ext)
      obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ExprOps.instantiate1Fast_run c6.ok.state hfv'
        (by rw [hb6]; rfl) k7
      have p7 : PStep s6 s7 := PStep.of_caches h1 h2 h3 h4 h5
      have hop : denoteE s7.store op = some (bodyP.instantiate1 (.fvar d domP) 0) := h7 _ hb6
      have c7 := c6.trans (p7.toCore c6.ok)
      obtain ⟨b', s8, k8, z8⟩ := bindOk z7
      have hwsop : Expr.WScoped (d + 1) (bodyP.instantiate1 (.fvar d domP) 0) :=
        Expr.WScoped.instantiate1 hwsd 0 hwsb
      obtain ⟨c8, F2, v', hF2, hb', hwsv'⟩ := ih (d + 1) op _ hwsop s7 s8 b' c7.ok
        ⟨denoteN_ext hT c7.ext, hop, denoteFEnv_ext c7.ext hfe⟩ k8
      obtain ⟨cl, s9, k9, z9⟩ := bindOk z8
      obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := AM.of_run (P := fun t => t = s8) rfl k9
        (ExprOps.abstract1Fast_spec fvarBSpec Arena.coreWalkFuel s8 b' d 0 c8.ok.state
          (by rw [hb']; rfl))
      have p9 : PStep s8 s9 := PStep.of_caches h1 h2 h3 h4 h5
      have hcl := h7 _ hb'
      have hd9 : denoteE s9.store dom = some domP :=
        denote_ext hd5 (((p6.ext.trans p7.ext).trans c8.ext).trans p9.ext)
      obtain ⟨p10, hr⟩ := internForallEE_run p9.ok hd9 hcl z9
      refine ⟨c7.trans (c8.trans ((p9.trans p10).toCore c8.ok)), max F1 F2, _, ?_, hr,
        by simp only [Expr.WScoped]; exact ⟨hwsd, ConLeche.WScoped.abstract1 0 hwsv'⟩⟩
      have hF2' := normPosDom_mono (Nat.le_max_right F1 F2) hF2
      simp only [ConLeche.fueledOps] at hF2'
      rw [ConLeche.normPosDom]
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false,
        ConLeche.fueledOps, bind, Except.bind, hF1' _ (Nat.le_max_left F1 F2)]
      simp only [hmw, hmd, Bool.not_true, Bool.false_eq_true, if_false]
      rw [hF2']
      rfl
    all_goals
      obtain ⟨rfl, rfl⟩ := pureOk z4
      refine ⟨c3, F1, wP, ?_, hwP3, hwsw⟩
      have hnot : ∀ a b m, wP ≠ .forallE a b m := by
        intro a b m h
        subst h
        rw [denoteE_view_eq hwf3 hv] at hwP3
        simp [denoteEView] at hwP3
      rw [ConLeche.normPosDom]
      simp only [hm, Bool.not_true, Bool.false_eq_true, if_false,
        ConLeche.fueledOps, bind, Except.bind, hF1' _ (Nat.le_refl _)]
      simp only [hmw, Bool.not_true, Bool.false_eq_true, if_false]
      clear hwP3 hmw hwsw hF1 hF1'
      cases wP
      case forallE a b m => exact absurd rfl (hnot a b m)
      all_goals rfl

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:141-175 normPosDom
Reduce a field domain until it no longer mentions the block, or give up.

**CLOSED** (task #97-P3-Ind round 7): `normPosDom_run` with the scope
conjunct dropped.

**Two preconditions it was missing** (round 7, round 6's §R6.3 finding): the
`whnf` slot is stated at a well-formed environment (`CoreSpec.knot` takes
`EnvWF env`) and at a WELL-SCOPED subject (`Expr.WScoped d`, the walk's own
depth).  The same repair as `checkStructDomsAt_spec`'s; no conclusion
changed. -/
theorem normPosDom_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T : NIdx)
    (TP : ConLeche.Name) (d fuel : Nat) (e : EIdx) (eP : Expr)
    (hws : Expr.WScoped d eP) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧ denoteE st e = some eP ∧
        denoteFEnv st fe = some env)
      (Arena.normPosDom μ fe T d fuel e)
      (fun st r => ∃ F v,
        ConLeche.normPosDom (ConLeche.fueledOps μ F) env TP d fuel eP = .ok v ∧
        denoteE st r = some v) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hstep, F, v, hF, hv, -⟩ :=
    normPosDom_run fe hk henv T TP fuel d e eP hws s₀ s' r hok hpre hrun
  exact ⟨hstep, F, v, hF, hv⟩

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:177-188 normFieldDoms
The constructor's field domains, each normalised, opened at free variables.

`sorry`: a `Nat` recursion over `normPosDom_spec` and
`Bridge/ExprOps/Subst.lean`'s `instantiate1Fast_spec`. -/
theorem normFieldDoms_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (T : NIdx) (TP : ConLeche.Name)
    (i n : Nat) (h : EIdx) (hP : Expr) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧ denoteE st h = some hP ∧
        denoteFEnv st fe = some env)
      (Arena.normFieldDoms μ fe T i n h)
      (fun st r => ∃ F bsP rP,
        ConLeche.normFieldDoms (ConLeche.fueledOps μ F) env TP i n hP
          = .ok (bsP, rP) ∧
        denoteBinders st r.1 = some bsP ∧ denoteE st r.2 = some rP) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
`zipFvarDoms` is task #97d-2's replacement for con-leche's `zipWith` inside
`normCtorVal`: it reads each free variable's own type off the store, which is
what makes the normalised domains the ones the walk opened.

**PROVED** (task #97-P3-Ind round 4): the list induction over `fvarTypeD_run`
(`Bridge/Inductives/Rel.lean`, off `Bridge/ExprOps/Spine.lean`'s closed
`fvarTypeD_spec`).  `fvarTypeD` is read-only, so the whole zip is one
`PStep.refl`. -/
theorem zipFvarDoms_spec (xs : List EIdx) (xsP : List Expr)
    (bs : List (EIdx × BinderMeta)) (bsP : List (Expr × BinderMeta)) :
    PSpec (fun st => Frontend.denoteEList st xs = some xsP ∧
        denoteBinders st bs = some bsP)
      (Arena.zipFvarDoms xs bs)
      (fun st r => ∃ ts, denoteBinders st r = some ts ∧
        ts.length = min xsP.length bsP.length) := by
  induction xs generalizing xsP bs bsP with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hx, hb⟩ := hpre
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.zipFvarDoms] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], rfl, by simp⟩
  | cons x xs ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hx, hb⟩ := hpre
    cases bs with
    | nil =>
      simp only [denoteBinders, Option.some.injEq] at hb
      subst hb
      simp only [Arena.zipFvarDoms] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨PStep.refl hok, [], rfl, by simp⟩
    | cons b bs =>
      obtain ⟨bt, bm⟩ := b
      simp only [Frontend.denoteEList] at hx
      cases hx1 : denoteE s₀.store x with
      | none => rw [hx1] at hx; simp at hx
      | some xP =>
        cases hxs : Frontend.denoteEList s₀.store xs with
        | none => rw [hx1, hxs] at hx; simp at hx
        | some xsP' =>
          rw [hx1, hxs] at hx
          obtain rfl := Option.some.inj hx
          simp only [denoteBinders] at hb
          cases hb1 : denoteE s₀.store bt with
          | none => rw [hb1] at hb; simp at hb
          | some btP =>
            cases hbs : denoteBinders s₀.store bs with
            | none => rw [hb1, hbs] at hb; simp at hb
            | some bsP' =>
              rw [hb1, hbs] at hb
              obtain rfl := Option.some.inj hb
              simp only [Arena.zipFvarDoms] at hrun
              obtain ⟨t, s₁, h1, h2⟩ := bindOk hrun
              obtain ⟨rfl, ht⟩ := fvarTypeD_run hok hx1 h1
              obtain ⟨rest, s₂, h3, h4⟩ := bindOk h2
              obtain ⟨hstep, ts, hts, hlen⟩ :=
                ih xsP' bs bsP' _ s₂ rest hok ⟨hxs, hbs⟩ h3
              obtain ⟨rfl, rfl⟩ := pureOk h4
              refine ⟨hstep, (xP.fvarTypeD, bm) :: ts, ?_, ?_⟩
              · simp only [denoteBinders, denote_ext ht hstep.ext, hts]
              · simp only [List.length_cons, hlen]
                omega

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:83-95 normCtorValF
The constructor's stored type rebuilt from the normalised domains.

`sorry`: `normFieldDoms_spec`, `zipFvarDoms_spec` and `closeTelescope_spec`. -/
theorem normCtorVal_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (T : NIdx) (TP : ConLeche.Name)
    (nP nF : Nat) (cvC cvCa : IConstantVal) (cvCP cvCaP : ConstantVal) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteCV st cvC = some cvCP ∧
        Frontend.denoteCV st cvCa = some cvCaP ∧
        denoteFEnv st fe = some env)
      (Arena.normCtorVal μ fe T nP nF cvC cvCa)
      (fun st r => ∃ F v,
        ConLeche.normCtorVal (ConLeche.fueledOps μ F) env TP nP nF cvCP cvCaP
          = .ok v ∧ Frontend.denoteCV st r = some v) := by
  sorry

/-! ## The constructors' stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:97-128 checkSumCtorF
One constructor checked: its telescope, its parameter domains, its residual,
its field sorts and its normalised stored value.

`sorry`: `checkSumTele_spec`, `checkStructDomsAt_spec`
(`Bridge/Inductives/StructInstall.lean`), `checkStructFieldSortsI_spec`,
`normCtorVal_spec` and `structCtorResidOk_spec`. -/
theorem checkSumCtor_spec {μ : CheckMode} {env : Env} (fe₀ fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvC : IConstantVal) (cvCP : ConstantVal) (nF : Nat)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        Frontend.denoteCV st cvC = some cvCP ∧
        Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteFEnv st fe₀ = some env₀ ∧ denoteFEnv st fe = some env)
      (Arena.checkSumCtor μ fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa)
      (fun st r => ∃ F cvCaP sortsP,
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env TP lpsP nP
          nIdx resSortP isProp large cvCP nF cvTaP = .ok (cvCaP, sortsP) ∧
        Frontend.denoteCV st r.1 = some cvCaP ∧
        denoteLList st.ls r.2 = some sortsP) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:255-267 checkSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:130-140 checkSumCtorsF
The whole constructor list.

`sorry`: a list induction over `checkSumCtor_spec`. -/
theorem checkSumCtors_spec {μ : CheckMode} {env : Env} (fe₀ fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat)) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteCtors st cs = some csP ∧
        denoteFEnv st fe₀ = some env₀ ∧ denoteFEnv st fe = some env)
      (Arena.checkSumCtors μ fe₀ fe T lps nP nIdx resSort isProp large cvTa cs)
      (fun st r => ∃ F ctorsAP sortssP,
        ConLeche.checkSumCtors (ConLeche.fueledOps μ F) env₀ env TP lpsP nP
          nIdx resSortP isProp large cvTaP csP = .ok (ctorsAP, sortssP) ∧
        denoteCtors st r.1 = some ctorsAP ∧
        denoteLLists st r.2 = some sortssP) := by
  sorry

/-! ## The constructors consed, and the rules -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:269-272 consSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:142-145 consSumCtorsF
The constructors pushed into the index.  PURE on both sides.

**CLOSED** (task #97-P3-Ind round 6). -/
theorem consSumCtors_spec (st : EStore) (nP : Nat)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
    (fe : IFEnv) (env : Env) (hcs : denoteCtors st cs = some csP)
    (hfe : denoteFEnv st fe = some env) (hcoh : IFEnvCoh fe) :
    InstRel fe (fun e => e = ConLeche.consSumCtors nP csP env) st
      (Arena.consSumCtors nP cs fe) := by
  induction cs generalizing csP fe env with
  | nil =>
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    exact ⟨hcoh, Pushed.refl _, Nat.le_refl _, ⟨env, hfe, rfl⟩, ProjOut.refl _ _⟩
  | cons c cs ih =>
    obtain ⟨cv, n⟩ := c
    simp only [denoteCtors] at hcs
    cases hcv : Frontend.denoteCV st cv with
    | none => rw [hcv] at hcs; simp at hcs
    | some cP =>
    cases hrest : denoteCtors st cs with
    | none => rw [hcv, hrest] at hcs; simp at hcs
    | some restP =>
    rw [hcv, hrest] at hcs
    obtain rfl := (Option.some.inj hcs).symm
    have hci : Frontend.denoteCI st (.ctorInfo cv nP n) = some (.ctorInfo cP nP n) := by
      simp only [Frontend.denoteCI, hcv, Option.map_some]
    have hpush := denoteFEnv_push hfe hci
    have h1 : InstRel fe (fun _ => True) st (fe.push (.ctorInfo cv nP n)) :=
      ⟨hcoh.push _, Pushed.push _ _, Nat.le_succ _, ⟨_, hpush, trivial⟩,
        ProjOut.push hcoh st (fun t h => by cases h)⟩
    have h2 := ih restP (fe.push (.ctorInfo cv nP n)) ⟨.ctorInfo cP nP n :: env.consts⟩
      hrest hpush (hcoh.push _)
    exact InstRel.trans (Ext.refl _) h1 h2

/-! ## The two rescue bits (task #97-P3-Ind round 6)

`Arena/Core.lean`'s `recRuleKOf` / `recRuleEtaOf` / `recRuleBits` have no
Theorem 1 anywhere in the Bridge; `sumRules` is their first consumer, so
their run forms are here, **on loan from the Core tier** (their module is
`Bridge/Core/**`, beside the other `CoreDefs` twins).  Each lookup is
`IFEnvOK`'s `hit`/`miss` pair and each comparison `denoteN_inj`. -/

/-- con-leche: none — a constructor type's result head, read three steps
deep (`piResult`, `getAppFn`, `view`), all read-only. -/
theorem ctorHead_facts {s s1 s2 s3 : AState} {ty pr fn : EIdx} {tyP : Expr}
    {v : ENodeView} (hok : StateOK s) (hd : denoteE s.store ty = some tyP)
    (k1 : Arena.piResult Arena.coreWalkFuel ty s = .ok (pr, s1))
    (k2 : Arena.getAppFn Arena.coreWalkFuel pr s1 = .ok (fn, s2))
    (k3 : Arena.view fn s2 = .ok (v, s3)) :
    s = s1 ∧ s = s2 ∧ s = s3 ∧ s.store.view fn = some v ∧
      denoteE s.store fn = some tyP.piResult.getAppFn := by
  obtain ⟨hs1, hpr⟩ := AM.of_run (P := fun t => t = s) rfl k1
    (ExprOps.piResult_spec Arena.coreWalkFuel s ty hok (by rw [hd]; rfl))
  subst hs1
  obtain ⟨hs2, hfn⟩ := getAppFn_run hok (hpr _ hd) k2
  subst hs2
  obtain ⟨hs3, hv⟩ := view_run k3
  exact ⟨rfl, rfl, hs3.symm, hv, hfn⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:821-830 recRuleKOf — the K bit at
install, in run form: read-only, and con-leche's verdict at `env.find?`. -/
theorem recRuleKOf_run {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    {ctor : NIdx} {ctorP : ConLeche.Name} {r : Bool}
    (hok : CheckOK μ env fe s) (hc : denoteN s.store.ns ctor = some ctorP)
    (hrun : Arena.recRuleKOf fe ctor s = .ok (r, s')) :
    s' = s ∧ r = ConLeche.recRuleKOf env.find? ctorP := by
  simp only [Arena.recRuleKOf] at hrun
  cases hf : fe.find? ctor with
  | none =>
    rw [hf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨rfl, ?_⟩
    simp only [ConLeche.recRuleKOf, IFEnvOK.miss hok.state hok.ienv hc hf]
  | some ci =>
  obtain ⟨nm, c, hnm, hci, henv⟩ := hok.ienv.hit ctor ci hf
  obtain rfl : nm = ctorP := Option.some.inj (hnm.symm.trans hc)
  rw [hf] at hrun
  simp only [ConLeche.recRuleKOf, henv]
  cases ci
  all_goals try
    (obtain ⟨rfl, rfl⟩ := pureOk hrun
     refine ⟨rfl, ?_⟩
     have hnc := denoteCI_not_ctor hci (by intro v a b h; cases h)
     split
     · rename_i cvj x cnF heq
       exact absurd (Option.some.inj heq) (hnc _ _ _)
     · rfl)
  rename_i cvj x cnF
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
  obtain ⟨cvjP, hcvj, rfl⟩ := hci
  dsimp only at hrun ⊢
  obtain ⟨pr, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨fn, s2, k2, z2⟩ := bindOk z1
  obtain ⟨v, s3, k3, z3⟩ := bindOk z2
  obtain ⟨rfl, rfl, rfl, hv, hfn⟩ := ctorHead_facts hok.state (denoteCV_type hcvj) k1 k2 k3
  cases v
  all_goals try
    (obtain ⟨rfl, rfl⟩ := pureOk z3
     refine ⟨rfl, ?_⟩
     have hnc := denote_not_const hok.state.wf hv hfn (by intro _ _ h; cases h)
     split
     · rename_i T us heq; exact absurd heq (hnc _ _)
     · rfl)
  rename_i T us
  obtain ⟨TP, usP, hfe, hT, -⟩ := denote_const_inv hok.state.wf hv hfn
  rw [hfe]
  dsimp only at z3 ⊢
  cases hfT : fe.find? T with
  | none =>
    rw [hfT] at z3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨rfl, ?_⟩
    simp only [IFEnvOK.miss hok.state hok.ienv hT hfT]
  | some ciT =>
  obtain ⟨nmT, cT, hnmT, hciT, henvT⟩ := hok.ienv.hit T ciT hfT
  obtain rfl : nmT = TP := Option.some.inj (hnmT.symm.trans hT)
  rw [hfT] at z3
  rw [henvT]
  cases ciT
  all_goals try
    (obtain ⟨rfl, rfl⟩ := pureOk z3
     refine ⟨rfl, ?_⟩
     have hni := denoteCI_not_ind hciT (by intro v a h; cases h)
     split
     · rename_i cvT caps heq; exact absurd (Option.some.inj heq) (hni _ _)
     · rfl)
  rename_i cvT caps
  simp only [Frontend.denoteCI] at hciT
  cases hcvT : Frontend.denoteCV s.store cvT with
  | none => rw [hcvT] at hciT; simp at hciT
  | some cvTP =>
  cases hcaps : Frontend.denoteCaps s.store caps with
  | none => rw [hcvT, hcaps] at hciT; simp at hciT
  | some capsP =>
  rw [hcvT, hcaps] at hciT
  obtain rfl := (Option.some.inj hciT).symm
  simp only [Frontend.denoteCaps] at hcaps
  split at hcaps
  · obtain rfl := (Option.some.inj hcaps).symm
    obtain ⟨rfl, rfl⟩ := pureOk z3
    exact ⟨rfl, rfl⟩
  · simp at hcaps

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:846-858 recRuleEtaOf — the
η-rescue bit at install, in run form.  The recursor's name is read back
(`readNameM`), so the frame is a `ReadbackFrame`. -/
theorem recRuleEtaOf_run {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    {recName ctor : NIdx} {recNameP ctorP : ConLeche.Name} {r : Bool}
    (hok : CheckOK μ env fe s) (hrn : denoteN s.store.ns recName = some recNameP)
    (hc : denoteN s.store.ns ctor = some ctorP)
    (hrun : Arena.recRuleEtaOf fe recName ctor s = .ok (r, s')) :
    Core.ReadbackFrame s s' ∧ r = ConLeche.recRuleEtaOf env.find? recNameP ctorP := by
  simp only [Arena.recRuleEtaOf] at hrun
  cases hf : fe.find? ctor with
  | none =>
    rw [hf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨Core.ReadbackFrame.refl _, ?_⟩
    simp only [ConLeche.recRuleEtaOf, IFEnvOK.miss hok.state hok.ienv hc hf]
  | some ci =>
  obtain ⟨nm, c, hnm, hci, henv⟩ := hok.ienv.hit ctor ci hf
  obtain rfl : nm = ctorP := Option.some.inj (hnm.symm.trans hc)
  rw [hf] at hrun
  simp only [ConLeche.recRuleEtaOf, henv]
  cases ci
  all_goals try
    (obtain ⟨rfl, rfl⟩ := pureOk hrun
     refine ⟨Core.ReadbackFrame.refl _, ?_⟩
     have hnc := denoteCI_not_ctor hci (by intro v a b h; cases h)
     split
     · rename_i cvj x cnF heq
       exact absurd (Option.some.inj heq) (hnc _ _ _)
     · rfl)
  rename_i cvj x cnF
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
  obtain ⟨cvjP, hcvj, rfl⟩ := hci
  dsimp only at hrun ⊢
  obtain ⟨pr, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨fn, s2, k2, z2⟩ := bindOk z1
  obtain ⟨v, s3, k3, z3⟩ := bindOk z2
  obtain ⟨rfl, rfl, rfl, hv, hfn⟩ := ctorHead_facts hok.state (denoteCV_type hcvj) k1 k2 k3
  cases v
  all_goals try
    (obtain ⟨rfl, rfl⟩ := pureOk z3
     refine ⟨Core.ReadbackFrame.refl _, ?_⟩
     have hnc := denote_not_const hok.state.wf hv hfn (by intro _ _ h; cases h)
     split
     · rename_i T us heq; exact absurd heq (hnc _ _)
     · rfl)
  rename_i T us
  obtain ⟨TP, usP, hfe, hT, -⟩ := denote_const_inv hok.state.wf hv hfn
  rw [hfe]
  dsimp only at z3 ⊢
  cases hfT : fe.find? T with
  | none =>
    rw [hfT] at z3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨Core.ReadbackFrame.refl _, ?_⟩
    simp only [IFEnvOK.miss hok.state hok.ienv hT hfT]
  | some ciT =>
  obtain ⟨nmT, cT, hnmT, hciT, henvT⟩ := hok.ienv.hit T ciT hfT
  obtain rfl : nmT = TP := Option.some.inj (hnmT.symm.trans hT)
  rw [hfT] at z3
  rw [henvT]
  cases ciT
  all_goals try
    (obtain ⟨rfl, rfl⟩ := pureOk z3
     refine ⟨Core.ReadbackFrame.refl _, ?_⟩
     have hni := denoteCI_not_ind hciT (by intro v a h; cases h)
     split
     · rename_i cvT caps heq; exact absurd (Option.some.inj heq) (hni _ _)
     · rfl)
  rename_i cvT caps
  simp only [Frontend.denoteCI] at hciT
  cases hcvT : Frontend.denoteCV s.store cvT with
  | none => rw [hcvT] at hciT; simp at hciT
  | some cvTP =>
  cases hcaps : Frontend.denoteCaps s.store caps with
  | none => rw [hcvT, hcaps] at hciT; simp at hciT
  | some capsP =>
  rw [hcvT, hcaps] at hciT
  obtain rfl := (Option.some.inj hciT).symm
  simp only [Frontend.denoteCaps] at hcaps
  split at hcaps
  · rename_i ct hct
    obtain rfl := (Option.some.inj hcaps).symm
    dsimp only
    dsimp only at z3
    obtain ⟨rn, s4, k4, z4⟩ := bindOk z3
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := AM.of_run (P := fun t => t = s) rfl k4
      (readNameM_spec s recName hok.caches.readN)
    obtain ⟨rfl, rfl⟩ := pureOk z4
    obtain rfl : rn = recNameP := Option.some.inj (h5.symm.trans hrn)
    refine ⟨Core.ReadbackFrame.ofReadN h1 h2 h3 h4 h6, ?_⟩
    rw [beq_handle_eq hok.state.wf hct hc,
      beq_nhandleList_eq hok.state.wf (denoteCV_lps hcvj) (denoteCV_lps hcvT)]
  · simp at hcaps

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:860-870 recRuleBits — the two
bits stamped, in run form: the rule denotes con-leche's stamped rule. -/
theorem recRuleBits_run {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    {recName : NIdx} {recNameP : ConLeche.Name} {rl rl' : IRecRule} {rlP : RecRule}
    (hok : CheckOK μ env fe s) (hrn : denoteN s.store.ns recName = some recNameP)
    (hrl : Frontend.denoteRule s.store rl = some rlP)
    (hrun : Arena.recRuleBits fe recName rl s = .ok (rl', s')) :
    Core.ReadbackFrame s s' ∧
      Frontend.denoteRule s'.store rl' = some (ConLeche.recRuleBits env.find? recNameP rlP) := by
  obtain ⟨hctor, -⟩ := denoteRule_ctor hrl
  simp only [Arena.recRuleBits] at hrun
  obtain ⟨k, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hk⟩ := recRuleKOf_run hok hctor k1
  rw [hs1] at z1
  obtain ⟨e, s2, k2, z2⟩ := bindOk z1
  obtain ⟨hfr, he⟩ := recRuleEtaOf_run hok hrn hctor k2
  obtain ⟨rfl, rfl⟩ := pureOk z2
  refine ⟨hfr, ?_⟩
  rw [hfr.store]
  simp only [Frontend.denoteRule] at hrl ⊢
  cases h1 : denoteN s.store.ns rl.ctor with
  | none => rw [h1] at hrl; simp at hrl
  | some c =>
  cases h2 : Frontend.denoteFire s.store rl.fire with
  | none => rw [h1, h2] at hrl; simp at hrl
  | some f =>
  cases h3 : denoteE s.store rl.rhs with
  | none => rw [h1, h2, h3] at hrl; simp at hrl
  | some x =>
  rw [h1, h2, h3] at hrl
  obtain rfl := (Option.some.inj hrl).symm
  simp only [ConLeche.recRuleBits, hk, he]

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:274-290 sumRules
The recursor's rules, one per constructor, with their firing bits.  **Task
#97d-2's deviation 3 again**: con-leche takes `find? : Name → Option
ConstantInfo` and the twin takes the index `fe`, so the statement compares
them at `find? := env.find?` — which is what `IFEnvOK` says the index is.

**CLOSED** (task #97-P3-Ind round 6). -/
theorem sumRules_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (recName : NIdx) (recNameP : ConLeche.Name) (nP mI rP : Nat)
    (recTy : EIdx) (recTyP : Expr) (cs : List (IConstantVal × Nat))
    (csP : List (ConstantVal × Nat)) (rhss : List EIdx) (rhssP : List Expr) :
    CSpec μ env fe
      (fun st => denoteN st.ns recName = some recNameP ∧
        denoteE st recTy = some recTyP ∧ denoteCtors st cs = some csP ∧
        Frontend.denoteEList st rhss = some rhssP ∧
        denoteFEnv st fe = some env)
      (Arena.sumRules fe recName nP mI rP recTy cs rhss)
      (fun st r => Frontend.denoteRules st r
        = some (ConLeche.sumRules env.find? recNameP nP mI rP recTyP csP rhssP)) := by
  induction cs generalizing csP rhss rhssP with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨-, -, hcs, -, -⟩ := hpre
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.sumRules] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨CoreStep.refl hok, ?_⟩
    cases rhssP <;> rfl
  | cons c cs ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hrn, hrt, hcs, hrh, hfe⟩ := hpre
    obtain ⟨cv, n⟩ := c
    simp only [denoteCtors] at hcs
    cases hcv : Frontend.denoteCV s₀.store cv with
    | none => rw [hcv] at hcs; simp at hcs
    | some cP =>
    cases hrest : denoteCtors s₀.store cs with
    | none => rw [hcv, hrest] at hcs; simp at hcs
    | some restP =>
    rw [hcv, hrest] at hcs
    obtain rfl := (Option.some.inj hcs).symm
    cases rhss with
    | nil =>
      simp only [Frontend.denoteEList, Option.some.injEq] at hrh
      subst hrh
      simp only [Arena.sumRules] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, rfl⟩
    | cons rhs rhss =>
    simp only [Frontend.denoteEList] at hrh
    cases hrhs : denoteE s₀.store rhs with
    | none => rw [hrhs] at hrh; simp at hrh
    | some rhsP =>
    cases hrhss : Frontend.denoteEList s₀.store rhss with
    | none => rw [hrhs, hrhss] at hrh; simp at hrh
    | some rhssP' =>
    rw [hrhs, hrhss] at hrh
    obtain rfl := (Option.some.inj hrh).symm
    simp only [Arena.sumRules] at hrun
    obtain ⟨b, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := AM.of_run (P := fun t => t = s₀) rfl k1
      (ExprOps.recRulePlain_spec Arena.coreWalkFuel s₀ recTy mI rP nP hok.state
        (by rw [hrt]; rfl))
    have p1 : PStep s₀ s1 := PStep.of_caches h1 h2 h3 h5 h6
    have hb : b = Expr.recRulePlain recTyP mI rP nP := h7 recTyP hrt
    have c1 := p1.toCore hok
    obtain ⟨rl, s2, k2, z2⟩ := bindOk z1
    have hrl : Frontend.denoteRule s1.store
        { ctor := cv.name, nfields := n, ctorParams := nP,
          fire := (if b then .plain else .inert), rhs := rhs, paramsBlind := true } =
        some { ctor := cP.name, nfields := n, ctorParams := nP,
               fire := (if Expr.recRulePlain recTyP mI rP nP then .plain else .inert),
               rhs := rhsP, paramsBlind := true } := by
      subst hb
      simp only [Frontend.denoteRule, denoteN_ext (denoteCV_name hcv) p1.ext,
        denote_ext hrhs p1.ext]
      cases Expr.recRulePlain recTyP mI rP nP <;> rfl
    obtain ⟨hfr, hrlr⟩ := recRuleBits_run c1.ok (denoteN_ext hrn p1.ext) hrl k2
    have c2 : CoreStep μ env fe s₀ s2 :=
      c1.trans ⟨Core.CheckOK.ofReadbackFrame c1.ok hfr, hfr.ext, hfr.pins⟩
    obtain ⟨rs, s3, k3, z3⟩ := bindOk z2
    obtain ⟨c3, hrs⟩ := ih restP rhss rhssP' s2 s3 rs c2.ok
      ⟨denoteN_ext hrn c2.ext, denote_ext hrt c2.ext, denoteCtors_ext c2.ext _ _ hrest,
        denoteEList_ext c2.ext _ _ hrhss, denoteFEnv_ext c2.ext hfe⟩ k3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨c2.trans c3, ?_⟩
    simp only [Frontend.denoteRules, denoteRule_ext hrlr c3.ext, hrs]
    rfl

end ConRon.Bridge.Inductives
