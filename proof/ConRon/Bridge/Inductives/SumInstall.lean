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
import ConLeche.Verify.FastOps
import ConRon.Bridge.Checker.Base
import ConLeche.Verify.BridgeWfImp

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

/-- con-leche: none — `whnfTelescope` is monotone in the fuel of its
`whnf`: `ConLeche.whnf_mono` at every binder. -/
theorem whnfTelescope_mono {μ : CheckMode} {env : Env} {F F' : Nat}
    (hle : F ≤ F') : ∀ {n i : Nat} {e : Expr} {v : List (Expr × BinderMeta) × Level},
    ConLeche.whnfTelescope (ConLeche.fueledOps μ F) env i n e = .ok v →
    ConLeche.whnfTelescope (ConLeche.fueledOps μ F') env i n e = .ok v := by
  intro n
  induction n with
  | zero =>
    intro i e v h
    simp only [ConLeche.whnfTelescope, ConLeche.fueledOps, bind, Except.bind] at h ⊢
    cases hw : ConLeche.whnf μ env F i e with
    | error x => rw [hw] at h; exact nomatch h
    | ok w => rw [hw] at h; rw [ConLeche.whnf_mono hle hw]; exact h
  | succ n ih =>
    intro i e v h
    simp only [ConLeche.whnfTelescope, ConLeche.fueledOps, bind, Except.bind] at h ⊢
    cases hw : ConLeche.whnf μ env F i e with
    | error x => rw [hw] at h; exact nomatch h
    | ok w =>
    rw [hw] at h; rw [ConLeche.whnf_mono hle hw]
    dsimp only at h ⊢
    cases w
    case forallE dom body bm =>
      dsimp only at h ⊢
      cases hr : ConLeche.whnfTelescope (ConLeche.fueledOps μ F) env (i + 1) n
          (body.instantiate1 (.fvar i dom)) with
      | error x =>
        simp only [ConLeche.fueledOps] at hr; rw [hr] at h; exact nomatch h
      | ok b' =>
        have hr' := ih hr
        simp only [ConLeche.fueledOps] at hr hr'
        rw [hr] at h; rw [hr']; exact h
    all_goals exact h

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:45-68 whnfTelescope
Peel `n` Π binders, reducing at each step, down to the result `Sort`.

**CLOSED** (task #97-P3-Ind round 7): a `Nat` recursion over
`CoreSpec.knot`'s `whnf` slot, `Bridge/Rel.lean`'s `forallE`/`sort`
inversions and `instantiate1Fast_run`, one fuel for the walk by
`whnfTelescope_mono` at `max`.

**Two preconditions it was missing** (round 7, §R6.3's repair): `EnvWF env`
and `Expr.WScoped i eP` — the `whnf` slot's own; the answer's `SimE` scope
and one `WScoped.instantiate1` carry it to the next binder. -/
theorem whnfTelescope_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (i n : Nat) (e : EIdx)
    (eP : Expr) (hws : Expr.WScoped i eP) :
    CSpec μ env fe
      (fun st => denoteE st e = some eP ∧ denoteFEnv st fe = some env)
      (Arena.whnfTelescope μ fe i n e)
      (fun st r => ∃ F bsP sP,
        ConLeche.whnfTelescope (ConLeche.fueledOps μ F) env i n eP
          = .ok (bsP, sP) ∧
        denoteBinders st r.1 = some bsP ∧ denoteL st.ls r.2 = some sP) := by
  have hknot := hk.knot env fe henv
  induction n generalizing i e eP with
  | zero =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨he, hfe⟩ := hpre
    simp only [Arena.whnfTelescope] at hrun
    obtain ⟨w, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨hok1, hx1, hp1, hsim⟩ := AM.of_run (P := fun u => u = s₀)
      (Q := fun r u => CheckOK μ env fe u ∧ Ext s₀.store u.store ∧
        u.pins = s₀.pins ∧ Core.SimE (ConLeche.whnf μ env) i eP u.store r)
      rfl k1 (hknot.whnf s₀ i e eP hok he hws)
    obtain ⟨wP, hwP, -, F1, hF1⟩ := hsim
    obtain ⟨v, s2, k2, z2⟩ := bindOk z1
    obtain ⟨hs2, hv⟩ := view_run k2
    rw [hs2] at z2
    cases v
    case sort u =>
      obtain ⟨uP, rfl, hu⟩ := denote_sort_inv hok1.state.wf hv hwP
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨⟨hok1, hx1, hp1⟩, F1, [], uP, ?_, rfl, hu⟩
      simp only [ConLeche.whnfTelescope, ConLeche.fueledOps, bind, Except.bind, hF1]
      rfl
    all_goals exact absurd z2 (fun h => failOk h)
  | succ n ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨he, hfe⟩ := hpre
    simp only [Arena.whnfTelescope] at hrun
    obtain ⟨w, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨hok1, hx1, hp1, hsim⟩ := AM.of_run (P := fun u => u = s₀)
      (Q := fun r u => CheckOK μ env fe u ∧ Ext s₀.store u.store ∧
        u.pins = s₀.pins ∧ Core.SimE (ConLeche.whnf μ env) i eP u.store r)
      rfl k1 (hknot.whnf s₀ i e eP hok he hws)
    have c1 : CoreStep μ env fe s₀ s1 := ⟨hok1, hx1, hp1⟩
    obtain ⟨wP, hwP, hwsw, F1, hF1⟩ := hsim
    obtain ⟨v, s2, k2, z2⟩ := bindOk z1
    obtain ⟨hs2, hv⟩ := view_run k2
    rw [hs2] at z2
    cases v
    case forallE dom body bm =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok1.state.wf hv hwP
      have hwsdb : Expr.WScoped i domP ∧ Expr.WScoped i bodyP := by
        simp only [Expr.WScoped] at hwsw; exact hwsw
      obtain ⟨hwsd, hwsb⟩ := hwsdb
      dsimp only at z2
      obtain ⟨fv, s3, k3, z3⟩ := bindOk z2
      obtain ⟨p3, hfv⟩ := internE_run hok1.state (viewOK_fvar (by rw [hd]; rfl)) k3
      have hfv' : denoteE s3.store fv = some (.fvar i domP) := by
        rw [hfv]; simp [denoteEView, denote_ext hd p3.ext]
      have c3 := c1.trans (p3.toCore hok1)
      obtain ⟨op, s4, k4, z4⟩ := bindOk z3
      have hb3 : denoteE s3.store body = some bodyP := denote_ext hb p3.ext
      obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ExprOps.instantiate1Fast_run c3.ok.state hfv'
        (by rw [hb3]; rfl) k4
      have p4 : PStep s3 s4 := PStep.of_caches h1 h2 h3 h4 h5
      have hop : denoteE s4.store op = some (bodyP.instantiate1 (.fvar i domP) 0) :=
        h7 _ hb3
      have c4 := c3.trans (p4.toCore c3.ok)
      obtain ⟨br, s5, k5, z5⟩ := bindOk z4
      obtain ⟨c5, F2, bsP, sP, hF2, hbs, hsP⟩ := ih (i + 1) op _
        (Expr.WScoped.instantiate1 hwsd 0 hwsb) s4 s5 br c4.ok
        ⟨hop, denoteFEnv_ext c4.ext hfe⟩ k5
      obtain ⟨rfl, rfl⟩ := pureOk z5
      refine ⟨c4.trans c5, max F1 F2, (domP, bm) :: bsP, sP, ?_, ?_, hsP⟩
      · have hF1' := ConLeche.whnf_mono (Nat.le_max_left F1 F2) hF1
        have hF2' := whnfTelescope_mono (Nat.le_max_right F1 F2) hF2
        simp only [ConLeche.fueledOps] at hF2'
        simp only [ConLeche.whnfTelescope, ConLeche.fueledOps, bind, Except.bind, hF1']
        rw [hF2']
        rfl
      · simp only [denoteBinders, denote_ext hd (p3.ext.trans (p4.ext.trans c5.ext)), hbs]
    all_goals exact absurd z2 (fun h => failOk h)

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
    (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (cv : IConstantVal) (cvP : ConstantVal)
    (n : Nat) (cvTa₀ : IConstantVal) (cvTa₀P : ConstantVal)
    (hws : Expr.WScoped 0 cvTa₀P.type) :
    CSpec μ env fe
      (fun st => Frontend.denoteCV st cv = some cvP ∧
        Frontend.denoteCV st cvTa₀ = some cvTa₀P ∧
        denoteFEnv st fe = some env)
      (Arena.checkSumTele μ fe cv n cvTa₀)
      (fun st r => ∃ F cvAP sP,
        ConLeche.checkSumTele (ConLeche.fueledOps μ F) env cvP n cvTa₀P
          = .ok (cvAP, sP) ∧
        Frontend.denoteCV st r.1 = some cvAP ∧ denoteL st.ls r.2 = some sP) := by
  have slow : ∀ (s₁ s'' : AState) (r : IConstantVal × LIdx), CheckOK μ env fe s₁ →
      Frontend.denoteCV s₁.store cv = some cvP →
      Frontend.denoteCV s₁.store cvTa₀ = some cvTa₀P →
      denoteFEnv s₁.store fe = some env →
      Arena.checkSumTele.checkSumTeleSlow μ fe cv n cvTa₀ s₁ = .ok (r, s'') →
      CoreStep μ env fe s₁ s'' ∧ ∃ F bsP sP cvAP,
        ConLeche.whnfTelescope (ConLeche.fueledOps μ F) env 0 n cvTa₀P.type
          = .ok (bsP, sP) ∧
        ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env
          { cvP with type := ConLeche.closeTelescope bsP 0 (.sort sP) } = .ok cvAP ∧
        Frontend.denoteCV s''.store r.1 = some cvAP ∧ denoteL s''.store.ls r.2 = some sP := by
    intro s₁ s'' r hck hcv hcv0 hfe hrun
    simp only [Arena.checkSumTele.checkSumTeleSlow] at hrun
    obtain ⟨bs, s₂, k2, z2⟩ := bindOk hrun
    obtain ⟨c2, F₁, bsP, sP, hF₁, hbs, hsP⟩ := whnfTelescope_spec fe hk henv 0 n cvTa₀.type
      cvTa₀P.type hws s₁ s₂ bs hck ⟨denoteCV_type hcv0, hfe⟩ k2
    obtain ⟨bsI, sI⟩ := bs
    simp only at hbs hsP z2
    obtain ⟨sortS, s₃, k3, z3⟩ := bindOk z2
    obtain ⟨p3, hsort⟩ := internSortE_run c2.ok.state hsP k3
    obtain ⟨ty, s₄, k4, z4⟩ := bindOk z3
    obtain ⟨p4, hty⟩ := closeTelescope_spec bsI bsP 0 sortS (.sort sP) s₃ s₄ ty p3.ok
      ⟨denoteBinders_ext p3.ext _ _ hbs, hsort⟩ k4
    have c4 := c2.trans ((p3.trans p4).toCore c2.ok)
    have x14 : Ext s₁.store s₄.store := c4.ext
    obtain ⟨cvA, s₅, k5, z5⟩ := bindOk z4
    have hcvT : Frontend.denoteCV s₄.store { cv with type := ty } =
        some { cvP with type := ConLeche.closeTelescope bsP 0 (.sort sP) } := by
      obtain ⟨hn, hl, -⟩ := denoteCV_inv hcv
      simp only [Frontend.denoteCV, denoteN_ext hn x14, denoteNListE_ext x14 _ _ hl, hty]
    obtain ⟨c5, cAP, F₂, hcA, hF₂⟩ := checkConstantVal_bridge hμ hk c4.ok henv hcvT k5
    obtain ⟨rfl, rfl⟩ := pureOk z5
    refine ⟨c4.trans c5, max F₁ F₂, bsP, sP, cAP,
      whnfTelescope_mono (Nat.le_max_left F₁ F₂) hF₁,
      checkConstantVal_mono (Nat.le_max_right F₁ F₂) hF₂, hcA,
      denoteL_ext hsP (p3.ext.trans (p4.ext.trans c5.ext))⟩
  intro s₀ s' r hck hpre hrun
  obtain ⟨hcv, hcv0, hfe⟩ := hpre
  simp only [Arena.checkSumTele] at hrun
  obtain ⟨sq, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hsq⟩ := stripPis_pstep hck.state (denoteCV_type hcv0) k1
  rw [hs1] at z1
  -- the slow arm, on both sides
  have finish : Arena.checkSumTele.checkSumTeleSlow μ fe cv n cvTa₀ s₀ = .ok (r, s') →
      (∀ bsP sP, ¬ cvTa₀P.type.stripPis n = some (bsP, .sort sP)) →
      CoreStep μ env fe s₀ s' ∧ ∃ F cvAP sP,
        ConLeche.checkSumTele (ConLeche.fueledOps μ F) env cvP n cvTa₀P = .ok (cvAP, sP) ∧
        Frontend.denoteCV s'.store r.1 = some cvAP ∧ denoteL s'.store.ls r.2 = some sP := by
    intro hz hns
    obtain ⟨c, F, bsP, sP, cvAP, hF₁, hF₂, hcA, hsP⟩ := slow s₀ s' r hck hcv hcv0 hfe hz
    refine ⟨c, F, cvAP, sP, ?_, hcA, hsP⟩
    have tail : (do
        let (bs, s) ← ConLeche.whnfTelescope (ConLeche.fueledOps μ F) env 0 n cvTa₀P.type
        let cvTa ← ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env
          { cvP with type := ConLeche.closeTelescope bs 0 (.sort s) }
        pure (cvTa, s) : CheckM (ConstantVal × Level)) = .ok (cvAP, sP) := by
      simp only [bind, Except.bind, hF₁, hF₂, pure, Except.pure]
    unfold ConLeche.checkSumTele
    rcases hsp : cvTa₀P.type.stripPis n with _ | ⟨bs, b⟩
    · exact tail
    · cases b
      case sort u => exact absurd hsp (hns bs u)
      all_goals exact tail
  cases sq with
  | none =>
    exact finish z1 (fun bsP sP h => by rw [stripPis_none hsq] at h; exact nomatch h)
  | some q =>
  obtain ⟨bs, body⟩ := q
  obtain ⟨xs, x, hxs, hbody⟩ := stripPis_some hsq
  dsimp only at z1
  obtain ⟨v, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨hs2, hv⟩ := view_run k2
  rw [hs2] at z2
  cases v
  case sort u =>
    obtain ⟨uP, rfl, hu⟩ := denote_sort_inv hck.state.wf hv hbody
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨CoreStep.refl hck, 0, cvTa₀P, uP, ?_, hcv0, hu⟩
    simp only [ConLeche.checkSumTele, hxs, pure, Except.pure]
  all_goals
    (refine finish z2 (fun bsP sP h => ?_)
     rw [hxs] at h
     obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
     rw [denoteE_view_eq hck.state.wf hv] at hbody
     simp [denoteEView] at hbody)

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
    (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (hcoh : IFEnvCoh fe)
    (p : Arena.InductiveShape)
    (q : ConLeche.InductiveShape) (isRec : Bool) :
    CSpec μ env fe
      (fun st => ShapeRel st p q ∧ denoteFEnv st fe = some env)
      (Arena.checkSumInd μ fe p isRec)
      (fun st r => ∃ F envP cvTaP qP,
        ConLeche.checkSumInd (ConLeche.fueledOps μ F) env q
            (fun x => ConLeche.nativeCapsAt x isRec) = .ok (envP, cvTaP, qP) ∧
        InstRel fe (fun e => e = envP) st r.1 ∧
        Frontend.denoteCV st r.2.1 = some cvTaP ∧ ShapeRel st r.2.2 qP) := by
  intro s₀ s' r hck hpre hrun
  obtain ⟨hsh, hfe⟩ := hpre
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  simp only [Arena.checkSumInd] at hrun
  -- the former's own check
  obtain ⟨cvTa₀, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨c1, cA₀, F₁, hcA₀, hF₁⟩ := checkConstantVal_bridge hμ hk hck henv hsh.cvT k1
  have hws : Expr.WScoped 0 cA₀.type :=
    Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  -- the telescope
  obtain ⟨t2, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨c2, F₂, cvTaP, sP, hF₂, hcvTa, hsP⟩ := checkSumTele_spec fe hμ hk henv p.cvT q.cvT
    (p.nP + p.nIdx) cvTa₀ cA₀ hws s₁ s₂ t2 c1.ok
    ⟨denoteCV_ext hsh.cvT c1.ext, hcA₀, denoteFEnv_ext c1.ext hfe⟩ k2
  obtain ⟨cvTa, so⟩ := t2
  simp only at hcvTa hsP z2
  have c12 := c1.trans c2
  -- the result sort
  obtain ⟨o, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨hs3, ho⟩ := stripPis_pstep c12.ok.state (denoteCV_type hcvTa) k3
  rw [hs3] at z3
  obtain ⟨bt, s₄, k4, z4⟩ := bindOk z3
  cases o with
  | none => simp only [Arena.unwrapOr] at k4; exact absurd k4 (fun h => failOk h)
  | some o' =>
  simp only [Arena.unwrapOr] at k4
  obtain ⟨rfl, rfl⟩ := pureOk k4
  obtain ⟨bs, tbody⟩ := bt
  obtain ⟨xs, tbodyP, htq, htb⟩ := stripPis_some ho
  dsimp only at z4
  obtain ⟨sortS, s₅, k5, z5⟩ := bindOk z4
  obtain ⟨p5, hsort⟩ := internSortE_run c12.ok.state hsP k5
  have c15 := c12.trans (p5.toCore c12.ok)
  have hbeq := beq_ehandle_eq c15.ok.state.wf (denote_ext htb p5.ext) hsort
  obtain ⟨hg, z6⟩ := AM.dunless_ok hnever z5
  replace z6 := AM.pure_bind_ok z6
  rw [hbeq] at hg
  -- the completed record and the capability record
  obtain ⟨p', s₆, k6, z7⟩ := bindOk z6
  have x15 : Ext s₀.store s₅.store := c15.ext
  obtain ⟨c6, hp'⟩ := withSort_spec fe p q so sP s₅ s₆ p' c15.ok
    ⟨hsh.ext x15, denoteL_ext hsP p5.ext⟩ k6
  have c16 := c15.trans c6
  obtain ⟨caps, s₇, k7, z8⟩ := bindOk z7
  obtain ⟨p7, hcaps⟩ := nativeCapsAt_spec p' (q.withSort sP) isRec s₆ s₇ caps c16.ok.state
    c16.ok.pins hp' k7
  obtain ⟨rfl, rfl⟩ := pureOk z8
  have c17 := c16.trans (p7.toCore c16.ok)
  have x7 : Ext s₄.store s'.store := p5.ext.trans (c6.ext.trans p7.ext)
  have hci : Frontend.denoteCI s'.store (.indInfo cvTa caps) =
      some (.indInfo cvTaP (ConLeche.nativeCapsAt (q.withSort sP) isRec)) := by
    simp only [Frontend.denoteCI, denoteCV_ext hcvTa x7, hcaps]
  refine ⟨c17, max F₁ F₂, _, cvTaP, q.withSort sP, ?_,
    ⟨hcoh.push _, Pushed.push _ _, Nat.le_succ _,
      ⟨_, denoteFEnv_push (denoteFEnv_ext c17.ext hfe) hci, rfl⟩,
      ProjOut.push hcoh _ (fun t h => IConstantInfo.noConfusion h)⟩,
    denoteCV_ext hcvTa x7, hp'.ext p7.ext⟩
  have g₁ := checkConstantVal_mono (Nat.le_max_left F₁ F₂) hF₁
  have g₂ : ConLeche.checkSumTele (ConLeche.fueledOps μ (max F₁ F₂)) env q.cvT
      (p.nP + p.nIdx) cA₀ = .ok (cvTaP, sP) := by
    rw [← ConLeche.checkSumTele_datF] at hF₂ ⊢
    exact (ConLeche.checkSumTele (ConLeche.fueledOpsM μ) env q.cvT (p.nP + p.nIdx)
      cA₀).property (Nat.le_max_right F₁ F₂) hF₂
  rw [hsh.nP, hsh.nIdx] at g₂ htq
  simp only [ConLeche.checkSumInd, bind, Except.bind, g₁, g₂, htq, ConLeche.unwrapOr,
    pure, Except.pure]
  rw [if_pos hg]

/-! ## The fields' universe bound -/

/-- con-leche: none — a level-handle list denotes across an append. -/
theorem denoteLList_append' {st : LStore} :
    ∀ {a : List LIdx} {as : List Level} {b : List LIdx} {bs : List Level},
      denoteLList st a = some as → denoteLList st b = some bs →
      denoteLList st (a ++ b) = some (as ++ bs) := by
  intro a
  induction a with
  | nil =>
    intro as b bs ha hb
    simp only [denoteLList, Option.some.injEq] at ha
    subst ha; simpa using hb
  | cons x xs ih =>
    intro as b bs ha hb
    simp only [denoteLList] at ha
    cases hx : denoteL st x with
    | none => rw [hx] at ha; simp [opt2] at ha
    | some y =>
      cases hxs : denoteLList st xs with
      | none => rw [hx, hxs] at ha; simp [opt2] at ha
      | some ys =>
        rw [hx, hxs] at ha
        simp only [opt2, Option.some.injEq] at ha
        subst ha
        simp only [List.cons_append, denoteLList, hx, ih hxs hb, opt2]

/-- con-leche: none — **an expression-handle list's `contains` is the
denotation's**, at both signs: `beq_ehandle_eq` at every element (the store is
hash-consed, so a handle equality IS a term equality). -/
theorem denoteEList_contains {st : EStore} (hwf : StoreWF st) :
    ∀ {xs : List EIdx} {xsP : List Expr}, Frontend.denoteEList st xs = some xsP →
      ∀ {h : EIdx} {hP : Expr}, denoteE st h = some hP →
        xs.contains h = xsP.contains hP := by
  intro xs
  induction xs with
  | nil =>
    intro xsP hxs h hP _
    simp only [Frontend.denoteEList, Option.some.injEq] at hxs
    subst hxs; rfl
  | cons x xs ih =>
    intro xsP hxs h hP hh
    simp only [Frontend.denoteEList] at hxs
    cases hx : denoteE st x with
    | none => rw [hx] at hxs; simp at hxs
    | some y =>
      cases hr : Frontend.denoteEList st xs with
      | none => rw [hx, hr] at hxs; simp at hxs
      | some ys =>
        rw [hx, hr] at hxs
        obtain rfl := (Option.some.inj hxs).symm
        simp only [List.contains_cons, beq_ehandle_eq hwf hh hx, ih hr hh]

/-- con-leche: none — `checkStructFieldSortsI` is monotone in the fuel of its
`inferType`/`ensureSort`. -/
theorem checkStructFieldSortsI_mono {μ : CheckMode} {env : Env} {F F' : Nat}
    (hle : F ≤ F') {isProp large : Bool} {sP : Level} {nP : Nat}
    {fvsP idxArgsP : List Expr} : ∀ {j : Nat} {ls : List Level},
    ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env isProp large sP nP
      fvsP idxArgsP j = .ok ls →
    ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F') env isProp large sP nP
      fvsP idxArgsP j = .ok ls := by
  intro j
  induction j with
  | zero => intro ls h; exact h
  | succ j ih =>
    intro ls h
    simp only [ConLeche.checkStructFieldSortsI, ConLeche.fueledOps, bind, Except.bind]
      at h ⊢
    cases ha : fvsP[j]? with
    | none =>
      simp [ha, ConLeche.unwrapOr, throw, throwThe, MonadExceptOf.throw] at h
    | some a =>
    simp only [ha, ConLeche.unwrapOr, pure, Except.pure] at h ⊢
    cases hi : ConLeche.inferTypeCore μ env F (nP + j) a.fvarTypeD with
    | error x => rw [hi] at h; exact nomatch h
    | ok t =>
    rw [hi] at h; rw [ConLeche.inferTypeCore_mono hle hi]
    dsimp only at h ⊢
    cases he : ConLeche.ensureSortCore μ env F (nP + j) t with
    | error x => rw [he] at h; exact nomatch h
    | ok u =>
    rw [he] at h; rw [ConLeche.ensureSortCore_mono hle he]
    dsimp only at h ⊢
    cases hr : ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env isProp
        large sP nP fvsP idxArgsP j with
    | error x =>
      simp only [ConLeche.fueledOps, pure, Except.pure] at hr
      rw [hr] at h
      exfalso
      revert h
      repeat' split
      all_goals simp_all [throw, throwThe, MonadExceptOf.throw]
    | ok rest =>
      have hr' := ih hr
      simp only [ConLeche.fueledOps, pure, Except.pure] at hr hr'
      rw [hr] at h; rw [hr']; exact h

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:114-139 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:45-61 checkStructFieldSortsIF
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:63-81 checkStructFieldSortsIFA
Each field's sort, checked against the family's — official's
subsingleton-elimination criterion at a one-constructor block.

**CLOSED** (task #97-P3-Ind round 7): a `Nat` recursion over `CoreSpec.knot`'s
`infer` slot, `CoreSpec.sort`'s `EnsureSortSpec`, `fvarTypeD_run`, the
universe comparison (`readLevel` twice and `liftFueled`), `lvlEq?_spec` at the
zero pin, and `denoteEList_contains` for the index test — one fuel for the
walk by `checkStructFieldSortsI_mono` at `max`.

**Two preconditions it was missing** (round 7, §R6.3's repair): `EnvWF env`
and, for each field it infers, the scope of that field's type at its depth —
`Expr.WScoped (nP + i) fvsP[i].fvarTypeD`, exactly `checkStructDomsAt_spec`'s
hypothesis on its left column. -/
theorem checkStructFieldSortsI_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (isProp large : Bool)
    (s : LIdx) (sP : Level) (nP : Nat) (fvs idxArgs : List EIdx)
    (fvsP idxArgsP : List Expr) (j : Nat)
    (hws : ∀ i, i < j → ∀ a, fvsP[i]? = some a → Expr.WScoped (nP + i) a.fvarTypeD) :
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
  have hknot := hk.knot env fe henv
  have hsort := hk.sort env fe henv
  induction j with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.checkStructFieldSortsI] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, 0, [], rfl, rfl⟩
  | succ j ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hs, hfvs, hidx, hfe⟩ := hpre
    simp only [Arena.checkStructFieldSortsI] at hrun
    obtain ⟨fv, s1, k1, z1⟩ := bindOk hrun
    cases hfv : fvs[j]? with
    | none =>
      rw [hfv] at k1; simp only [Arena.unwrapOr] at k1; exact absurd k1 (fun h => failOk h)
    | some fv' =>
    rw [hfv] at k1; simp only [Arena.unwrapOr] at k1
    obtain ⟨rfl, hs1⟩ := pureOk k1
    rw [hs1] at z1
    obtain ⟨aP, haP, hda⟩ := ExprOps.denoteEList_getElem? fvs fvsP hfvs j fv hfv
    obtain ⟨t, s2, k2, z2⟩ := bindOk z1
    obtain ⟨hs2, ht⟩ := fvarTypeD_run hok.state hda k2
    rw [hs2] at z2
    have hwsa := hws j (Nat.lt_succ_self j) aP haP
    obtain ⟨ty, s3, k3, z3⟩ := bindOk z2
    obtain ⟨hok3, hx3, hp3, hsim3⟩ := AM.of_run (P := fun u => u = s₀)
      (Q := fun r u => CheckOK μ env fe u ∧ Ext s₀.store u.store ∧
        u.pins = s₀.pins ∧
        Core.SimE (ConLeche.inferTypeCore μ env) (nP + j) aP.fvarTypeD u.store r)
      rfl k3 (hknot.infer s₀ (nP + j) t aP.fvarTypeD hok ht hwsa)
    have c3 : CoreStep μ env fe s₀ s3 := ⟨hok3, hx3, hp3⟩
    obtain ⟨tyP, htyP, hwsty, F1, hF1⟩ := hsim3
    obtain ⟨u, s4, k4, z4⟩ := bindOk z3
    obtain ⟨hok4, hx4, hp4, hsim4⟩ := AM.of_run (P := fun u => u = s3)
      (Q := fun r u => CheckOK μ env fe u ∧ Ext s3.store u.store ∧
        u.pins = s3.pins ∧
        SimL (ConLeche.ensureSortCore μ env) (nP + j) tyP u.store r)
      rfl k4 (hsort s3 (nP + j) ty tyP hok3 htyP hwsty)
    have c4 : CoreStep μ env fe s₀ s4 := c3.trans ⟨hok4, hx4, hp4⟩
    obtain ⟨uP, huP, F2, hF2⟩ := hsim4
    -- the common tail: the recursive call and the snoc
    have tail : ∀ (s5 : AState), CoreStep μ env fe s4 s5 →
        (do let rest ← Arena.checkStructFieldSortsI μ fe isProp large s nP fvs idxArgs j
            pure (rest ++ [u]) : AM (List LIdx)) s5 = .ok (r, s') →
        CoreStep μ env fe s₀ s' ∧ ∃ F3 restP,
          ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F3) env isProp
            large sP nP fvsP idxArgsP j = .ok restP ∧
          denoteLList s'.store.ls r = some (restP ++ [uP]) := by
      intro s5 c5 z5
      have c05 := c4.trans c5
      obtain ⟨rest, s6, k6, z6⟩ := bindOk z5
      obtain ⟨c6, F3, restP, hF3, hrest⟩ := ih (fun i hi => hws i (Nat.lt_succ_of_lt hi))
        s5 s6 rest c05.ok ⟨denoteL_ext hs c05.ext, denoteEList_ext c05.ext _ _ hfvs,
          denoteEList_ext c05.ext _ _ hidx, denoteFEnv_ext c05.ext hfe⟩ k6
      obtain ⟨rfl, rfl⟩ := pureOk z6
      refine ⟨c05.trans c6, F3, restP, hF3, ?_⟩
      exact denoteLList_append' hrest (by
        simp only [denoteLList, denoteL_ext huP (c5.ext.trans c6.ext), opt2])
    have hF1' : ∀ F, F1 ≤ F →
        ConLeche.inferTypeCore μ env F (nP + j) aP.fvarTypeD = .ok tyP :=
      fun F hle => ConLeche.inferTypeCore_mono hle hF1
    have hF2' : ∀ F, F2 ≤ F → ConLeche.ensureSortCore μ env F (nP + j) tyP = .ok uP :=
      fun F hle => ConLeche.ensureSortCore_mono hle hF2
    cases isProp with
    | false =>
      simp only [Bool.not_false, if_true] at z4
      obtain ⟨lu, s5, k5, z5⟩ := bindOk z4
      obtain ⟨hs5, hlu⟩ := readLevel_run k5
      rw [hs5] at z5
      obtain ⟨ls, s6, k6, z6⟩ := bindOk z5
      obtain ⟨hs6, hls⟩ := readLevel_run k6
      rw [hs6] at z6
      obtain ⟨b, s7, k7, z7⟩ := bindOk z6
      have hlu' : lu = uP := Option.some.inj (hlu.symm.trans huP)
      have hls' : ls = sP := Option.some.inj (hls.symm.trans (denoteL_ext hs c4.ext))
      subst hlu' hls'
      cases hleq : Level.leq lu ls with
      | none =>
        rw [hleq] at k7; simp only [Arena.liftFueled] at k7
        exact absurd k7 (fun h => failOk h)
      | some bb =>
      rw [hleq] at k7; simp only [Arena.liftFueled] at k7
      cases bb with
      | false =>
        obtain ⟨rfl, rfl⟩ := pureOk k7
        simp only [Bool.false_eq_true, if_false] at z7
        obtain ⟨_, _, k, _⟩ := bindOk z7
        exact absurd k (fun h => failOk h)
      | true =>
      obtain ⟨rfl, rfl⟩ := pureOk k7
      simp only [if_true] at z7
      obtain ⟨_, s8, k8, z8⟩ := bindOk z7
      obtain ⟨-, rfl⟩ := pureOk k8
      obtain ⟨c, F3, restP, hF3, hr⟩ := tail _ (CoreStep.refl hok4) z8
      refine ⟨c, max (max F1 F2) F3, restP ++ [lu], ?_, hr⟩
      have e1 := hF1' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      have e2 := hF2' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      have e3 := checkStructFieldSortsI_mono (Nat.le_max_right (max F1 F2) F3) hF3
      simp only [ConLeche.fueledOps, pure, Except.pure] at e3
      generalize max (max F1 F2) F3 = Fm at e1 e2 e3 ⊢
      simp only [ConLeche.checkStructFieldSortsI, haP, ConLeche.unwrapOr, ConLeche.fueledOps,
        bind, Except.bind, pure, Except.pure, e1, e2]
      simp [ConLeche.liftFueled, hleq, e3, pure, Except.pure]
    | true =>
    cases large with
    | false =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at z4
      obtain ⟨_, s5, k5, z5⟩ := bindOk z4
      obtain ⟨-, rfl⟩ := pureOk k5
      obtain ⟨c, F3, restP, hF3, hr⟩ := tail _ (CoreStep.refl hok4) z5
      refine ⟨c, max (max F1 F2) F3, restP ++ [uP], ?_, hr⟩
      have e1 := hF1' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      have e2 := hF2' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      have e3 := checkStructFieldSortsI_mono (Nat.le_max_right (max F1 F2) F3) hF3
      simp only [ConLeche.fueledOps, pure, Except.pure] at e3
      generalize max (max F1 F2) F3 = Fm at e1 e2 e3 ⊢
      simp only [ConLeche.checkStructFieldSortsI, haP, ConLeche.unwrapOr, ConLeche.fueledOps,
        bind, Except.bind, pure, Except.pure, e1, e2]
      simp [e3]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true] at z4
      obtain ⟨z, s5, k5, z5⟩ := bindOk z4
      obtain ⟨hs5, hz⟩ := zeroLevel_run hok4.pins k5
      rw [hs5] at z5
      obtain ⟨vv, s6, k6, z6⟩ := bindOk z5
      obtain ⟨hok6, hst6, hp6, lu, lz, hlu, hlz, hvv⟩ :=
        AM.of_run (P := fun t => t = s4) rfl k6 (Core.lvlEq?_spec s4 u z hok4)
      have hlu' : lu = uP := Option.some.inj (hlu.symm.trans huP)
      have hlz' : lz = .zero := Option.some.inj (hlz.symm.trans hz)
      subst hlu' hlz'
      have c6 : CoreStep μ env fe s4 s6 := ⟨hok6, by rw [hst6]; exact Ext.refl _, hp6⟩
      have hcont : idxArgs.contains fv = idxArgsP.contains aP :=
        denoteEList_contains hok4.state.wf (denoteEList_ext c4.ext _ _ hidx)
          (denote_ext hda c4.ext)
      rw [hvv, hcont] at z6
      split at z6
      case isFalse hn =>
        obtain ⟨_, _, k, _⟩ := bindOk z6; exact absurd k (fun h => failOk h)
      case isTrue hy =>
      obtain ⟨_, s8, k8, z8⟩ := bindOk z6
      obtain ⟨-, rfl⟩ := pureOk k8
      obtain ⟨c, F3, restP, hF3, hr⟩ := tail _ c6 z8
      refine ⟨c, max (max F1 F2) F3, restP ++ [lu], ?_, hr⟩
      have e1 := hF1' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      have e2 := hF2' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      have e3 := checkStructFieldSortsI_mono (Nat.le_max_right (max F1 F2) F3) hF3
      simp only [ConLeche.fueledOps, pure, Except.pure] at e3
      generalize max (max F1 F2) F3 = Fm at e1 e2 e3 ⊢
      simp only [ConLeche.checkStructFieldSortsI, haP, ConLeche.unwrapOr, ConLeche.fueledOps,
        bind, Except.bind, pure, Except.pure, e1, e2]
      simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hy
      simp [e3]
      intro hn
      exact hy.resolve_left hn

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

/-- con-leche: none — `normFieldDoms` is monotone in the fuel of its
`whnf`: `normPosDom_mono` at every field. -/
theorem normFieldDoms_mono {μ : CheckMode} {env : Env} {TP : ConLeche.Name}
    {F F' : Nat} (hle : F ≤ F') : ∀ {n i : Nat} {e : Expr}
    {v : List (Expr × BinderMeta) × Expr},
    ConLeche.normFieldDoms (ConLeche.fueledOps μ F) env TP i n e = .ok v →
    ConLeche.normFieldDoms (ConLeche.fueledOps μ F') env TP i n e = .ok v := by
  intro n
  induction n with
  | zero => intro i e v h; simpa [ConLeche.normFieldDoms] using h
  | succ n ih =>
    intro i e v h
    cases e
    case forallE dom body bm =>
      simp only [ConLeche.normFieldDoms, bind, Except.bind] at h ⊢
      cases hd : ConLeche.normPosDom (ConLeche.fueledOps μ F) env TP i 1024 dom with
      | error x => rw [hd] at h; exact nomatch h
      | ok d' =>
      rw [hd] at h
      rw [normPosDom_mono hle hd]
      dsimp only at h ⊢
      cases hr : ConLeche.normFieldDoms (ConLeche.fueledOps μ F) env TP (i + 1) n
          (body.instantiate1 (.fvar i dom)) with
      | error x => rw [hr] at h; exact nomatch h
      | ok b' =>
        rw [hr] at h
        rw [ih hr]
        exact h
    all_goals simp [ConLeche.normFieldDoms, throw, throwThe, MonadExceptOf.throw] at h

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:177-188 normFieldDoms
The constructor's field domains, each normalised, opened at free variables.

**CLOSED** (task #97-P3-Ind round 7): a `Nat` recursion over
`normPosDom_spec` and `Bridge/ExprOps/Inst1.lean`'s `instantiate1Fast_run`,
one fuel for the whole walk by `normFieldDoms_mono` at `max`.

**Two preconditions it was missing** (round 7, §R6.3's repair): `EnvWF env`
and the telescope's scope at its opening depth, `Expr.WScoped i hP` — each
field domain is normalised at the depth it is opened at, which is where
`normPosDom_spec` now asks for it, and one `WScoped.instantiate1` carries it
under the binder. -/
theorem normFieldDoms_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T : NIdx)
    (TP : ConLeche.Name) (i n : Nat) (h : EIdx) (hP : Expr)
    (hws : Expr.WScoped i hP) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧ denoteE st h = some hP ∧
        denoteFEnv st fe = some env)
      (Arena.normFieldDoms μ fe T i n h)
      (fun st r => ∃ F bsP rP,
        ConLeche.normFieldDoms (ConLeche.fueledOps μ F) env TP i n hP
          = .ok (bsP, rP) ∧
        denoteBinders st r.1 = some bsP ∧ denoteE st r.2 = some rP) := by
  induction n generalizing i h hP with
  | zero =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨-, hh, -⟩ := hpre
    simp only [Arena.normFieldDoms] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, 0, [], hP, by simp [ConLeche.normFieldDoms, pure,
      Except.pure], rfl, hh⟩
  | succ n ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hT, hh, hfe⟩ := hpre
    simp only [Arena.normFieldDoms] at hrun
    obtain ⟨v, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body bm =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.state.wf hv hh
      have hwsdb : Expr.WScoped i domP ∧ Expr.WScoped i bodyP := by
        simp only [Expr.WScoped] at hws; exact hws
      obtain ⟨hwsd, hwsb⟩ := hwsdb
      dsimp only at z1
      obtain ⟨d', s2, k2, z2⟩ := bindOk z1
      obtain ⟨c2, F1, dP', hF1, hd'⟩ := normPosDom_spec fe hk henv T TP i 1024 dom domP
        hwsd s₀ s2 d' hok ⟨hT, hd, hfe⟩ k2
      obtain ⟨fv, s3, k3, z3⟩ := bindOk z2
      have hd2 : denoteE s2.store dom = some domP := denote_ext hd c2.ext
      obtain ⟨p3, hfv⟩ := internE_run c2.ok.state (viewOK_fvar (by rw [hd2]; rfl)) k3
      have hfv' : denoteE s3.store fv = some (.fvar i domP) := by
        rw [hfv]; simp [denoteEView, denote_ext hd2 p3.ext]
      have c3 := c2.trans (p3.toCore c2.ok)
      obtain ⟨op, s4, k4, z4⟩ := bindOk z3
      have hb3 : denoteE s3.store body = some bodyP := denote_ext hb c3.ext
      obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ExprOps.instantiate1Fast_run c3.ok.state hfv'
        (by rw [hb3]; rfl) k4
      have p4 : PStep s3 s4 := PStep.of_caches h1 h2 h3 h4 h5
      have hop : denoteE s4.store op = some (bodyP.instantiate1 (.fvar i domP) 0) :=
        h7 _ hb3
      have c4 := c3.trans (p4.toCore c3.ok)
      obtain ⟨br, s5, k5, z5⟩ := bindOk z4
      obtain ⟨c5, F2, bsP, rP, hF2, hbs, hr⟩ := ih (i + 1) op _
        (Expr.WScoped.instantiate1 hwsd 0 hwsb) s4 s5 br c4.ok
        ⟨denoteN_ext hT c4.ext, hop, denoteFEnv_ext c4.ext hfe⟩ k5
      obtain ⟨rfl, rfl⟩ := pureOk z5
      refine ⟨c4.trans c5, max F1 F2, (dP', bm) :: bsP, rP, ?_, ?_, hr⟩
      · have hF1' := normPosDom_mono (Nat.le_max_left F1 F2) hF1
        have hF2' := normFieldDoms_mono (Nat.le_max_right F1 F2) hF2
        simp only [ConLeche.normFieldDoms, bind, Except.bind, hF1']
        rw [hF2']
        rfl
      · simp only [denoteBinders, denote_ext hd' (p3.ext.trans (p4.ext.trans c5.ext)), hbs]
    all_goals exact absurd z1 (fun h => failOk h)

/-! ## The telescope opener (task #97-P3-Ind round 7, on loan)

`Arena/CheckerBase.lean`'s `openPisAtFvars` / `openPisAtFvarsFGo` /
`openPisAtFvarsF` had no Theorem 1 anywhere in the Bridge; `normCtorVal`,
`checkSumCtor` and the native install's field walks are their first
consumers.  **Owner: the Checker tier** (`Bridge/Checker/**`, beside the
other `CheckerBase` twins; `Arena/CheckerBase.lean:570`'s own caller will want
it).  The one-pass form is related to con-leche's one-pass form walk for walk
(the arena's push-order vector is `ExprOps.InstLVec` of con-leche's cons-order
list), and con-leche's own `openPisAtFvarsF_eq` turns the answer into the
binder-at-a-time `openPisAtFvars` that con-leche's callers read. -/

/-- con-leche: none — the denotation of an opener's answer: `none` is
`none`, a `some` denotes when its free variables and its residual do. -/
def denoteOpen (st : EStore) :
    Option (List EIdx × EIdx) → Option (Option (List Expr × Expr))
  | none => some none
  | some (fvs, e) =>
    (Frontend.denoteEList st fvs).bind fun xs => (denoteE st e).map fun x => some (xs, x)

/-- con-leche: none — `denoteOpen` at a `some`, from its two halves. -/
theorem denoteOpen_some {st : EStore} {fvs : List EIdx} {e : EIdx}
    {xs : List Expr} {x : Expr} (h1 : Frontend.denoteEList st fvs = some xs)
    (h2 : denoteE st e = some x) : denoteOpen st (some (fvs, e)) = some (some (xs, x)) := by
  simp [denoteOpen, h1, h2]

/-- con-leche: none — and read back into its two halves. -/
theorem denoteOpen_some_inv {st : EStore} {fvs : List EIdx} {e : EIdx}
    {o : Option (List Expr × Expr)} (h : denoteOpen st (some (fvs, e)) = some o) :
    ∃ xs x, o = some (xs, x) ∧ Frontend.denoteEList st fvs = some xs ∧
      denoteE st e = some x := by
  simp only [denoteOpen, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨xs, h1, x, h2, rfl⟩ := h
  exact ⟨xs, x, rfl, h1, h2⟩

/-- con-leche: none — `denoteOpen` survives an arena extension. -/
theorem denoteOpen_ext {st st' : EStore} (hx : Ext st st')
    {r : Option (List EIdx × EIdx)} {o : Option (List Expr × Expr)}
    (h : denoteOpen st r = some o) : denoteOpen st' r = some o := by
  cases r with
  | none => exact h
  | some p =>
    obtain ⟨fvs, e⟩ := p
    obtain ⟨xs, x, rfl, h1, h2⟩ := denoteOpen_some_inv h
    exact denoteOpen_some (denoteEList_ext hx _ _ h1) (denote_ext h2 hx)

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:130-140 openPisAtFvars — **the
binder-at-a-time opener, as a run**: pure grade, and the answer denotes
con-leche's. -/
theorem openPisAtFvars_run : ∀ (n : Nat) {i : Nat} {h : EIdx} {hP : Expr}
    {s₀ s' : AState} {r : Option (List EIdx × EIdx)},
    StateOK s₀ → denoteE s₀.store h = some hP →
    Arena.openPisAtFvars n h i s₀ = .ok (r, s') →
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvars n hP i) := by
  intro n
  induction n with
  | zero =>
    intro i h hP s₀ s' r hok hh hrun
    simp only [Arena.openPisAtFvars] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, by simp [denoteOpen, Frontend.denoteEList, hh,
      ConLeche.openPisAtFvars]⟩
  | succ n ih =>
    intro i h hP s₀ s' r hok hh hrun
    simp only [Arena.openPisAtFvars] at hrun
    obtain ⟨v, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body bm =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      dsimp only at z1
      obtain ⟨fv, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, hfv⟩ := internE_run hok (viewOK_fvar (by rw [hd]; rfl)) k2
      have hfv' : denoteE s2.store fv = some (.fvar i domP) := by
        rw [hfv]; simp [denoteEView, denote_ext hd p2.ext]
      obtain ⟨op, s3, k3, z3⟩ := bindOk z2
      have hb2 : denoteE s2.store body = some bodyP := denote_ext hb p2.ext
      obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ExprOps.instantiate1Fast_run p2.ok hfv'
        (by rw [hb2]; rfl) k3
      have p3 : PStep s2 s3 := PStep.of_caches h1 h2 h3 h4 h5
      have hop : denoteE s3.store op = some (bodyP.instantiate1 (.fvar i domP) 0) :=
        h7 _ hb2
      obtain ⟨o, s4, k4, z4⟩ := bindOk z3
      obtain ⟨p4, ho⟩ := ih p3.ok hop k4
      have p24 := p2.trans (p3.trans p4)
      simp only [ConLeche.openPisAtFvars]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p24, ?_⟩
        have hn : ConLeche.openPisAtFvars n (bodyP.instantiate1 (.fvar i domP)) (i + 1)
            = none := (Option.some.inj ho).symm
        simp [denoteOpen, hn]
      | some q =>
        obtain ⟨fvs, e⟩ := q
        obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p24, ?_⟩
        rw [hx]
        exact denoteOpen_some (by
          simp only [Frontend.denoteEList, denote_ext hfv' (p3.ext.trans p4.ext),
            h1]) h2
    all_goals
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b m => simp [denoteEView] at hh
      all_goals rfl

/-- con-leche: none — `InstLVec` grows by a push at the front of the list. -/
theorem InstLVec_push {st : EStore} {acc : Array EIdx} {ws : List Expr} {x : EIdx}
    {xP : Expr} (h : ExprOps.InstLVec st acc ws) (hx : denoteE st x = some xP) :
    ExprOps.InstLVec st (acc.push x) (xP :: ws) := by
  simp only [ExprOps.InstLVec, Array.toList_push, List.reverse_cons]
  exact denoteEList_append h (by simp [Frontend.denoteEList, hx])

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:153-167 openPisAtFvarsFGo — **the
one-pass opener's core, as a run**: the arena's push-order vector is
`InstLVec` of con-leche's cons-order list. -/
theorem openPisAtFvarsFGo_run : ∀ (n : Nat) {acc : Array EIdx} {ws : List Expr}
    {i : Nat} {h : EIdx} {hP : Expr} {s₀ s' : AState} {r : Option (List EIdx × EIdx)},
    StateOK s₀ → ExprOps.InstLVec s₀.store acc ws → denoteE s₀.store h = some hP →
    Arena.openPisAtFvarsFGo acc n h i s₀ = .ok (r, s') →
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvarsFGo ws n hP i) := by
  intro n
  induction n with
  | zero =>
    intro acc ws i h hP s₀ s' r hok hacc hh hrun
    simp only [Arena.openPisAtFvarsFGo] at hrun
    obtain ⟨e, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run hok hacc
      (by rw [hh]; rfl) k1
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨PStep.of_caches h1 h2 h3 h4 h5, ?_⟩
    simp [denoteOpen, Frontend.denoteEList, h7 _ hh, ConLeche.openPisAtFvarsFGo]
  | succ n ih =>
    intro acc ws i h hP s₀ s' r hok hacc hh hrun
    simp only [Arena.openPisAtFvarsFGo] at hrun
    obtain ⟨v, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body bm =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      dsimp only at z1
      obtain ⟨dd, s2, k2, z2⟩ := bindOk z1
      obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run hok hacc
        (by rw [hd]; rfl) k2
      have p2 : PStep s₀ s2 := PStep.of_caches h1 h2 h3 h4 h5
      have hdd : denoteE s2.store dd = some (domP.instantiateList ws 0) := h7 _ hd
      obtain ⟨fv, s3, k3, z3⟩ := bindOk z2
      obtain ⟨p3, hfv⟩ := internE_run p2.ok (viewOK_fvar (by rw [hdd]; rfl)) k3
      have hfv' : denoteE s3.store fv = some (.fvar i (domP.instantiateList ws 0)) := by
        rw [hfv]; simp [denoteEView, denote_ext hdd p3.ext]
      obtain ⟨o, s4, k4, z4⟩ := bindOk z3
      obtain ⟨p4, ho⟩ := ih p3.ok (InstLVec_push (hacc.ext (p2.ext.trans p3.ext)) hfv')
        (denote_ext hb (p2.ext.trans p3.ext)) k4
      have p24 := p2.trans (p3.trans p4)
      simp only [ConLeche.openPisAtFvarsFGo]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p24, ?_⟩
        have hn : ConLeche.openPisAtFvarsFGo (.fvar i (domP.instantiateList ws) :: ws) n
            bodyP (i + 1) = none := (Option.some.inj ho).symm
        simp [denoteOpen, hn]
      | some q =>
        obtain ⟨fvs, e⟩ := q
        obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p24, ?_⟩
        rw [hx]
        exact denoteOpen_some (by
          simp only [Frontend.denoteEList, denote_ext hfv' p4.ext, h1]) h2
    all_goals
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b m => simp [denoteEView] at hh
      all_goals rfl

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:169-176 openPisAtFvarsF — **the
one-pass opener, as a run**, answering con-leche's binder-at-a-time
`openPisAtFvars` (through con-leche's `openPisAtFvarsF_eq`), which is what
con-leche's `normCtorVal` and `checkSumCtor` call. -/
theorem openPisAtFvarsF_run {n i : Nat} {h : EIdx} {hP : Expr} {s₀ s' : AState}
    {r : Option (List EIdx × EIdx)} (hok : StateOK s₀)
    (hh : denoteE s₀.store h = some hP)
    (hrun : Arena.openPisAtFvarsF n h i s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvars n hP i) := by
  rw [← ConLeche.openPisAtFvarsF_eq]
  simp only [Arena.openPisAtFvarsF] at hrun
  obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := openPisAtFvarsFGo_run n hok
    (show ExprOps.InstLVec s₀.store #[] [] from rfl) hh k1
  simp only [ConLeche.openPisAtFvarsF]
  cases o with
  | some q =>
    obtain ⟨fvs, e⟩ := q
    obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨p1, ?_⟩
    rw [hx]
    exact denoteOpen_some h1 h2
  | none =>
    have hn : ConLeche.openPisAtFvarsFGo [] n hP i = none := (Option.some.inj ho).symm
    rw [hn]
    obtain ⟨p2, h2⟩ := openPisAtFvars_run n p1.ok (denote_ext hh p1.ext) z1
    exact ⟨p1.trans p2, h2⟩

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
(its `zipWith`) — `zipFvarDoms_spec` with the answer named, not only
measured: the twin's list IS con-leche's `List.zipWith` of the variables'
domains and the binders' metadata (task #97-P3-Ind round 8). -/
theorem zipFvarDoms_run (xs : List EIdx) (xsP : List Expr)
    (bs : List (EIdx × BinderMeta)) (bsP : List (Expr × BinderMeta)) :
    PSpec (fun st => Frontend.denoteEList st xs = some xsP ∧
        denoteBinders st bs = some bsP)
      (Arena.zipFvarDoms xs bs)
      (RB (List.zipWith (fun (x : Expr) (b : Expr × BinderMeta) => (x.fvarTypeD, b.2))
        xsP bsP)) := by
  induction xs generalizing xsP bs bsP with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hx, hb⟩ := hpre
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.zipFvarDoms] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, by show denoteBinders _ _ = _; simp [denoteBinders]⟩
  | cons x xs ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hx, hb⟩ := hpre
    cases bs with
    | nil =>
      simp only [denoteBinders, Option.some.injEq] at hb
      subst hb
      simp only [Arena.zipFvarDoms] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨PStep.refl hok, by show denoteBinders _ _ = _; simp [denoteBinders]⟩
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
              obtain ⟨hstep, hts⟩ := ih xsP' bs bsP' _ s₂ rest hok ⟨hxs, hbs⟩ h3
              obtain ⟨rfl, rfl⟩ := pureOk h4
              refine ⟨hstep, ?_⟩
              show denoteBinders _ _ = _
              simp only [denoteBinders, denote_ext ht hstep.ext]
              rw [show denoteBinders s'.store rest = _ from hts]
              rfl

/-- con-leche: none — binder lists denote across an append. -/
theorem denoteBinders_append {st : EStore} :
    ∀ {as bs : List (EIdx × BinderMeta)} {asP bsP : List (Expr × BinderMeta)},
      denoteBinders st as = some asP → denoteBinders st bs = some bsP →
      denoteBinders st (as ++ bs) = some (asP ++ bsP)
  | [], bs, asP, bsP, ha, hb => by
    simp only [denoteBinders, Option.some.injEq] at ha
    subst ha; simpa using hb
  | (t, m) :: as, bs, asP, bsP, ha, hb => by
    simp only [denoteBinders] at ha
    cases ht : denoteE st t with
    | none => rw [ht] at ha; simp at ha
    | some x =>
    cases has : denoteBinders st as with
    | none => rw [ht, has] at ha; simp at ha
    | some rest =>
    rw [ht, has] at ha
    obtain rfl := (Option.some.inj ha).symm
    simp only [List.cons_append, denoteBinders, ht, denoteBinders_append has hb,
      List.cons_append]

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:83-95 normCtorValF
The constructor's stored type rebuilt from the normalised domains.

`sorry`: `normFieldDoms_spec`, `zipFvarDoms_spec` and `closeTelescope_spec`. -/
theorem normCtorVal_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T : NIdx) (TP : ConLeche.Name)
    (nP nF : Nat) (cvC cvCa : IConstantVal) (cvCP cvCaP : ConstantVal)
    (hws : Expr.WScoped 0 cvCaP.type) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteCV st cvC = some cvCP ∧
        Frontend.denoteCV st cvCa = some cvCaP ∧
        denoteFEnv st fe = some env)
      (Arena.normCtorVal μ fe T nP nF cvC cvCa)
      (fun st r => ∃ F v,
        ConLeche.normCtorVal (ConLeche.fueledOps μ F) env TP nP nF cvCP cvCaP
          = .ok v ∧ Frontend.denoteCV st r = some v) := by
  intro s₀ s' r hck hpre hrun
  obtain ⟨hT, hcvC, hcvCa, hfe⟩ := hpre
  simp only [Arena.normCtorVal] at hrun
  -- the parameter binders
  obtain ⟨o1, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, ho1⟩ := stripPis_pstep hck.state (denoteCV_type hcvCa) k1
  rw [hs1] at z1
  obtain ⟨q1, s₂, k2, z2⟩ := bindOk z1
  cases o1 with
  | none => simp only [Arena.unwrapOr] at k2; exact absurd k2 (fun h => failOk h)
  | some o1' =>
  simp only [Arena.unwrapOr] at k2
  obtain ⟨hq1, hs2⟩ := pureOk k2
  subst hq1
  rw [hs2] at z2
  obtain ⟨cbs, cb⟩ := q1
  obtain ⟨cbsP, cbP, hsp, hcbs, -⟩ := denoteBP_someB ho1
  dsimp only at z2
  -- the opened telescope
  obtain ⟨o2, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨p3, ho2⟩ := openPisAtFvarsF_run hck.state (denoteCV_type hcvCa) k3
  obtain ⟨q2, s₄, k4, z4⟩ := bindOk z3
  cases o2 with
  | none => simp only [Arena.unwrapOr] at k4; exact absurd k4 (fun h => failOk h)
  | some o2' =>
  simp only [Arena.unwrapOr] at k4
  obtain ⟨hq2, hs4⟩ := pureOk k4
  subst hq2
  rw [hs4] at z4
  obtain ⟨fvs, crest⟩ := q2
  obtain ⟨fvsP, crestP, hop, hfvs, hcrest⟩ := denoteOpen_some_inv ho2
  dsimp only at z4
  have hwsC : Expr.WScoped nP crestP := by
    have := (ConLeche.openPisAtFvars_WScoped _ _ _ hop hws).2
    simpa using this
  generalize hpbsP : List.zipWith (fun (x : Expr) (b : Expr × BinderMeta) =>
    (x.fvarTypeD, b.2)) fvsP cbsP = pbsP
  -- the parameters' domains, read off the opened variables
  obtain ⟨pbs, s₅, k5, z5⟩ := bindOk z4
  obtain ⟨p5, hpbs⟩ := zipFvarDoms_run fvs fvsP cbs cbsP s₃ s₅ pbs p3.ok
    ⟨hfvs, denoteBinders_ext p3.ext _ _ hcbs⟩ k5
  rw [hpbsP] at hpbs
  have c5 : CoreStep μ env fe s₀ s₅ := (p3.trans p5).toCore hck
  -- the fields' domains, normalised
  obtain ⟨fr, s₆, k6, z6⟩ := bindOk z5
  obtain ⟨c6, F₁, fbsP, residP, hF₁, hfbs, hres⟩ := normFieldDoms_spec fe hk henv T TP nP nF
    crest crestP hwsC s₅ s₆ fr c5.ok
    ⟨denoteN_ext hT c5.ext, denote_ext hcrest p5.ext, denoteFEnv_ext c5.ext hfe⟩ k6
  obtain ⟨fbs, resid⟩ := fr
  simp only at hfbs hres z6
  -- the telescope closed again
  obtain ⟨ty', s₇, k7, z7⟩ := bindOk z6
  obtain ⟨p7, hty'⟩ := closeTelescope_spec (pbs ++ fbs) (pbsP ++ fbsP) 0 resid residP s₆ s₇ ty'
    c6.ok.state ⟨denoteBinders_append (denoteBinders_ext c6.ext _ _ hpbs) hfbs, hres⟩ k7
  have c7 := (c5.trans c6).trans (p7.toCore (c5.trans c6).ok)
  have hbeq := beq_ehandle_eq c7.ok.state.wf hty' (denote_ext (denoteCV_type hcvCa) c7.ext)
  generalize hty'P : ConLeche.closeTelescope (pbsP ++ fbsP) 0 residP = tyP at hty' hbeq
  have hpure : ∀ F, F₁ ≤ F →
      ConLeche.normCtorVal (ConLeche.fueledOps μ F) env TP nP nF cvCP cvCaP =
        (if tyP == cvCaP.type then pure cvCaP
         else ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env
           { cvCP with type := tyP }) := by
    intro F hle
    have g₁ := normFieldDoms_mono (μ := μ) (env := env) hle hF₁
    rw [← hty'P, ← hpbsP]
    simp only [ConLeche.normCtorVal, hsp, hop, ConLeche.unwrapOr, pure, Except.pure, bind,
      Except.bind, g₁]
  split at z7
  · rename_i heq
    obtain ⟨rfl, rfl⟩ := pureOk z7
    rw [hbeq] at heq
    refine ⟨c7, F₁, cvCaP, ?_, denoteCV_ext hcvCa c7.ext⟩
    rw [hpure F₁ (Nat.le_refl _), if_pos heq]
    rfl
  · rename_i hne
    rw [hbeq] at hne
    have hcvT : Frontend.denoteCV s₇.store { cvC with type := ty' } =
        some { cvCP with type := tyP } := by
      obtain ⟨hn, hl, -⟩ := denoteCV_inv hcvC
      simp only [Frontend.denoteCV, denoteN_ext hn c7.ext, denoteNListE_ext c7.ext _ _ hl, hty']
    obtain ⟨c8, cAP, F₂, hcA, hF₂⟩ := checkConstantVal_bridge hμ hk c7.ok henv hcvT z7
    refine ⟨c7.trans c8, max F₁ F₂, cAP, ?_, hcA⟩
    rw [hpure (max F₁ F₂) (Nat.le_max_left _ _), if_neg hne]
    exact checkConstantVal_mono (Nat.le_max_right _ _) hF₂

/-! ## The constructors' stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:97-128 checkSumCtorF
One constructor checked: its telescope, its parameter domains, its residual,
its field sorts and its normalised stored value.

`sorry`: `checkSumTele_spec`, `checkStructDomsAt_spec`
(`Bridge/Inductives/StructInstall.lean`), `checkStructFieldSortsI_spec`,
`normCtorVal_spec` and `structCtorResidOk_spec`. -/
theorem checkSumCtor_spec {μ : CheckMode} {env : Env} (fe₀ fe : IFEnv)
    (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvC : IConstantVal) (cvCP : ConstantVal) (nF : Nat)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env)
    (hws : Expr.WScoped 0 cvTaP.type) :
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
    (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
    (hws : Expr.WScoped 0 cvTaP.type) :
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
