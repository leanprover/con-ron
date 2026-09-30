/-
# `ConRon.Bridge.Inductives.SumInstall` — Theorem 1 for the block install's shared stages

`Arena/Inductives/SumInstall.lean`'s twins against
`ConLeche/Kernel/Inductives/SumInstall.lean` (and the `…F` `abbrev`s of
`SumInstallF.lean`, which are the same functions — task #97d-2's deviation 1).
These are the shared stages the uniform route's block install runs
(`checkBlockTele`, `checkBlockCtors`, `checkBlockIdxSorts`, `checkBlock`): the
former's telescope, the per-field universe bound, the constructors' stage, the
constructors consed and the stored rules.  (The capability record, the
positivity normalisation and the former's install stage went with con-leche's
fixpoint route, task #105, and their lemmas with them; `closeTelescope`'s is
`Bridge/Inductives/FieldTele.lean`'s now, beside its twin's new home.)

**Mostly CORE grade.**  `whnfTelescope` calls `whnf`, `checkStructFieldSortsI`
calls `inferTypeCore` and `ensureSort`, `checkSumTele` and `checkSumCtor` call
all of them — so their frame is `CoreStep` and their hypothesis is
`CoreSpec`.  `consSumCtors` is pure on both sides, and the field and index
resolution walks are pure grade.  The last section restates every core-grade
statement as a `CSpecF` against con-leche's `FueledM` function (task #105).

## Task #97d-2's removed higher-order argument here

* `sumRules`' `find? : Name → Option ConstantInfo` became `fe : IFEnv`.  The
  statement compares it at `find? := env.find?`, which is what `IFEnvOK`'s
  `hit`/`cover` pair says the index is.
-/
import ConRon.Bridge.Inductives.StructInstall
import ConLeche.Verify.FastOps
import ConRon.Bridge.Checker.Base
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Inductives.DirectInv
import ConRon.Bridge.Inductives.FieldTele

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The former's telescope -/

/-- con-leche: none — **`Arena.whnfTelescope`'s equation at `0`**.  The twin
matches on the pair `(view e', n)` (so the Rust's one `match` is kept), and
Lean's equation compiler cannot derive the unfolding of that structural
recursion (`failed to generate equational theorem`); the two cases are
definitional, one `rfl` per view.  Belongs beside the twin's other run lemmas
(a shared file), stated here while this module is its one consumer. -/
theorem whnfTelescope_zero_eq (μ : CheckMode) (fe : IFEnv) (i : Nat) (e : EIdx) :
    Arena.whnfTelescope μ fe i 0 e = (do
      let e' ← Arena.whnf μ fe Arena.checkFuel i e
      match ← view e' with
      | .sort s => pure ([], s)
      | _ => Arena.fail (.invalid "direct sum: type former does not reduce to a sort")) := by
  show _ = bind (Arena.whnf μ fe Arena.checkFuel i e) _
  delta Arena.whnfTelescope
  refine congrArg (bind (Arena.whnf μ fe Arena.checkFuel i e)) (funext fun e' => ?_)
  refine congrArg (bind (view e')) (funext fun v => ?_)
  cases v <;> rfl

/-- con-leche: none — **`Arena.whnfTelescope`'s equation at `n + 1`**; see
`whnfTelescope_zero_eq`. -/
theorem whnfTelescope_succ_eq (μ : CheckMode) (fe : IFEnv) (i n : Nat) (e : EIdx) :
    Arena.whnfTelescope μ fe i (n + 1) e = (do
      let e' ← Arena.whnf μ fe Arena.checkFuel i e
      match ← view e' with
      | .forallE dom body bm => do
        let fv ← internE (.fvar i dom)
        let b ← instantiate1Fast coreWalkFuel body fv 0
        let (bs, s) ← Arena.whnfTelescope μ fe (i + 1) n b
        pure ((dom, bm) :: bs, s)
      | _ => Arena.fail (.invalid
          "direct sum: type former does not reduce to a telescope")) := by
  show _ = bind (Arena.whnf μ fe Arena.checkFuel i e) _
  delta Arena.whnfTelescope
  refine congrArg (bind (Arena.whnf μ fe Arena.checkFuel i e)) (funext fun e' => ?_)
  refine congrArg (bind (view e')) (funext fun v => ?_)
  cases v <;> rfl

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

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:34-57 whnfTelescope
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
    rw [whnfTelescope_zero_eq] at hrun
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
    rw [whnfTelescope_succ_eq] at hrun
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

/-- con-leche: none — a handle denoting a sort carries the sort tag (the
tag-first test's `else` side cannot be a sort). -/
private theorem sortTag_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {u : Level}
    (hd : denoteE st h = some (.sort u)) : h.tag = ETag.sort := by
  obtain ⟨v, _, ht, hv⟩ := PW.denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:59-73 checkSumTele
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
The type former's stage: the telescope checked and the result sort measured.

**CLOSED** (task #97-P3-Ind round 8), over `whnfTelescope_spec` and `closeTelescope_spec`, plus `CoreSpec.knot`'s
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
  obtain ⟨xs, x, hxs, -, hbody⟩ := denoteBP_some hsq
  dsimp only at z1
  by_cases htg : (body.tag == ETag.sort) = true
  · rw [if_pos htg] at z1
    obtain ⟨o, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨hs2, ho⟩ := AM.of_run (P := fun t => t = s₀) rfl k2 (viewSort_spec s₀ body)
    subst hs2
    cases o with
    | none => exact absurd z2 (fun h => PW.failDanglingE_ok h)
    | some u =>
      have hv := view_of_viewSort_tag htg ho.symm
      obtain ⟨uP, rfl, hu⟩ := denote_sort_inv hck.state.wf hv hbody
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨CoreStep.refl hck, 0, cvTa₀P, uP, ?_, hcv0, hu⟩
      simp only [ConLeche.checkSumTele, hxs, pure, Except.pure]
  · rw [if_neg htg] at z1
    refine finish z1 (fun bsP sP h => ?_)
    rw [hxs] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact htg (by rw [sortTag_of_denote hck.state.wf hbody]; rfl)

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

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:75-100 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-48 checkStructFieldSortsIF
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:50-68 checkStructFieldSortsIFA
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
      have hlu := (Core.readLevelM_denote hok4.caches.readL k5).1
      have c5 : CoreStep μ env fe s4 s5 := (readLevelM_pstep hok4.state k5).toCore hok4
      obtain ⟨ls, s6, k6, z6⟩ := bindOk z5
      have hls := (Core.readLevelM_denote c5.ok.caches.readL k6).1
      have c6 : CoreStep μ env fe s5 s6 := (readLevelM_pstep c5.ok.state k6).toCore c5.ok
      obtain ⟨b, s7, k7, z7⟩ := bindOk z6
      have hlu' : lu = uP := Option.some.inj (hlu.symm.trans huP)
      have hls' : ls = sP :=
        Option.some.inj (hls.symm.trans (denoteL_ext hs (c4.ext.trans c5.ext)))
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
      obtain ⟨c, F3, restP, hF3, hr⟩ := tail _ (c5.trans c6) z8
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

/-! ## The telescope opener (task #97-P3-Ind round 7, on loan)

`Arena/CheckerBase.lean`'s `openPisAtFvars` / `openPisAtFvarsFGo` /
`openPisAtFvarsF` had no Theorem 1 anywhere in the Bridge; `checkSumCtor` is
their consumer here.  **Owner: the Checker tier** (`Bridge/Checker/**`, beside the
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
    -- the tag-first twin (task #97-T2-LOCKSTEP lane Checker, D1)
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
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
    -- the tag-first twin (task #97-T2-LOCKSTEP lane Checker, D1)
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
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
con-leche's `checkSumCtor` calls. -/
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

/-! ## The constructors' stage -/

/-- con-leche: ConLeche/Verify/BridgeWfImp.lean:451-543 openPisAtFvars_index /
openPisAtFvars_WScoped — **an opened variable's domain is scoped at its own
position**: the `j`-th variable is `fvar (i + j)`, and the opening's scope
conjunct says its domain is scoped there. -/
theorem open_fvar_scope {n i : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : ConLeche.openPisAtFvars n e i = some (fvs, body)) (hw : Expr.WScoped i e) :
    ∀ (j : Nat) (x : Expr), fvs[j]? = some x → Expr.WScoped (i + j) x.fvarTypeD := by
  intro j x hx
  obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ h j x hx
  have hw' := (ConLeche.openPisAtFvars_WScoped _ _ _ h hw).1 _ (List.mem_of_getElem? hx)
  simp only [Expr.WScoped] at hw'
  exact hw'.2

/-- con-leche: none — `Arena.fvarTypeDs` (`xs.map Expr.fvarTypeD` over
handles, `Arena/CheckerBase.lean`), as a run: it reads the store only. -/
theorem fvarTypeDs_run : ∀ (xs : List EIdx) (xsP : List Expr) {s₀ s' : AState}
    {r : List EIdx}, StateOK s₀ → Frontend.denoteEList s₀.store xs = some xsP →
    Arena.fvarTypeDs xs s₀ = .ok (r, s') →
    PStep s₀ s' ∧ Frontend.denoteEList s'.store r = some (xsP.map Expr.fvarTypeD)
  | [], xsP, s₀, s', r, hok, hx, hrun => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.fvarTypeDs] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | x :: xs, xsP, s₀, s', r, hok, hx, hrun => by
    simp only [Frontend.denoteEList] at hx
    cases hx1 : denoteE s₀.store x with
    | none => rw [hx1] at hx; simp at hx
    | some xP =>
    cases hxs : Frontend.denoteEList s₀.store xs with
    | none => rw [hx1, hxs] at hx; simp at hx
    | some rest =>
    rw [hx1, hxs] at hx
    obtain rfl := (Option.some.inj hx).symm
    simp only [Arena.fvarTypeDs] at hrun
    obtain ⟨t, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨rfl, ht⟩ := fvarTypeD_run hok hx1 k1
    obtain ⟨ts, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hts⟩ := fvarTypeDs_run xs rest hok hxs k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p2, ?_⟩
    simp only [Frontend.denoteEList, denote_ext ht p2.ext, hts, List.map_cons]

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
(its field-domain test) — `Arena.fieldDomsResolve` answers
`xs.all fun x => x.fvarTypeD.constsResolve env₀` at the pre-block index. -/
theorem fieldDomsResolve_spec {env₀ : Env} {fe₀ : IFEnv} :
    ∀ (xs : List EIdx) (xsP : List Expr) {s₀ s' : AState} {b : Bool},
    ReadOK env₀ fe₀ s₀ → Frontend.denoteEList s₀.store xs = some xsP →
    Arena.fieldDomsResolve fe₀ xs s₀ = .ok (b, s') →
    PStep s₀ s' ∧ b = xsP.all fun x => x.fvarTypeD.constsResolve env₀
  | [], xsP, s₀, s', b, hok, hx, hrun => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.fieldDomsResolve] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok.state, rfl⟩
  | x :: xs, xsP, s₀, s', b, hok, hx, hrun => by
    simp only [Frontend.denoteEList] at hx
    cases hx1 : denoteE s₀.store x with
    | none => rw [hx1] at hx; simp at hx
    | some xP =>
    cases hxs : Frontend.denoteEList s₀.store xs with
    | none => rw [hx1, hxs] at hx; simp at hx
    | some rest =>
    rw [hx1, hxs] at hx
    obtain rfl := (Option.some.inj hx).symm
    simp only [Arena.fieldDomsResolve] at hrun
    obtain ⟨t, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨rfl, ht⟩ := fvarTypeD_run hok.state hx1 k1
    obtain ⟨c, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hc⟩ := constsResolveFFast_pstep hok ht k2
    have hok₂ := hok.mono p2.ok p2.ext p2.pins
    cases c with
    | false =>
      simp only [Bool.false_eq_true, if_false] at z2
      obtain ⟨rfl, rfl⟩ := pureOk z2
      exact ⟨p2, by simp [List.all_cons, ← hc]⟩
    | true =>
      simp only [if_true] at z2
      obtain ⟨p3, hr⟩ := fieldDomsResolve_spec xs rest hok₂
        (denoteEList_ext p2.ext _ _ hxs) z2
      exact ⟨p2.trans p3, by simp [List.all_cons, ← hc, hr]⟩

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
(its index-expression test) — `Arena.idxArgsResolve` answers
`es.all fun e => e.constsResolve env₀` at the pre-block index. -/
theorem idxArgsResolve_spec {env₀ : Env} {fe₀ : IFEnv} :
    ∀ (es : List EIdx) (esP : List Expr) {s₀ s' : AState} {b : Bool},
    ReadOK env₀ fe₀ s₀ → Frontend.denoteEList s₀.store es = some esP →
    Arena.idxArgsResolve fe₀ es s₀ = .ok (b, s') →
    PStep s₀ s' ∧ b = esP.all fun e => e.constsResolve env₀
  | [], esP, s₀, s', b, hok, hx, hrun => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.idxArgsResolve] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok.state, rfl⟩
  | x :: xs, esP, s₀, s', b, hok, hx, hrun => by
    simp only [Frontend.denoteEList] at hx
    cases hx1 : denoteE s₀.store x with
    | none => rw [hx1] at hx; simp at hx
    | some xP =>
    cases hxs : Frontend.denoteEList s₀.store xs with
    | none => rw [hx1, hxs] at hx; simp at hx
    | some rest =>
    rw [hx1, hxs] at hx
    obtain rfl := (Option.some.inj hx).symm
    simp only [Arena.idxArgsResolve] at hrun
    obtain ⟨c, s₂, k2, z2⟩ := bindOk hrun
    obtain ⟨p2, hc⟩ := constsResolveFFast_pstep hok hx1 k2
    have hok₂ := hok.mono p2.ok p2.ext p2.pins
    cases c with
    | false =>
      simp only [Bool.false_eq_true, if_false] at z2
      obtain ⟨rfl, rfl⟩ := pureOk z2
      exact ⟨p2, by simp [List.all_cons, ← hc]⟩
    | true =>
      simp only [if_true] at z2
      obtain ⟨p3, hr⟩ := idxArgsResolve_spec xs rest hok₂
        (denoteEList_ext p2.ext _ _ hxs) z2
      exact ⟨p2.trans p3, by simp [List.all_cons, ← hc, hr]⟩

/-- con-leche: ConLeche/Verify/BridgeDecl.lean checkSumCtor_datF — `checkSumCtor`
at `fueledOps` is monotone in the fuel, through the `FueledM` run's own
monotonicity. -/
theorem checkSumCtor_up {μ : CheckMode} {F G : Nat} {env₀ env : Env} {T : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nIdx : Nat} {rs : Level} {isProp large : Bool}
    {cvC : ConstantVal} {nF : Nat} {cvTa : ConstantVal}
    {v : ConstantVal × List Level} (hle : F ≤ G)
    (h : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env T lps nP nIdx rs isProp
      large cvC nF cvTa = .ok v) :
    ConLeche.checkSumCtor (ConLeche.fueledOps μ G) env₀ env T lps nP nIdx rs isProp
      large cvC nF cvTa = .ok v := by
  rw [← ConLeche.checkSumCtor_datF] at h ⊢
  exact (ConLeche.checkSumCtor (ConLeche.fueledOpsM μ) env₀ env T lps nP nIdx rs isProp
    large cvC nF cvTa).property hle h

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:70-100 checkSumCtorF
One constructor checked: its constant check (stored as declared), its
residual, its parameter domains, its field and index resolution, and its
field sorts.

**CLOSED** (task #97-P3-Ind round 8; task #105 dropped the normalisation),
over `checkConstantVal_bridge`, `checkStructDomsAt_spec`
(`Bridge/Inductives/StructInstall.lean`), `checkStructFieldSortsI_spec`,
`fieldDomsResolve_spec`, `idxArgsResolve_spec` and `structCtorResidOk_spec`. -/
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
        denoteFEnv st fe₀ = some env₀ ∧ denoteFEnv st fe = some env ∧
        IFEnvOKS env₀ fe₀ st)
      (Arena.checkSumCtor μ fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa)
      (fun st r => ∃ F cvCaP sortsP,
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env TP lpsP nP
          nIdx resSortP isProp large cvCP nF cvTaP = .ok (cvCaP, sortsP) ∧
        Frontend.denoteCV st r.1 = some cvCaP ∧
        denoteLList st.ls r.2 = some sortsP) := by
  intro s₀ s' r hck hpre hrun
  obtain ⟨hT, hlps, hrs, hcvC, hcvTa, hfe₀, hfe, hok₀⟩ := hpre
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  simp only [Arena.checkSumCtor] at hrun
  -- the constructor's own check (stored as declared)
  obtain ⟨cvCa, s₂, k1, z2⟩ := bindOk hrun
  obtain ⟨c12, cAP, F₁, hcA, hF₁⟩ := checkConstantVal_bridge hμ hk hck henv hcvC k1
  have x1 := c12.ext
  -- the stored constructor is a checked constant: closed
  have hwsA : Expr.WScoped 0 cAP.type :=
    Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  -- the result shape
  obtain ⟨o3, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨hs3, ho3⟩ := stripPis_pstep c12.ok.state (denoteCV_type hcA) k3
  rw [hs3] at z3
  obtain ⟨q3, s₄, k4, z4⟩ := bindOk z3
  cases o3 with
  | none => simp only [Arena.unwrapOr] at k4; exact absurd k4 (fun h => failOk h)
  | some o3' =>
  simp only [Arena.unwrapOr] at k4
  obtain ⟨hq3, hs4⟩ := pureOk k4
  subst hq3
  rw [hs4] at z4
  obtain ⟨cbs, cbody⟩ := q3
  obtain ⟨cxs, cbodyP, hsp, -, hcb⟩ := denoteBP_some ho3
  dsimp only at z4
  have x02 := c12.ext
  obtain ⟨b5, s₅, k5, z5⟩ := bindOk z4
  obtain ⟨p5, hb5⟩ := structCtorResidOk_spec T TP lps lpsP nP nF nIdx cbody cbodyP s₂ s₅ b5
    c12.ok.state ⟨denoteN_ext hT x02, denoteNListE_ext x02 _ _ hlps, hcb⟩ k5
  obtain ⟨hr5, z6⟩ := AM.dunless_ok hnever z5
  replace z6 := AM.pure_bind_ok z6
  rw [hb5] at hr5
  have c5 := c12.trans (p5.toCore c12.ok)
  -- the constructor's parameters, opened
  obtain ⟨o6, s₆, k6, z7⟩ := bindOk z6
  obtain ⟨p6, ho6⟩ := openPisAtFvarsF_run c5.ok.state
    (denote_ext (denoteCV_type hcA) p5.ext) k6
  obtain ⟨cq, s₇, k7, z8⟩ := bindOk z7
  cases o6 with
  | none => simp only [Arena.unwrapOr] at k7; exact absurd k7 (fun h => failOk h)
  | some o6' =>
  simp only [Arena.unwrapOr] at k7
  obtain ⟨hq6, hs7⟩ := pureOk k7
  subst hq6
  rw [hs7] at z8
  obtain ⟨cfvsP, crestP, hcq, hcfvs, hcrest⟩ := denoteOpen_some_inv ho6
  -- the former's parameters, opened
  have c6 := c5.trans (p6.toCore c5.ok)
  obtain ⟨o8, s₈, k8, z9⟩ := bindOk z8
  obtain ⟨p8, ho8⟩ := openPisAtFvarsF_run c6.ok.state
    (denote_ext (denoteCV_type hcvTa) (x1.trans (p5.ext.trans p6.ext))) k8
  obtain ⟨tq, s₉, k9, z10⟩ := bindOk z9
  cases o8 with
  | none => simp only [Arena.unwrapOr] at k9; exact absurd k9 (fun h => failOk h)
  | some o8' =>
  simp only [Arena.unwrapOr] at k9
  obtain ⟨hq8, hs9⟩ := pureOk k9
  subst hq8
  rw [hs9] at z10
  obtain ⟨tfvsP, trestP, htq, htfvs, htrest⟩ := denoteOpen_some_inv ho8
  have c8 := c6.trans (p8.toCore c6.ok)
  -- the domains the pins compare
  obtain ⟨doms, s₁₀, k10, z11⟩ := bindOk z10
  obtain ⟨p10, hdoms⟩ := fvarTypeDs_run tq.1 tfvsP c8.ok.state htfvs k10
  have c10 := c8.trans (p10.toCore c8.ok)
  obtain ⟨u11, s₁₁, k11, z12⟩ := bindOk z11
  have x6_10 : Ext s₆.store s₁₀.store := p8.ext.trans p10.ext
  obtain ⟨c11, F₃, hF₃⟩ := checkStructDomsAt_spec fe hk henv 0 cq.1 doms cfvsP
    (tfvsP.map Expr.fvarTypeD) nP (by
      intro i _ a b ha hb
      refine ⟨open_fvar_scope hcq hwsA i a ha, ?_⟩
      rw [List.getElem?_map] at hb
      cases hti : tfvsP[i]? with
      | none => rw [hti] at hb; exact nomatch hb
      | some t =>
        rw [hti] at hb
        obtain rfl := (Option.some.inj hb).symm
        exact open_fvar_scope htq hws i t hti) s₁₀ s₁₁ u11 c10.ok
    ⟨denoteEList_ext x6_10 _ _ hcfvs, hdoms, denoteFEnv_ext c10.ext hfe⟩ k11
  have c11' := c10.trans c11
  -- the fields, opened past the parameters
  obtain ⟨o12, s₁₂, k12, z13⟩ := bindOk z12
  obtain ⟨p12, ho12⟩ := openPisAtFvarsF_run c11'.ok.state
    (denote_ext hcrest ((p8.ext.trans p10.ext).trans c11.ext)) k12
  obtain ⟨xq, s₁₃, k13, z14⟩ := bindOk z13
  cases o12 with
  | none => simp only [Arena.unwrapOr] at k13; exact absurd k13 (fun h => failOk h)
  | some o12' =>
  simp only [Arena.unwrapOr] at k13
  obtain ⟨hq12, hs13⟩ := pureOk k13
  subst hq12
  rw [hs13] at z14
  obtain ⟨xfvsP, xrestP, hxq, hxfvs, hxrest⟩ := denoteOpen_some_inv ho12
  have c12' := c11'.trans (p12.toCore c11'.ok)
  -- the family head and the residual's spine
  obtain ⟨us, s₁₄, k14, z15⟩ := bindOk z14
  have x0_12 := c12'.ext
  obtain ⟨p14, hus⟩ := paramLevels_spec lps lpsP s₁₂ s₁₄ us c12'.ok.state
    (denoteNListE_ext x0_12 _ _ hlps) k14
  obtain ⟨hd, s₁₅, k15, z16⟩ := bindOk z15
  obtain ⟨p15, hhd⟩ := internConstE_run p14.ok (denoteN_ext hT (x0_12.trans p14.ext)) hus k15
  have c15 := c12'.trans ((p14.trans p15).toCore c12'.ok)
  have x12_15 : Ext s₁₂.store s₁₅.store := p14.ext.trans p15.ext
  obtain ⟨xfn, s₁₆, k16, z17⟩ := bindOk z16
  obtain ⟨hs16, hxfn⟩ := getAppFn_run c15.ok.state (denote_ext hxrest x12_15) k16
  rw [hs16] at z17
  obtain ⟨xargs, s₁₇, k17, z18⟩ := bindOk z17
  obtain ⟨hs17, hxargs⟩ := getAppArgs_run c15.ok.state (denote_ext hxrest x12_15) k17
  rw [hs17] at z18
  have hwf15 := c15.ok.state.wf
  have x7_15 : Ext s₆.store s₁₅.store :=
    (p8.ext.trans p10.ext).trans (c11.ext.trans (p12.ext.trans x12_15))
  have hg := AM.dunless_ok hnever z18
  obtain ⟨hg1, z19⟩ := hg
  replace z19 := AM.pure_bind_ok z19
  rw [beq_ehandle_eq hwf15 hxfn hhd,
    beq_ehandleList_eq hwf15 (denoteEList_take hxargs nP) (denoteEList_ext x7_15 _ _ hcfvs),
    show xargs.length = xrestP.getAppArgs.length from
      (ExprOps.denoteEList_length _ _ hxargs).symm] at hg1
  -- the fields' domains resolve before the block
  have hread₀ : ReadOK env₀ fe₀ s₁₅ :=
    ⟨c15.ok.state, c15.ok.pins, hok₀.mono c15.ext s₁₅ rfl⟩
  obtain ⟨b20, s₂₀, k20, z20⟩ := bindOk z19
  obtain ⟨p20, hb20⟩ := fieldDomsResolve_spec xq.1 xfvsP hread₀
    (denoteEList_ext x12_15 _ _ hxfvs) k20
  obtain ⟨hg2, z21⟩ := AM.dunless_ok hnever z20
  replace z21 := AM.pure_bind_ok z21
  rw [hb20] at hg2
  obtain ⟨b22, s₂₂, k22, z22⟩ := bindOk z21
  obtain ⟨p22, hb22⟩ := idxArgsResolve_spec (xargs.drop nP) (xrestP.getAppArgs.drop nP)
    (hread₀.mono p20.ok p20.ext p20.pins)
    (denoteEList_drop (denoteEList_ext p20.ext _ _ hxargs) nP) k22
  obtain ⟨hg3, z23⟩ := AM.dunless_ok hnever z22
  replace z23 := AM.pure_bind_ok z23
  rw [hb22] at hg3
  -- the field sorts
  have c22 := c15.trans ((p20.trans p22).toCore c15.ok)
  have x15_22 : Ext s₁₅.store s₂₂.store := p20.ext.trans p22.ext
  obtain ⟨sorts, s₂₃, k23, z24⟩ := bindOk z23
  have hxpos : ∀ i, i < nF → ∀ a, xfvsP[i]? = some a → Expr.WScoped (nP + i) a.fvarTypeD := by
    intro i _ a ha
    have hwsc : Expr.WScoped nP crestP := by
      have := (ConLeche.openPisAtFvars_WScoped _ _ _ hcq hwsA).2
      simpa using this
    exact open_fvar_scope hxq hwsc i a ha
  obtain ⟨c23, F₄, sortsP, hF₄, hsorts⟩ := checkStructFieldSortsI_spec fe hk henv isProp large
    resSort resSortP nP xq.1 (xargs.drop nP) xfvsP (xrestP.getAppArgs.drop nP) nF hxpos
    s₂₂ s₂₃ sorts c22.ok
    ⟨denoteL_ext hrs c22.ext, denoteEList_ext (x12_15.trans x15_22) _ _ hxfvs,
      denoteEList_drop (denoteEList_ext x15_22 _ _ hxargs) nP, denoteFEnv_ext c22.ext hfe⟩ k23
  obtain ⟨rfl, rfl⟩ := pureOk z24
  refine ⟨c22.trans c23, max F₁ (max F₃ F₄), cAP, sortsP, ?_,
    denoteCV_ext hcA ((p5.ext.trans p6.ext).trans (x7_15.trans (x15_22.trans c23.ext))),
    hsorts⟩
  have g₁ := checkConstantVal_mono (show F₁ ≤ max F₁ (max F₃ F₄) by omega) hF₁
  have g₃ := checkStructDomsAt_mono (show F₃ ≤ max F₁ (max F₃ F₄) by omega) hF₃
  have g₄ := checkStructFieldSortsI_mono (show F₄ ≤ max F₁ (max F₃ F₄) by omega) hF₄
  simp only [ConLeche.checkSumCtor, bind, Except.bind, g₁, hsp, ConLeche.unwrapOr, pure,
    Except.pure, hr5, if_true, hcq, htq]
  rw [g₃]
  simp only [hxq]
  rw [if_pos hg1, if_pos hg2, if_pos hg3, g₄]

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:149-161 checkSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:102-112 checkSumCtorsF
The whole constructor list.

**CLOSED** (task #97-P3-Ind round 8), over a list induction over `checkSumCtor_spec`. -/
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
        denoteFEnv st fe₀ = some env₀ ∧ denoteFEnv st fe = some env ∧
        IFEnvOKS env₀ fe₀ st)
      (Arena.checkSumCtors μ fe₀ fe T lps nP nIdx resSort isProp large cvTa cs)
      (fun st r => ∃ F ctorsAP sortssP,
        ConLeche.checkSumCtors (ConLeche.fueledOps μ F) env₀ env TP lpsP nP
          nIdx resSortP isProp large cvTaP csP = .ok (ctorsAP, sortssP) ∧
        denoteCtors st r.1 = some ctorsAP ∧
        denoteLLists st r.2 = some sortssP) := by
  induction cs generalizing csP with
  | nil =>
    intro s₀ s' r hck hpre hrun
    obtain ⟨-, -, -, -, hcs, -, -, -⟩ := hpre
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.checkSumCtors] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hck, 0, [], [], rfl, rfl, rfl⟩
  | cons c cs ih =>
    intro s₀ s' r hck hpre hrun
    obtain ⟨hT, hlps, hrs, hcvTa, hcs, hfe₀, hfe, hok₀⟩ := hpre
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
    simp only [Arena.checkSumCtors] at hrun
    obtain ⟨t1, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, F₁, cvCaP, sortsP, hF₁, hcA, hsorts⟩ := checkSumCtor_spec fe₀ fe hμ hk henv T TP
      lps lpsP nP nIdx resSort resSortP isProp large cv cP n cvTa cvTaP env₀ hws s₀ s₁ t1 hck
      ⟨hT, hlps, hrs, hcv, hcvTa, hfe₀, hfe, hok₀⟩ k1
    obtain ⟨cvCa, sorts⟩ := t1
    simp only at hcA hsorts z1
    have x1 := c1.ext
    obtain ⟨t2, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨c2, F₂, restAP, srestP, hF₂, hra, hsr⟩ := ih restP s₁ s₂ t2 c1.ok
      ⟨denoteN_ext hT x1, denoteNListE_ext x1 _ _ hlps, denoteL_ext hrs x1,
        denoteCV_ext hcvTa x1, denoteCtors_ext x1 _ _ hrest, denoteFEnv_ext x1 hfe₀,
        denoteFEnv_ext x1 hfe, hok₀.mono x1⟩ k2
    obtain ⟨rest, srest⟩ := t2
    simp only at hra hsr z2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨c1.trans c2, max F₁ F₂, (cvCaP, n) :: restAP, sortsP :: srestP, ?_, ?_, ?_⟩
    · have g₁ := checkSumCtor_up (Nat.le_max_left F₁ F₂) hF₁
      have g₂ : ConLeche.checkSumCtors (ConLeche.fueledOps μ (max F₁ F₂)) env₀ env TP lpsP nP
          nIdx resSortP isProp large cvTaP restP = .ok (restAP, srestP) := by
        rw [← ConLeche.checkSumCtors_datF] at hF₂ ⊢
        exact (ConLeche.checkSumCtors (ConLeche.fueledOpsM μ) env₀ env TP lpsP nP nIdx resSortP
          isProp large cvTaP restP).property (Nat.le_max_right F₁ F₂) hF₂
      simp only [ConLeche.checkSumCtors, bind, Except.bind, g₁, g₂, pure, Except.pure]
    · simp only [denoteCtors, denoteCV_ext hcA c2.ext, hra]
    · have e1 : denoteLList s'.store.ls sorts = some sortsP :=
        denoteLList_ext c2.ext.lss.ls _ _ hsorts
      show denoteLLists _ _ = _
      simp only [denoteLLists, e1, hsr]

/-! ## The constructors consed, and the rules -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:163-166 consSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:114-117 consSumCtorsF
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

/-- con-leche: none — a constructor type's result head, two steps deep
(`piResult`, `getAppFn`), both read-only: the half of `ctorHead_facts` that
precedes the tag-first twin's `view` (task #97-P5-Core round 4). -/
theorem ctorHead_facts₂ {s s1 s2 : AState} {ty pr fn : EIdx} {tyP : Expr}
    (hok : StateOK s) (hd : denoteE s.store ty = some tyP)
    (k1 : Arena.piResult Arena.coreWalkFuel ty s = .ok (pr, s1))
    (k2 : Arena.getAppFn Arena.coreWalkFuel pr s1 = .ok (fn, s2)) :
    s = s1 ∧ s = s2 ∧ denoteE s.store fn = some tyP.piResult.getAppFn := by
  obtain ⟨hs1, hpr⟩ := AM.of_run (P := fun t => t = s) rfl k1
    (ExprOps.piResult_spec Arena.coreWalkFuel s ty hok (by rw [hd]; rfl))
  subst hs1
  obtain ⟨hs2, hfn⟩ := getAppFn_run hok (hpr _ hd) k2
  subst hs2
  exact ⟨rfl, rfl, hfn⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:821-830 recRuleKOf — the K bit at
install, in run form: read-only, and con-leche's verdict at `env.find?`. -/
theorem recRuleKOf_runX {env : Env} {fe : IFEnv} {s s' : AState}
    {ctor : NIdx} {ctorP : ConLeche.Name} {r : Bool}
    (hst : StateOK s) (hi : IFEnvOK env fe s) (hc : denoteN s.store.ns ctor = some ctorP)
    (hrun : Arena.recRuleKOf fe ctor s = .ok (r, s')) :
    s' = s ∧ r = ConLeche.recRuleKOf env.find? ctorP := by
  simp only [Arena.recRuleKOf] at hrun
  cases hf : fe.find? ctor with
  | none =>
    rw [hf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨rfl, ?_⟩
    simp only [ConLeche.recRuleKOf, IFEnvOK.miss hst hi hc hf]
  | some ci =>
  obtain ⟨nm, c, hnm, hci, henv⟩ := hi.hit ctor ci hf
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
  obtain ⟨hs1, hs2, hfn⟩ := ctorHead_facts₂ hst (denoteCV_type hcvj) k1 k2
  subst s1; subst s2
  obtain ⟨v0, hv0⟩ := denoteE_view hfn
  obtain ⟨v, s3, k3, z3⟩ := bindOk (tagIf_view_run hv0
    (fun hne => by cases v0 <;> first | rfl | exact absurd rfl hne) z2)
  obtain ⟨hs3, hv⟩ := view_run k3
  subst s3
  cases v
  all_goals try
    (obtain ⟨rfl, rfl⟩ := pureOk z3
     refine ⟨rfl, ?_⟩
     have hnc := denote_not_const hst.wf hv hfn (by intro _ _ h; cases h)
     split
     · rename_i T us heq; exact absurd heq (hnc _ _)
     · rfl)
  rename_i T us
  obtain ⟨TP, usP, hfe, hT, -⟩ := denote_const_inv hst.wf hv hfn
  rw [hfe]
  dsimp only at z3 ⊢
  cases hfT : fe.find? T with
  | none =>
    rw [hfT] at z3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨rfl, ?_⟩
    simp only [IFEnvOK.miss hst hi hT hfT]
  | some ciT =>
  obtain ⟨nmT, cT, hnmT, hciT, henvT⟩ := hi.hit T ciT hfT
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
theorem recRuleEtaOf_runX {μ : CheckMode} {env envC : Env} {fe feC : IFEnv} {s s' : AState}
    {recName ctor : NIdx} {recNameP ctorP : ConLeche.Name} {r : Bool}
    (hok : CheckOK μ envC feC s) (hi : IFEnvOK env fe s) (hrn : denoteN s.store.ns recName = some recNameP)
    (hc : denoteN s.store.ns ctor = some ctorP)
    (hrun : Arena.recRuleEtaOf fe recName ctor s = .ok (r, s')) :
    Core.ReadbackFrame s s' ∧ r = ConLeche.recRuleEtaOf env.find? recNameP ctorP := by
  simp only [Arena.recRuleEtaOf] at hrun
  cases hf : fe.find? ctor with
  | none =>
    rw [hf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨Core.ReadbackFrame.refl _, ?_⟩
    simp only [ConLeche.recRuleEtaOf, IFEnvOK.miss hok.state hi hc hf]
  | some ci =>
  obtain ⟨nm, c, hnm, hci, henv⟩ := hi.hit ctor ci hf
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
  obtain ⟨hs1, hs2, hfn⟩ := ctorHead_facts₂ hok.state (denoteCV_type hcvj) k1 k2
  subst s1; subst s2
  obtain ⟨v0, hv0⟩ := denoteE_view hfn
  obtain ⟨v, s3, k3, z3⟩ := bindOk (tagIf_view_run hv0
    (fun hne => by cases v0 <;> first | rfl | exact absurd rfl hne) z2)
  obtain ⟨hs3, hv⟩ := view_run k3
  subst s3
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
    simp only [IFEnvOK.miss hok.state hi hT hfT]
  | some ciT =>
  obtain ⟨nmT, cT, hnmT, hciT, henvT⟩ := hi.hit T ciT hfT
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
  · rename_i ct _ _ hct _ _
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
theorem recRuleBits_runX {μ : CheckMode} {env envC : Env} {fe feC : IFEnv} {s s' : AState}
    {recName : NIdx} {recNameP : ConLeche.Name} {rl rl' : IRecRule} {rlP : RecRule}
    (hok : CheckOK μ envC feC s) (hi : IFEnvOK env fe s) (hrn : denoteN s.store.ns recName = some recNameP)
    (hrl : Frontend.denoteRule s.store rl = some rlP)
    (hrun : Arena.recRuleBits fe recName rl s = .ok (rl', s')) :
    Core.ReadbackFrame s s' ∧
      Frontend.denoteRule s'.store rl' = some (ConLeche.recRuleBits env.find? recNameP rlP) := by
  obtain ⟨hctor, -⟩ := denoteRule_ctor hrl
  simp only [Arena.recRuleBits] at hrun
  obtain ⟨k, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hk⟩ := recRuleKOf_runX hok.state hi hctor k1
  rw [hs1] at z1
  obtain ⟨e, s2, k2, z2⟩ := bindOk z1
  obtain ⟨hfr, he⟩ := recRuleEtaOf_runX hok hi hrn hctor k2
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


/-! ## The monad-generic forms (task #105)

The uniform route's con-leche stages are written over a `CheckerOps m`, and
its consumers (`checkBlockTele`, `checkBlockCtors`, `checkBlockIdxSorts`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`) run them at the monotone
fueled operations `fueledOpsM μ`.  Each statement above concludes the pure
side's run at `fueledOps μ F` for some `F`; the forms below restate it as a
`CSpecF` against the `FueledM` function, by that stage's `_datF` lemma
(`ConLeche/Verify/BridgeDecl.lean`).  The scoping hypotheses are stated as
con-leche's cached template states them (`ConLeche/Verify/Cached/
BridgeCS3.lean`'s `whnfTelescopeS_sim`, `checkSumTeleS_sim`,
`checkSumCtorsS_sim`; `NestPosC.lean`'s `checkStructFieldSortsIS_sim`), and
`checkSumTele`'s answer carries the scope of the stored type, as
`checkSumTeleS_sim`'s does.  The scoping and freshness facts the block stage
reads off the constructors (`checkBlockCtors_types`, `checkBlockCtors_fresh`)
are facts of the pure run, which `FOk` hands over. -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:59-73 checkSumTele
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
`checkSumTele_spec` against `checkSumTele (fueledOpsM μ)`, with the stored
type's scope (`checkSumTeleS_sim`'s answer): the declared one on the fast
path, a checked constant's on the slow one (`checkSumTele_shape`,
`checkConstantVal_typeWF`). -/
theorem checkSumTele_specF {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (cv : IConstantVal) (cvP : ConstantVal)
    (n : Nat) (cvTa₀ : IConstantVal) (cvTa₀P : ConstantVal)
    (hws : Expr.WScoped 0 cvTa₀P.type) :
    CSpecF μ env fe
      (fun st => Frontend.denoteCV st cv = some cvP ∧
        Frontend.denoteCV st cvTa₀ = some cvTa₀P ∧
        denoteFEnv st fe = some env)
      (Arena.checkSumTele μ fe cv n cvTa₀)
      (fun st r v => Frontend.denoteCV st r.1 = some v.1 ∧ denoteL st.ls r.2 = some v.2 ∧
        Expr.WScoped 0 v.1.type)
      (ConLeche.checkSumTele (fueledOpsM μ) env cvP n cvTa₀P) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hstep, F, cvAP, sP, hF, h1, h2⟩ :=
    checkSumTele_spec fe hμ hk henv cv cvP n cvTa₀ cvTa₀P hws s₀ s' r hok hpre hrun
  refine ⟨hstep, (cvAP, sP), ⟨h1, h2, ?_⟩, F, by rw [checkSumTele_datF]; exact hF⟩
  rcases ConLeche.checkSumTele_shape hF with ⟨rfl, -⟩ | ⟨_, hc⟩
  · exact hws
  · exact Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hc).1

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:75-100 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-48 checkStructFieldSortsIF
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:50-68 checkStructFieldSortsIFA
`checkStructFieldSortsI_spec` against `checkStructFieldSortsI (fueledOpsM μ)`,
the field scopes stated as `checkStructFieldSortsIS_sim`'s `hfvs`. -/
theorem checkStructFieldSortsI_specF {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (isProp large : Bool)
    (s : LIdx) (sP : Level) (nP : Nat) (fvs idxArgs : List EIdx)
    (fvsP idxArgsP : List Expr) (j : Nat)
    (hfvs : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x → Expr.WScoped (nP + i) x.fvarTypeD) :
    CSpecF μ env fe
      (fun st => denoteL st.ls s = some sP ∧
        Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st idxArgs = some idxArgsP ∧
        denoteFEnv st fe = some env)
      (Arena.checkStructFieldSortsI μ fe isProp large s nP fvs idxArgs j)
      (fun st r v => denoteLList st.ls r = some v)
      (ConLeche.checkStructFieldSortsI (fueledOpsM μ) env isProp large sP nP fvsP idxArgsP j) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hstep, F, ls, hF, h1⟩ := checkStructFieldSortsI_spec fe hk henv isProp large s sP nP
    fvs idxArgs fvsP idxArgsP j (fun i _ a ha => hfvs i a ha) s₀ s' r hok hpre hrun
  exact ⟨hstep, ls, h1, F, by rw [checkStructFieldSortsI_datF]; exact hF⟩

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:149-161 checkSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:102-112 checkSumCtorsF
`checkSumCtors_spec` against `checkSumCtors (fueledOpsM μ)` — the form the
uniform route's constructor stage (`checkBlockCtors`, run at the formers'
environment `env` with the pre-block `env₀`) consumes. -/
theorem checkSumCtors_specF {μ : CheckMode} {env : Env} (fe₀ fe : IFEnv)
    (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
    (hTf : cvTaP.type.hasFvar = false) :
    CSpecF μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteCtors st cs = some csP ∧
        denoteFEnv st fe₀ = some env₀ ∧ denoteFEnv st fe = some env ∧
        IFEnvOKS env₀ fe₀ st)
      (Arena.checkSumCtors μ fe₀ fe T lps nP nIdx resSort isProp large cvTa cs)
      (fun st r v => denoteCtors st r.1 = some v.1 ∧ denoteLLists st r.2 = some v.2)
      (ConLeche.checkSumCtors (fueledOpsM μ) env₀ env TP lpsP nP nIdx resSortP isProp large
        cvTaP csP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hstep, F, ctorsAP, sortssP, hF, h1, h2⟩ := checkSumCtors_spec fe₀ fe hμ hk henv T TP
    lps lpsP nP nIdx resSort resSortP isProp large cvTa cvTaP env₀ cs csP
    (Expr.WScoped.of_not_hasFvar hTf) s₀ s' r hok hpre hrun
  exact ⟨hstep, (ctorsAP, sortssP), ⟨h1, h2⟩, F,
    by rw [ConLeche.checkSumCtors_datF]; exact hF⟩

end ConRon.Bridge.Inductives
