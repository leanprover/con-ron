/-
# `ConRon.Bridge.Inductives.SumInstall` — Theorem 1 for the block install's shared stages

`Arena/Inductives/SumInstall.lean`'s twins against
`ConLeche/Kernel/Inductives/SumInstall.lean` (and the `…F` `abbrev`s of
`SumInstallF.lean`, which are the same functions — task #97d-2's deviation 1).
These are the shared stages the block's check runs (`checkBlockTele`,
`checkBlockCtors`, `checkBlockIdxSorts`): the former's telescope, the
per-field universe bound, the constructors' stage, the constructors consed and
the stored rules.

**Mostly CORE grade.**  `checkStructFieldSortsI` calls `inferTypeCore` and
`ensureSort`, `checkSumCtor` calls them and the constant check — so their
frame is `CoreStep` and their hypothesis is `CoreSpec`.  `checkSumTele`,
`consSumCtors` and `sumRules` are pure on both sides, and the field and index
resolution walks are pure grade.  The last section restates every core-grade
statement as a `CSpecF` against con-leche's `FueledM` function (task #105).
-/
module

import ConRon.Bridge.Inductives.StructInstall
import ConRon.Bridge.Checker.Base
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Denote.IndFrame
import ConRon.Bridge.Inductives.FieldTele
import ConRon.Bridge.Inductives.StructParts
public import ConRon.Bridge.Inductives.Rel
import ConLeche.Verify.Cached.BridgeCS3
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Cached
public import ConRon.Bridge.Core.Walks.Frame
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## Opened telescopes' variable types -/

/-- con-leche: ConLeche/Verify/Denote/IndFrame.lean:305 openPisAtFvars_typeWScoped —
**an opened telescope's variables carry types scoped at their own frame**. -/
theorem openers_typeD_WScoped {n off : Nat} {e : ConLeche.Expr} {fvs : List ConLeche.Expr}
    {body : ConLeche.Expr}
    (h : ConLeche.openPisAtFvars n e off = some (fvs, body)) (he : ConLeche.Expr.WScoped off e) :
    ∀ (i : Nat) (x : ConLeche.Expr), fvs[i]? = some x → ConLeche.Expr.WScoped (off + i) x.fvarTypeD :=
  ConLeche.openPisAtFvars_typeWScoped n h he

/-! ## The former's telescope -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:33-38 checkSumTele
The type former's stage: `n` Π binders ending in a sort, the former as it is
(`reduceMember` has put it at its telescope).  Pure on both sides: the twin
reads the residual's tag and its sort. -/
theorem checkSumTele_spec (n : Nat) (cvTa₀ : IConstantVal) (cvTa₀P : ConstantVal) :
    PSpec (fun st => Frontend.denoteCV st cvTa₀ = some cvTa₀P)
      (Arena.checkSumTele n cvTa₀)
      (fun st r => ∃ sP, (ConLeche.checkSumTele n cvTa₀P : CheckM _) = .ok (cvTa₀P, sP) ∧
        Frontend.denoteCV st r.1 = some cvTa₀P ∧ denoteL st.ls r.2 = some sP) := by
  intro s₀ s' r hok hcv0 hrun
  simp only [Arena.checkSumTele] at hrun
  obtain ⟨sq, s₁, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hsq⟩ := stripPis_pstep hok (denoteCV_type hcv0) k1
  rw [hs1] at z1
  cases sq with
  | none => exact absurd z1 (fun h => AM.fail_ok h)
  | some q =>
  obtain ⟨bs, body⟩ := q
  obtain ⟨xs, x, hxs, -, hbody⟩ := denoteBP_some hsq
  dsimp only at z1
  by_cases htg : (body.tag == ETag.sort) = true
  · rw [ite_eq_left htg] at z1
    obtain ⟨o, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨hs2, ho⟩ := AM.of_run (P := fun t => t = s₀) rfl k2 (viewSort_spec s₀ body)
    subst hs2
    cases o with
    | none => exact absurd z2 (fun h => failDanglingE_ok h)
    | some u =>
      have hv := view_of_viewSort_tag htg ho.symm
      obtain ⟨uP, rfl, hu⟩ := denote_sort_inv hok.wf hv hbody
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
      refine ⟨PStep.refl hok, uP, ?_, hcv0, hu⟩
      simp only [ConLeche.checkSumTele, hxs, pure, Except.pure]
  · rw [ite_eq_right htg] at z1
    exact absurd z1 (fun h => AM.fail_ok h)

/-! ## The fields' universe bound -/

/-- con-leche: none — **an expression-handle list's `contains` is the
denotation's**, at both signs: `beq_of_denoteE` at every element (the store is
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
        simp only [List.contains_cons, beq_of_denoteE hwf hh hx, ih hr hh]

/-- con-leche: none — `checkStructFieldSortsI` is monotone in the fuel of its
`inferType`/`ensureSort`. -/
theorem checkStructFieldSortsI_mono {μ : CheckMode} {env : Env} {F F' : Nat}
    (hle : F ≤ F') {isProp large : Bool} {sP : Level} {nP : Nat}
    {fvsP idxArgsP : List Expr} : ∀ {j : Nat},
    ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env isProp large sP nP
      fvsP idxArgsP j = .ok () →
    ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F') env isProp large sP nP
      fvsP idxArgsP j = .ok () := by
  intro j
  induction j with
  | zero => intro h; exact h
  | succ j ih =>
    intro h
    simp only [ConLeche.checkStructFieldSortsI, ConLeche.fueledOps, bind, Except.bind]
      at h ⊢
    cases ha : fvsP[j]? with
    | none =>
      simp [ha, ConLeche.unwrapOr, throw, throwThe, MonadExceptOf.throw] at h
    | some a =>
    simp only [ha, ConLeche.unwrapOr, pure, Except.pure] at h ⊢
    cases hi : ConLeche.inferTypeCore μ false env F (nP + j) a.fvarTypeD with
    | error x => rw [hi] at h; exact nomatch h
    | ok t =>
    rw [hi] at h; rw [ConLeche.inferTypeCore_mono hle hi]
    dsimp only at h ⊢
    cases he : ConLeche.ensureSortCore μ false env F (nP + j) t with
    | error x => rw [he] at h; exact nomatch h
    | ok u =>
    rw [he] at h; rw [ConLeche.ensureSortCore_mono hle he]
    dsimp only at h ⊢
    cases hr : ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env isProp
        large sP nP fvsP idxArgsP j with
    | error x =>
      simp only [ConLeche.fueledOps] at hr
      rw [hr] at h
      exfalso
      revert h
      repeat' split
      all_goals simp_all [throw, throwThe, MonadExceptOf.throw]
    | ok rest =>
      have hr' := ih hr
      simp only [ConLeche.fueledOps] at hr hr'
      rw [hr] at h; rw [hr']; exact h

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:75-100 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-48 checkStructFieldSortsIF
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:50-68 checkStructFieldSortsIFA
Each field's sort, checked against the family's — official's
subsingleton-elimination criterion at a one-constructor block.

**Proof:** a `Nat` recursion over `CoreSpec.knot`'s
`infer` slot, `CoreSpec.sort`'s `EnsureSortSpec`, `fvarTypeD_run`, the
universe comparison (`readLevel` twice and `liftFueled`), `lvlEq?_spec` at the
zero pin, and `denoteEList_contains` for the index test — one fuel for the
walk by `checkStructFieldSortsI_mono` at `max`.

**Two preconditions**: `EnvWF env`
and, for each field it infers, the scope of that field's type at its depth —
`Expr.WScoped (nP + i) fvsP[i].fvarTypeD`, exactly `checkStructDomsAt_spec`'s
hypothesis on its left column. -/
theorem checkStructFieldSortsI_spec {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env) (isProp large : Bool)
    (s : LIdx) (sP : Level) (nP : Nat) (fvs idxArgs : List EIdx)
    (fvsP idxArgsP : List Expr) (j : Nat)
    (hws : ∀ i, i < j → ∀ a, fvsP[i]? = some a → Expr.WScoped (nP + i) a.fvarTypeD) :
    CSpec env fe
      (fun st => denoteL st.ls s = some sP ∧
        Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st idxArgs = some idxArgsP)
      (Arena.checkStructFieldSortsI .verified fe isProp large s nP fvs idxArgs j)
      (fun _ _ => ∃ F,
        ConLeche.checkStructFieldSortsI (ConLeche.fueledOps .verified F) env isProp
          large sP nP fvsP idxArgsP j = .ok ()) := by
  have hknot := hk.knot env fe henv
  have hsort := hk.sort env fe henv
  induction j with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.checkStructFieldSortsI] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, 0, rfl⟩
  | succ j ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hs, hfvs, hidx⟩ := hpre
    simp only [Arena.checkStructFieldSortsI] at hrun
    obtain ⟨fv, s1, k1, z1⟩ := AM.bind_ok hrun
    cases hfv : fvs[j]? with
    | none =>
      rw [hfv] at k1; simp only [Arena.unwrapOr] at k1; exact absurd k1 (fun h => AM.fail_ok h)
    | some fv' =>
    rw [hfv] at k1; simp only [Arena.unwrapOr] at k1
    obtain ⟨rfl, hs1⟩ := AM.pure_ok k1
    rw [hs1] at z1
    obtain ⟨aP, haP, hda⟩ := ExprOps.denoteEList_getElem? fvs fvsP hfvs j fv hfv
    obtain ⟨t, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨hs2, ht⟩ := fvarTypeD_run hok.state hda k2
    rw [hs2] at z2
    have hwsa := hws j (Nat.lt_succ_self j) aP haP
    obtain ⟨ty, s3, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨hok3, hx3, hp3, hsim3⟩ := AM.of_run (P := fun u => u = s₀)
      (Q := fun r u => CheckOK false env fe u ∧ Ext s₀.store u.store ∧
        u.pins = s₀.pins ∧
        Core.SimE (ConLeche.inferTypeCore .verified false env) (nP + j) aP.fvarTypeD u.store r)
      rfl k3 (hknot.infer s₀ (nP + j) t aP.fvarTypeD hok ht hwsa)
    have c3 : CoreStep env fe s₀ s3 := ⟨hok3, hx3, hp3⟩
    obtain ⟨tyP, htyP, hwsty, F1, hF1⟩ := hsim3
    obtain ⟨u, s4, k4, z4⟩ := AM.bind_ok z3
    obtain ⟨hok4, hx4, hp4, hsim4⟩ := AM.of_run (P := fun u => u = s3)
      (Q := fun r u => CheckOK false env fe u ∧ Ext s3.store u.store ∧
        u.pins = s3.pins ∧
        SimL (ConLeche.ensureSortCore .verified false env) (nP + j) tyP u.store r)
      rfl k4 (hsort s3 (nP + j) ty tyP hok3 htyP hwsty)
    have c4 : CoreStep env fe s₀ s4 := c3.trans ⟨hok4, hx4, hp4⟩
    obtain ⟨uP, huP, F2, hF2⟩ := hsim4
    -- the common tail: the recursive call
    have tail : ∀ (s5 : AState), CoreStep env fe s4 s5 →
        Arena.checkStructFieldSortsI .verified fe isProp large s nP fvs idxArgs j s5
          = .ok (r, s') →
        CoreStep env fe s₀ s' ∧ ∃ F3,
          ConLeche.checkStructFieldSortsI (ConLeche.fueledOps .verified F3) env isProp
            large sP nP fvsP idxArgsP j = .ok () := by
      intro s5 c5 z5
      have c05 := c4.trans c5
      obtain ⟨c6, F3, hF3⟩ := ih (fun i hi => hws i (Nat.lt_succ_of_lt hi))
        s5 s' r c05.ok ⟨denoteL_ext hs c05.ext, denoteEList_ext c05.ext _ _ hfvs,
          denoteEList_ext c05.ext _ _ hidx⟩ z5
      exact ⟨c05.trans c6, F3, hF3⟩
    have hF1' : ∀ F, F1 ≤ F →
        ConLeche.inferTypeCore .verified false env F (nP + j) aP.fvarTypeD = .ok tyP :=
      fun F hle => ConLeche.inferTypeCore_mono hle hF1
    have hF2' : ∀ F, F2 ≤ F → ConLeche.ensureSortCore .verified false env F (nP + j) tyP = .ok uP :=
      fun F hle => ConLeche.ensureSortCore_mono hle hF2
    cases isProp with
    | false =>
      simp only [Bool.not_false, ite_true] at z4
      obtain ⟨lu, s5, k5, z5⟩ := AM.bind_ok z4
      have hlu := (Core.readLevelM_denote hok4.caches.readL k5).1
      have c5 : CoreStep env fe s4 s5 := (readLevelM_pstep hok4.state k5).toCore hok4
      obtain ⟨ls, s6, k6, z6⟩ := AM.bind_ok z5
      have hls := (Core.readLevelM_denote c5.ok.caches.readL k6).1
      have c6 : CoreStep env fe s5 s6 := (readLevelM_pstep c5.ok.state k6).toCore c5.ok
      obtain ⟨b, s7, k7, z7⟩ := AM.bind_ok z6
      have hlu' : lu = uP := Option.some.inj (hlu.symm.trans huP)
      have hls' : ls = sP :=
        Option.some.inj (hls.symm.trans (denoteL_ext hs (c4.ext.trans c5.ext)))
      subst hlu' hls'
      cases hleq : Level.leq lu ls with
      | none =>
        rw [hleq] at k7; simp only [Arena.liftFueled] at k7
        exact absurd k7 (fun h => AM.fail_ok h)
      | some bb =>
      rw [hleq] at k7; simp only [Arena.liftFueled] at k7
      cases bb with
      | false =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k7
        simp only [Bool.false_eq_true, ite_false] at z7
        obtain ⟨_, _, k, _⟩ := AM.bind_ok z7
        exact absurd k (fun h => AM.fail_ok h)
      | true =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k7
      simp only [ite_true] at z7
      obtain ⟨_, s8, k8, z8⟩ := AM.bind_ok z7
      obtain ⟨-, rfl⟩ := AM.pure_ok k8
      obtain ⟨c, F3, hF3⟩ := tail _ (c5.trans c6) z8
      refine ⟨c, max (max F1 F2) F3, ?_⟩
      have e1 := hF1' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      have e2 := hF2' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      have e3 := checkStructFieldSortsI_mono (Nat.le_max_right (max F1 F2) F3) hF3
      simp only [ConLeche.fueledOps] at e3
      generalize max (max F1 F2) F3 = Fm at e1 e2 e3 ⊢
      simp only [ConLeche.checkStructFieldSortsI, haP, ConLeche.unwrapOr, ConLeche.fueledOps,
        bind, Except.bind, pure, Except.pure, e1, e2]
      simp [ConLeche.liftFueled, hleq, e3, pure, Except.pure]
    | true =>
    cases large with
    | false =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at z4
      obtain ⟨_, s5, k5, z5⟩ := AM.bind_ok z4
      obtain ⟨-, rfl⟩ := AM.pure_ok k5
      obtain ⟨c, F3, hF3⟩ := tail _ (CoreStep.refl hok4) z5
      refine ⟨c, max (max F1 F2) F3, ?_⟩
      have e1 := hF1' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      have e2 := hF2' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      have e3 := checkStructFieldSortsI_mono (Nat.le_max_right (max F1 F2) F3) hF3
      simp only [ConLeche.fueledOps] at e3
      generalize max (max F1 F2) F3 = Fm at e1 e2 e3 ⊢
      simp only [ConLeche.checkStructFieldSortsI, haP, ConLeche.unwrapOr, ConLeche.fueledOps,
        bind, Except.bind, pure, Except.pure, e1, e2]
      simp [e3]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at z4
      obtain ⟨z, s5, k5, z5⟩ := AM.bind_ok z4
      obtain ⟨hs5, hz⟩ := zeroLevel_run hok4.pins k5
      rw [hs5] at z5
      obtain ⟨vv, s6, k6, z6⟩ := AM.bind_ok z5
      obtain ⟨hok6, hst6, hp6, lu, lz, hlu, hlz, hvv⟩ :=
        AM.of_run (P := fun t => t = s4) rfl k6 (Core.lvlEq?_spec s4 u z hok4)
      have hlu' : lu = uP := Option.some.inj (hlu.symm.trans huP)
      have hlz' : lz = .zero := Option.some.inj (hlz.symm.trans hz)
      subst hlu' hlz'
      have c6 : CoreStep env fe s4 s6 := ⟨hok6, by rw [hst6]; exact Ext.refl _, hp6⟩
      have hcont : idxArgs.contains fv = idxArgsP.contains aP :=
        denoteEList_contains hok4.state.wf (denoteEList_ext c4.ext _ _ hidx)
          (denote_ext hda c4.ext)
      rw [hvv, hcont] at z6
      split at z6
      case isFalse hn =>
        obtain ⟨_, _, k, _⟩ := AM.bind_ok z6; exact absurd k (fun h => AM.fail_ok h)
      case isTrue hy =>
      obtain ⟨_, s8, k8, z8⟩ := AM.bind_ok z6
      obtain ⟨-, rfl⟩ := AM.pure_ok k8
      obtain ⟨c, F3, hF3⟩ := tail _ c6 z8
      refine ⟨c, max (max F1 F2) F3, ?_⟩
      have e1 := hF1' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      have e2 := hF2' (max (max F1 F2) F3)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      have e3 := checkStructFieldSortsI_mono (Nat.le_max_right (max F1 F2) F3) hF3
      simp only [ConLeche.fueledOps] at e3
      generalize max (max F1 F2) F3 = Fm at e1 e2 e3 ⊢
      simp only [ConLeche.checkStructFieldSortsI, haP, ConLeche.unwrapOr, ConLeche.fueledOps,
        bind, Except.bind, pure, Except.pure, e1, e2]
      simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hy
      simp [e3]
      intro hn
      exact hy.resolve_left hn

/-! ## The constructors' stage -/

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
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
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
    obtain ⟨t, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, ht⟩ := fvarTypeD_run hok hx1 k1
    obtain ⟨ts, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hts⟩ := fvarTypeDs_run xs rest hok hxs k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
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
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
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
    obtain ⟨t, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, ht⟩ := fvarTypeD_run hok.state hx1 k1
    obtain ⟨c, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hc⟩ := constsResolveFFast_pstep hok ht k2
    have hok₂ := hok.mono p2.ok p2.ext p2.pins
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at z2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
      exact ⟨p2, by simp [List.all_cons, ← hc]⟩
    | true =>
      simp only [ite_true] at z2
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
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
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
    obtain ⟨c, s₂, k2, z2⟩ := AM.bind_ok hrun
    obtain ⟨p2, hc⟩ := constsResolveFFast_pstep hok hx1 k2
    have hok₂ := hok.mono p2.ok p2.ext p2.pins
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at z2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
      exact ⟨p2, by simp [List.all_cons, ← hc]⟩
    | true =>
      simp only [ite_true] at z2
      obtain ⟨p3, hr⟩ := idxArgsResolve_spec xs rest hok₂
        (denoteEList_ext p2.ext _ _ hxs) z2
      exact ⟨p2.trans p3, by simp [List.all_cons, ← hc, hr]⟩

/-- con-leche: ConLeche/Verify/BridgeDecl.lean checkSumCtor_datF — `checkSumCtor`
at `fueledOps` is monotone in the fuel, through the `FueledM` run's own
monotonicity. -/
theorem checkSumCtor_up {μ : CheckMode} {F G : Nat} {env₀ env : Env} {T : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nIdx : Nat} {rs : Level} {isProp large : Bool}
    {cvC : ConstantVal} {nF : Nat} {cvTa : ConstantVal}
    (hle : F ≤ G)
    (h : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env T lps nP nIdx rs isProp
      large cvC nF cvTa = .ok ()) :
    ConLeche.checkSumCtor (ConLeche.fueledOps μ G) env₀ env T lps nP nIdx rs isProp
      large cvC nF cvTa = .ok () := by
  rw [← ConLeche.checkSumCtor_datF] at h ⊢
  exact (ConLeche.checkSumCtor (ConLeche.fueledOpsM μ) env₀ env T lps nP nIdx rs isProp
    large cvC nF cvTa).property hle h

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:70-100 checkSumCtorF
One constructor checked: its constant check (stored as declared), its
residual, its parameter domains, its field and index resolution, and its
field sorts.

**Proof:** over `checkConstantVal_bridge`, `checkStructDomsAt_spec`
(`Bridge/Inductives/StructInstall.lean`), `checkStructFieldSortsI_spec`,
`fieldDomsResolve_spec`, `idxArgsResolve_spec` and `structCtorResidOk_spec`. -/
theorem checkSumCtor_spec {env : Env} (fe₀ fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvC : IConstantVal) (cvCP : ConstantVal) (nF : Nat)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env)
    (hws : Expr.WScoped 0 cvTaP.type) :
    CSpec env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        Frontend.denoteCV st cvC = some cvCP ∧
        Frontend.denoteCV st cvTa = some cvTaP ∧
        IFEnvOKS env₀ fe₀ st)
      (Arena.checkSumCtor .verified fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa)
      (fun _ _ => ∃ F,
        ConLeche.checkSumCtor (ConLeche.fueledOps .verified F) env₀ env TP lpsP nP
          nIdx resSortP isProp large cvCP nF cvTaP = .ok ()) := by
  intro s₀ s' r hck hpre hrun
  obtain ⟨hT, hlps, hrs, hcvC, hcvTa, hok₀⟩ := hpre
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  simp only [Arena.checkSumCtor] at hrun
  -- the constructor's own check (stored as declared)
  obtain ⟨_, s₂, k1, z2⟩ := AM.bind_ok hrun
  obtain ⟨c12, F₁, hF₁⟩ := checkConstantVal_bridge hk hck henv hcvC k1
  have hcA : Frontend.denoteCV s₂.store cvC = some cvCP := denoteCV_ext hcvC c12.ext
  have x1 := c12.ext
  -- the stored constructor is a checked constant: closed
  have hwsA : Expr.WScoped 0 cvCP.type :=
    Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  -- the result shape
  obtain ⟨o3, s₃, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨hs3, ho3⟩ := stripPis_pstep c12.ok.state (denoteCV_type hcA) k3
  rw [hs3] at z3
  obtain ⟨q3, s₄, k4, z4⟩ := AM.bind_ok z3
  cases o3 with
  | none => simp only [Arena.unwrapOr] at k4; exact absurd k4 (fun h => AM.fail_ok h)
  | some o3' =>
  simp only [Arena.unwrapOr] at k4
  obtain ⟨hq3, hs4⟩ := AM.pure_ok k4
  subst hq3
  rw [hs4] at z4
  obtain ⟨cbs, cbody⟩ := q3
  obtain ⟨cxs, cbodyP, hsp, -, hcb⟩ := denoteBP_some ho3
  dsimp only at z4
  have x02 := c12.ext
  obtain ⟨b5, s₅, k5, z5⟩ := AM.bind_ok z4
  obtain ⟨p5, hb5⟩ := structCtorResidOk_spec T TP lps lpsP nP nF nIdx cbody cbodyP s₂ s₅ b5
    c12.ok.state ⟨denoteN_ext hT x02, denoteNListE_ext x02 _ _ hlps, hcb⟩ k5
  obtain ⟨hr5, z6⟩ := AM.dunless_ok hnever z5
  replace z6 := AM.pure_bind_ok z6
  rw [hb5] at hr5
  have c5 := c12.trans (p5.toCore c12.ok)
  -- the constructor's parameters, opened
  obtain ⟨o6, s₆, k6, z7⟩ := AM.bind_ok z6
  obtain ⟨p6, ho6⟩ := openPisAtFvarsF_run c5.ok.state
    (denote_ext (denoteCV_type hcA) p5.ext) k6
  obtain ⟨cq, s₇, k7, z8⟩ := AM.bind_ok z7
  cases o6 with
  | none => simp only [Arena.unwrapOr] at k7; exact absurd k7 (fun h => AM.fail_ok h)
  | some o6' =>
  simp only [Arena.unwrapOr] at k7
  obtain ⟨hq6, hs7⟩ := AM.pure_ok k7
  subst hq6
  rw [hs7] at z8
  obtain ⟨cfvsP, crestP, hcq, hcfvs, hcrest⟩ := denoteOpen_some_inv ho6
  -- the former's parameters, opened
  have c6 := c5.trans (p6.toCore c5.ok)
  obtain ⟨o8, s₈, k8, z9⟩ := AM.bind_ok z8
  obtain ⟨p8, ho8⟩ := openPisAtFvarsF_run c6.ok.state
    (denote_ext (denoteCV_type hcvTa) (x1.trans (p5.ext.trans p6.ext))) k8
  obtain ⟨tq, s₉, k9, z10⟩ := AM.bind_ok z9
  cases o8 with
  | none => simp only [Arena.unwrapOr] at k9; exact absurd k9 (fun h => AM.fail_ok h)
  | some o8' =>
  simp only [Arena.unwrapOr] at k9
  obtain ⟨hq8, hs9⟩ := AM.pure_ok k9
  subst hq8
  rw [hs9] at z10
  obtain ⟨tfvsP, trestP, htq, htfvs, htrest⟩ := denoteOpen_some_inv ho8
  have c8 := c6.trans (p8.toCore c6.ok)
  -- the domains the pins compare
  obtain ⟨doms, s₁₀, k10, z11⟩ := AM.bind_ok z10
  obtain ⟨p10, hdoms⟩ := fvarTypeDs_run tq.1 tfvsP c8.ok.state htfvs k10
  have c10 := c8.trans (p10.toCore c8.ok)
  obtain ⟨u11, s₁₁, k11, z12⟩ := AM.bind_ok z11
  have x6_10 : Ext s₆.store s₁₀.store := p8.ext.trans p10.ext
  obtain ⟨c11, F₃, hF₃⟩ := checkStructDomsAt_spec fe hk henv 0 cq.1 doms cfvsP
    (tfvsP.map Expr.fvarTypeD) nP (by
      intro i _ a b ha hb
      refine ⟨ConRon.Bridge.Inductives.openers_typeD_WScoped hcq hwsA i a ha, ?_⟩
      rw [List.getElem?_map] at hb
      cases hti : tfvsP[i]? with
      | none => rw [hti] at hb; exact nomatch hb
      | some t =>
        rw [hti] at hb
        obtain rfl := (Option.some.inj hb).symm
        exact ConRon.Bridge.Inductives.openers_typeD_WScoped htq hws i t hti) s₁₀ s₁₁ u11 c10.ok
    ⟨denoteEList_ext x6_10 _ _ hcfvs, hdoms⟩ k11
  have c11' := c10.trans c11
  -- the fields, opened past the parameters
  obtain ⟨o12, s₁₂, k12, z13⟩ := AM.bind_ok z12
  obtain ⟨p12, ho12⟩ := openPisAtFvarsF_run c11'.ok.state
    (denote_ext hcrest ((p8.ext.trans p10.ext).trans c11.ext)) k12
  obtain ⟨xq, s₁₃, k13, z14⟩ := AM.bind_ok z13
  cases o12 with
  | none => simp only [Arena.unwrapOr] at k13; exact absurd k13 (fun h => AM.fail_ok h)
  | some o12' =>
  simp only [Arena.unwrapOr] at k13
  obtain ⟨hq12, hs13⟩ := AM.pure_ok k13
  subst hq12
  rw [hs13] at z14
  obtain ⟨xfvsP, xrestP, hxq, hxfvs, hxrest⟩ := denoteOpen_some_inv ho12
  have c12' := c11'.trans (p12.toCore c11'.ok)
  -- the family head and the residual's spine
  obtain ⟨us, s₁₄, k14, z15⟩ := AM.bind_ok z14
  have x0_12 := c12'.ext
  obtain ⟨p14, hus⟩ := paramLevels_spec lps lpsP s₁₂ s₁₄ us c12'.ok.state
    (denoteNListE_ext x0_12 _ _ hlps) k14
  obtain ⟨hd, s₁₅, k15, z16⟩ := AM.bind_ok z15
  obtain ⟨p15, hhd⟩ := internConstE_run p14.ok (denoteN_ext hT (x0_12.trans p14.ext)) hus k15
  have c15 := c12'.trans ((p14.trans p15).toCore c12'.ok)
  have x12_15 : Ext s₁₂.store s₁₅.store := p14.ext.trans p15.ext
  obtain ⟨xfn, s₁₆, k16, z17⟩ := AM.bind_ok z16
  obtain ⟨hs16, hxfn⟩ := getAppFn_run c15.ok.state (denote_ext hxrest x12_15) k16
  rw [hs16] at z17
  obtain ⟨xargs, s₁₇, k17, z18⟩ := AM.bind_ok z17
  obtain ⟨hs17, hxargs⟩ := getAppArgs_run c15.ok.state (denote_ext hxrest x12_15) k17
  rw [hs17] at z18
  have hwf15 := c15.ok.state.wf
  have x7_15 : Ext s₆.store s₁₅.store :=
    (p8.ext.trans p10.ext).trans (c11.ext.trans (p12.ext.trans x12_15))
  have hg := AM.dunless_ok hnever z18
  obtain ⟨hg1, z19⟩ := hg
  replace z19 := AM.pure_bind_ok z19
  rw [beq_of_denoteE hwf15 hxfn hhd,
    beq_of_denoteEList hwf15 (denoteEList_take hxargs nP) (denoteEList_ext x7_15 _ _ hcfvs),
    show xargs.length = xrestP.getAppArgs.length from
      (ExprOps.denoteEList_length _ _ hxargs).symm] at hg1
  -- the fields' domains resolve before the block
  have hread₀ : ReadOK env₀ fe₀ s₁₅ :=
    ⟨c15.ok.state, c15.ok.pins, hok₀.mono c15.ext s₁₅ rfl⟩
  obtain ⟨b20, s₂₀, k20, z20⟩ := AM.bind_ok z19
  obtain ⟨p20, hb20⟩ := fieldDomsResolve_spec xq.1 xfvsP hread₀
    (denoteEList_ext x12_15 _ _ hxfvs) k20
  obtain ⟨hg2, z21⟩ := AM.dunless_ok hnever z20
  replace z21 := AM.pure_bind_ok z21
  rw [hb20] at hg2
  obtain ⟨b22, s₂₂, k22, z22⟩ := AM.bind_ok z21
  obtain ⟨p22, hb22⟩ := idxArgsResolve_spec (xargs.drop nP) (xrestP.getAppArgs.drop nP)
    (hread₀.mono p20.ok p20.ext p20.pins)
    (denoteEList_drop (denoteEList_ext p20.ext _ _ hxargs) nP) k22
  obtain ⟨hg3, z23⟩ := AM.dunless_ok hnever z22
  replace z23 := AM.pure_bind_ok z23
  rw [hb22] at hg3
  -- the field sorts
  have c22 := c15.trans ((p20.trans p22).toCore c15.ok)
  have x15_22 : Ext s₁₅.store s₂₂.store := p20.ext.trans p22.ext
  have hxpos : ∀ i, i < nF → ∀ a, xfvsP[i]? = some a → Expr.WScoped (nP + i) a.fvarTypeD := by
    intro i _ a ha
    have hwsc : Expr.WScoped nP crestP := by
      have := (ConLeche.openPisAtFvars_WScoped _ _ _ hcq hwsA).2
      simpa using this
    exact ConRon.Bridge.Inductives.openers_typeD_WScoped hxq hwsc i a ha
  obtain ⟨c23, F₄, hF₄⟩ := checkStructFieldSortsI_spec fe hk henv isProp large
    resSort resSortP nP xq.1 (xargs.drop nP) xfvsP (xrestP.getAppArgs.drop nP) nF hxpos
    s₂₂ s' r c22.ok
    ⟨denoteL_ext hrs c22.ext, denoteEList_ext (x12_15.trans x15_22) _ _ hxfvs,
      denoteEList_drop (denoteEList_ext x15_22 _ _ hxargs) nP⟩ z23
  refine ⟨c22.trans c23, max F₁ (max F₃ F₄), ?_⟩
  have g₁ := checkConstantVal_mono (show F₁ ≤ max F₁ (max F₃ F₄) by omega) hF₁
  have g₃ := checkStructDomsAt_mono (show F₃ ≤ max F₁ (max F₃ F₄) by omega) hF₃
  have g₄ := checkStructFieldSortsI_mono (show F₄ ≤ max F₁ (max F₃ F₄) by omega) hF₄
  simp only [ConLeche.checkSumCtor, bind, Except.bind, g₁, hsp, ConLeche.unwrapOr, pure,
    Except.pure, hr5, ite_true, hcq, htq]
  rw [g₃]
  simp only [hxq]
  rw [ite_eq_left hg1, ite_eq_left hg2, ite_eq_left hg3, g₄]

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:149-161 checkSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:102-112 checkSumCtorsF
The whole constructor list.

**Proof:** a list induction over `checkSumCtor_spec`. -/
theorem checkSumCtors_spec {env : Env} (fe₀ fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
    (hws : Expr.WScoped 0 cvTaP.type) :
    CSpec env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteCtors st cs = some csP ∧
        IFEnvOKS env₀ fe₀ st)
      (Arena.checkSumCtors .verified fe₀ fe T lps nP nIdx resSort isProp large cvTa cs)
      (fun _ _ => ∃ F,
        ConLeche.checkSumCtors (ConLeche.fueledOps .verified F) env₀ env TP lpsP nP
          nIdx resSortP isProp large cvTaP csP = .ok ()) := by
  induction cs generalizing csP with
  | nil =>
    intro s₀ s' r hck hpre hrun
    obtain ⟨-, -, -, -, hcs, -⟩ := hpre
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.checkSumCtors] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hck, 0, rfl⟩
  | cons c cs ih =>
    intro s₀ s' r hck hpre hrun
    obtain ⟨hT, hlps, hrs, hcvTa, hcs, hok₀⟩ := hpre
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
    obtain ⟨t1, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, F₁, hF₁⟩ := checkSumCtor_spec fe₀ fe hk henv T TP
      lps lpsP nP nIdx resSort resSortP isProp large cv cP n cvTa cvTaP env₀ hws s₀ s₁ t1 hck
      ⟨hT, hlps, hrs, hcv, hcvTa, hok₀⟩ k1
    have x1 := c1.ext
    obtain ⟨c2, F₂, hF₂⟩ := ih restP s₁ s' r c1.ok
      ⟨denoteN_ext hT x1, denoteNListE_ext x1 _ _ hlps, denoteL_ext hrs x1,
        denoteCV_ext hcvTa x1, denoteCtors_ext x1 _ _ hrest, hok₀.mono x1⟩ z1
    refine ⟨c1.trans c2, max F₁ F₂, ?_⟩
    have g₁ := checkSumCtor_up (Nat.le_max_left F₁ F₂) hF₁
    have g₂ : ConLeche.checkSumCtors (ConLeche.fueledOps .verified (max F₁ F₂)) env₀ env TP lpsP nP
        nIdx resSortP isProp large cvTaP restP = .ok () := by
      rw [← ConLeche.checkSumCtors_datF] at hF₂ ⊢
      exact (ConLeche.checkSumCtors (ConLeche.fueledOpsM .verified) env₀ env TP lpsP nP nIdx resSortP
        isProp large cvTaP restP).property (Nat.le_max_right F₁ F₂) hF₂
    simp only [ConLeche.checkSumCtors, bind, Except.bind, g₁, g₂]

/-! ## The constructors consed, and the rules -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:163-166 consSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:114-117 consSumCtorsF
The constructors pushed into the index, each with its family `T`.  PURE on both
sides. -/
theorem consSumCtors_spec (st : EStore) (nP : Nat) {T : NIdx} {TP : ConLeche.Name}
    (hT : denoteN st.ns T = some TP)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
    (fe : IFEnv) (env : Env) (hwf : StoreWF st) (hcs : denoteCtors st cs = some csP)
    (hfe : EnvRel env fe st) :
    InstRel (fun e => e = ConLeche.consSumCtors nP TP csP env) st
      (Arena.consSumCtors nP T cs fe) := by
  induction cs generalizing csP fe env with
  | nil =>
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    exact ⟨env, hfe, rfl⟩
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
    have hci : Frontend.denoteCI st (.ctorInfo cv nP n T) = some (.ctorInfo cP nP n TP) := by
      simp only [Frontend.denoteCI, hcv, hT]
    exact ih restP (fe.push (.ctorInfo cv nP n T)) ⟨.ctorInfo cP nP n TP :: env.consts, env.tables⟩
      hrest (hfe.push hwf hci)

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:124-130 sumRules
The stored rules denote: pure on both sides, constructor `j`'s with the
right-hand side `j`, `.plain`. -/
theorem sumRules_denote {st : EStore} :
    ∀ (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
      (rhss : List EIdx) (rhssP : List Expr),
      denoteCtors st cs = some csP → Frontend.denoteEList st rhss = some rhssP →
      Frontend.denoteRules st (Arena.sumRules cs rhss) = some (ConLeche.sumRules csP rhssP)
  | [], csP, rhss, rhssP, hcs, _ => by
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.sumRules, ConLeche.sumRules, Frontend.denoteRules]
  | (cv, n) :: cs, csP, [], rhssP, hcs, hr => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hr
    subst hr
    simp only [denoteCtors] at hcs
    split at hcs
    · obtain rfl := (Option.some.inj hcs).symm
      simp only [Arena.sumRules, ConLeche.sumRules, Frontend.denoteRules]
    · exact nomatch hcs
  | (cv, n) :: cs, csP, rhs :: rhss, rhssP, hcs, hr => by
    simp only [denoteCtors] at hcs
    split at hcs
    · rename_i c rest hc hrest
      obtain rfl := (Option.some.inj hcs).symm
      simp only [Frontend.denoteEList] at hr
      cases h1 : denoteE st rhs with
      | none => rw [h1] at hr; simp at hr
      | some x =>
      cases h2 : Frontend.denoteEList st rhss with
      | none => rw [h1, h2] at hr; simp at hr
      | some xs =>
      rw [h1, h2] at hr
      obtain rfl := (Option.some.inj hr).symm
      simp only [Arena.sumRules, ConLeche.sumRules, Frontend.denoteRules, Frontend.denoteRule,
        denoteCV_name hc, Frontend.denoteFire, h1, sumRules_denote cs rest rhss xs hrest h2]
    · exact nomatch hcs

/-! ## The monad-generic forms (task #105)

The uniform route's con-leche stages are written over a `CheckerOps m`, and
its consumers (`checkBlockTele`, `checkBlockCtors`, `checkBlockIdxSorts`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`) run them at the monotone
fueled operations `fueledOpsM .verified`.  Each statement above concludes the pure
side's run at `fueledOps .verified F` for some `F`; the forms below restate it as a
`CSpecF` against the `FueledM` function, by that stage's `_datF` lemma
(`ConLeche/Verify/BridgeDecl.lean`).  The scoping hypotheses are stated as
con-leche's cached template states them (`ConLeche/Verify/Cached/
BridgeCS3.lean`'s `checkSumTeleS_spec`, `checkSumCtorsS_spec`;
`NestPosC.lean`'s `checkStructFieldSortsIS_spec`), and `checkSumTele`'s answer
carries the scope of the stored type. -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:33-38 checkSumTele
`checkSumTele_spec` against `checkSumTele` at `FueledM`, with the stored type's
scope: the former is returned as it is. -/
theorem checkSumTele_specF {env : Env} (fe : IFEnv)
    (n : Nat) (cvTa₀ : IConstantVal) (cvTa₀P : ConstantVal)
    (hws : Expr.WScoped 0 cvTa₀P.type) :
    CSpecF env fe
      (fun st => Frontend.denoteCV st cvTa₀ = some cvTa₀P)
      (Arena.checkSumTele n cvTa₀)
      (fun st r v => Frontend.denoteCV st r.1 = some v.1 ∧ denoteL st.ls r.2 = some v.2 ∧
        Expr.WScoped 0 v.1.type)
      (ConLeche.checkSumTele n cvTa₀P) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hstep, sP, hF, h1, h2⟩ :=
    checkSumTele_spec n cvTa₀ cvTa₀P s₀ s' r hok.state hpre hrun
  exact ⟨hstep.toCore hok, (cvTa₀P, sP), ⟨h1, h2, hws⟩, 0, by rw [checkSumTele_datF]; exact hF⟩

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:75-100 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-48 checkStructFieldSortsIF
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:50-68 checkStructFieldSortsIFA
`checkStructFieldSortsI_spec` against `checkStructFieldSortsI (fueledOpsM .verified)`,
the field scopes stated as `checkStructFieldSortsIS_sim`'s `hfvs`. -/
theorem checkStructFieldSortsI_specF {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env) (isProp large : Bool)
    (s : LIdx) (sP : Level) (nP : Nat) (fvs idxArgs : List EIdx)
    (fvsP idxArgsP : List Expr) (j : Nat)
    (hfvs : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x → Expr.WScoped (nP + i) x.fvarTypeD) :
    CSpecF env fe
      (fun st => denoteL st.ls s = some sP ∧
        Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st idxArgs = some idxArgsP)
      (Arena.checkStructFieldSortsI .verified fe isProp large s nP fvs idxArgs j)
      (fun _ _ _ => True)
      (ConLeche.checkStructFieldSortsI (fueledOpsM .verified) env isProp large sP nP fvsP idxArgsP j) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hstep, F, hF⟩ := checkStructFieldSortsI_spec fe hk henv isProp large s sP nP
    fvs idxArgs fvsP idxArgsP j (fun i _ a ha => hfvs i a ha) s₀ s' r hok hpre hrun
  exact ⟨hstep, (), trivial, F, by rw [checkStructFieldSortsI_datF]; exact hF⟩

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:149-161 checkSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:102-112 checkSumCtorsF
`checkSumCtors_spec` against `checkSumCtors (fueledOpsM .verified)` — the form the
uniform route's constructor stage (`checkBlockCtors`, run at the formers'
environment `env` with the pre-block `env₀`) consumes. -/
theorem checkSumCtors_specF {env : Env} (fe₀ fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
    (hTf : cvTaP.type.hasFvar = false) :
    CSpecF env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteCtors st cs = some csP ∧
        IFEnvOKS env₀ fe₀ st)
      (Arena.checkSumCtors .verified fe₀ fe T lps nP nIdx resSort isProp large cvTa cs)
      (fun _ _ _ => True)
      (ConLeche.checkSumCtors (fueledOpsM .verified) env₀ env TP lpsP nP nIdx resSortP isProp large
        cvTaP csP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hstep, F, hF⟩ := checkSumCtors_spec fe₀ fe hk henv T TP
    lps lpsP nP nIdx resSort resSortP isProp large cvTa cvTaP env₀ cs csP
    (Expr.WScoped.of_not_hasFvar hTf) s₀ s' r hok hpre hrun
  exact ⟨hstep, (), trivial, F, by rw [ConLeche.checkSumCtors_datF]; exact hF⟩

end ConRon.Bridge.Inductives
