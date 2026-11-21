/-
# `ConRon.Bridge.Modular.ReachValid` — the reach's validation of its records, Theorem 1 (task #166)

The twin's `validateCtx` (`Arena/Modular/Reach.lean`) accepting is upstream's
(`ConLeche/Driver/Reach.lean` `validateCtx`): every record `recordOk`.  Each clause is the
existing walk's Theorem 1 (`hasFvarFast_spec`, `looseBVarsBoundedFast_spec`,
`allLevelParamsDefined_run`, `stripLams_pstep`, `streamNestedOk_run`, `piResult_run`,
`getAppFn_run`, `litShapeOk_run`), in the Closure run style (`AM.bind_ok`); the twin's own
extra bounds (`rP + nfields < 2^64`, `numParams + 1 < 2^64`) only make it stricter.
-/
module

public import ConRon.Bridge.Modular.ReachTail
public import ConRon.Bridge.Inductives.StreamRecs
public import ConRon.Bridge.Inductives.XFreeIota
public import ConRon.Bridge.Checker.Install
import ConLeche.Verify.Cached.GuardsC
import ConRon.Bridge.ExprOps.Ranges
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Core.Walks.IotaLeaves
import ConRon.Bridge.Core.Walks.PropRead
import ConLeche.Verify.Cached.OpsC

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean ConRon.Bridge.Inductives

/-- con-leche: ConLeche/Driver/Reach.lean:104-107 exprOk — **an expression's syntactic
clauses**, read back: the twin's answer is upstream's, the store, caches and pins unmoved. -/
theorem exprOk_run {s s' : AState} {lps : List NIdx} {ks : List ConLeche.Name} {k : Nat}
    {e : EIdx} {x : Expr} {b : Bool} (hok : StateOK s)
    (hl : Frontend.denoteNList s.store.ns lps = some ks) (hd : denoteE s.store e = some x)
    (h : ConRon.Arena.Modular.exprOk lps k e s = .ok (b, s')) :
    s'.store = s.store ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      b = ConLeche.Driver.exprOk ks k x := by
  simp only [ConRon.Arena.Modular.exprOk] at h
  obtain ⟨b1, s1, h1, h2⟩ := AM.bind_ok h
  obtain ⟨e1, c1, p1, r1⟩ := AM.of_run (P := fun t => t = s) rfl h1
    (ExprOps.hasFvarFast_spec coreWalkFuel s e hok (by rw [hd]; rfl))
  have hr1 := r1 x hd
  have hok1 : StateOK s1 := ⟨by rw [e1]; exact hok.wf⟩
  cases b1 with
  | true =>
    simp only [↓reduceIte] at h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    refine ⟨e1, c1, p1, ?_⟩
    simp [ConLeche.Driver.exprOk, ← hr1]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind] at h2
    obtain ⟨b2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨e2, c2, p2, r2⟩ := AM.of_run (P := fun t => t = s1) rfl h3
      (ExprOps.looseBVarsBoundedFast_spec coreWalkFuel k s1 e hok1 (by rw [e1, hd]; rfl))
    have hr2 := r2 x (by rw [e1]; exact hd)
    cases b2 with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      refine ⟨e2.trans e1, c2.trans c1, p2.trans p1, ?_⟩
      simp [ConLeche.Driver.exprOk, ← hr1, ← hr2]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h4
      have hok2 : StateOK s2 := ⟨by rw [e2, e1]; exact hok.wf⟩
      obtain ⟨e3, c3, p3, r3⟩ := allLevelParamsDefined_run hok2 (by rw [e2, e1]; exact hl)
        (by rw [e2, e1]; exact hd) h4
      refine ⟨e3.trans (e2.trans e1), c3.trans (c2.trans c1), p3.trans (p2.trans p1), ?_⟩
      simp [ConLeche.Driver.exprOk, ← hr1, ← hr2, r3, ConLeche.Expr.allLevelParamsDefinedC_spec]

/-! ## The scratch flag -/

theorem XFree.ite' {α : Type} {c : Prop} [Decidable c] {t e : AM α} (ht : XFree t)
    (he : XFree e) : XFree (if c then t else e) := by
  split <;> assumption

/-- `xfree_auto`, with `if`s and `let`s taken apart too. -/
macro "xauto" : tactic => `(tactic| repeat (first
  | exact XFree.pure _
  | exact XFree.fail _
  | exact XFree.failDanglingE
  | exact XFree.get
  | assumption
  | (solve_by_elim (maxDepth := 2))
  | (refine XFree.ite' ?_ ?_)
  | (refine XFree.bind ?_ (fun _ => ?_))
  | split
  | (dsimp only)))

theorem XFree.pinAt' (k : Nat) : XFree (Arena.pinAt k) := by
  unfold Arena.pinAt; xfree_auto

theorem XFree.pinSortOne' : XFree Arena.pinSortOne := by
  unfold Arena.pinSortOne; xfree_auto

theorem XFree.emptyLevels' : XFree Arena.emptyLevels := by
  unfold Arena.emptyLevels
  first | xfree_auto | exact XFree.internLsNode _

theorem XFree.constE' (n : NIdx) : XFree (Arena.constE n) := by
  unfold Arena.constE
  exact XFree.bind XFree.emptyLevels' fun _ => XFree.internE _

theorem XFree.litShapeOk' (c : IConstantInfo) : XFree (Arena.litShapeOk c) := by
  have h1 := XFree.pinAt'; have h2 := XFree.pinSortOne'; have h3 := XFree.constE'
  have h4 := XFree.internE; have h5 := XFree.internLNode; have h6 := XFree.view'
  have h7 := XFree.internLsNode
  unfold Arena.litShapeOk Arena.natIndOk Arena.natZeroOk Arena.natSuccOk Arena.stringTyOk
    Arena.stringOfListTyOk Arena.listTyOk Arena.listNilTyOk Arena.listConsTyOk Arena.charTyOk
    Arena.charOfNatTyOk Arena.sortOne Arena.pinNat Arena.pinNatZero Arena.pinNatSucc
    Arena.pinString Arena.pinStringOfList Arena.pinList Arena.pinListNil Arena.pinListCons
    Arena.pinChar Arena.pinCharOfNat
  xauto

theorem XFree.streamNestedOk' (ty : EIdx) (mI rP : Nat) (fire : IRecRuleFire) :
    XFree (Arena.streamNestedOk ty mI rP fire) := by
  have h1 := XFree.stripPis; have h2 := XFree.viewBind; have h3 := XFree.getAppFn
  have h4 := XFree.viewConst; have h5 := XFree.getAppArgs; have h6 := XFree.liftLooseBVarsFast
  have h7 := XFree.internBVarE
  have h9 : ∀ us : LsIdx, XFree (Arena.viewLs us) := fun us => by unfold Arena.viewLs; xauto
  have hm : ∀ (n : Nat) (ps : List EIdx),
      XFree (ps.mapM (Arena.liftLooseBVarsFast coreWalkFuel n 0) : AM (List EIdx)) :=
    fun n ps => XFree.mapM (fun e => h6 _ _ _ e) ps
  have hb : ∀ n : Nat,
      XFree ((List.range n).mapM (fun i => Arena.internBVarE (n - 1 - i)) : AM (List EIdx)) :=
    fun n => XFree.mapM (fun i => h7 _) _
  unfold Arena.streamNestedOk Arena.streamNestedDom
  xauto

/-! ## Steps -/

theorem CStep.same {s s' : AState} (hok : DriverOK s) (e : s'.store = s.store)
    (c : s'.caches = s.caches) (p : s'.pins = s.pins) : CStep s s' :=
  ⟨⟨DriverOK.of_check (hok.mono ⟨by rw [e]; exact hok.state.wf⟩ (by rw [e]; exact Ext.refl _) c p) p,
    by rw [e]; exact Ext.refl _, p⟩, by rw [e]⟩

theorem CStep.of_check {s s' : AState}
    (h : CheckOK false Env.empty (driverFE s.pins) s') (hx : Ext s.store s'.store)
    (p : s'.pins = s.pins) (hx' : s'.store.scratchOn = s.store.scratchOn) : CStep s s' :=
  ⟨⟨DriverOK.of_check h p, hx, p⟩, hx'⟩

/-! ## The clauses -/

/-- con-leche: ConLeche/Driver/Reach.lean:109-122 nestedOk — `pins.all (exprOk lps k)`. -/
theorem exprsOk_run {lps : List NIdx} {ks : List ConLeche.Name} {k : Nat} :
    ∀ {es : List EIdx} {xs : List Expr} {s s' : AState},
      DriverOK s → Frontend.denoteNList s.store.ns lps = some ks →
      Frontend.denoteEList s.store es = some xs →
      ConRon.Arena.Modular.exprsOk lps k es s = .ok (true, s') →
      CStep s s' ∧ xs.all (ConLeche.Driver.exprOk ks k) = true
  | [], xs, s, s', hok, _, hx, h => by
    simp only [ConRon.Arena.Modular.exprsOk] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    exact ⟨CStep.refl hok, rfl⟩
  | e :: es, xs, s, s', hok, hl, hx, h => by
    obtain ⟨x, xs', hd, hds, rfl⟩ := denoteEList_cons hx
    simp only [ConRon.Arena.Modular.exprsOk] at h
    obtain ⟨b, s1, h1, h2⟩ := AM.bind_ok h
    obtain ⟨e1, c1, p1, hb⟩ := exprOk_run hok.state hl hd h1
    have c1' := CStep.same hok e1 c1 p1
    cases b with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h2
      obtain ⟨h, -⟩ := AM.pure_ok h2
      cases h
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h2
      obtain ⟨c2, hall⟩ := exprsOk_run c1'.ok (by rw [e1]; exact hl) (by rw [e1]; exact hds) h2
      exact ⟨c1'.trans c2, by simp [← hb, hall]⟩

/-- con-leche: ConLeche/Driver/Reach.lean:109-122 nestedOk — `lvls.all (·.allParamsDefined ps)`. -/
theorem levelsDefined_run {ps : List ConLeche.Name} :
    ∀ {ls : List LIdx} {us : List Level} {s s' : AState},
      DriverOK s → denoteLList s.store.ls ls = some us →
      ConRon.Arena.Modular.levelsDefined ps ls s = .ok (true, s') →
      CStep s s' ∧ us.all (·.allParamsDefined ps) = true
  | [], us, s, s', hok, hu, h => by
    simp only [ConRon.Arena.Modular.levelsDefined] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    simp only [denoteLList, Option.some.injEq] at hu
    subst hu
    exact ⟨CStep.refl hok, rfl⟩
  | l :: ls, us, s, s', hok, hu, h => by
    simp only [denoteLList] at hu
    cases h1 : denoteL s.store.ls l with
    | none => rw [h1] at hu; simp at hu
    | some u =>
    cases h2 : denoteLList s.store.ls ls with
    | none => rw [h1, h2] at hu; simp at hu
    | some us' =>
    rw [h1, h2] at hu
    obtain rfl := (Option.some.inj hu).symm
    simp only [ConRon.Arena.Modular.levelsDefined] at h
    obtain ⟨v, s1, k1, k2⟩ := AM.bind_ok h
    obtain ⟨hck1, e1, p1, hv⟩ := AM.of_run (P := fun t => t = s) rfl k1
      (Core.readLevelM_specC s l hok)
    obtain rfl : v = u := Option.some.inj (hv.symm.trans h1)
    have c1 : CStep s s1 := CStep.of_check hck1 (by rw [e1]; exact Ext.refl _) p1 (by rw [e1])
    by_cases hd : v.allParamsDefined ps = true
    · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k2
      obtain ⟨c2, hall⟩ := levelsDefined_run c1.ok (by rw [e1]; exact h2) k2
      exact ⟨c1.trans c2, by simp [hd, hall]⟩
    · simp only [hd, Bool.not_false, ↓reduceIte] at k2
      obtain ⟨h, -⟩ := AM.pure_ok k2
      cases h

/-! ## A recursor rule -/

/-- con-leche: ConLeche/Driver/Reach.lean:109-122 nestedOk — upstream's nested clause is the
kernel's `streamNestedOk` beside the scoping clauses. -/
theorem nestedOk_eq (lps : List ConLeche.Name) (ty : Expr) (mI rP : Nat) (lvls : List Level)
    (pins : List Expr) :
    ConLeche.Driver.nestedOk lps ty mI rP lvls pins =
      (decide (rP ≤ mI) && lvls.all (·.allParamsDefined lps) &&
        pins.all (ConLeche.Driver.exprOk lps rP) &&
        ConLeche.streamNestedOk ty mI rP (.nested lvls pins)) := by
  have hl : (pins.map fun e => Expr.liftLooseBVarsC (mI - rP) e 0) =
      pins.map (Expr.liftLooseBVars (mI - rP) 0) := by
    congr 1; funext e; exact ConLeche.Expr.liftLooseBVarsC_spec
  simp only [ConLeche.Driver.nestedOk, ConLeche.streamNestedOk, hl]
  congr 1
  cases ty.stripPis mI with
  | none => rfl
  | some p =>
    obtain ⟨a, b⟩ := p
    cases b with
    | forallE dom body =>
      dsimp only
      cases dom.getAppFn <;> simp
    | _ => rfl

theorem nestedOk_run {lps : List NIdx} {ks : List ConLeche.Name} {ty : EIdx} {tyC : Expr}
    {mI rP : Nat} {fire : IRecRuleFire} {fireC : RecRuleFire} {s s' : AState}
    (hok : DriverOK s) (hl : Frontend.denoteNList s.store.ns lps = some ks)
    (hty : denoteE s.store ty = some tyC) (hf : Frontend.denoteFire s.store fire = some fireC)
    (h : ConRon.Arena.Modular.nestedOk lps ty mI rP fire s = .ok (true, s')) :
    CStep s s' ∧ ∀ lvls pins, fireC = .nested lvls pins →
      ConLeche.Driver.nestedOk ks tyC mI rP lvls pins = true := by
  cases fire with
  | plain =>
    simp only [Frontend.denoteFire, Option.some.injEq] at hf; subst hf
    simp only [ConRon.Arena.Modular.nestedOk] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, fun _ _ h => nomatch h⟩
  | levels lvls =>
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨_, -, rfl⟩ := hf
    simp only [ConRon.Arena.Modular.nestedOk] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, fun _ _ h => nomatch h⟩
  | nested lvls pins =>
    simp only [Frontend.denoteFire] at hf
    cases hls : denoteLList s.store.ls lvls with
    | none => rw [hls] at hf; exact nomatch hf
    | some ls =>
    cases hps : Frontend.denoteEList s.store pins with
    | none => rw [hls, hps] at hf; exact nomatch hf
    | some ps =>
    rw [hls, hps] at hf
    obtain rfl := (Option.some.inj hf).symm
    simp only [ConRon.Arena.Modular.nestedOk] at h
    by_cases hle : rP ≤ mI
    · simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
      obtain ⟨xs, s1, k1, k2⟩ := AM.bind_ok h
      obtain ⟨rfl, hxs⟩ := readNames_run k1
      obtain rfl : xs = ks := Option.some.inj (hxs.symm.trans hl)
      obtain ⟨b, s2, k3, k4⟩ := AM.bind_ok k2
      cases b with
      | false =>
        simp only [Bool.not_false, ↓reduceIte] at k4
        obtain ⟨h, -⟩ := AM.pure_ok k4; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at k4
      obtain ⟨c2, hlv⟩ := levelsDefined_run hok hls k3
      obtain ⟨b', s3, k5, k6⟩ := AM.bind_ok k4
      cases b' with
      | false =>
        simp only [Bool.not_false, ↓reduceIte] at k6
        obtain ⟨h, -⟩ := AM.pure_ok k6; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at k6
      obtain ⟨c3, hps'⟩ := exprsOk_run c2.ok (denoteNList_ext c2.ext.lss.ls.ns _ _ hl)
        (denoteEList_ext c2.ext _ _ hps) k5
      have hok3 := c3.ok
      obtain ⟨q4, hsn⟩ := streamNestedOk_run hok3.state (denote_ext hty (c2.ext.trans c3.ext))
        (denoteFire_ext (g := .nested ls ps) (by simp [Frontend.denoteFire, hls, hps]) (c2.ext.trans c3.ext)) k6
      have c4 : CStep s3 s' := CStep.of_pstep hok3 q4 (XFree.streamNestedOk' _ _ _ _ _ _ _ k6)
      refine ⟨(c2.trans c3).trans c4, fun lvls' pins' he => ?_⟩
      cases he
      simp only [nestedOk_eq, hle, decide_true, hlv, hps', ← hsn, Bool.true_and]
    · simp only [hle, decide_false, Bool.not_false, ↓reduceIte] at h
      obtain ⟨h, -⟩ := AM.pure_ok h; cases h

theorem ruleOk_run {lps : List NIdx} {ks : List ConLeche.Name} {ty : EIdx} {tyC : Expr}
    {mI rP : Nat} {r : IRecRule} {rC : RecRule} {s s' : AState}
    (hok : DriverOK s) (hl : Frontend.denoteNList s.store.ns lps = some ks)
    (hty : denoteE s.store ty = some tyC) (hr : Frontend.denoteRule s.store r = some rC)
    (h : ConRon.Arena.Modular.ruleOk lps ty mI rP r s = .ok (true, s')) :
    CStep s s' ∧ ConLeche.Driver.ruleOk ks tyC mI rP rC = true := by
  simp only [Frontend.denoteRule] at hr
  split at hr
  · next c f x hc hf hx =>
    cases hr
    simp only [ConRon.Arena.Modular.ruleOk] at h
    obtain ⟨b, s1, k1, k2⟩ := AM.bind_ok h
    obtain ⟨e1, cc1, p1, hb⟩ := exprOk_run hok.state hl hx k1
    have c1 := CStep.same hok e1 cc1 p1
    cases b with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at k2
      obtain ⟨h, -⟩ := AM.pure_ok k2; cases h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k2
    by_cases hle : rP ≤ mI
    · simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at k2
      by_cases hbig : rP + r.nfields ≥ 2 ^ 64
      · simp only [hbig, ↓reduceIte] at k2
        obtain ⟨h, -⟩ := AM.pure_ok k2; cases h
      · simp only [hbig, ↓reduceIte] at k2
        obtain ⟨o, s2, k3, k4⟩ := AM.bind_ok k2
        obtain ⟨rfl, ho⟩ := stripLams_pstep c1.ok.state (by rw [e1]; exact hx) k3
        cases o with
        | none =>
          obtain ⟨h, -⟩ := AM.pure_ok k4; cases h
        | some q =>
        obtain ⟨_, _, hq, -, -⟩ := denoteBP_some ho
        dsimp only at k4
        obtain ⟨c2, hn⟩ := nestedOk_run c1.ok (by rw [e1]; exact hl) (by rw [e1]; exact hty)
          (by rw [e1]; exact hf) k4
        refine ⟨c1.trans c2, ?_⟩
        simp only [ConLeche.Driver.ruleOk, ← hb, hle, decide_true, Bool.true_and, hq,
          Option.isSome_some]
        cases f with
        | nested lvls pins => exact hn lvls pins rfl
        | plain => rfl
        | levels _ => rfl
    · simp only [hle, decide_false, Bool.not_false, ↓reduceIte] at k2
      obtain ⟨h, -⟩ := AM.pure_ok k2; cases h
  · cases hr

theorem rulesOk_run {lps : List NIdx} {ks : List ConLeche.Name} {ty : EIdx} {tyC : Expr}
    {mI rP : Nat} : ∀ {rs : List IRecRule} {rsC : List RecRule} {s s' : AState},
      DriverOK s → Frontend.denoteNList s.store.ns lps = some ks →
      denoteE s.store ty = some tyC → Frontend.denoteRules s.store rs = some rsC →
      ConRon.Arena.Modular.rulesOk lps ty mI rP rs s = .ok (true, s') →
      CStep s s' ∧ rsC.all (ConLeche.Driver.ruleOk ks tyC mI rP) = true
  | [], rsC, s, s', hok, _, _, hr, h => by
    simp only [Frontend.denoteRules, Option.some.injEq] at hr; subst hr
    simp only [ConRon.Arena.Modular.rulesOk] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, rfl⟩
  | r :: rs, rsC, s, s', hok, hl, hty, hr, h => by
    simp only [Frontend.denoteRules] at hr
    cases h1 : Frontend.denoteRule s.store r with
    | none => rw [h1] at hr; simp at hr
    | some x =>
    cases h2 : Frontend.denoteRules s.store rs with
    | none => rw [h1, h2] at hr; simp at hr
    | some xs =>
    rw [h1, h2] at hr
    obtain rfl := (Option.some.inj hr).symm
    simp only [ConRon.Arena.Modular.rulesOk] at h
    obtain ⟨b, s1, k1, k2⟩ := AM.bind_ok h
    cases b with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at k2
      obtain ⟨h, -⟩ := AM.pure_ok k2; cases h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k2
    obtain ⟨c1, hx⟩ := ruleOk_run hok hl hty h1 k1
    obtain ⟨c2, hxs⟩ := rulesOk_run c1.ok (denoteNList_ext c1.ext.lss.ls.ns _ _ hl)
      (denote_ext hty c1.ext) (denoteRules_ext c1.ext _ _ h2) k2
    exact ⟨c1.trans c2, by simp [hx, hxs]⟩

/-! ## A constant, a table, a record -/

theorem ctorHeadOk_run {cv : IConstantVal} {c : ConstantVal} {ind : NIdx} {indC : ConLeche.Name}
    {s s' : AState} (hok : DriverOK s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hi : denoteN s.store.ns ind = some indC)
    (h : ConRon.Arena.Modular.ctorHeadOk cv ind s = .ok (true, s')) :
    CStep s s' ∧ ConLeche.Driver.ctorHeadOk c indC = true := by
  obtain ⟨-, -, hty⟩ := denoteCV_inv hcv
  simp only [ConRon.Arena.Modular.ctorHeadOk] at h
  obtain ⟨b, s1, k1, k2⟩ := AM.bind_ok h
  obtain ⟨hs1, hb⟩ := piResult_run hok.state hty k1
  subst hs1
  obtain ⟨hd, s2, k3, k4⟩ := AM.bind_ok k2
  obtain ⟨hs2, hhd⟩ := getAppFn_run hok.state hb k3
  subst hs2
  by_cases htg : hd.tag = ETag.const
  · simp only [htg, beq_self_eq_true, ↓reduceIte] at k4
    obtain ⟨o, s3, k5, k6⟩ := AM.bind_ok k4
    obtain ⟨hs3, ho⟩ := AM.of_run (P := fun t => t = _) rfl k5 (ConRon.Bridge.Core.viewConstName_spec _ hd)
    subst hs3
    cases o with
    | none => obtain ⟨h, -⟩ := AM.pure_ok k6; cases h
    | some t =>
    obtain ⟨hv, rfl⟩ := AM.pure_ok k6
    have hti : t = ind := by simpa using hv.symm
    subst hti
    obtain ⟨us, hview⟩ := view_of_viewConstName htg ho.symm
    have he := (denoteE_view_eq hok.state.wf hview).symm.trans hhd
    simp only [denoteEView, opt2_eq_some_iff] at he
    obtain ⟨tC, usC, htC, -, he⟩ := he
    refine ⟨CStep.refl hok, ?_⟩
    simp only [ConLeche.Driver.ctorHeadOk, ← he]
    rw [Option.some.inj (htC.symm.trans hi)]
    simp
  · simp only [show (hd.tag == ETag.const) = false from by simpa using htg,
      Bool.false_eq_true, ↓reduceIte] at k4
    obtain ⟨h, -⟩ := AM.pure_ok k4; cases h

theorem constOk_run {ci : IConstantInfo} {c : ConstantInfo} {s s' : AState}
    (hok : DriverOK s) (hci : Frontend.denoteCI s.store ci = some c)
    (h : ConRon.Arena.Modular.constOk ci s = .ok (true, s')) :
    CStep s s' ∧ ConLeche.Driver.constOk c = true := by
  -- the type clause, common to every arm
  have ty1 : ∀ {cv : IConstantVal} {cvC : ConstantVal} {s s' : AState} {b : Bool},
      DriverOK s → Frontend.denoteCV s.store cv = some cvC →
      ConRon.Arena.Modular.exprOk cv.levelParams 0 cv.type s = .ok (b, s') →
      CStep s s' ∧ b = ConLeche.Driver.exprOk cvC.levelParams 0 cvC.type := by
    intro cv cvC s s' b hok hcv h
    obtain ⟨-, hl, ht⟩ := denoteCV_inv hcv
    obtain ⟨e1, c1, p1, hb⟩ := exprOk_run hok.state hl ht h
    exact ⟨CStep.same hok e1 c1 p1, hb⟩
  cases ci with
  | axiomInfo cv =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
    obtain ⟨cvC, hcv, rfl⟩ := hci
    simp only [ConRon.Arena.Modular.constOk] at h
    obtain ⟨c1, hb⟩ := ty1 hok hcv h
    exact ⟨c1, by simp only [ConLeche.Driver.constOk]; exact hb.symm⟩
  | thmInfo cv =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
    obtain ⟨cvC, hcv, rfl⟩ := hci
    simp only [ConRon.Arena.Modular.constOk] at h
    obtain ⟨c1, hb⟩ := ty1 hok hcv h
    exact ⟨c1, by simp only [ConLeche.Driver.constOk]; exact hb.symm⟩
  | indInfo cv caps =>
    simp only [Frontend.denoteCI] at hci
    split at hci
    · next cvC capsC hcv _ =>
      cases hci
      simp only [ConRon.Arena.Modular.constOk] at h
      obtain ⟨c1, hb⟩ := ty1 hok hcv h
      exact ⟨c1, by simp only [ConLeche.Driver.constOk]; exact hb.symm⟩
    · cases hci
  | defnInfo cv v hint =>
    simp only [Frontend.denoteCI] at hci
    split at hci
    · next cvC x hcv hx =>
      cases hci
      simp only [ConRon.Arena.Modular.constOk] at h
      obtain ⟨b, s1, k1, k2⟩ := AM.bind_ok h
      obtain ⟨c1, hb⟩ := ty1 hok hcv k1
      cases b with
      | false =>
        simp only [Bool.not_false, ↓reduceIte] at k2
        obtain ⟨h, -⟩ := AM.pure_ok k2; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k2
      obtain ⟨-, hl, -⟩ := denoteCV_inv hcv
      obtain ⟨e2, cc2, p2, hb2⟩ := exprOk_run c1.ok.state
        (denoteNList_ext c1.ext.lss.ls.ns _ _ hl) (denote_ext hx c1.ext) k2
      exact ⟨c1.trans (CStep.same c1.ok e2 cc2 p2), by simp [ConLeche.Driver.constOk, ← hb, ← hb2]⟩
    · cases hci
  | recInfo cv mI rP k rules =>
    simp only [Frontend.denoteCI] at hci
    split at hci
    · next cvC rulesC hcv hr =>
      cases hci
      simp only [ConRon.Arena.Modular.constOk] at h
      obtain ⟨b, s1, k1, k2⟩ := AM.bind_ok h
      obtain ⟨c1, hb⟩ := ty1 hok hcv k1
      cases b with
      | false =>
        simp only [Bool.not_false, ↓reduceIte] at k2
        obtain ⟨h, -⟩ := AM.pure_ok k2; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k2
      obtain ⟨-, hl, ht⟩ := denoteCV_inv hcv
      obtain ⟨c2, hrs⟩ := rulesOk_run c1.ok (denoteNList_ext c1.ext.lss.ls.ns _ _ hl)
        (denote_ext ht c1.ext) (denoteRules_ext c1.ext _ _ hr) k2
      exact ⟨c1.trans c2, by simp [ConLeche.Driver.constOk, ← hb, hrs]⟩
    · cases hci
  | ctorInfo cv nP nF T =>
    simp only [Frontend.denoteCI] at hci
    split at hci
    · next cvC TC hcv hT =>
      cases hci
      simp only [ConRon.Arena.Modular.constOk] at h
      obtain ⟨b, s1, k1, k2⟩ := AM.bind_ok h
      obtain ⟨c1, hb⟩ := ty1 hok hcv k1
      cases b with
      | false =>
        simp only [Bool.not_false, ↓reduceIte] at k2
        obtain ⟨h, -⟩ := AM.pure_ok k2; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k2
      obtain ⟨c2, hh⟩ := ctorHeadOk_run c1.ok (denoteCV_ext hcv c1.ext)
        (denoteN_ext hT c1.ext) k2
      exact ⟨c1.trans c2, by simp [ConLeche.Driver.constOk, ← hb, hh]⟩
    · cases hci

theorem denoteEList_length {st : EStore} :
    ∀ {l : List EIdx} {xs : List Expr}, Frontend.denoteEList st l = some xs → l.length = xs.length
  | [], xs, h => by simp only [Frontend.denoteEList, Option.some.injEq] at h; subst h; rfl
  | e :: l, xs, h => by
    obtain ⟨x, xs', -, h2, rfl⟩ := denoteEList_cons h
    simp [denoteEList_length h2]

theorem tableOk_run {t : IProjTable} {tC : ProjTable} {s s' : AState} (hok : DriverOK s)
    (ht : Frontend.denoteProjTable s.store t = some tC)
    (h : ConRon.Arena.Modular.tableOk t s = .ok (true, s')) :
    CStep s s' ∧ ConLeche.Driver.tableOk tC = true := by
  simp only [Frontend.denoteProjTable] at ht
  split at ht
  · next sn lps c hsn hlps hc =>
    split at ht
    · next bs hbs =>
      cases ht
      simp only [Frontend.denoteEArray] at hbs
      split at hbs
      · next xs hxs =>
        cases hbs
        simp only [ConRon.Arena.Modular.tableOk] at h
        by_cases hsz : (t.bodies.size != t.numFields) = true
        · simp only [hsz, ↓reduceIte] at h
          obtain ⟨h, -⟩ := AM.pure_ok h; cases h
        · simp only [hsz, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
          by_cases hbig : t.numParams + 1 ≥ 2 ^ 64
          · simp only [hbig, ↓reduceIte] at h
            obtain ⟨h, -⟩ := AM.pure_ok h; cases h
          · simp only [hbig, ↓reduceIte] at h
            obtain ⟨c1, hall⟩ := exprsOk_run hok hlps hxs h
            refine ⟨c1, ?_⟩
            have hlen : xs.length = t.bodies.size := by
              simpa using (denoteEList_length hxs).symm
            simp only [ConLeche.Driver.tableOk, Bool.and_eq_true, beq_iff_eq]
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hsz
            refine ⟨by simp [hlen, hsz], ?_⟩
            simpa [Array.all_eq_true, List.all_eq_true] using hall
      · cases hbs
    · cases ht
  · cases ht

theorem constsOk_run : ∀ {L : List IConstantInfo} {LC : List ConstantInfo} {s s' : AState},
    DriverOK s → Frontend.denoteCIList s.store L = some LC →
    ConRon.Arena.Modular.constsOk L s = .ok (true, s') →
    CStep s s' ∧ LC.all (fun c => ConLeche.Driver.constOk c && ConLeche.litShapeOk c) = true
  | [], LC, s, s', hok, hL, h => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at hL; subst hL
    simp only [ConRon.Arena.Modular.constsOk] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, rfl⟩
  | c :: L, LC, s, s', hok, hL, h => by
    simp only [Frontend.denoteCIList] at hL
    cases h1 : Frontend.denoteCI s.store c with
    | none => rw [h1] at hL; simp at hL
    | some x =>
    cases h2 : Frontend.denoteCIList s.store L with
    | none => rw [h1, h2] at hL; simp at hL
    | some xs =>
    rw [h1, h2] at hL
    obtain rfl := (Option.some.inj hL).symm
    simp only [ConRon.Arena.Modular.constsOk] at h
    obtain ⟨b, s1, k1, k2⟩ := AM.bind_ok h
    cases b with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at k2
      obtain ⟨h, -⟩ := AM.pure_ok k2; cases h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k2
    obtain ⟨c1, hx⟩ := constOk_run hok h1 k1
    obtain ⟨b', s2, k3, k4⟩ := AM.bind_ok k2
    obtain ⟨hck2, hx2, hp2, hb'⟩ := AM.of_run (P := fun t => t = s1)
      (Q := fun r t => CheckOK false Env.empty (driverFE s1.pins) t ∧ Ext s1.store t.store ∧
        t.pins = s1.pins ∧ r = ConLeche.litShapeOk x)
      rfl k3 (litShapeOk_run s1 c x c1.ok (denoteCI_ext h1 c1.ext))
    have c2 : CStep s1 s2 := CStep.of_check hck2 hx2 hp2
      (XFree.litShapeOk' c _ _ _ k3)
    cases b' with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at k4
      obtain ⟨h, -⟩ := AM.pure_ok k4; cases h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at k4
    have c12 := c1.trans c2
    obtain ⟨c3, hxs⟩ := constsOk_run c12.ok (denoteCIList_mono c12.ext _ _ h2) k4
    exact ⟨c12.trans c3, by simp [hx, ← hb', hxs]⟩

theorem tablesOk_run : ∀ {Q : List IProjTable} {QC : List ProjTable} {s s' : AState},
    DriverOK s → Frontend.denoteProjTableList s.store Q = some QC →
    ConRon.Arena.Modular.tablesOk Q s = .ok (true, s') →
    CStep s s' ∧ QC.all ConLeche.Driver.tableOk = true
  | [], QC, s, s', hok, hQ, h => by
    simp only [Frontend.denoteProjTableList, Option.some.injEq] at hQ; subst hQ
    simp only [ConRon.Arena.Modular.tablesOk] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, rfl⟩
  | t :: Q, QC, s, s', hok, hQ, h => by
    simp only [Frontend.denoteProjTableList] at hQ
    cases h1 : Frontend.denoteProjTable s.store t with
    | none => rw [h1] at hQ; simp at hQ
    | some x =>
    cases h2 : Frontend.denoteProjTableList s.store Q with
    | none => rw [h1, h2] at hQ; simp at hQ
    | some xs =>
    rw [h1, h2] at hQ
    obtain rfl := (Option.some.inj hQ).symm
    simp only [ConRon.Arena.Modular.tablesOk] at h
    obtain ⟨b, s1, k1, k2⟩ := AM.bind_ok h
    cases b with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at k2
      obtain ⟨h, -⟩ := AM.pure_ok k2; cases h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k2
    obtain ⟨c1, hx⟩ := tableOk_run hok h1 k1
    obtain ⟨c2, hxs⟩ := tablesOk_run c1.ok (denoteProjTableList_ext c1.ext h2) k2
    exact ⟨c1.trans c2, by simp [hx, hxs]⟩

/-- con-leche: ConLeche/Driver/Reach.lean:154-157 recordOk — **a record the twin validates is
one upstream validates**, from a driver's state with no scratch tier open, which it keeps. -/
theorem recordOk_run {d : IDeclaration} {dC : Declaration} {s s' : AState}
    (hok : DriverOK s) (hoff : s.store.scratchOn = false) (hp : PersDecl d)
    (hd : Frontend.denoteDecl s.store d = some dC)
    (h : ConRon.Arena.Modular.recordOk d s = .ok (true, s')) :
    CStepW s s' ∧ s'.store.scratchOn = false ∧ ConLeche.Driver.recordOk dC = true := by
  simp only [ConRon.Arena.Modular.recordOk] at h
  obtain ⟨cs, s1, k1, k2⟩ := AM.bind_ok h
  obtain ⟨hok1, hx1, hp1, hoff1, hcs, -⟩ := constsSpec hok hoff hp hd k1
  obtain ⟨b, s2, k3, k4⟩ := AM.bind_ok k2
  cases b with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at k4
    obtain ⟨h, -⟩ := AM.pure_ok k4; cases h
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k4
  obtain ⟨c2, hcok⟩ := constsOk_run hok1 hcs k3
  have hoff2 : s2.store.scratchOn = false := by rw [c2.scr]; exact hoff1
  obtain ⟨ts, s3, k5, k6⟩ := AM.bind_ok k4
  obtain ⟨hok3, hx3, hp3, hoff3, hts, -⟩ := tablesSpec c2.ok hoff2 hp
    (denoteDecl_ext (hx1.trans c2.ext) hd) k5
  obtain ⟨c4, htok⟩ := tablesOk_run hok3 hts k6
  refine ⟨⟨c4.ok, ((hx1.trans c2.ext).trans hx3).trans c4.ext, ?_⟩, by rw [c4.scr]; exact hoff3, ?_⟩
  · rw [c4.pins, hp3, c2.pins, hp1]
  · simp only [ConLeche.Driver.recordOk, hcok, htok, Bool.and_self]

/-- con-leche: ConLeche/Driver/Reach.lean:830-837 validateCtx — **the twin's validation
accepting is upstream's**: every context record `recordOk`. -/
theorem validateCtx_run : ∀ {ds : List IDeclaration} {hs : Array NIdx} {i : Nat}
    {dsC : List Declaration} {s s' : AState},
    DriverOK s → s.store.scratchOn = false → (∀ d ∈ ds, PersDecl d) →
    denoteDecls s.store ds = some dsC →
    ConRon.Arena.Modular.validateCtx ds hs i s = .ok ((), s') →
    CStepW s s' ∧ s'.store.scratchOn = false ∧ dsC.all ConLeche.Driver.recordOk = true
  | [], hs, i, dsC, s, s', hok, hoff, _, hd, h => by
    simp only [denoteDecls, Option.some.injEq] at hd; subst hd
    simp only [ConRon.Arena.Modular.validateCtx] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨CStepW.refl hok, hoff, rfl⟩
  | d :: ds, hs, i, dsC, s, s', hok, hoff, hp, hd, h => by
    simp only [denoteDecls] at hd
    cases h1 : Frontend.denoteDecl s.store d with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : denoteDecls s.store ds with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [ConRon.Arena.Modular.validateCtx] at h
    obtain ⟨b, s1, k1, k2⟩ := AM.bind_ok h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at k2
      obtain ⟨_, _, _, k⟩ := AM.bind_ok k2
      exact absurd k fail_not_ok
    | true =>
    simp only [↓reduceIte] at k2
    obtain ⟨c1, hoff1, hx⟩ := recordOk_run hok hoff (hp d (List.mem_cons_self ..)) h1 k1
    obtain ⟨c2, hoff2, hxs⟩ := validateCtx_run c1.ok hoff1
      (fun d hd => hp d (List.mem_cons_of_mem _ hd)) (denoteDecls_ext c1.ext _ _ h2) k2
    exact ⟨c1.trans c2, hoff2, by simp [hx, hxs]⟩

end ConRon.Bridge.Modular
