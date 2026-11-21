/-
# `ConRon.Bridge.Inductives.IotaRead` — Theorem 1 for the ι reading rule

`Arena/Inductives/IotaRead.lean` against con-leche's
`ConLeche/Kernel/Inductives/IotaRead.lean` (`blockReadsOk`) and `IotaEq.lean`.
-/
module

public import ConRon.Bridge.Grind
import ConRon.Bridge.Specs
import ConRon.Bridge.SpecsL
import ConRon.Bridge.GrindAttr
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.IotaLeaves
public import ConRon.Bridge.Inductives.BlockTail
import ConRon.Bridge.Inductives.Install
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Core.Walks.Former
import ConRon.Bridge.Core.Walks.Spine
public import ConRon.Arena.Inductives.IotaRead
public import ConLeche.Kernel.Inductives.IotaRead

public section

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## `piTele` -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:83-86 Expr.piTele — one
equation over the tag. -/
theorem piTele_eq (x : Expr) : x.piTele =
    if exprTag x = ETag.forallE then ((exprBody x).piTele.1 + 1, (exprBody x).piTele.2)
    else (0, x) := by
  cases x <;> simp [Expr.piTele, exprTag, exprBody, ETag.forallE, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:83-86 Expr.piTele —
**THEOREM 1** for `piTele`: the binder count and the body. -/
theorem piTele_spec : ∀ (fuel : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ piTele fuel h
    ⦃fun r s' => s' = s₀ ∧ RelV (fun e => e.piTele.1) s₀.store h r.1 ∧
        RelE (fun e => e.piTele.2) s₀.store h s₀.store r.2; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h _ _
    sym only [bridge_grind] => vcgen [piTele] <;> finish
  | succ fuel ih =>
    intro s₀ h hok hden
    sym only [bridge_grind, piTele_eq] => vcgen [piTele, ih] <;> finish

variable {eager : Bool} {env : Env} {fe : IFEnv}

/-! ## `lvlEq` -/

local grind_pattern [bridge_grind] nameIdx => denoteN st.ns n
local grind_pattern [bridge_grind] NameIdx.some => NameIdx st n (some nm)
local grind_pattern [bridge_grind] eIdxAt => denoteE st n
local grind_pattern [bridge_grind] EIdxAt.some => EIdxAt st n (some e)

local grind_pattern [bridge_grind] view_of_viewConst => st.viewConst i, some (n, us) where
  guard st.viewConst i = some (n, us)

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:99-112 Expr.lvlEq — its
answer at two denotations. -/
@[expose] def LvlEqA (x y : Expr) (r : Bool) : Prop := r = x.lvlEq y

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:99-112 Expr.lvlEq — one
equation over the tags and the projections. -/
theorem lvlEq_eq (x y : Expr) : x.lvlEq y =
    if x = y then true
    else if exprTag x ≠ exprTag y then false
    else if exprTag x = ETag.sort then Level.isEquiv (exprSort x) (exprSort y) == some true
    else if exprTag x = ETag.const then
      (exprConstName x == exprConstName y &&
        Level.isEquivList (exprConstLevels x) (exprConstLevels y) == some true)
    else if exprTag x = ETag.app then
      ((exprFn x).lvlEq (exprFn y) && (exprArg x).lvlEq (exprArg y))
    else if exprTag x = ETag.lam ∨ exprTag x = ETag.forallE then
      ((exprBinderType x).lvlEq (exprBinderType y) && (exprBody x).lvlEq (exprBody y))
    else if exprTag x = ETag.letE then
      ((exprBinderType x).lvlEq (exprBinderType y) &&
        (exprLetVal x).lvlEq (exprLetVal y) && (exprBody x).lvlEq (exprBody y))
    else if exprTag x = ETag.proj then
      (exprProjName x == exprProjName y && exprProjIdx x == exprProjIdx y &&
        (exprProjStruct x).lvlEq (exprProjStruct y))
    else false := by
  by_cases hxy : x = y
  · subst hxy; simp only [↓reduceIte]; cases x <;> simp [Expr.lvlEq]
  simp only [hxy, ↓reduceIte]
  have hb : (x == y) = false := by simpa using hxy
  have lv : ∀ t v b, exprLetVal (.letE t v b) = v := fun t v b => by
    have := exprTag_letE (e := .letE t v b) rfl
    injection this with _ h; exact h.symm
  have ps : ∀ n i e, exprProjStruct (.proj n i e) = e := fun n i e => by
    have := exprTag_proj (e := .proj n i e) rfl
    injection this with _ _ h; exact h.symm
  cases x <;> cases y <;> simp_all [Expr.lvlEq, exprTag, exprSort, exprConstName,
    exprConstLevels, exprFn, exprArg, exprBinderType, exprBody, exprProjName, exprProjIdx,
    ETag.forallE, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE,
    ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:99-112 Expr.lvlEq —
**THEOREM 1** for `lvlEq`: equal up to equivalent universe levels. -/
theorem lvlEq_spec : ∀ (fuel : Nat) (s₀ : AState) (a b : EIdx),
    CheckOK eager env fe s₀ → (denoteE s₀.store a).isSome = true →
    (denoteE s₀.store b).isSome = true →
    ⦃fun s => s = s₀⦄ lvlEq fuel a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        PairAns LvlEqA (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ a b _ _ _
    sym only [bridge_grind] => vcgen [lvlEq] <;> finish
  | succ fuel ih =>
    intro s₀ a b hok ha hb
    sym only [bridge_grind, lvlEq_eq, LvlEqA] =>
      vcgen [lvlEq, ih, Core.readLevelM_specC (eager := eager) (env := env) (fe := fe),
        Core.readLevelsM_specC (eager := eager) (env := env) (fe := fe)] <;> finish

/-! ## con-leche's side, decomposed

The twin reads the recursor's frame once per recursor (`iotaRecOf`) and each
rule's minor premise from it (`iotaPartsOfAt`); `iotaPartsOf_eq` is
con-leche's `iotaPartsOf` split the same way. -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:88-94 minorsOf — the
filter's test, as a function of the position. -/
@[expose] def minorP (pre : List Expr) (mot q : Nat) : Bool :=
  match ((pre.getD q default).piTele.2).getAppFn with
  | .bvar m => decide (mot < q) && m == (pre.getD q default).piTele.1 + (q - 1 - mot)
  | _ => false

theorem minorsOf_eq (pre : List Expr) (mot : Nat) :
    ConLeche.minorsOf pre mot = (List.range pre.length).filter (minorP pre mot) := rfl

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — its
rule-independent part (`Arena.IotaRec`'s denotation). -/
structure IotaRecP where
  pre : List Expr
  minors : List Nat
  us : List Level
  params : List Expr

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — past
the motive's head `k`. -/
@[expose] def iotaRecMajorP (pre doms : List Expr) (nIdx rP k : Nat) : Option IotaRecP :=
  match (doms.getD nIdx default).getAppFn with
  | .const _ us =>
    some ⟨pre, ConLeche.minorsOf pre (rP + nIdx - k), us,
      ((doms.getD nIdx default).getAppArgs.take
        ((doms.getD nIdx default).getAppArgs.length - nIdx)).map (ConLeche.Expr.dropVars nIdx)⟩
  | _ => none

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — the
rule-independent part. -/
@[expose] def iotaRecP (cv : ConstantVal) (mI rP : Nat) : Option IotaRecP :=
  match ConLeche.iotaFrame cv mI rP with
  | some (pre, doms, body, _) =>
    match body.getAppFn with
    | .bvar k => iotaRecMajorP pre doms (mI - rP) rP k
    | _ => none
  | none => none

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — the
rule's part. -/
@[expose] def iotaPartsOfAtP (r : IotaRecP) (rP nIdx i nF : Nat) : Option IotaParts :=
  match r.minors[i]? with
  | none => none
  | some q =>
    match (r.pre.getD q default).stripPis nF with
    | none => none
    | some (fd, inner) => some ⟨fd.mapIdx (fun j d => d.liftLooseBVars (rP - q) j),
        (inner.piTele.2.getAppArgs.take nIdx).map
          (fun a => (a.dropVars inner.piTele.1).liftLooseBVars (rP - q) nF),
        r.us, r.params⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — the
split the twin's `iotaRecOf`/`iotaPartsOfAt` make. -/
theorem iotaPartsOf_eq (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule) :
    ConLeche.iotaPartsOf cv mI rP i rl =
      (iotaRecP cv mI rP).bind (fun r => iotaPartsOfAtP r rP (mI - rP) i rl.nfields) := by
  unfold ConLeche.iotaPartsOf iotaRecP
  cases ConLeche.iotaFrame cv mI rP with
  | none => rfl
  | some f =>
    obtain ⟨pre, doms, body, u⟩ := f
    simp only [Option.bind_eq_bind, Option.bind_some, iotaRecMajorP, iotaPartsOfAtP,
      List.getD_eq_getElem?_getD]
    cases hb : body.getAppFn with
    | bvar k =>
      simp only
      cases hq : (ConLeche.minorsOf pre (rP + (mI - rP) - k))[i]? with
      | none =>
        cases hd : (doms[mI - rP]?.getD default).getAppFn <;> simp [hq]
      | some q =>
        cases hs : Expr.stripPis rl.nfields (pre[q]?.getD default) with
        | none => cases hd : (doms[mI - rP]?.getD default).getAppFn <;> simp [hq, hs]
        | some p =>
          obtain ⟨fd, inner⟩ := p
          cases hd : (doms[mI - rP]?.getD default).getAppFn <;> simp [hq, hs]
    | _ => rfl

/-- con-leche: none — the frame's denotation. -/
@[expose] def RecRel (st : EStore) (r : IotaRec) (x : IotaRecP) : Prop :=
  Frontend.denoteEList st r.pre = some x.pre ∧ r.minors = x.minors ∧
    denoteLs st.lss r.us = some x.us ∧ Frontend.denoteEList st r.params = some x.params

theorem RecRel.mono {st st' : EStore} (hx : Ext st st') {r : IotaRec} {x : IotaRecP}
    (h : RecRel st r x) : RecRel st' r x :=
  ⟨denoteEList_ext hx _ _ h.1, h.2.1, denoteLs_ext h.2.2.1 hx, denoteEList_ext hx _ _ h.2.2.2⟩

/-- con-leche: none — a rule's parts' denotation. -/
@[expose] def PartsRel (st : EStore) (p : IIotaParts) (x : IotaParts) : Prop :=
  Frontend.denoteEList st p.fieldDoms = some x.fieldDoms ∧
    Frontend.denoteEList st p.idx = some x.idx ∧
    denoteLs st.lss p.us = some x.us ∧ Frontend.denoteEList st p.params = some x.params

theorem PartsRel.mono {st st' : EStore} (hx : Ext st st') {p : IIotaParts} {x : IotaParts}
    (h : PartsRel st p x) : PartsRel st' p x :=
  ⟨denoteEList_ext hx _ _ h.1, denoteEList_ext hx _ _ h.2.1, denoteLs_ext h.2.2.1 hx,
    denoteEList_ext hx _ _ h.2.2.2⟩

/-! ## The primitives, in run form at the core frame -/

theorem getD_runC {s s' : AState} {xs : List EIdx} {xsP : List Expr} {i : Nat} {r : EIdx}
    (hok : CheckOK false env fe s) (hxs : Frontend.denoteEList s.store xs = some xsP)
    (hrun : Arena.exprGetD xs i s = .ok (r, s')) :
    CoreStep env fe s s' ∧ denoteE s'.store r = some (xsP.getD i default) := by
  obtain ⟨p, hr⟩ := exprGetD_spec xs xsP i s s' r hok.state hxs hrun
  exact ⟨p.toCore hok, hr⟩

theorem piTele_run {s s' : AState} {h : EIdx} {hP : Expr} {r : Nat × EIdx}
    (hok : CheckOK false env fe s) (hd : denoteE s.store h = some hP)
    (hrun : Arena.piTele coreWalkFuel h s = .ok (r, s')) :
    s' = s ∧ r.1 = hP.piTele.1 ∧ denoteE s.store r.2 = some hP.piTele.2 := by
  obtain ⟨h1, h2, h3⟩ := AM.of_run (P := fun t => t = s) rfl hrun
    (piTele_spec coreWalkFuel s h hok.state (by rw [hd]; rfl))
  subst h1
  exact ⟨rfl, h2 hP hd, h3 hP hd⟩

theorem liftFast_run {s s' : AState} {amt c : Nat} {e r : EIdx} {eP : Expr}
    (hok : CheckOK false env fe s) (he : denoteE s.store e = some eP)
    (hrun : liftLooseBVarsFast coreWalkFuel amt c e s = .ok (r, s')) :
    CoreStep env fe s s' ∧ denoteE s'.store r = some (eP.liftLooseBVars amt c) := by
  obtain ⟨q1, q2, -, q4, q5, -, -, q8⟩ := AM.of_run (P := fun t => t = s) rfl hrun
    (ExprOps.liftLooseBVarsFast_spec coreWalkFuel amt c s e hok.state (by rw [he]; rfl))
  exact ⟨⟨hok.mono q1 q2 q4 q5, q2, q5⟩, q8 eP he⟩

theorem dropVars_runC {n : Nat} {s s' : AState} {e r : EIdx} {eP : Expr}
    (hok : CheckOK false env fe s) (he : denoteE s.store e = some eP)
    (hrun : Arena.exprDropVars n e s = .ok (r, s')) :
    CoreStep env fe s s' ∧ denoteE s'.store r = some (eP.dropVars n) := by
  obtain ⟨p, -, hr⟩ := exprDropVars_run n hok.state hok.pins he hrun
  exact ⟨p.toCore hok, hr⟩

theorem viewBVar_run {s s' : AState} {h : EIdx} {r : Option Nat}
    (hrun : viewBVar h s = .ok (r, s')) : s' = s ∧ r = s.store.viewBVar h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewBVar_spec s h)

theorem viewSort_run {s s' : AState} {h : EIdx} {r : Option LIdx}
    (hrun : viewSort h s = .ok (r, s')) : s' = s ∧ r = s.store.viewSort h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewSort_spec s h)

/-- con-leche: none — a handle whose tag is not `t` denotes no term of tag `t`. -/
theorem exprTag_ne {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr} {t : UInt32}
    (hd : denoteE st h = some e) (htg : ¬ (h.tag == t) = true) : exprTag e ≠ t := by
  intro hc; apply htg; rw [tag_of_denote hwf hd, hc]; simp

/-! ## The recursor's frame (`iotaRecOf`) -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:32-43 motiveLevel? — an
accepting reading is con-leche's (the level itself is not compared: the rule
reads only that there is one). -/
theorem motiveLevel?_run {s s' : AState} {pre : List EIdx} {preP : List Expr} {nIdx : Nat}
    {body : EIdx} {bodyP : Expr} {r : Option LIdx} (hok : CheckOK false env fe s)
    (hpre : Frontend.denoteEList s.store pre = some preP)
    (hb : denoteE s.store body = some bodyP)
    (hrun : Arena.motiveLevel? pre nIdx body s = .ok (r, s')) :
    CoreStep env fe s s' ∧
      (r.isSome = true → (ConLeche.motiveLevel? preP nIdx bodyP).isSome = true) := by
  simp only [Arena.motiveLevel?] at hrun
  obtain ⟨hd, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hhd⟩ := getAppFn_run hok.state hb h1
  by_cases htg : (hd.tag == ETag.bvar) = true
  · rw [ite_eq_left htg] at h2
    obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, ho⟩ := viewBVar_run h3
    cases o with
    | none => exact absurd h4 (fun hc => failDanglingE_ok hc)
    | some k =>
    have hk : bodyP.getAppFn = .bvar k :=
      denote_bvar_inv hok.state.wf (view_of_viewBVar (by simpa using htg) ho.symm) hhd
    have hlen : pre.length = preP.length := (ExprOps.denoteEList_length _ _ hpre).symm
    dsimp only at h4
    by_cases h5 : nIdx + 1 ≤ k
    · rw [ite_eq_left h5] at h4
      by_cases h6 : k < nIdx + 1 + pre.length
      · rw [ite_eq_left h6] at h4
        obtain ⟨d, s₃, h7, h8⟩ := AM.bind_ok h4
        obtain ⟨c3, hdd⟩ := getD_runC hok hpre h7
        obtain ⟨rr, s₄, h9, h10⟩ := AM.bind_ok h8
        obtain ⟨rfl, hrr⟩ := piResult_run c3.ok.state hdd h9
        by_cases hts : (rr.tag == ETag.sort) = true
        · rw [ite_eq_left hts] at h10
          obtain ⟨o2, s₅, h11, h12⟩ := AM.bind_ok h10
          obtain ⟨rfl, ho2⟩ := viewSort_run h11
          cases o2 with
          | none => exact absurd h12 (fun hc => failDanglingE_ok hc)
          | some u =>
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h12
          obtain ⟨l, hl, -⟩ := denote_sort_inv c3.ok.state.wf
            (view_of_viewSort (by simpa using hts) ho2.symm) hrr
          refine ⟨c3, fun _ => ?_⟩
          simp only [List.getD_eq_getElem?_getD] at hl
          simp [ConLeche.motiveLevel?, hk, h5, h6, hl, ← hlen]
        · rw [ite_eq_right hts] at h10
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h10
          exact ⟨c3, by simp⟩
      · rw [ite_eq_right h6] at h4
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
        exact ⟨CoreStep.refl hok, by simp⟩
    · rw [ite_eq_right h5] at h4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      exact ⟨CoreStep.refl hok, by simp⟩
  · rw [ite_eq_right htg] at h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨CoreStep.refl hok, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:45-53 iotaFrame — an
accepting reading is con-leche's. -/
theorem iotaFrame_run {s s' : AState} {cv : IConstantVal} {cvP : ConstantVal} {mI rP : Nat}
    {r : Option (List EIdx × List EIdx × EIdx × LIdx)} (hok : CheckOK false env fe s)
    (hcv : Frontend.denoteCV s.store cv = some cvP)
    (hrun : Arena.iotaFrame cv mI rP s = .ok (r, s')) :
    CoreStep env fe s s' ∧ ∀ pre doms body u, r = some (pre, doms, body, u) →
      ∃ preP domsP bodyP uP, ConLeche.iotaFrame cvP mI rP = some (preP, domsP, bodyP, uP) ∧
        Frontend.denoteEList s'.store pre = some preP ∧
        Frontend.denoteEList s'.store doms = some domsP ∧ denoteE s'.store body = some bodyP := by
  simp only [Arena.iotaFrame] at hrun
  obtain ⟨o1, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hb1⟩ := stripPis_pstep hok.state (denoteCV_type hcv) h1
  cases o1 with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨CoreStep.refl hok, by simp⟩
  | some q1 =>
  obtain ⟨pre, rest⟩ := q1
  obtain ⟨preP, restP, hsp1, hpre, hrest⟩ := denoteBP_some hb1
  dsimp only at h2
  obtain ⟨o2, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨rfl, hb2⟩ := stripPis_pstep hok.state hrest h3
  cases o2 with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
    exact ⟨CoreStep.refl hok, by simp⟩
  | some q2 =>
  obtain ⟨doms, body⟩ := q2
  obtain ⟨domsP, bodyP, hsp2, hdoms, hbody⟩ := denoteBP_some hb2
  dsimp only at h4
  obtain ⟨o3, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨c3, hml⟩ := motiveLevel?_run hok hpre hbody h5
  cases o3 with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
    exact ⟨c3, by simp⟩
  | some u =>
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
  obtain ⟨uP, huP⟩ := Option.isSome_iff_exists.mp (hml rfl)
  refine ⟨c3, ?_⟩
  intro pre' doms' body' u' he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  refine ⟨preP, domsP, bodyP, uP, ?_, denoteEList_ext c3.ext _ _ hpre,
    denoteEList_ext c3.ext _ _ hdoms, denote_ext hbody c3.ext⟩
  simp [ConLeche.iotaFrame, hsp1, hsp2, huP]

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:88-94 minorsOf — one
position's test, exactly. -/
theorem isMinorAt_run {s s' : AState} {pre : List EIdx} {preP : List Expr} {mot q : Nat}
    {r : Bool} (hok : CheckOK false env fe s)
    (hpre : Frontend.denoteEList s.store pre = some preP)
    (hrun : Arena.isMinorAt pre mot q s = .ok (r, s')) :
    CoreStep env fe s s' ∧ r = minorP preP mot q := by
  simp only [Arena.isMinorAt] at hrun
  obtain ⟨d, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨c1, hd⟩ := getD_runC hok hpre h1
  obtain ⟨t, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨rfl, ht1, ht2⟩ := piTele_run c1.ok hd h3
  obtain ⟨hh, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨rfl, hhh⟩ := getAppFn_run c1.ok.state ht2 h5
  by_cases htg : (hh.tag == ETag.bvar) = true
  · rw [ite_eq_left htg] at h6
    obtain ⟨o, s₄, h7, h8⟩ := AM.bind_ok h6
    obtain ⟨rfl, ho⟩ := viewBVar_run h7
    cases o with
    | none => exact absurd h8 (fun hc => failDanglingE_ok hc)
    | some m =>
    have hk := denote_bvar_inv c1.ok.state.wf (view_of_viewBVar (by simpa using htg) ho.symm) hhh
    simp only [List.getD_eq_getElem?_getD] at hk ht1
    dsimp only at h8
    by_cases hmq : mot < q
    · rw [ite_eq_left hmq] at h8
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h8
      exact ⟨c1, by simp [minorP, hk, hmq, ht1]⟩
    · rw [ite_eq_right hmq] at h8
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h8
      exact ⟨c1, by simp [minorP, hk, hmq]⟩
  · rw [ite_eq_right htg] at h6
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
    refine ⟨c1, ?_⟩
    have hne := exprTag_ne c1.ok.state.wf hhh htg
    unfold minorP
    split
    · rename_i m hm; rw [hm] at hne; exact absurd rfl hne
    · rfl

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:88-94 minorsOf — the
positions from `q` on, exactly. -/
theorem minorsFrom_run (pre : List EIdx) (preP : List Expr) (mot : Nat) :
    ∀ (n q : Nat), pre.length - q = n → ∀ {s s' : AState} {r : List Nat},
      CheckOK false env fe s → Frontend.denoteEList s.store pre = some preP →
      Arena.minorsFrom pre mot q s = .ok (r, s') →
      CoreStep env fe s s' ∧ r = (List.range' q (pre.length - q)).filter (minorP preP mot) := by
  intro n
  induction n with
  | zero =>
    intro q hn s s' r hok hpre hrun
    rw [Arena.minorsFrom] at hrun
    rw [ite_eq_right (by omega)] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by rw [hn]; rfl⟩
  | succ n ih =>
    intro q hn s s' r hok hpre hrun
    rw [Arena.minorsFrom] at hrun
    rw [ite_eq_left (by omega)] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨c1, hb⟩ := isMinorAt_run hok hpre h1
    obtain ⟨rest, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨c2, hrest⟩ := ih (q + 1) (by omega) c1.ok (denoteEList_ext c1.ext _ _ hpre) h3
    have hr : pre.length - q = (pre.length - (q + 1)) + 1 := by omega
    refine ⟨c1.trans ?_, ?_⟩
    · cases b <;> (obtain ⟨rfl, rfl⟩ := AM.pure_ok h4; exact c2)
    · rw [hr, List.range'_succ, List.filter_cons, ← hb, ← hrest]
      cases b <;> (obtain ⟨rfl, rfl⟩ := AM.pure_ok h4; simp)

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — past
the motive's head. -/
theorem iotaRecMajor_run {s s' : AState} {pre doms : List EIdx} {preP domsP : List Expr}
    {nIdx rP k : Nat} {r : Option IotaRec} (hok : CheckOK false env fe s)
    (hpre : Frontend.denoteEList s.store pre = some preP)
    (hdoms : Frontend.denoteEList s.store doms = some domsP)
    (hrun : Arena.iotaRecMajor pre doms nIdx rP k s = .ok (r, s')) :
    CoreStep env fe s s' ∧ ∀ rr, r = some rr →
      ∃ x, iotaRecMajorP preP domsP nIdx rP k = some x ∧ RecRel s'.store rr x := by
  simp only [Arena.iotaRecMajor] at hrun
  obtain ⟨ms, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨c1, hms⟩ := minorsFrom_run pre preP (rP + nIdx - k) _ 0 rfl hok hpre h1
  have hlen : pre.length = preP.length := (ExprOps.denoteEList_length _ _ hpre).symm
  rw [Nat.sub_zero, hlen, ← List.range_eq_range', ← minorsOf_eq] at hms
  obtain ⟨dom, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨c2, hdom⟩ := getD_runC c1.ok (denoteEList_ext c1.ext _ _ hdoms) h3
  obtain ⟨dh, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨rfl, hdh⟩ := getAppFn_run c2.ok.state hdom h5
  by_cases htc : (dh.tag == ETag.const) = true
  · rw [ite_eq_left htc] at h6
    obtain ⟨o, s₄, h7, h8⟩ := AM.bind_ok h6
    obtain ⟨rfl, ho⟩ := viewConst_run h7
    cases o with
    | none => exact absurd h8 (fun hc => failDanglingE_ok hc)
    | some q =>
    obtain ⟨cn, us⟩ := q
    obtain ⟨nm, ls, hgf, -, hus⟩ := denote_const_inv c2.ok.state.wf
      (view_of_viewConst (by simpa using htc) ho.symm) hdh
    dsimp only at h8
    obtain ⟨args, s₅, h9, h10⟩ := AM.bind_ok h8
    obtain ⟨rfl, hargs⟩ := getAppArgs_run c2.ok.state hdom h9
    have hal : args.length = (domsP.getD nIdx default).getAppArgs.length :=
      (ExprOps.denoteEList_length _ _ hargs).symm
    obtain ⟨ps, s₆, h11, h12⟩ := AM.bind_ok h10
    obtain ⟨p6, -, hps⟩ := dropVarsList_run nIdx _ _ c2.ok.state c2.ok.pins
      (denoteEList_take hargs (args.length - nIdx)) h11
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h12
    have c6 := p6.toCore c2.ok
    refine ⟨c1.trans (c2.trans c6), ?_⟩
    intro rr hrr
    obtain rfl := (Option.some.inj hrr).symm
    refine ⟨⟨preP, ConLeche.minorsOf preP (rP + nIdx - k), ls,
      (((domsP.getD nIdx default).getAppArgs.take
        ((domsP.getD nIdx default).getAppArgs.length - nIdx)).map (ConLeche.Expr.dropVars nIdx))⟩,
      by simp only [iotaRecMajorP, hgf], ?_⟩
    refine ⟨denoteEList_ext (c1.ext.trans (c2.ext.trans c6.ext)) _ _ hpre, hms,
      denoteLs_ext hus c6.ext, ?_⟩
    rw [hal] at hps
    exact hps
  · rw [ite_eq_right htc] at h6
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
    exact ⟨c1.trans c2, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — the
recursor's frame, read once: an accepting reading is con-leche's. -/
theorem iotaRecOf_run {s s' : AState} {cv : IConstantVal} {cvP : ConstantVal} {mI rP : Nat}
    {r : Option IotaRec} (hok : CheckOK false env fe s)
    (hcv : Frontend.denoteCV s.store cv = some cvP)
    (hrun : Arena.iotaRecOf cv mI rP s = .ok (r, s')) :
    CoreStep env fe s s' ∧ ∀ rr, r = some rr →
      ∃ x, iotaRecP cvP mI rP = some x ∧ RecRel s'.store rr x := by
  simp only [Arena.iotaRecOf] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨c1, hfr⟩ := iotaFrame_run hok hcv h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨c1, by simp⟩
  | some q =>
  obtain ⟨pre, doms, body, u⟩ := q
  obtain ⟨preP, domsP, bodyP, uP, hf, hpre, hdoms, hbody⟩ := hfr _ _ _ _ rfl
  dsimp only at h2
  obtain ⟨hd, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨rfl, hhd⟩ := getAppFn_run c1.ok.state hbody h3
  by_cases htg : (hd.tag == ETag.bvar) = true
  · rw [ite_eq_left htg] at h4
    obtain ⟨o2, s₃, h5, h6⟩ := AM.bind_ok h4
    obtain ⟨rfl, ho⟩ := viewBVar_run h5
    cases o2 with
    | none => exact absurd h6 (fun hc => failDanglingE_ok hc)
    | some k =>
    have hk : bodyP.getAppFn = .bvar k :=
      denote_bvar_inv c1.ok.state.wf (view_of_viewBVar (by simpa using htg) ho.symm) hhd
    dsimp only at h6
    obtain ⟨c2, hm⟩ := iotaRecMajor_run c1.ok hpre hdoms h6
    refine ⟨c1.trans c2, fun rr hrr => ?_⟩
    obtain ⟨x, hx, hrel⟩ := hm rr hrr
    exact ⟨x, by simp only [iotaRecP, hf, hk, hx], hrel⟩
  · rw [ite_eq_right htg] at h4
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
    exact ⟨c1, by simp⟩

/-! ## A rule's parts off the recursor's type (`iotaPartsOfAt`) -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — the
fields' `mapIdx`, from field `j` on. -/
theorem liftFieldDoms_run (amt : Nat) : ∀ (ds : List EIdx) (dsP : List Expr) (j : Nat)
    {s s' : AState} {r : List EIdx},
    CheckOK false env fe s → Frontend.denoteEList s.store ds = some dsP →
    Arena.liftFieldDoms amt ds j s = .ok (r, s') →
    CoreStep env fe s s' ∧
      Frontend.denoteEList s'.store r = some (dsP.mapIdx (fun k d => d.liftLooseBVars amt (j + k)))
  | [], dsP, j, s, s', r, hok, hd, hrun => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.liftFieldDoms] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, rfl⟩
  | d :: ds, dsP, j, s, s', r, hok, hd, hrun => by
    simp only [Frontend.denoteEList] at hd
    cases h1 : denoteE s.store d with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : Frontend.denoteEList s.store ds with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [Arena.liftFieldDoms] at hrun
    obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, hb⟩ := liftFast_run hok h1 k1
    obtain ⟨bs, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨c2, hbs⟩ := liftFieldDoms_run amt ds xs (j + 1) c1.ok
      (denoteEList_ext c1.ext _ _ h2) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨c1.trans c2, ?_⟩
    have e : (xs.mapIdx fun k d => d.liftLooseBVars amt (j + 1 + k)) =
        xs.mapIdx (fun i d => d.liftLooseBVars amt (j + (i + 1))) := by
      congr 1; funext i d; rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [List.mapIdx_cons, ← e]
    simp only [Frontend.denoteEList, denote_ext hb c2.ext, hbs, Nat.add_zero]

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — the
indices' `map`. -/
theorem liftIdxArgs_run (amt nT nF : Nat) : ∀ (as : List EIdx) (asP : List Expr)
    {s s' : AState} {r : List EIdx},
    CheckOK false env fe s → Frontend.denoteEList s.store as = some asP →
    Arena.liftIdxArgs amt nT nF as s = .ok (r, s') →
    CoreStep env fe s s' ∧
      Frontend.denoteEList s'.store r =
        some (asP.map (fun a => (a.dropVars nT).liftLooseBVars amt nF))
  | [], asP, s, s', r, hok, hd, hrun => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.liftIdxArgs] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, rfl⟩
  | a :: as, asP, s, s', r, hok, hd, hrun => by
    simp only [Frontend.denoteEList] at hd
    cases h1 : denoteE s.store a with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : Frontend.denoteEList s.store as with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [Arena.liftIdxArgs] at hrun
    obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, hb⟩ := dropVars_runC hok h1 k1
    obtain ⟨b2, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨c2, hb2⟩ := liftFast_run c1.ok hb k2
    obtain ⟨bs, s₃, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨c3, hbs⟩ := liftIdxArgs_run amt nT nF as xs c2.ok
      (denoteEList_ext (c1.ext.trans c2.ext) _ _ h2) k3
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
    refine ⟨c1.trans (c2.trans c3), ?_⟩
    simp only [List.map_cons, Frontend.denoteEList, denote_ext hb2 c3.ext, hbs]

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf — the
rule's part, at the recursor's frame: an accepting reading is con-leche's. -/
theorem iotaPartsOfAt_run {s s' : AState} {rr : IotaRec} {x : IotaRecP} {rP nIdx i : Nat}
    {rl : IRecRule} {r : Option IIotaParts} (hok : CheckOK false env fe s)
    (hrr : RecRel s.store rr x)
    (hrun : Arena.iotaPartsOfAt rr rP nIdx i rl s = .ok (r, s')) :
    CoreStep env fe s s' ∧ ∀ p, r = some p →
      ∃ pP, iotaPartsOfAtP x rP nIdx i rl.nfields = some pP ∧ PartsRel s'.store p pP := by
  simp only [Arena.iotaPartsOfAt] at hrun
  by_cases hi : i < rr.minors.length
  · rw [ite_eq_left hi] at hrun
    obtain ⟨d, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨c1, hd⟩ := getD_runC hok hrr.1 h1
    obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, hb⟩ := stripPis_pstep c1.ok.state hd h3
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      exact ⟨c1, by simp⟩
    | some q =>
    obtain ⟨fd, inner⟩ := q
    obtain ⟨fdP, innerP, hsp, hfd, hinner⟩ := denoteBP_some hb
    dsimp only at h4
    obtain ⟨fds, s₃, h5, h6⟩ := AM.bind_ok h4
    obtain ⟨c3, hfds⟩ := liftFieldDoms_run _ fd fdP 0 c1.ok hfd h5
    obtain ⟨t, s₄, h7, h8⟩ := AM.bind_ok h6
    obtain ⟨rfl, ht1, ht2⟩ := piTele_run c3.ok (denote_ext hinner c3.ext) h7
    obtain ⟨args, s₅, h9, h10⟩ := AM.bind_ok h8
    obtain ⟨rfl, hargs⟩ := getAppArgs_run c3.ok.state ht2 h9
    obtain ⟨idx, s₆, h11, h12⟩ := AM.bind_ok h10
    obtain ⟨c6, hidx⟩ := liftIdxArgs_run _ _ _ _ _ c3.ok (denoteEList_take hargs nIdx) h11
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h12
    have cc := c1.trans (c3.trans c6)
    refine ⟨cc, fun p hp => ?_⟩
    obtain rfl := (Option.some.inj hp).symm
    have hq : x.minors[i]? = some (rr.minors.getD i 0) := by
      rw [← hrr.2.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    refine ⟨⟨fdP.mapIdx (fun j d => d.liftLooseBVars (rP - rr.minors.getD i 0) j),
      (innerP.piTele.2.getAppArgs.take nIdx).map
          (fun a => (a.dropVars innerP.piTele.1).liftLooseBVars (rP - rr.minors.getD i 0)
            rl.nfields),
      x.us, x.params⟩, ?_, ?_⟩
    · simp only [iotaPartsOfAtP, hq, hsp]
    · refine ⟨?_, ?_, denoteLs_ext hrr.2.2.1 cc.ext, denoteEList_ext cc.ext _ _ hrr.2.2.2⟩
      · simp only [Nat.zero_add] at hfds
        exact denoteEList_ext c6.ext _ _ hfds
      · rw [ht1] at hidx; exact hidx
  · rw [ite_eq_right hi] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩

/-! ## A rule's parts through its constructor (`iotaPartsAt`) -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:50-58 RecRule.ctorLevels. -/
theorem ctorLevelsAt_run {s s' : AState} {rl : IRecRule} {rlP : RecRule} {lps : List NIdx}
    {lpsP : List ConLeche.Name} {r : LsIdx} (hok : CheckOK false env fe s)
    (hf : Frontend.denoteFire s.store rl.fire = some rlP.fire)
    (hlps : Frontend.denoteNList s.store.ns lps = some lpsP)
    (hrun : Arena.ctorLevelsAt rl lps s = .ok (r, s')) :
    CoreStep env fe s s' ∧ denoteLs s'.store.lss r = some (rlP.ctorLevels lpsP) := by
  simp only [Arena.ctorLevelsAt] at hrun
  unfold ConLeche.RecRule.ctorLevels
  cases hfr : rl.fire with
  | plain =>
    rw [hfr] at hrun hf
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    rw [← hf]
    obtain ⟨p, hr⟩ := paramLevels_run hok.state hlps hrun
    exact ⟨⟨hok.mono p.ok p.ext p.caches p.pins, p.ext, p.pins⟩, hr⟩
  | nested lvls pins =>
    rw [hfr] at hrun hf
    simp only [Frontend.denoteFire] at hf
    cases h1 : denoteLList s.store.ls lvls with
    | none => rw [h1] at hf; simp at hf
    | some ls =>
    cases h2 : Frontend.denoteEList s.store pins with
    | none => rw [h1, h2] at hf; simp at hf
    | some ps =>
    rw [h1, h2] at hf
    rw [← Option.some.inj hf]
    obtain ⟨p, hr⟩ := internLsNode_run hok.state h1 hrun
    exact ⟨p.toCore hok, hr⟩
  | levels lvls =>
    rw [hfr] at hrun hf
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨ls, h1, hls⟩ := hf
    rw [← hls]
    obtain ⟨p, hr⟩ := internLsNode_run hok.state h1 hrun
    exact ⟨p.toCore hok, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:60-66 RecRule.iotaParams —
the prefix's variables from `i` on. -/
theorem iotaBVars_run (rP n : Nat) : ∀ (m i : Nat), n - i = m → ∀ {s s' : AState}
    {r : List EIdx}, CheckOK false env fe s → Arena.iotaBVars rP n i s = .ok (r, s') →
    CoreStep env fe s s' ∧ Frontend.denoteEList s'.store r =
      some ((List.range' i (n - i)).map fun j => Expr.bvar (rP - 1 - j)) := by
  intro m
  induction m with
  | zero =>
    intro i hm s s' r hok hrun
    rw [Arena.iotaBVars, ite_eq_right (by omega)] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by rw [hm]; rfl⟩
  | succ m ih =>
    intro i hm s s' r hok hrun
    rw [Arena.iotaBVars, ite_eq_left (by omega)] at hrun
    obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, hb⟩ := internBVarE_run hok.state k1
    have c1 := p1.toCore hok
    obtain ⟨bs, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨c2, hbs⟩ := ih (i + 1) (by omega) c1.ok k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨c1.trans c2, ?_⟩
    rw [show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ]
    simp only [List.map_cons, Frontend.denoteEList, denote_ext hb c2.ext, hbs]

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:60-66 RecRule.iotaParams. -/
theorem iotaParamsAt_run {s s' : AState} {rl : IRecRule} {rlP : RecRule} {rP cnP : Nat}
    {r : List EIdx} (hok : CheckOK false env fe s)
    (hf : Frontend.denoteFire s.store rl.fire = some rlP.fire)
    (hrun : Arena.iotaParamsAt rl rP cnP s = .ok (r, s')) :
    CoreStep env fe s s' ∧ Frontend.denoteEList s'.store r = some (rlP.iotaParams rP cnP) := by
  simp only [Arena.iotaParamsAt] at hrun
  unfold ConLeche.RecRule.iotaParams
  have bv : ∀ {s₀ : AState}, CheckOK false env fe s₀ →
      Arena.iotaBVars rP (min cnP rP) 0 s₀ = .ok (r, s') →
      CoreStep env fe s₀ s' ∧ Frontend.denoteEList s'.store r =
        some ((List.range (min cnP rP)).map fun i => Expr.bvar (rP - 1 - i)) := by
    intro s₀ h0 hr
    obtain ⟨c, h⟩ := iotaBVars_run rP (min cnP rP) _ 0 rfl h0 hr
    refine ⟨c, ?_⟩
    rw [Nat.sub_zero, ← List.range_eq_range'] at h
    exact h
  cases hfr : rl.fire with
  | plain =>
    rw [hfr] at hrun hf
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    rw [← hf]
    exact bv hok hrun
  | nested lvls pins =>
    rw [hfr] at hrun hf
    simp only [Frontend.denoteFire] at hf
    cases h1 : denoteLList s.store.ls lvls with
    | none => rw [h1] at hf; simp at hf
    | some ls =>
    cases h2 : Frontend.denoteEList s.store pins with
    | none => rw [h1, h2] at hf; simp at hf
    | some ps =>
    rw [h1, h2] at hf
    rw [← Option.some.inj hf]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, h2⟩
  | levels lvls =>
    rw [hfr] at hrun hf
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨ls, -, hls⟩ := hf
    rw [← hls]
    exact bv hok hrun

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:70-82 iotaPartsAt — an
accepting reading is con-leche's, with the parameter domains `paramsAnnEq`
strips off the same instantiated type. -/
theorem iotaPartsAt_run {s s' : AState} {cvj : IConstantVal} {cvjP : ConstantVal}
    {cnP mI rP : Nat} {rl : IRecRule} {rlP : RecRule} {r : Option (IIotaParts × List EIdx)}
    (hok : CheckOK false env fe s) (hcv : Frontend.denoteCV s.store cvj = some cvjP)
    (hrl : Frontend.denoteRule s.store rl = some rlP)
    (hrun : Arena.iotaPartsAt cvj cnP mI rP rl s = .ok (r, s')) :
    CoreStep env fe s s' ∧ ∀ p pd, r = some (p, pd) → ∃ pP pdP rest,
      ConLeche.iotaPartsAt cvjP cnP mI rP rlP = some pP ∧ PartsRel s'.store p pP ∧
      (cvjP.type.instantiateLevelParams cvjP.levelParams
        (rlP.ctorLevels cvjP.levelParams)).stripPis cnP = some (pdP, rest) ∧
      Frontend.denoteEList s'.store pd = some pdP := by
  obtain ⟨-, hlp, hty⟩ := denoteCV_inv hcv
  obtain ⟨-, hfire, -, hnf⟩ := denoteRule_inv hrl
  simp only [Arena.iotaPartsAt] at hrun
  obtain ⟨lvls, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨c1, hlvls⟩ := ctorLevelsAt_run hok hfire hlp h1
  obtain ⟨params, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨c2, hparams⟩ := iotaParamsAt_run c1.ok (denoteFire_ext hfire c1.ext) h3
  have c12 := c1.trans c2
  obtain ⟨ty, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨q1, q2, q3, hty3⟩ := AM.of_run (P := fun t => t = s₂) rfl h5
    (Core.instLPFast_specC (eager := false) (env := env) (fe := fe) s₂ cvj.levelParams lvls
      cvj.type _ _ _ c2.ok (denoteNList_ext c12.ext.lss.ls.ns _ _ hlp)
      (denoteLs_ext hlvls c2.ext) (denote_ext hty c12.ext))
  have c3 : CoreStep env fe s₂ s₃ := ⟨q1, q2, q3⟩
  obtain ⟨o, s₄, h7, h8⟩ := AM.bind_ok h6
  obtain ⟨rfl, hb⟩ := stripPis_pstep q1.state hty3 h7
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h8
    exact ⟨c12.trans c3, by simp⟩
  | some q =>
  obtain ⟨pd, ctorBody⟩ := q
  obtain ⟨pdP, cbP, hsp, hpd, hcb⟩ := denoteBP_some hb
  dsimp only at h8
  simp only [Arena.iotaPartsAtBody] at h8
  obtain ⟨body, s₅, h9, h10⟩ := AM.bind_ok h8
  have hv : ExprOps.InstLVec s₄.store params.toArray (rlP.iotaParams rP cnP).reverse := by
    unfold ExprOps.InstLVec
    rw [List.reverse_reverse, List.toList_toArray]
    exact denoteEList_ext c3.ext _ _ hparams
  obtain ⟨w1, w2, -, w4, w5, -, w7⟩ :=
    ExprOps.instantiateLiftFast_run q1.state hv (by rw [hcb]; rfl) h9
  have c5 : CoreStep env fe s₄ s₅ := ⟨q1.mono w1 w2 w4 w5, w2, w5⟩
  have hbody := w7 _ hcb
  obtain ⟨o2, s₆, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨rfl, hb2⟩ := stripPis_pstep w1 hbody h11
  cases o2 with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h12
    exact ⟨c12.trans (c3.trans c5), by simp⟩
  | some q2 =>
  obtain ⟨fdoms, concl⟩ := q2
  obtain ⟨fdomsP, conclP, hsp2, hfdoms, hconcl⟩ := denoteBP_some hb2
  dsimp only at h12
  obtain ⟨args, s₇, h13, h14⟩ := AM.bind_ok h12
  obtain ⟨rfl, hargs⟩ := getAppArgs_run w1 hconcl h13
  have cc := c12.trans (c3.trans c5)
  have hpl : params.length = (rlP.iotaParams rP cnP).length :=
    (ExprOps.denoteEList_length _ _ hparams).symm
  have hal : args.length = conclP.getAppArgs.length :=
    (ExprOps.denoteEList_length _ _ hargs).symm
  by_cases g1 : params.length = cnP
  · rw [ite_eq_left g1] at h14
    by_cases g2 : rP ≤ mI
    · rw [ite_eq_left g2] at h14
      by_cases g3 : (args.drop cnP).length = mI - rP
      · rw [ite_eq_left g3] at h14
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h14
        refine ⟨cc, fun p pd' he => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨⟨fdomsP, conclP.getAppArgs.drop cnP, rlP.ctorLevels cvjP.levelParams,
          rlP.iotaParams rP cnP⟩, pdP, cbP, ?_, ?_, hsp, denoteEList_ext c5.ext _ _ hpd⟩
        · rw [hnf] at hsp2
          have g3' : conclP.getAppArgs.length - cnP = mI - rP := by
            rw [List.length_drop] at g3; rw [← hal]; exact g3
          simp [ConLeche.iotaPartsAt, hsp, hsp2, ← hpl, g1, g2, g3'] <;> rfl
        · exact ⟨hfdoms, denoteEList_drop hargs cnP,
            denoteLs_ext hlvls (c2.ext.trans (c3.ext.trans c5.ext)),
            denoteEList_ext (c3.ext.trans c5.ext) _ _ hparams⟩
      · rw [ite_eq_right g3] at h14
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h14
        exact ⟨cc, by simp⟩
    · rw [ite_eq_right g2] at h14
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h14
      exact ⟨cc, by simp⟩
  · rw [ite_eq_right g1] at h14
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h14
    exact ⟨cc, by simp⟩

/-! ## The comparisons -/

theorem denoteEList_cons_inv {st : EStore} {a : EIdx} {as : List EIdx} {xs : List Expr}
    (h : Frontend.denoteEList st (a :: as) = some xs) :
    ∃ x xs', xs = x :: xs' ∧ denoteE st a = some x ∧ Frontend.denoteEList st as = some xs' := by
  simp only [Frontend.denoteEList] at h
  cases h1 : denoteE st a with
  | none => rw [h1] at h; simp at h
  | some x =>
  cases h2 : Frontend.denoteEList st as with
  | none => rw [h1, h2] at h; simp at h
  | some xs' =>
  rw [h1, h2] at h
  exact ⟨x, xs', (Option.some.inj h).symm, rfl, rfl⟩

theorem denoteEList_nil_inv {st : EStore} {xs : List Expr}
    (h : Frontend.denoteEList st [] = some xs) : xs = [] := by
  simp only [Frontend.denoteEList, Option.some.injEq] at h; exact h.symm

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:99-112 Expr.lvlEq — the
run form at the core frame. -/
theorem lvlEq_run {s s' : AState} {a b : EIdx} {aP bP : Expr} {r : Bool}
    (hok : CheckOK false env fe s) (ha : denoteE s.store a = some aP)
    (hb : denoteE s.store b = some bP)
    (hrun : lvlEq coreWalkFuel a b s = .ok (r, s')) :
    CoreStep env fe s s' ∧ r = aP.lvlEq bP := by
  obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s) rfl hrun
    (lvlEq_spec coreWalkFuel s a b hok (by rw [ha]; rfl) (by rw [hb]; rfl))
  rw [ha, hb] at h4
  exact ⟨⟨h1, by rw [h2]; exact Ext.refl _, h3⟩, h4⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:160-164 listRel —
`listRel Expr.lvlEq`, exactly. -/
theorem listLvlEq_run : ∀ (as bs : List EIdx) (asP bsP : List Expr) {s s' : AState}
    {r : Bool}, CheckOK false env fe s → Frontend.denoteEList s.store as = some asP →
    Frontend.denoteEList s.store bs = some bsP →
    Arena.listLvlEq as bs s = .ok (r, s') →
    CoreStep env fe s s' ∧ r = ConLeche.listRel Expr.lvlEq asP bsP
  | [], [], asP, bsP, s, s', r, hok, ha, hb, hrun => by
    obtain rfl := denoteEList_nil_inv ha
    obtain rfl := denoteEList_nil_inv hb
    simp only [Arena.listLvlEq] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, rfl⟩
  | [], b :: bs, asP, bsP, s, s', r, hok, ha, hb, hrun => by
    obtain rfl := denoteEList_nil_inv ha
    obtain ⟨y, ys, rfl, -, -⟩ := denoteEList_cons_inv hb
    simp only [Arena.listLvlEq] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, rfl⟩
  | a :: as, [], asP, bsP, s, s', r, hok, ha, hb, hrun => by
    obtain rfl := denoteEList_nil_inv hb
    obtain ⟨x, xs, rfl, -, -⟩ := denoteEList_cons_inv ha
    simp only [Arena.listLvlEq] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, rfl⟩
  | a :: as, b :: bs, asP, bsP, s, s', r, hok, ha, hb, hrun => by
    obtain ⟨x, xs, rfl, hx, hxs⟩ := denoteEList_cons_inv ha
    obtain ⟨y, ys, rfl, hy, hys⟩ := denoteEList_cons_inv hb
    simp only [Arena.listLvlEq] at hrun
    obtain ⟨c, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨c1, hc⟩ := lvlEq_run hok hx hy h1
    cases c with
    | true =>
      rw [ite_eq_left rfl] at h2
      obtain ⟨c2, hr⟩ := listLvlEq_run as bs xs ys c1.ok (denoteEList_ext c1.ext _ _ hxs)
        (denoteEList_ext c1.ext _ _ hys) h2
      exact ⟨c1.trans c2, by simp [ConLeche.listRel, ← hc, hr]⟩
    | false =>
      rw [ite_eq_right (by simp)] at h2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨c1, by simp [ConLeche.listRel, ← hc]⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:114-118 optParamName — a
top-level name, interned. -/
theorem topName_run {s s' : AState} {str : String} {r : NIdx}
    (hok : CheckOK false env fe s) (hrun : Arena.topName str s = .ok (r, s')) :
    CoreStep env fe s s' ∧ denoteN s'.store.ns r = some (.str .anonymous str) := by
  simp only [Arena.topName] at hrun
  obtain ⟨a, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨p1, ha⟩ := internNNode_run hok.state
    (by intro c hc; simp [NNodeView.children] at hc) h1
  have ha' : denoteN s₁.store.ns a = some .anonymous := by rw [ha]; rfl
  obtain ⟨p2, hr⟩ := internStrN_run p1.ok ha' h2
  exact ⟨(p1.trans p2).toCore hok, hr⟩

/-- con-leche: none — a handle comparison that accepts names one term. -/
theorem nidx_eq_of_beq {st : NStore} {a b : NIdx} {x y : ConLeche.Name}
    (h : (a == b) = true) (ha : denoteN st a = some x) (hb : denoteN st b = some y) :
    x = y := by
  rw [beq_iff_eq.mp h, hb] at ha; exact (Option.some.inj ha).symm

section Ann

variable {E : Env} {feR : IFEnv}

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:120-127 annWitness — an
accepting walk is con-leche's verdict. -/
theorem annWitness_run {s s' : AState} {D : EIdx} {DP : Expr} {r : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hD : denoteE s.store D = some DP)
    (hrun : Arena.annWitness feR D s = .ok (r, s')) :
    CoreStep env fe s s' ∧ (r = true → ConLeche.annWitness E.find? DP = true) := by
  simp only [Arena.annWitness] at hrun
  by_cases htc : (D.tag == ETag.const) = true
  · rw [ite_eq_left htc] at hrun
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, ho⟩ := viewConst_run h1
    cases o with
    | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
    | some q =>
    obtain ⟨n, us⟩ := q
    obtain ⟨nm, ls, rfl, hn, hus⟩ := denote_const_inv hok.state.wf
      (view_of_viewConst (by simpa using htc) ho.symm) hD
    dsimp only at h2
    obtain ⟨o2, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, ho2⟩ := viewLsLen_run h3
    rw [Core.viewLen_of_denoteLs hus] at ho2
    subst ho2
    rcases ls with _ | ⟨l, ls'⟩
    · simp only [List.length_nil] at h4
      obtain ⟨m, s₃, h5, h6⟩ := AM.bind_ok h4
      obtain ⟨p3, hm⟩ := internStrN_run hok.state hn h5
      have c3 := p3.toCore hok
      have hfr := IFEnvOK.findRel c3.ok.state (hE.mono c3.ext) hm
      cases hfc : feR.find? m with
      | none =>
        rw [hfc] at h6
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
        exact ⟨c3, by simp⟩
      | some c =>
        rw [hfc] at h6 hfr
        rcases hfr with ⟨h, -⟩ | ⟨ci, cP, hci, hcP, hden⟩
        · exact absurd h (by simp)
        obtain rfl := Option.some.inj hci
        dsimp only at h6
        by_cases ht : (c.toConstantVal.type == D) = true
        · rw [ite_eq_left ht] at h6
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
          refine ⟨c3, fun hr => ?_⟩
          obtain ⟨-, hlp, hty⟩ := denoteCV_inv (denoteCI_toConstantVal hden)
          rw [beq_iff_eq.mp ht, denote_ext hD c3.ext] at hty
          have hlen := denoteNList_length _ _ hlp
          have hr' : c.toConstantVal.levelParams.length = 0 := by simpa using hr
          rw [hr'] at hlen
          simp [ConLeche.annWitness, hcP, ← Option.some.inj hty,
            List.eq_nil_of_length_eq_zero hlen.symm]
        · rw [ite_eq_right ht] at h6
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
          exact ⟨c3, by simp⟩
    · have h4' : (pure false : AM Bool) _ = .ok (r, s') := h4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4'
      exact ⟨CoreStep.refl hok, by simp⟩
  · rw [ite_eq_right htc] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:129-134 annIdentVal —
the body under `fun (α : Sort p')`. -/
theorem annIdentBody_run {s s' : AState} {p p' : NIdx} {pN p'N : ConLeche.Name}
    {arity : Nat} {b : EIdx} {bP : Expr} {r : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hp : denoteN s.store.ns p = some pN) (hp' : denoteN s.store.ns p' = some p'N)
    (hb : denoteE s.store b = some bP)
    (hrun : Arena.annIdentBody feR p p' arity b s = .ok (r, s')) :
    CoreStep env fe s s' ∧
      (r = true → ConLeche.annIdentVal E.find? [pN] arity (.lam (.sort (.param p'N)) bP) = true) := by
  simp only [Arena.annIdentBody] at hrun
  by_cases ha1 : (arity == 1) = true
  · rw [ite_eq_left ha1] at hrun
    obtain rfl : arity = 1 := by simpa using ha1
    by_cases t1 : (b.tag == ETag.bvar) = true
    · rw [ite_eq_left t1] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
      obtain ⟨rfl, ho⟩ := viewBVar_run h1
      cases o with
      | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
      | some j =>
      obtain rfl := denote_bvar_inv hok.state.wf (view_of_viewBVar (by simpa using t1) ho.symm) hb
      dsimp only at h2
      by_cases hj : (j == 0) = true
      · rw [ite_eq_left hj] at h2
        obtain rfl : j = 0 := by simpa using hj
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
        refine ⟨CoreStep.refl hok, fun hr => ?_⟩
        obtain rfl := nidx_eq_of_beq hr hp hp'
        simp [ConLeche.annIdentVal]
      · rw [ite_eq_right hj] at h2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
        exact ⟨CoreStep.refl hok, by simp⟩
    · rw [ite_eq_right t1] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, by simp⟩
  · rw [ite_eq_right ha1] at hrun
    by_cases ha2 : (arity == 2) = true
    · rw [ite_eq_left ha2] at hrun
      obtain rfl : arity = 2 := by simpa using ha2
      by_cases t1 : (b.tag == ETag.lam) = true
      · rw [ite_eq_left t1] at hrun
        obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
        obtain ⟨rfl, ho⟩ := viewBind_run h1
        cases o with
        | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
        | some q =>
        obtain ⟨D, c⟩ := q
        obtain ⟨DP, cP, rfl, hD, hc⟩ := denote_lam_inv hok.state.wf
          (view_of_viewBind_lam (by simpa using t1) ho.symm) hb
        dsimp only at h2
        by_cases t2 : (c.tag == ETag.bvar) = true
        · rw [ite_eq_left t2] at h2
          obtain ⟨o2, s₂, h3, h4⟩ := AM.bind_ok h2
          obtain ⟨rfl, ho2⟩ := viewBVar_run h3
          cases o2 with
          | none => exact absurd h4 (fun hc => failDanglingE_ok hc)
          | some j =>
          obtain rfl := denote_bvar_inv hok.state.wf
            (view_of_viewBVar (by simpa using t2) ho2.symm) hc
          dsimp only at h4
          by_cases hj : (j == 1) = true
          · rw [ite_eq_left hj] at h4
            obtain rfl : j = 1 := by simpa using hj
            by_cases hpp : (p == p') = true
            · rw [ite_eq_left hpp] at h4
              obtain rfl := nidx_eq_of_beq hpp hp hp'
              obtain ⟨z, s₃, h5, h6⟩ := AM.bind_ok h4
              obtain ⟨p5, hz⟩ := internBVarE_run hok.state h5
              have c5 := p5.toCore hok
              by_cases hDz : (D == z) = true
              · rw [ite_eq_left hDz] at h6
                obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
                refine ⟨c5, fun _ => ?_⟩
                have hDP : DP = .bvar 0 := by
                  rw [beq_iff_eq.mp hDz] at hD
                  have := denote_ext hD c5.ext
                  rw [hz] at this; exact (Option.some.inj this).symm
                simp [ConLeche.annIdentVal, hDP]
              · rw [ite_eq_right hDz] at h6
                obtain ⟨c6, hw⟩ := annWitness_run c5.ok (hE.mono c5.ext)
                  (denote_ext hD c5.ext) h6
                refine ⟨c5.trans c6, fun hr => ?_⟩
                simp [ConLeche.annIdentVal, hw hr]
            · rw [ite_eq_right hpp] at h4
              obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
              exact ⟨CoreStep.refl hok, by simp⟩
          · rw [ite_eq_right hj] at h4
            obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
            exact ⟨CoreStep.refl hok, by simp⟩
        · rw [ite_eq_right t2] at h2
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
          exact ⟨CoreStep.refl hok, by simp⟩
      · rw [ite_eq_right t1] at hrun
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        exact ⟨CoreStep.refl hok, by simp⟩
    · rw [ite_eq_right ha2] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:129-134 annIdentVal. -/
theorem annIdentVal_run {s s' : AState} {lps : List NIdx} {lpsP : List ConLeche.Name}
    {arity : Nat} {v : EIdx} {vP : Expr} {r : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hlps : Frontend.denoteNList s.store.ns lps = some lpsP)
    (hv : denoteE s.store v = some vP)
    (hrun : Arena.annIdentVal feR lps arity v s = .ok (r, s')) :
    CoreStep env fe s s' ∧ (r = true → ConLeche.annIdentVal E.find? lpsP arity vP = true) := by
  simp only [Arena.annIdentVal] at hrun
  by_cases h1 : (lps.length == 1) = true
  · rw [ite_eq_left h1] at hrun
    obtain ⟨p0, rfl⟩ : ∃ p0, lps = [p0] := by
      rcases lps with _ | ⟨p0, _ | ⟨_, _⟩⟩ <;> simp at h1
      exact ⟨p0, rfl⟩
    cases hp0 : denoteN s.store.ns p0 with
    | none => simp [Frontend.denoteNList, hp0] at hlps
    | some pN =>
    simp [Frontend.denoteNList, hp0] at hlps
    subst hlps
    by_cases t2 : (v.tag == ETag.lam) = true
    · rw [ite_eq_left t2] at hrun
      obtain ⟨o, s₁, h2, h3⟩ := AM.bind_ok hrun
      obtain ⟨rfl, ho⟩ := viewBind_run h2
      cases o with
      | none => exact absurd h3 (fun hc => failDanglingE_ok hc)
      | some q =>
      obtain ⟨ty, b⟩ := q
      obtain ⟨tyP, bP, rfl, hty, hb⟩ := denote_lam_inv hok.state.wf
        (view_of_viewBind_lam (by simpa using t2) ho.symm) hv
      dsimp only at h3
      by_cases t3 : (ty.tag == ETag.sort) = true
      · rw [ite_eq_left t3] at h3
        obtain ⟨o2, s₂, h4, h5⟩ := AM.bind_ok h3
        obtain ⟨rfl, ho2⟩ := viewSort_run h4
        cases o2 with
        | none => exact absurd h5 (fun hc => failDanglingE_ok hc)
        | some u =>
        obtain ⟨l, rfl, hl⟩ := denote_sort_inv hok.state.wf
          (view_of_viewSort (by simpa using t3) ho2.symm) hty
        dsimp only at h5
        obtain ⟨w, s₃, h6, h7⟩ := AM.bind_ok h5
        obtain ⟨rfl, hw⟩ := viewL_run h6
        obtain ⟨rk, hrk⟩ := hok.state.wf
        cases w with
        | param p' =>
          obtain ⟨p'N, rfl, hp'⟩ := denoteL_param_inv hrk.lsWF hw hl
          dsimp only at h7
          exact annIdentBody_run hok hE hp0 hp' hb h7
        | zero => obtain ⟨rfl, rfl⟩ := AM.pure_ok h7; exact ⟨CoreStep.refl hok, by simp⟩
        | succ a => obtain ⟨rfl, rfl⟩ := AM.pure_ok h7; exact ⟨CoreStep.refl hok, by simp⟩
        | max a b => obtain ⟨rfl, rfl⟩ := AM.pure_ok h7; exact ⟨CoreStep.refl hok, by simp⟩
        | imax a b => obtain ⟨rfl, rfl⟩ := AM.pure_ok h7; exact ⟨CoreStep.refl hok, by simp⟩
      · rw [ite_eq_right t3] at h3
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
        exact ⟨CoreStep.refl hok, by simp⟩
    · rw [ite_eq_right t2] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, by simp⟩
  · rw [ite_eq_right h1] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:136-145 annIdent. -/
theorem annIdent_run {s s' : AState} {n : NIdx} {nm : ConLeche.Name} {arity : Nat} {r : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hn : denoteN s.store.ns n = some nm)
    (hrun : Arena.annIdent feR n arity s = .ok (r, s')) :
    CoreStep env fe s s' ∧ (r = true → ConLeche.annIdent E.find? nm arity = true) := by
  simp only [Arena.annIdent] at hrun
  have hfr := IFEnvOK.findRel hok.state hE hn
  cases hf : feR.find? n with
  | none =>
    rw [hf] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩
  | some ci =>
    rw [hf] at hrun hfr
    rcases hfr with ⟨h, -⟩ | ⟨ci', cP, hci, hcP, hden⟩
    · exact absurd h (by simp)
    obtain rfl := Option.some.inj hci
    cases ci with
    | defnInfo cv v h =>
      dsimp only at hrun
      simp only [Frontend.denoteCI] at hden
      cases hcv : Frontend.denoteCV s.store cv with
      | none => rw [hcv] at hden; simp at hden
      | some cvP =>
      cases hv : denoteE s.store v with
      | none => rw [hcv, hv] at hden; simp at hden
      | some vP =>
      rw [hcv, hv] at hden
      obtain rfl := (Option.some.inj hden).symm
      obtain ⟨c, hr⟩ := annIdentVal_run hok hE (denoteCV_inv hcv).2.1 hv hrun
      exact ⟨c, fun h' => by simp [ConLeche.annIdent, hcP, hr h']⟩
    | axiomInfo _ => obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨CoreStep.refl hok, by simp⟩
    | thmInfo _ => obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨CoreStep.refl hok, by simp⟩
    | indInfo _ _ => obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨CoreStep.refl hok, by simp⟩
    | ctorInfo _ _ _ _ =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨CoreStep.refl hok, by simp⟩
    | recInfo _ _ _ _ _ =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨CoreStep.refl hok, by simp⟩

theorem annEq_of_lvlEq (find? : ConLeche.Name → Option ConstantInfo) {a c : Expr}
    (h : a.lvlEq c = true) : ConLeche.annEq find? a c = true := by
  unfold ConLeche.annEq; split <;> simp [h]

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:147-158 annEq — the
annotation's name and the identity test, at a one-level constant head. -/
theorem annHead_run {s s' : AState} {n : NIdx} {nm : ConLeche.Name} {us : LsIdx}
    {ls : List Level} {arity : Nat} {s1 s2 : String} {K : Prop}
    {k : AM Bool} {r : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hn : denoteN s.store.ns n = some nm) (hus : denoteLs s.store.lss us = some ls)
    (hk : ∀ {t t' : AState} {b : Bool}, CheckOK false env fe t → IFEnvOK E feR t →
      Ext s.store t.store → k t = .ok (b, t') → CoreStep env fe t t' ∧ (b = true → K))
    (hrun : (do
      match ← viewLsLen us with
      | some 1 => do
        let o ← topName s1
        let t ← topName s2
        if n == o || n == t then
          if ← annIdent feR n arity then k else pure false
        else pure false
      | some _ => pure false
      | none => failDanglingLs) s = .ok (r, s')) :
    CoreStep env fe s s' ∧ (r = true → (∃ l, ls = [l]) ∧
      (nm = .str .anonymous s1 ∨ nm = .str .anonymous s2) ∧
      ConLeche.annIdent E.find? nm arity = true ∧ K) := by
  obtain ⟨o4, s₁, h9, h10⟩ := AM.bind_ok hrun
  obtain ⟨rfl, ho4⟩ := viewLsLen_run h9
  rw [Core.viewLen_of_denoteLs hus] at ho4
  subst ho4
  rcases ls with _ | ⟨l, _ | ⟨l2, ls'⟩⟩
  · have h10' : (pure false : AM Bool) _ = .ok (r, s') := h10
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h10'
    exact ⟨CoreStep.refl hok, by simp⟩
  · simp only [List.length_cons, List.length_nil, Nat.zero_add] at h10
    obtain ⟨o, s₂, h11, h12⟩ := AM.bind_ok h10
    obtain ⟨c2, hoN⟩ := topName_run hok h11
    obtain ⟨t, s₃, h13, h14⟩ := AM.bind_ok h12
    obtain ⟨c3, htN⟩ := topName_run c2.ok h13
    have c23 := c2.trans c3
    have hn3 := denoteN_ext hn c23.ext
    by_cases t4 : (n == o || n == t) = true
    · rw [ite_eq_left t4] at h14
      have hname : nm = .str .anonymous s1 ∨ nm = .str .anonymous s2 := by
        simp only [Bool.or_eq_true] at t4
        rcases t4 with h | h
        · exact Or.inl (nidx_eq_of_beq h hn3 (denoteN_ext hoN c3.ext))
        · exact Or.inr (nidx_eq_of_beq h hn3 htN)
      obtain ⟨bi, s₄, h15, h16⟩ := AM.bind_ok h14
      obtain ⟨c4, hbi⟩ := annIdent_run c3.ok (hE.mono c23.ext) hn3 h15
      cases bi with
      | true =>
        rw [ite_eq_left rfl] at h16
        obtain ⟨c5, hK⟩ := hk c4.ok (hE.mono (c23.ext.trans c4.ext)) (c23.ext.trans c4.ext) h16
        exact ⟨c23.trans (c4.trans c5), fun hr => ⟨⟨l, rfl⟩, hname, hbi rfl, hK hr⟩⟩
      | false =>
        rw [ite_eq_right (by simp)] at h16
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h16
        exact ⟨c23.trans c4, by simp⟩
    · rw [ite_eq_right t4] at h14
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h14
      exact ⟨c23, by simp⟩
  · have h10' : (pure false : AM Bool) _ = .ok (r, s') := h10
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h10'
    exact ⟨CoreStep.refl hok, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:147-158 annEq — an
accepting walk is con-leche's verdict. -/
theorem annEq_run : ∀ (fuel : Nat) {s s' : AState} {a c : EIdx} {aP cP : Expr} {r : Bool},
    CheckOK false env fe s → IFEnvOK E feR s → denoteE s.store a = some aP →
    denoteE s.store c = some cP →
    Arena.annEq feR fuel a c s = .ok (r, s') →
    CoreStep env fe s s' ∧ (r = true → ConLeche.annEq E.find? aP cP = true)
  | 0, s, s', a, c, aP, cP, r, hok, hE, ha, hc, hrun => by
    simp only [Arena.annEq] at hrun; exact absurd hrun (fun h => AM.fail_ok h)
  | fuel + 1, s, s', a, c, aP, cP, r, hok, hE, ha, hc, hrun => by
    simp only [Arena.annEq] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨c1, hb⟩ := lvlEq_run hok ha hc h1
    cases b with
    | true =>
      rw [ite_eq_left rfl] at h2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨c1, fun _ => annEq_of_lvlEq _ hb.symm⟩
    | false =>
    rw [ite_eq_right (by simp)] at h2
    have hok1 := c1.ok
    have hE1 := hE.mono c1.ext
    have ha1 := denote_ext ha c1.ext
    have hc1 := denote_ext hc c1.ext
    by_cases t1 : (c.tag == ETag.app) = true
    · rw [ite_eq_left t1] at h2
      obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨rfl, ho⟩ := viewApp_run h3
      cases o with
      | none => exact absurd h4 (fun h => failDanglingE_ok h)
      | some q =>
      obtain ⟨f, x⟩ := q
      obtain ⟨fP, xP, rfl, hf, hx⟩ := denote_app_inv hok1.state.wf
        (view_of_viewApp (by simpa using t1) ho.symm) hc1
      dsimp only at h4
      by_cases t2 : (f.tag == ETag.app) = true
      · rw [ite_eq_left t2] at h4
        obtain ⟨o2, s₃, h5, h6⟩ := AM.bind_ok h4
        obtain ⟨rfl, ho2⟩ := viewApp_run h5
        cases o2 with
        | none => exact absurd h6 (fun h => failDanglingE_ok h)
        | some q2 =>
        obtain ⟨g, a'⟩ := q2
        obtain ⟨gP, aP', rfl, hg, ha'⟩ := denote_app_inv hok1.state.wf
          (view_of_viewApp (by simpa using t2) ho2.symm) hf
        dsimp only at h6
        by_cases t3 : (g.tag == ETag.const) = true
        · rw [ite_eq_left t3] at h6
          obtain ⟨o3, s₄, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨rfl, ho3⟩ := viewConst_run h7
          cases o3 with
          | none => exact absurd h8 (fun h => failDanglingE_ok h)
          | some q3 =>
          obtain ⟨n, us⟩ := q3
          obtain ⟨nm, ls, rfl, hn, hus⟩ := denote_const_inv hok1.state.wf
            (view_of_viewConst (by simpa using t3) ho3.symm) hg
          dsimp only at h8
          obtain ⟨c9, hr⟩ := annHead_run (K := ConLeche.annEq E.find? aP aP' = true)
            (k := Arena.annEq feR fuel a a') hok1 hE1 hn hus
            (fun ht hEt hx hk => annEq_run fuel ht hEt (denote_ext ha1 hx) (denote_ext ha' hx) hk)
            h8
          refine ⟨c1.trans c9, fun hrt => ?_⟩
          obtain ⟨⟨l, rfl⟩, hname, hid, hK⟩ := hr hrt
          simp only [ConLeche.annEq]
          rcases hname with rfl | rfl <;>
            simp [ConLeche.optParamName, ConLeche.autoParamName, hid, hK]
        · rw [ite_eq_right t3] at h6
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
          exact ⟨c1, by simp⟩
      · rw [ite_eq_right t2] at h4
        by_cases t3 : (f.tag == ETag.const) = true
        · rw [ite_eq_left t3] at h4
          obtain ⟨o3, s₄, h7, h8⟩ := AM.bind_ok h4
          obtain ⟨rfl, ho3⟩ := viewConst_run h7
          cases o3 with
          | none => exact absurd h8 (fun h => failDanglingE_ok h)
          | some q3 =>
          obtain ⟨n, us⟩ := q3
          obtain ⟨nm, ls, rfl, hn, hus⟩ := denote_const_inv hok1.state.wf
            (view_of_viewConst (by simpa using t3) ho3.symm) hf
          dsimp only at h8
          obtain ⟨c9, hr⟩ := annHead_run (K := ConLeche.annEq E.find? aP xP = true)
            (k := Arena.annEq feR fuel a x) hok1 hE1 hn hus
            (fun ht hEt hx' hk => annEq_run fuel ht hEt (denote_ext ha1 hx') (denote_ext hx hx') hk)
            h8
          refine ⟨c1.trans c9, fun hrt => ?_⟩
          obtain ⟨⟨l, rfl⟩, hname, hid, hK⟩ := hr hrt
          simp only [ConLeche.annEq]
          rcases hname with rfl | rfl <;>
            simp [ConLeche.outParamName, ConLeche.semiOutParamName, hid, hK]
        · rw [ite_eq_right t3] at h4
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
          exact ⟨c1, by simp⟩
    · rw [ite_eq_right t1] at h2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨c1, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:160-164 listRel —
`listRel (annEq find?)`: an accepting walk is con-leche's verdict. -/
theorem listAnnEq_run : ∀ (as bs : List EIdx) (asP bsP : List Expr) {s s' : AState}
    {r : Bool}, CheckOK false env fe s → IFEnvOK E feR s →
    Frontend.denoteEList s.store as = some asP →
    Frontend.denoteEList s.store bs = some bsP →
    Arena.listAnnEq feR as bs s = .ok (r, s') →
    CoreStep env fe s s' ∧ (r = true → ConLeche.listRel (ConLeche.annEq E.find?) asP bsP = true)
  | [], [], asP, bsP, s, s', r, hok, _, ha, hb, hrun => by
    obtain rfl := denoteEList_nil_inv ha
    obtain rfl := denoteEList_nil_inv hb
    simp only [Arena.listAnnEq] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, fun _ => rfl⟩
  | [], b :: bs, asP, bsP, s, s', r, hok, _, ha, hb, hrun => by
    simp only [Arena.listAnnEq] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩
  | a :: as, [], asP, bsP, s, s', r, hok, _, ha, hb, hrun => by
    simp only [Arena.listAnnEq] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩
  | a :: as, b :: bs, asP, bsP, s, s', r, hok, hE, ha, hb, hrun => by
    obtain ⟨x, xs, rfl, hx, hxs⟩ := denoteEList_cons_inv ha
    obtain ⟨y, ys, rfl, hy, hys⟩ := denoteEList_cons_inv hb
    simp only [Arena.listAnnEq] at hrun
    obtain ⟨c, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨c1, hc⟩ := annEq_run coreWalkFuel hok hE hx hy h1
    cases c with
    | true =>
      rw [ite_eq_left rfl] at h2
      obtain ⟨c2, hr⟩ := listAnnEq_run as bs xs ys c1.ok (hE.mono c1.ext)
        (denoteEList_ext c1.ext _ _ hxs) (denoteEList_ext c1.ext _ _ hys) h2
      exact ⟨c1.trans c2, fun h => by simp [ConLeche.listRel, hc rfl, hr h]⟩
    | false =>
      rw [ite_eq_right (by simp)] at h2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨c1, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:166-175 paramsAnnEq — the
recursor's side of the parameter test. -/
theorem paramsAnnEq_run {s s' : AState} {cnP : Nat} {cv : IConstantVal} {cvP : ConstantVal}
    {pd : List EIdx} {pdP : List Expr} {r : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hcv : Frontend.denoteCV s.store cv = some cvP)
    (hpd : Frontend.denoteEList s.store pd = some pdP)
    (hrun : Arena.paramsAnnEq feR cnP cv pd s = .ok (r, s')) :
    CoreStep env fe s s' ∧ (r = true → ∃ rdP rest, cvP.type.stripPis cnP = some (rdP, rest) ∧
      ConLeche.listRel (ConLeche.annEq E.find?) rdP pdP = true) := by
  simp only [Arena.paramsAnnEq] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hb⟩ := stripPis_pstep hok.state (denoteCV_type hcv) h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨CoreStep.refl hok, by simp⟩
  | some q =>
  obtain ⟨rd, rest⟩ := q
  obtain ⟨rdP, restP, hsp, hrd, -⟩ := denoteBP_some hb
  dsimp only at h2
  obtain ⟨c, hr⟩ := listAnnEq_run rd pd rdP pdP hok hE hrd hpd h2
  exact ⟨c, fun h => ⟨rdP, restP, hsp, hr h⟩⟩

end Ann

/-! ## The rule, the recursor, the block's recursors -/

section Rules

variable {E : Env} {feR : IFEnv}

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:177-185 iotaPartsRel — an
accepting walk is con-leche's verdict. -/
theorem iotaPartsRel_run {s s' : AState} {cnP : Nat} {cv : IConstantVal} {cvP cvjP : ConstantVal}
    {rl : IRecRule} {rlP : RecRule} {p' p : IIotaParts} {p'P pP : IotaParts}
    {pd : List EIdx} {pdP : List Expr} {rest : Expr} {r : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hcv : Frontend.denoteCV s.store cv = some cvP)
    (hfire : Frontend.denoteFire s.store rl.fire = some rlP.fire)
    (hp' : PartsRel s.store p' p'P) (hp : PartsRel s.store p pP)
    (hpdP : (cvjP.type.instantiateLevelParams cvjP.levelParams
      (rlP.ctorLevels cvjP.levelParams)).stripPis cnP = some (pdP, rest))
    (hpd : Frontend.denoteEList s.store pd = some pdP)
    (hrun : Arena.iotaPartsRel feR cnP cv rl p' p pd s = .ok (r, s')) :
    CoreStep env fe s s' ∧
      (r = true → ConLeche.iotaPartsRel E.find? cvjP cnP cvP rlP p'P pP = true) := by
  simp only [Arena.iotaPartsRel] at hrun
  by_cases e1 : ¬ (p'.idx == p.idx) = true
  · rw [ite_eq_right e1] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩
  replace e1 := Decidable.of_not_not e1
  rw [ite_eq_left e1] at hrun
  by_cases e2 : ¬ (p'.us == p.us) = true
  · rw [ite_eq_right e2] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩
  replace e2 := Decidable.of_not_not e2
  rw [ite_eq_left e2] at hrun
  by_cases e3 : ¬ (p'.params == p.params) = true
  · rw [ite_eq_right e3] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩
  replace e3 := Decidable.of_not_not e3
  rw [ite_eq_left e3] at hrun
  have hidx : p'P.idx = pP.idx := by
    have h := hp'.2.1; rw [beq_iff_eq.mp e1, hp.2.1] at h; exact (Option.some.inj h).symm
  have hus : p'P.us = pP.us := by
    have h := hp'.2.2.1; rw [beq_iff_eq.mp e2, hp.2.2.1] at h; exact (Option.some.inj h).symm
  have hpar : p'P.params = pP.params := by
    have h := hp'.2.2.2; rw [beq_iff_eq.mp e3, hp.2.2.2] at h; exact (Option.some.inj h).symm
  obtain ⟨b, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨c1, hb⟩ := listLvlEq_run _ _ _ _ hok hp'.1 hp.1 h1
  cases b with
  | true =>
    rw [ite_eq_left rfl] at h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    refine ⟨c1, fun _ => ?_⟩
    simp [ConLeche.iotaPartsRel, hidx, hus, hpar, ← hb]
  | false =>
  rw [ite_eq_right (by simp)] at h2
  cases hfr : rl.fire with
  | plain =>
    rw [hfr] at h2 hfire
    simp only [Frontend.denoteFire, Option.some.injEq] at hfire
    dsimp only at h2
    obtain ⟨b2, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨c2, hb2⟩ := paramsAnnEq_run c1.ok (hE.mono c1.ext) (denoteCV_ext hcv c1.ext)
      (denoteEList_ext c1.ext _ _ hpd) h3
    cases b2 with
    | true =>
      rw [ite_eq_left rfl] at h4
      have x12 := c1.ext.trans c2.ext
      obtain ⟨c3, hb3⟩ := listAnnEq_run _ _ _ _ c2.ok (hE.mono x12)
        (denoteEList_ext x12 _ _ hp'.1) (denoteEList_ext x12 _ _ hp.1) h4
      refine ⟨c1.trans (c2.trans c3), fun hr => ?_⟩
      obtain ⟨rdP, rest', hsp, hrel⟩ := hb2 rfl
      simp [ConLeche.iotaPartsRel, ConLeche.paramsAnnEq, hidx, hus, hpar, ← hfire, hsp, hpdP,
        hrel, hb3 hr]
    | false =>
      rw [ite_eq_right (by simp)] at h4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      exact ⟨c1.trans c2, by simp⟩
  | nested _ _ =>
    rw [hfr] at h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨c1, by simp⟩
  | levels _ =>
    rw [hfr] at h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨c1, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:187-196 ruleReadsB — an
accepting walk is con-leche's verdict. -/
theorem ruleReads_run {s s' : AState} {cv : IConstantVal} {cvP : ConstantVal}
    {rr : Option IotaRec} {mI rP i : Nat} {rl : IRecRule} {rlP : RecRule} {r : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hcv : Frontend.denoteCV s.store cv = some cvP)
    (hrr : ∀ r0, rr = some r0 → ∃ x, iotaRecP cvP mI rP = some x ∧ RecRel s.store r0 x)
    (hrl : Frontend.denoteRule s.store rl = some rlP)
    (hrun : Arena.ruleReads feR cv rr mI rP i rl s = .ok (r, s')) :
    CoreStep env fe s s' ∧ (r = true → ConLeche.ruleReadsB E.find? cvP mI rP i rlP = true) := by
  simp only [Arena.ruleReads] at hrun
  obtain ⟨hctor, hfire, -, hnf⟩ := denoteRule_inv hrl
  cases rr with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩
  | some r0 =>
  obtain ⟨x, hx, hrel⟩ := hrr r0 rfl
  dsimp only at hrun
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨c1, hpo⟩ := iotaPartsOfAt_run hok hrel h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨c1, by simp⟩
  | some p' =>
  obtain ⟨p'P, hp'P, hp'rel⟩ := hpo p' rfl
  dsimp only at h2
  have hfr := IFEnvOK.findRel c1.ok.state (hE.mono c1.ext) (denoteN_ext hctor c1.ext)
  cases hf : feR.find? rl.ctor with
  | none =>
    rw [hf] at h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨c1, by simp⟩
  | some ci =>
  rw [hf] at h2 hfr
  rcases hfr with ⟨h, -⟩ | ⟨ci', cP, hci, hcP, hden⟩
  · exact absurd h (by simp)
  obtain rfl := Option.some.inj hci
  cases ci with
  | ctorInfo cvj cnP nF T =>
    dsimp only at h2
    simp only [Frontend.denoteCI] at hden
    cases hcvj : Frontend.denoteCV s₁.store cvj with
    | none => rw [hcvj] at hden; simp at hden
    | some cvjP =>
    cases hT : denoteN s₁.store.ns T with
    | none => rw [hcvj, hT] at hden; simp at hden
    | some TP =>
    rw [hcvj, hT] at hden
    obtain rfl := (Option.some.inj hden).symm
    obtain ⟨o2, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨c2, hpa⟩ := iotaPartsAt_run c1.ok hcvj (denoteRule_ext hrl c1.ext) h3
    cases o2 with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      exact ⟨c1.trans c2, by simp⟩
    | some q =>
    obtain ⟨p, pd⟩ := q
    obtain ⟨pP, pdP, rest, hpP, hprel, hpdP, hpd⟩ := hpa p pd rfl
    dsimp only at h4
    have x12 := c1.ext.trans c2.ext
    obtain ⟨c3, hrel3⟩ := iotaPartsRel_run c2.ok (hE.mono x12) (denoteCV_ext hcv x12)
      (denoteFire_ext hfire x12) (hp'rel.mono c2.ext) hprel hpdP hpd h4
    refine ⟨c1.trans (c2.trans c3), fun hr => ?_⟩
    simp only [ConLeche.ruleReadsB, iotaPartsOf_eq, hx, Option.bind_some, ← hnf, hp'P, hcP, hpP]
    exact hrel3 hr
  | axiomInfo _ => obtain ⟨rfl, rfl⟩ := AM.pure_ok h2; exact ⟨c1, by simp⟩
  | defnInfo _ _ _ => obtain ⟨rfl, rfl⟩ := AM.pure_ok h2; exact ⟨c1, by simp⟩
  | thmInfo _ => obtain ⟨rfl, rfl⟩ := AM.pure_ok h2; exact ⟨c1, by simp⟩
  | indInfo _ _ => obtain ⟨rfl, rfl⟩ := AM.pure_ok h2; exact ⟨c1, by simp⟩
  | recInfo _ _ _ _ _ => obtain ⟨rfl, rfl⟩ := AM.pure_ok h2; exact ⟨c1, by simp⟩

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:198-207 recReadsOk —
the rules from position `i` on. -/
theorem rulesRead_run {cv : IConstantVal} {cvP : ConstantVal} {rr : Option IotaRec}
    {mI rP : Nat} : ∀ (rules : List IRecRule) (rulesP : List RecRule) (i : Nat)
    {s s' : AState} {r : Bool}, CheckOK false env fe s → IFEnvOK E feR s →
    Frontend.denoteCV s.store cv = some cvP →
    (∀ r0, rr = some r0 → ∃ x, iotaRecP cvP mI rP = some x ∧ RecRel s.store r0 x) →
    Frontend.denoteRules s.store rules = some rulesP →
    Arena.rulesRead feR cv rr mI rP rules i s = .ok (r, s') →
    CoreStep env fe s s' ∧
      (r = true → ∀ y ∈ rulesP.zipIdx i, ConLeche.ruleReadsB E.find? cvP mI rP y.2 y.1 = true)
  | [], rulesP, i, s, s', r, hok, _, _, _, hd, hrun => by
    simp only [Frontend.denoteRules, Option.some.injEq] at hd
    subst hd
    simp only [Arena.rulesRead] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, by simp⟩
  | rl :: rest, rulesP, i, s, s', r, hok, hE, hcv, hrr, hd, hrun => by
    simp only [Frontend.denoteRules] at hd
    cases h1 : Frontend.denoteRule s.store rl with
    | none => rw [h1] at hd; simp at hd
    | some rlP =>
    cases h2 : Frontend.denoteRules s.store rest with
    | none => rw [h1, h2] at hd; simp at hd
    | some restP =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [Arena.rulesRead] at hrun
    obtain ⟨b, s₁, k1, k2⟩ := AM.bind_ok hrun
    obtain ⟨c1, hb⟩ := ruleReads_run hok hE hcv hrr h1 k1
    cases b with
    | true =>
      rw [ite_eq_left rfl] at k2
      obtain ⟨c2, hall⟩ := rulesRead_run rest restP (i + 1) c1.ok (hE.mono c1.ext)
        (denoteCV_ext hcv c1.ext)
        (fun r0 h => let ⟨x, hx, hr⟩ := hrr r0 h; ⟨x, hx, hr.mono c1.ext⟩)
        (denoteRules_ext c1.ext _ _ h2) k2
      refine ⟨c1.trans c2, fun hr y hy => ?_⟩
      simp only [List.zipIdx_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hb rfl
      · exact hall hr y hy
    | false =>
      rw [ite_eq_right (by simp)] at k2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      exact ⟨c1, by simp⟩

theorem forM_ok {α ε : Type} (g : α → Except ε Unit) :
    ∀ (l : List α), (∀ x ∈ l, g x = .ok ()) → l.forM g = .ok ()
  | [], _ => rfl
  | a :: l, h => by
    have e : (a :: l).forM g = (g a >>= fun _ => l.forM g) := rfl
    rw [e, h a (by simp)]
    exact forM_ok g l (fun x hx => h x (by simp [hx]))

theorem denoteCI_not_rec {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c)
    (hne : ∀ v mI rP k rs, ci ≠ .recInfo v mI rP k rs) :
    ∀ v mI rP k rs, c ≠ .recInfo v mI rP k rs := by
  cases ci <;> simp_all [Frontend.denoteCI, Option.map_eq_some_iff] <;> grind

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:198-207 recReadsOk — an
accepting walk at one constant is con-leche's verdict. -/
theorem recReads_run {s s' : AState} {ci : IConstantInfo} {cP : ConstantInfo} {r : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hd : Frontend.denoteCI s.store ci = some cP)
    (hrun : Arena.recReads feR ci s = .ok (r, s')) :
    CoreStep env fe s s' ∧ (r = true → ConLeche.recReadsOk E.find? cP = .ok ()) := by
  cases ci with
  | recInfo cv mI rP k rules =>
    simp only [Frontend.denoteCI] at hd
    cases hcv : Frontend.denoteCV s.store cv with
    | none => rw [hcv] at hd; simp at hd
    | some cvP =>
    cases hrs : Frontend.denoteRules s.store rules with
    | none => rw [hcv, hrs] at hd; simp at hd
    | some rulesP =>
    rw [hcv, hrs] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [Arena.recReads] at hrun
    obtain ⟨rr, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨c1, hrr⟩ := iotaRecOf_run hok hcv h1
    obtain ⟨c2, hall⟩ := rulesRead_run rules rulesP 0 c1.ok (hE.mono c1.ext)
      (denoteCV_ext hcv c1.ext) hrr (denoteRules_ext c1.ext _ _ hrs) h2
    refine ⟨c1.trans c2, fun hr => ?_⟩
    simp only [ConLeche.recReadsOk]
    apply forM_ok
    intro y hy
    obtain ⟨rl, j⟩ := y
    have hy' := hall hr (rl, j) hy
    dsimp only at hy' ⊢
    rw [hy']
    rfl
  | _ =>
    simp only [Arena.recReads] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨CoreStep.refl hok, fun _ => ?_⟩
    cases cP with
    | recInfo v mI rP k rs =>
      exact absurd rfl (denoteCI_not_rec hd (by intro _ _ _ _ _ h; cases h) v mI rP k rs)
    | _ => rfl

end Rules

/-! ## The recursors' walk -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:210-214 blockReadsOk —
**THEOREM 1 for `recsRead`**: an accepting walk over the block's recursors,
at an index that answers for `E`, is con-leche's `recReadsOk` at every one of
them, at `E.find?`. -/
theorem recsRead_bridge {env E : Env} {fe feR : IFEnv} {s s' : AState}
    {recs : List IConstantInfo} {rs : List ConstantInfo} {b : Bool}
    (hok : CheckOK false env fe s) (hE : IFEnvOK E feR s)
    (hd : Frontend.denoteCIList s.store recs = some rs)
    (hrun : recsRead feR recs s = .ok (b, s')) :
    CheckOK false env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      (b = true → rs.forM (recReadsOk E.find?) = .ok ()) := by
  induction recs generalizing s rs with
  | nil =>
    simp only [Frontend.denoteCIList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.recsRead] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨hok, Ext.refl _, rfl, fun _ => rfl⟩
  | cons ci rest ih =>
    simp only [Frontend.denoteCIList] at hd
    cases h1 : Frontend.denoteCI s.store ci with
    | none => rw [h1] at hd; simp at hd
    | some cP =>
    cases h2 : Frontend.denoteCIList s.store rest with
    | none => rw [h1, h2] at hd; simp at hd
    | some rsP =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [Arena.recsRead] at hrun
    obtain ⟨c, s₁, k1, k2⟩ := AM.bind_ok hrun
    obtain ⟨c1, hc⟩ := recReads_run hok hE h1 k1
    cases c with
    | true =>
      rw [ite_eq_left rfl] at k2
      obtain ⟨o2, x2, p2, hr2⟩ := ih c1.ok (hE.mono c1.ext) (denoteCIList_mono c1.ext _ _ h2) k2
      refine ⟨o2, c1.ext.trans x2, by rw [p2, c1.pins], fun hb => ?_⟩
      have e : (cP :: rsP).forM (recReadsOk E.find?) =
          (recReadsOk E.find? cP >>= fun _ => rsP.forM (recReadsOk E.find?)) := rfl
      rw [e, hc rfl]
      exact hr2 hb
    | false =>
      rw [ite_eq_right (by simp)] at k2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      exact ⟨c1.ok, c1.ext, c1.pins, by simp⟩

/-! ## The block -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:210-214 blockReadsOk —
**THEOREM 1 for the ι reading rule at a block**: the twin pushes the block's
constants onto the input index in place, walks the recursors there and undoes
the pushes.  The index comes back answering as the input one; an accepting
verdict is con-leche's `blockReadsOk` at the environment the block's install
produces, whatever its tables (the rule reads constants only). -/
theorem blockReadsAt_bridge {env : Env} {fe : IFEnv} {s s' : AState}
    {p : Arena.BlockShape} {pP : ConLeche.BlockShape} {r : Bool × IFEnv}
    (hok : CheckOK false env fe s) (hrel : EnvRel env fe s.store)
    (hp : dShape s.store p = some pP)
    (hrun : blockReadsAt fe p s = .ok (r, s')) :
    CheckOK false env r.2 s' ∧ EnvRel env r.2 s'.store ∧ Ext s.store s'.store ∧
      s'.pins = s.pins ∧
      (r.1 = true → ∀ Q, blockReadsOk (env.pushDelta (blockConstants pP) Q).find? pP = .ok ()) := by
  simp only [blockReadsAt] at hrun
  obtain ⟨cs, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨p1, -, hcs⟩ := blockConstants_run hok.state hok.pins hok.caches.readL hp h1
  have c1 : CheckOK false env fe s₁ := CheckOK.monoF hok p1.ok p1.ext p1.cframe p1.pins
  obtain ⟨recs, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨p2, -, hrecs⟩ := blockRecs_run p.recs pP.recs c1.state c1.pins
    (dShape_ext p1.ext _ _ hp) (dRec_ext.list p1.ext _ _ (dShape_inv hp).2.1) h3
  have c2 : CheckOK false env fe s₂ := CheckOK.monoF c1 p2.ok p2.ext p2.cframe p2.pins
  have hcs₂ := denoteCIList_mono p2.ext _ _ hcs
  have hrel₂ : EnvRel env fe s₂.store := hrel.mono (p1.ext.trans p2.ext)
  have hE := BT.consBlockRecsTemp_ok c2.state cs _ fe env [] hcs₂ (hrel₂.ifenv) hrel₂.gate
    hrel₂.stored
  obtain ⟨news, hn, hpop⟩ := BT.consBlockRecsTemp_pop cs fe []
  rw [List.nil_append] at hn
  obtain ⟨ok, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨c3, x3, pn3, hok3⟩ := recsRead_bridge c2 hE hrecs h5
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
  have hfl : FlagsOK ((news.foldr (fun (x : NIdx × Option IConstantInfo) acc =>
      acc.popTemp x.1 x.2) (Arena.consBlockRecsTemp cs fe []).1).setFlags fe.natLit fe.strLit) :=
    (hrel₂.ienv s₂ rfl).flags.of_same (hpop.2.2.1 ▸ rfl)
      (fun n => by rw [IFEnv.setFlags_find?]; exact hpop.find? n) rfl rfl
  have hfeq : GR.FEq ((news.foldr (fun (x : NIdx × Option IConstantInfo) acc =>
      acc.popTemp x.1 x.2) (Arena.consBlockRecsTemp cs fe []).1).setFlags fe.natLit fe.strLit) fe :=
    hpop
  have hrel₃ : EnvRel env _ s'.store := BT.EnvRel.feq hfeq (hrel₂.mono x3) hfl
  simp only [hn]
  refine ⟨⟨c3.state, c3.caches, c3.pins, hrel₃.ifenv⟩, hrel₃, p1.ext.trans (p2.ext.trans x3),
    by rw [pn3, p2.pins, p1.pins], ?_⟩
  · intro hb Q
    have key := hok3 hb
    simp only [ConLeche.blockReadsOk]
    have hfind : (env.pushDelta (ConLeche.blockConstants pP) Q).find? =
        (⟨(ConLeche.blockConstants pP).reverse ++ env.consts, env.tables⟩ : Env).find? := by
      funext n; simp [ConLeche.Env.pushDelta, ConLeche.Env.find?]
    rw [hfind]
    exact key

end ConRon.Bridge.Inductives
