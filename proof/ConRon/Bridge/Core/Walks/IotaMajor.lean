/-
# `ConRon.Bridge.Core.Walks.IotaMajor` — the ι major's preparation

Task #97-P3-Core round 6 (lane `iota`): `litMajorToCtor`, the stuck-major
rescue `majorToCtor` (K, η, the pinned `And`) and `prepareMajor`, which runs
them in the official kernel's order.  See `Walks/Iota.lean`'s note for the two
preconditions (`hμ`, `EnvWF env`).
-/
import ConRon.Bridge.Core.Walks.IotaLeaves

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 2. The major's preparation -/

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — every
major but a string literal takes the `Nat` conversion. -/
theorem litMajorToCtorFueled_nstr {F d : Nat} {x : Expr}
    (hx : ∀ str, x ≠ .lit (.strVal str)) :
    ConLeche.litMajorToCtorFueled mode env F d x =
      .ok (ConLeche.litToCtorIfNat env x) := by
  cases x with
  | lit l =>
    cases l with
    | strVal str => exact absurd rfl (hx str)
    | natVal n => rfl
  | _ => rfl

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — **THEOREM
1 for `litMajorToCtor`**: a `Nat` literal one layer, a supported `String`
literal to its reduced constructor form. -/
theorem litMajorToCtor_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.litMajorToCtor (coreKnot mode fe id fuel) fe d h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.litMajorToCtorFueled mode env F d x) d
          s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  unfold ConRon.Arena.litMajorToCtor
  refine view_bind_triple hv ?_
  -- every major but a string literal: the `Nat` conversion
  have hnat : (∀ str, x ≠ .lit (.strVal str)) →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.litToCtorIfNat fe h
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          SimEOp (fun F => ConLeche.litMajorToCtorFueled mode env F d x) d
            s'.store r⌝⦄ := by
    intro hnl
    refine triple_mono (litToCtorIfNat_spec s₀ h x hok hden) ?_
    rintro r s' ⟨hok', hx', hp', hr⟩
    refine ⟨hok', hx', hp', _, hr, ConLeche.litToCtorIfNat_WScoped hw, 0, ?_⟩
    exact litMajorToCtorFueled_nstr hnl
  cases v
  case lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    cases l with
    | natVal n => exact hnat (by intro str h; cases h)
    | strVal str =>
      dsimp only
      refine triple_seq (strLitSupported_spec s₀ hok) ?_
      rintro sup s1 ⟨hok1, hx1, hp1, hsup⟩
      split
      next hsupt =>
        have hS : ConLeche.strLitSupported env = true := hsup ▸ hsupt
        refine triple_seq (strLitToConstructor_spec s1 str hok1) ?_
        rintro c s2 ⟨hok2, hx2, hp2, hc⟩
        refine triple_mono (hsim.whnf s2 d c _ hok2 hc
          (strLitToConstructor_WScoped str d)) ?_
        rintro r s3 ⟨hok3, hx3, hp3, w, hw3, hww, F, hF⟩
        refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1),
          w, hw3, hww, F, ?_⟩
        simp only [ConLeche.litMajorToCtorFueled, ConLeche.litMajorToCtor, hS,
          if_true]
        exact hF
      next hsupf =>
        have hS : ConLeche.strLitSupported env = false := by
          rw [← hsup]; simpa using hsupf
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok1, hx1, hp1, .lit (.strVal str), denote_ext hden hx1, hw, 0,
          ?_⟩
        simp only [ConLeche.litMajorToCtorFueled, ConLeche.litMajorToCtor, hS,
          Bool.false_eq_true, if_false]
        rfl
  all_goals
    dsimp only
    refine hnat ?_
    intro str hx
    subst hx
    have := view_of_denote_lit hwf hv hden
    cases this

/-! ### `majorToCtor`'s pure side, one function per rescue branch

con-leche's `majorToCtor` at `pureFns mode env F`, past the shared prefix
(not a constructor application, a single rule, its constructor's inductive),
split into the three branches — each a copy of the con-leche text that
`majorToCtorFueled_pre` ties to the original by `rfl`, so the copies cannot
drift. -/

/-- con-leche: ConLeche/Kernel/Core.lean:571-617 majorToCtor — the K branch. -/
def mtcK (mode : CheckMode) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    CheckM Expr :=
  (ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ cvj.levelParams.length = ust.length then
      if cnP ≤ tmaj.getAppArgs.length then
        let fab := Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)
        if fab.wscopedB d && fab.looseBVarsBounded 0 &&
            fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
          ConLeche.iotaCerts (ConLeche.pureFns mode env F) env d false
              (cvj.type.instantiateLevelParams cvj.levelParams ust)
              (tmaj.getAppArgs.take cnP) >>= fun rc =>
          if rc then
            (ConLeche.pureFns mode env F).inferIO d fab >>= fun tfab =>
            (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
            if rd then
              ConLeche.proofIrrel (ConLeche.pureFns mode env F) env d fab major >>=
                fun r => if r then pure fab else pure major
            else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:618-658 majorToCtor — the η branch. -/
def mtcEta (mode : CheckMode) (env : Env) (F d : Nat) (cvj cvT : ConstantVal)
    (caps : IndCaps) (T : ConLeche.Name) (major : Expr) : CheckM Expr :=
  (ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        ConLeche.capsNeverZero cvT.levelParams ust caps = true then
      let fab := Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)
      if fab.wscopedB d && fab.looseBVarsBounded 0 &&
          fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
        ConLeche.iotaCerts (ConLeche.pureFns mode env F) env d false
            (cvj.type.instantiateLevelParams cvj.levelParams ust)
            (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major
              caps.etaFields) >>= fun rc =>
        if rc then
          ConLeche.structEtaCertWith mode (ConLeche.pureFns mode env F) env d fab
              major tmaj >>= fun r =>
          if r then pure fab
          else if caps.etaFields = 0 then
            ConLeche.proofIrrel (ConLeche.pureFns mode env F) env d fab major >>=
              fun r' => if r' then pure fab else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:659-721 majorToCtor — the pinned
`And` branch. -/
def mtcAnd (mode : CheckMode) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    CheckM Expr :=
  (ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
        cvj.levelParams.length = ust.length ∧
        ConLeche.andRescueSlots env rl.ctor cnP ust = true then
      let fab := Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])
      if fab.wscopedB d && fab.looseBVarsBounded 0 &&
          fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
        ConLeche.iotaCerts (ConLeche.pureFns mode env F) env d false
            (cvj.type.instantiateLevelParams cvj.levelParams ust)
            (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major]) >>= fun rc =>
        if rc then
          (ConLeche.pureFns mode env F).inferIO d fab >>= fun tfab =>
          (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
          if rd then
            ConLeche.proofIrrel (ConLeche.pureFns mode env F) env d fab major >>=
              fun r => if r then pure fab else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — the prefix:
past it, the three branches. -/
theorem majorToCtorFueled_pre {F d : Nat} {cn : ConLeche.Name} {rl : RecRule}
    {x : Expr} {cvj cvT : ConstantVal} {cnP cnF : Nat} {T : ConLeche.Name}
    {lus : List Level} {caps : IndCaps}
    (hnc : ConLeche.isCtorApp env x = false)
    (hfj : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hpr : cvj.type.piResult.getAppFn = .const T lus)
    (hfT : env.find? T = some (.indInfo cvT caps)) :
    ConLeche.majorToCtorFueled mode env F d cn [rl] x =
      if rl.k = true then mtcK mode env F d rl cvj cnP T x
      else if rl.eta = true then mtcEta mode env F d cvj cvT caps T x
      else if T = ConLeche.andName then mtcAnd mode env F d rl cvj cnP T x
      else pure x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hfj, hpr,
    hfT, Bool.false_eq_true, if_false]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — a constructor
application stays. -/
theorem majorToCtorFueled_ctor {F d : Nat} {cn : ConLeche.Name}
    {rules : List RecRule} {x : Expr} (h : ConLeche.isCtorApp env x = true) :
    ConLeche.majorToCtorFueled mode env F d cn rules x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, h, if_true]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — every prefix
miss leaves the major alone. -/
theorem majorToCtorFueled_nrules {F d : Nat} {cn : ConLeche.Name}
    {rules : List RecRule} {x : Expr} (hnc : ConLeche.isCtorApp env x = false)
    (h : ∀ rl, rules ≠ [rl]) :
    ConLeche.majorToCtorFueled mode env F d cn rules x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc,
    Bool.false_eq_true, if_false]
  match rules, h with
  | [], _ => rfl
  | [rl], h => exact absurd rfl (h rl)
  | _ :: _ :: _, _ => rfl

theorem majorToCtorFueled_nctor {F d : Nat} {cn : ConLeche.Name} {rl : RecRule}
    {x : Expr} (hnc : ConLeche.isCtorApp env x = false)
    (h : ∀ cvj cnP cnF, env.find? rl.ctor ≠ some (.ctorInfo cvj cnP cnF)) :
    ConLeche.majorToCtorFueled mode env F d cn [rl] x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc,
    Bool.false_eq_true, if_false]
  first
    | rfl
    | (split
       · rename_i cvj cnP cnF heq; exact absurd heq (h cvj cnP cnF)
       · rfl)

theorem majorToCtorFueled_nhead {F d : Nat} {cn : ConLeche.Name} {rl : RecRule}
    {x : Expr} {cvj : ConstantVal} {cnP cnF : Nat}
    (hnc : ConLeche.isCtorApp env x = false)
    (hfj : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (h : ∀ T lus, cvj.type.piResult.getAppFn ≠ .const T lus) :
    ConLeche.majorToCtorFueled mode env F d cn [rl] x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hfj,
    Bool.false_eq_true, if_false]
  first
    | rfl
    | (split
       · rename_i T lus heq; exact absurd heq (h T lus)
       · rfl)

theorem majorToCtorFueled_nind {F d : Nat} {cn : ConLeche.Name} {rl : RecRule}
    {x : Expr} {cvj : ConstantVal} {cnP cnF : Nat} {T : ConLeche.Name}
    {lus : List Level}
    (hnc : ConLeche.isCtorApp env x = false)
    (hfj : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hpr : cvj.type.piResult.getAppFn = .const T lus)
    (h : ∀ cvT caps, env.find? T ≠ some (.indInfo cvT caps)) :
    ConLeche.majorToCtorFueled mode env F d cn [rl] x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hfj, hpr,
    Bool.false_eq_true, if_false]
  first
    | rfl
    | (split
       · rename_i cvT caps heq; exact absurd heq (h cvT caps)
       · rfl)

/-- con-leche: none — two name handles are equal exactly when their
denotations are (`denoteN` is injective on a well-formed store). -/
theorem nidx_eq_iff {st : EStore} (hwf : StoreWF st) {a b : NIdx}
    {x y : ConLeche.Name} (ha : denoteN st.ns a = some x)
    (hb : denoteN st.ns b = some y) : a = b ↔ x = y := by
  obtain ⟨rk, hrk⟩ := hwf
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact denoteN_inj hrk.nsWF ha hb

/-- con-leche: ConLeche/Kernel/Core.lean:571-617 majorToCtor — the K branch
past its three syntactic guards, as a function of the three verdicts. -/
theorem mtcK_fire {F d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T T' : ConLeche.Name} {x tm tmaj tf : Expr} {ust : List Level}
    {b3 b5 b6 : Bool}
    (e1 : ConLeche.inferTypeIO mode env F d x = .ok tm)
    (e2 : ConLeche.whnf mode env F d tm = .ok tmaj)
    (hgf : tmaj.getAppFn = .const T' ust)
    (hg1 : T' = T ∧ cvj.levelParams.length = ust.length)
    (hg2 : cnP ≤ tmaj.getAppArgs.length)
    (hgd : ((Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).wscopedB d &&
      (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).looseBVarsBounded 0 &&
      (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).fvarLeaves.all
        (fun l => x.fvarLeaves.contains l)) = true)
    (h3 : ConLeche.iotaCertsFueled mode env F d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs.take cnP) = .ok b3)
    (h4 : b3 = true → ConLeche.inferTypeIO mode env F d
      (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) = .ok tf)
    (h5 : b3 = true → ConLeche.isDefEqCore mode env F d tmaj tf = .ok b5)
    (h6 : b3 = true → b5 = true → ConLeche.proofIrrelFueled mode env F d
      (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) x = .ok b6) :
    mtcK mode env F d rl cvj cnP T x = .ok (if b3 && b5 && b6 then
      Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP) else x) := by
  have e1' : (ConLeche.pureFns mode env F).inferIO d x = .ok tm := e1
  have e2' : (ConLeche.pureFns mode env F).whnf d tm = .ok tmaj := e2
  have h3' : ConLeche.iotaCerts (ConLeche.pureFns mode env F) env d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs.take cnP) = .ok b3 := h3
  simp only [mtcK, e1', e2', bind, Except.bind, hgf]
  rw [if_pos hg1, if_pos hg2]
  simp only [hgd, if_true, h3']
  cases b3
  · rfl
  · have h4' : (ConLeche.pureFns mode env F).inferIO d
        (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) = .ok tf :=
      h4 rfl
    have h5' : (ConLeche.pureFns mode env F).defeq d tmaj tf = .ok b5 := h5 rfl
    simp only [if_true, h4', h5']
    cases b5
    · rfl
    · have h6' : ConLeche.proofIrrel (ConLeche.pureFns mode env F) env d
          (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) x =
          .ok b6 := h6 rfl rfl
      simp only [if_true, h6']
      cases b6 <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:571-617 majorToCtor — **the K
rescue** (`to_cnstr_when_K`): the parameters-only constructor application
fabricated from the major's type, certified by the constructor's telescope,
the official type check, and proof irrelevance (the two certificate families
gated on `mode.certs`, which `hμ` sets). -/
theorem majorK_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (rl : IRecRule) (rl' : RecRule) (major : EIdx)
    (x : Expr) (icvj : IConstantVal) (dcvj : ConstantVal) (cnP cnF : Nat)
    (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₁) (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hT : denoteN s₁.store.ns T = some Tn)
    (hfj : env.find? rl'.ctor = some (.ctorInfo dcvj cnP cnF)) :
    ⦃fun s => ⌜s = s₁⌝⦄ (do
      let tmaj ← (coreKnot mode fe id fuel).whnf d
        (← (coreKnot mode fe id fuel).inferIO d major)
      match ← view (← getAppFn coreWalkFuel tmaj) with
      | .const T' ust => do
        let ustl ← viewLs ust
        if T' = T ∧ icvj.levelParams.length = ustl.length then do
          let targs ← getAppArgs coreWalkFuel tmaj
          if cnP ≤ targs.length then do
            let hd ← internE (.const rl.ctor ust)
            let fab ← mkAppN hd (targs.take cnP)
            if ← fabScopeOk d fab major then do
              let famK ←
                if mode.certs then
                  ConRon.Arena.iotaCerts (coreKnot mode fe id fuel) fe d false
                    (← constTyAt icvj ust) (targs.take cnP)
                else pure true
              if famK then do
                if ← (coreKnot mode fe id fuel).defeq d tmaj
                    (← (coreKnot mode fe id fuel).inferIO d fab) then do
                  let irK ←
                    if mode.certs then
                      ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d fab major
                    else pure true
                  if irK then pure fab else pure major
                else pure major
              else pure major
            else pure major
          else pure major
        else pure major
      | _ => pure major : AM EIdx)
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (fun F => mtcK mode env F d rl' dcvj cnP Tn x) d s'.store r⌝⦄ := by
  have hcert : mode.certs = true := ConLeche.certs_of_verifiedChecks hμ
  obtain ⟨_, _, _, _, hrlc, _, _⟩ := rule_denote hrl'
  obtain ⟨_, hlpsj, _⟩ := denoteCV_inv hdcvj
  have hnamej : dcvj.name = rl'.ctor := env_find_name hfj
  -- stage: the major's io-grade type, head-normalised
  refine triple_seq (hsim.inferIO s₁ d major x hok hmaj hw) ?_
  rintro tm s2 ⟨hok2, hx2, hp2, vtm, hvtm, hwvtm, F1, hF1⟩
  refine triple_seq (hsim.whnf s2 d tm vtm hok2 hvtm hwvtm) ?_
  rintro tmaj s3 ⟨hok3, hx3, hp3, vtmaj, hvtmaj, hwvtmaj, F2, hF2⟩
  have hx13 := hx2.trans hx3
  have hp13 : s3.pins = s₁.pins := hp3.trans hp2
  have hwf3 := hok3.state.wf
  have hA : ∀ G, max F1 F2 ≤ G →
      (ConLeche.pureFns mode env G).inferIO d x = .ok vtm ∧
      (ConLeche.pureFns mode env G).whnf d vtm = .ok vtmaj := fun G hG =>
    ⟨ConLeche.inferTypeIO_mono (by omega) hF1, ConLeche.whnf_mono (by omega) hF2⟩
  -- stage: the type's head
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s3 tmaj hok3.state
    (by rw [hvtmaj]; rfl)) ?_
  rintro hh s4 ⟨hs4, hrelF⟩
  subst s4
  have hdd := hrelF vtmaj hvtmaj
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine view_bind_triple hvh ?_
  cases vh
  case const T' ust =>
    obtain ⟨Tn', lsu, hgf, hTn', hlsu⟩ := denote_const_inv hwf3 hvh hdd
    dsimp only
    refine triple_seq (viewLs_spec s3 ust) ?_
    rintro ustl s5 ⟨hs5, hustl⟩
    subst s5
    have hul := view_len_of_denoteLs hlsu hustl
    have hcond : (T' = T ∧ icvj.levelParams.length = ustl.length) ↔
        (Tn' = Tn ∧ dcvj.levelParams.length = lsu.length) := by
      rw [nidx_eq_iff hwf3 hTn' (denoteN_ext hT hx13), hul,
        ← denoteNList_len hlpsj]
    by_cases hg1 : T' = T ∧ icvj.levelParams.length = ustl.length
    · rw [if_pos hg1]
      have hg1P := hcond.mp hg1
      refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s3 tmaj hok3.state
        (by rw [hvtmaj]; rfl)) ?_
      rintro targs s6 ⟨hs6, hrelA⟩
      subst s6
      have htargs := hrelA vtmaj hvtmaj
      have htl := denoteEList_len htargs
      by_cases hg2 : cnP ≤ targs.length
      · rw [if_pos hg2]
        have hg2P : cnP ≤ vtmaj.getAppArgs.length := by rw [htl]; exact hg2
        refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
          s3 (.const rl.ctor ust) hok3 (viewOK_const
            (nview_isSome_of_denote (denoteN_ext hrlc hx13))
            (by obtain ⟨w, hw', _⟩ := denoteLs_view hlsu; rw [hw']; rfl))) ?_
        rintro hd s7 ⟨hok7, hx7, hp7, hhd⟩
        have hhd' : denoteE s7.store hd = some (.const rl'.ctor lsu) := by
          rw [hhd]
          simp only [denoteEView, denoteN_ext (denoteN_ext hrlc hx13) hx7,
            denoteLs_ext hlsu hx7, opt2]
        have htk := ExprOps.denoteEList_take cnP _ _ (denoteEList_ext hx7 _ _ htargs)
        refine triple_seq (ExprOps.mkAppN_spec (targs.take cnP) s7 hd hok7.state
          (by rw [hhd']; rfl) (by rw [htk]; rfl)) ?_
        rintro fab s8 ⟨hst8, hx8, _, _, hc8, hp8, hrel⟩
        have hok8 : CheckOK mode env fe s8 := hok7.mono hst8 hx8 hc8 hp8
        have hfab := hrel _ _ hhd' htk
        have hx18 := hx13.trans (hx7.trans hx8)
        have hp18 : s8.pins = s₁.pins := hp8.trans (hp7.trans hp13)
        refine triple_seq (fabScopeOk_spec s8 d fab major _ x hok8 hfab
          (denote_ext hmaj hx18)) ?_
        rintro gd s9 ⟨hok9, hst9, hp9, hgd⟩
        have hx19 : Ext s₁.store s9.store := by rw [hst9]; exact hx18
        have hp19 : s9.pins = s₁.pins := hp9.trans hp18
        by_cases hgt : gd = true
        · rw [if_pos hgt]
          have hgP := hgd ▸ hgt
          have hwfab : Expr.WScoped d (Expr.mkAppN (.const rl'.ctor lsu)
              (vtmaj.getAppArgs.take cnP)) := by
            simp only [Bool.and_eq_true] at hgP
            exact Expr.WScoped.of_wscopedB hgP.1.1
          have hx39 : Ext s3.store s9.store := hx7.trans (by rw [hst9]; exact hx8)
          have hTs : ∀ {b3 b5 b6 : Bool} {tf : Expr} {G : Nat}, max F1 F2 ≤ G →
              ConLeche.iotaCertsFueled mode env G d false
                (dcvj.type.instantiateLevelParams dcvj.levelParams lsu)
                (vtmaj.getAppArgs.take cnP) = .ok b3 →
              (b3 = true → ConLeche.inferTypeIO mode env G d
                (Expr.mkAppN (.const rl'.ctor lsu) (vtmaj.getAppArgs.take cnP)) = .ok tf) →
              (b3 = true → ConLeche.isDefEqCore mode env G d vtmaj tf = .ok b5) →
              (b3 = true → b5 = true → ConLeche.proofIrrelFueled mode env G d
                (Expr.mkAppN (.const rl'.ctor lsu) (vtmaj.getAppArgs.take cnP)) x = .ok b6) →
              mtcK mode env G d rl' dcvj cnP Tn x = .ok (if b3 && b5 && b6 then
                Expr.mkAppN (.const rl'.ctor lsu) (vtmaj.getAppArgs.take cnP) else x) := by
            intro b3 b5 b6 tf G hG h3 h4 h5 h6
            obtain ⟨e1, e2⟩ := hA G hG
            have hg1' : Tn' = Tn ∧ dcvj.levelParams.length = lsu.length := hg1P
            rw [← hg1'.1]
            exact mtcK_fire e1 e2 hgf ⟨rfl, hg1'.2⟩ hg2P hgP h3 h4 h5 h6
          rw [if_pos hcert]
          refine triple_seq (constTyAt_spec s9 icvj ust rl'.ctor lsu (.ctorInfo dcvj cnP cnF)
            hok9 (by rw [denoteCV_name (denoteCV_ext hdcvj hx19), hnamej])
            (denoteLs_ext hlsu hx39) hfj (denoteCV_ext hdcvj hx19)) ?_
          rintro tyC s10 ⟨hok10, hx10, hp10, htyC⟩
          have hwtyC : Expr.WScoped d
              (dcvj.type.instantiateLevelParams dcvj.levelParams lsu) :=
            Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfj lsu)
          have htk10 := ExprOps.denoteEList_take cnP _ _
            (denoteEList_ext (hx39.trans hx10) _ _ htargs)
          refine triple_seq (iotaCerts_spec hsim d false tyC (targs.take cnP) s10 hok10
            ⟨_, _, htyC, hwtyC, htk10, fun z hz =>
              Expr.WScoped.getAppArgs hwvtmaj z (List.mem_of_mem_take hz)⟩) ?_
          rintro c1 s11 ⟨hok11, hx11, hp11, hc1⟩
          obtain ⟨F3, hF3⟩ := hc1 _ _ htyC htk10
          have hx311 := hx39.trans (hx10.trans hx11)
          have hx111 := hx19.trans (hx10.trans hx11)
          have hp111 : s11.pins = s₁.pins := hp11.trans (hp10.trans hp19)
          by_cases hc1t : c1 = true
          · rw [if_pos hc1t]
            subst hc1t
            have hfab11 := denote_ext hfab (by rw [← hst9]; exact hx10.trans hx11)
            refine triple_seq (hsim.inferIO s11 d fab _ hok11 hfab11 hwfab) ?_
            rintro tf s12 ⟨hok12, hx12, hp12, vtf, hvtf, hwvtf, F4, hF4⟩
            refine triple_seq (hsim.defeq s12 d tmaj tf vtmaj vtf hok12
              (denote_ext hvtmaj (hx311.trans hx12)) hvtf hwvtmaj hwvtf) ?_
            rintro rd s13 ⟨hok13, hx13', hp13', F5, hF5⟩
            have hx113 := hx111.trans (hx12.trans hx13')
            have hp113 : s13.pins = s₁.pins := hp13'.trans (hp12.trans hp111)
            by_cases hrd : rd = true
            · rw [if_pos hrd]
              subst hrd
              rw [if_pos hcert]
              refine triple_seq (proofIrrel_spec hsim s13 d fab major _ x hok13
                (denote_ext hfab11 (hx12.trans hx13')) (denote_ext hmaj hx113) hwfab hw) ?_
              rintro ir s14 ⟨hok14, hx14, hp14, F6, hF6⟩
              have hv := hTs (b3 := true) (b5 := true) (b6 := ir)
                (G := max (max F1 F2) (max F3 (max F4 (max F5 F6)))) (by omega)
                (iotaCertsFueled_mono (by omega) hF3)
                (fun _ => ConLeche.inferTypeIO_mono (by omega) hF4)
                (fun _ => ConLeche.isDefEqCore_mono (by omega) hF5)
                (fun _ _ => proofIrrelFueled_mono (by omega) hF6)
              have hfab14 := denote_ext hfab11 (hx12.trans (hx13'.trans hx14))
              have hmaj14 := denote_ext hmaj (hx113.trans hx14)
              cases ir
              · mvcgen
                bridge_peel; subst_vars
                exact ⟨hok14, hx113.trans hx14, hp14.trans hp113, x, hmaj14, hw, _, hv⟩
              · mvcgen
                bridge_peel; subst_vars
                exact ⟨hok14, hx113.trans hx14, hp14.trans hp113, _, hfab14, hwfab, _, hv⟩
            · rw [if_neg hrd]
              have hrdf : rd = false := by simpa using hrd
              subst hrdf
              have hv := hTs (b3 := true) (b5 := false) (b6 := false)
                (G := max (max F1 F2) (max F3 (max F4 F5))) (by omega)
                (iotaCertsFueled_mono (by omega) hF3)
                (fun _ => ConLeche.inferTypeIO_mono (by omega) hF4)
                (fun _ => ConLeche.isDefEqCore_mono (by omega) hF5)
                (fun _ h => by cases h)
              mvcgen
              bridge_peel; subst_vars
              exact ⟨hok13, hx113, hp113, x, denote_ext hmaj hx113, hw, _, hv⟩
          · rw [if_neg hc1t]
            have hc1f : c1 = false := by simpa using hc1t
            subst hc1f
            have hv := hTs (b3 := false) (b5 := false) (b6 := false) (tf := x)
              (G := max (max F1 F2) F3) (by omega)
              (iotaCertsFueled_mono (by omega) hF3)
              (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
            mvcgen
            bridge_peel; subst_vars
            exact ⟨hok11, hx111, hp111, x, denote_ext hmaj hx111, hw, _, hv⟩
        · rw [if_neg hgt]
          have hgf' : gd = false := by simpa using hgt
          have hres : ∀ G, max F1 F2 ≤ G →
              mtcK mode env G d rl' dcvj cnP Tn x = .ok x := by
            intro G hG
            obtain ⟨e1, e2⟩ := hA G hG
            simp only [mtcK, e1, e2, bind, Except.bind, hgf]
            rw [if_pos hg1P, if_pos hg2P]
            simp only [← hgd, hgf']
            rfl
          mvcgen
          bridge_peel; subst_vars
          exact ⟨hok9, hx19, hp19, x, denote_ext hmaj hx19, hw, _,
            hres _ (Nat.le_refl _)⟩
      · rw [if_neg hg2]
        have hres : ∀ G, max F1 F2 ≤ G →
            mtcK mode env G d rl' dcvj cnP Tn x = .ok x := by
          intro G hG
          obtain ⟨e1, e2⟩ := hA G hG
          simp only [mtcK, e1, e2, bind, Except.bind, hgf]
          rw [if_pos hg1P, if_neg (by rw [htl]; exact hg2)]
          rfl
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok3, hx13, hp13, x, denote_ext hmaj hx13, hw, _,
          hres _ (Nat.le_refl _)⟩
    · rw [if_neg hg1]
      have hres : ∀ G, max F1 F2 ≤ G →
          mtcK mode env G d rl' dcvj cnP Tn x = .ok x := by
        intro G hG
        obtain ⟨e1, e2⟩ := hA G hG
        simp only [mtcK, e1, e2, bind, Except.bind, hgf]
        rw [if_neg (fun h => hg1 (hcond.mpr h))]
        rfl
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok3, hx13, hp13, x, denote_ext hmaj hx13, hw, _,
        hres _ (Nat.le_refl _)⟩
  all_goals
    dsimp only
    have hnc := denote_not_const hwf3 hvh hdd (by intro c us h; cases h)
    have hres : ∀ G, max F1 F2 ≤ G →
        mtcK mode env G d rl' dcvj cnP Tn x = .ok x := by
      intro G hG
      obtain ⟨e1, e2⟩ := hA G hG
      simp only [mtcK, e1, e2, bind, Except.bind]
      first
        | rfl
        | (split
           · rename_i c us heq; exact absurd heq (hnc c us)
           · rfl)
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok3, hx13, hp13, x, denote_ext hmaj hx13, hw, _, hres _ (Nat.le_refl _)⟩

/-- con-leche: none — a denoted capability record's fields. -/
theorem denoteCaps_fields {st : EStore} {c : IIndCaps} {dc : IndCaps}
    (h : Frontend.denoteCaps st c = some dc) :
    dc.eta = c.eta ∧ denoteN st.ns c.etaCtor = some dc.etaCtor ∧
      dc.etaParams = c.etaParams ∧ dc.etaFields = c.etaFields ∧
      dc.sortZ = c.sortZ := by
  simp only [Frontend.denoteCaps] at h
  split at h
  · rename_i ct hct; cases h; exact ⟨rfl, hct, rfl, rfl, rfl⟩
  · simp at h

/-- con-leche: ConLeche/Kernel/Core.lean:618-658 majorToCtor — the η branch
past its guards, as a function of the three verdicts. -/
theorem mtcEta_fire {F d : Nat} {cvj cvT : ConstantVal} {caps : IndCaps}
    {T T' : ConLeche.Name} {x tm tmaj : Expr} {ust : List Level}
    {b3 b4 b5 : Bool}
    (e1 : ConLeche.inferTypeIO mode env F d x = .ok tm)
    (e2 : ConLeche.whnf mode env F d tm = .ok tmaj)
    (hgf : tmaj.getAppFn = .const T' ust)
    (hg : T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
      ust.length = cvT.levelParams.length ∧
      ConLeche.capsNeverZero cvT.levelParams ust caps = true)
    (hgd : ((Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields)).wscopedB d &&
      (Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields)).looseBVarsBounded 0 &&
      (Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields)).fvarLeaves.all
        (fun l => x.fvarLeaves.contains l)) = true)
    (h3 : ConLeche.iotaCertsFueled mode env F d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields) = .ok b3)
    (h4 : b3 = true → ConLeche.structEtaCertWithFueled mode env F d
      (Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields)) x tmaj
      = .ok b4)
    (h5 : b3 = true → b4 = false → caps.etaFields = 0 →
      ConLeche.proofIrrelFueled mode env F d
        (Expr.mkAppN (.const caps.etaCtor ust)
          (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields)) x
        = .ok b5) :
    mtcEta mode env F d cvj cvT caps T x = .ok
      (if b3 && (b4 || (decide (caps.etaFields = 0) && b5)) then
        Expr.mkAppN (.const caps.etaCtor ust)
          (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields)
      else x) := by
  have e1' : (ConLeche.pureFns mode env F).inferIO d x = .ok tm := e1
  have e2' : (ConLeche.pureFns mode env F).whnf d tm = .ok tmaj := e2
  have h3' : ConLeche.iotaCerts (ConLeche.pureFns mode env F) env d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields) = .ok b3 := h3
  simp only [mtcEta, e1', e2', bind, Except.bind, hgf]
  rw [if_pos hg]
  simp only [hgd, if_true, h3']
  cases b3
  · rfl
  · have h4' : ConLeche.structEtaCertWith mode (ConLeche.pureFns mode env F) env d
        (Expr.mkAppN (.const caps.etaCtor ust)
          (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields)) x tmaj
        = .ok b4 := h4 rfl
    simp only [if_true, h4']
    cases b4
    · simp only [Bool.false_eq_true, if_false]
      by_cases hz : caps.etaFields = 0
      · have h5' : ConLeche.proofIrrel (ConLeche.pureFns mode env F) env d
            (Expr.mkAppN (.const caps.etaCtor ust)
              (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs x caps.etaFields)) x
            = .ok b5 := h5 rfl rfl hz
        rw [if_pos hz]
        simp only [h5']
        cases b5 <;> simp [hz, pure, Except.pure]
      · rw [if_neg hz]
        simp [hz, pure, Except.pure]
    · simp [pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:659-721 majorToCtor — the `And`
branch past its guards, as a function of the three verdicts. -/
theorem mtcAnd_fire {F d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T T' : ConLeche.Name} {x tm tmaj tf : Expr} {ust : List Level}
    {b3 b5 b6 : Bool}
    (e1 : ConLeche.inferTypeIO mode env F d x = .ok tm)
    (e2 : ConLeche.whnf mode env F d tm = .ok tmaj)
    (hgf : tmaj.getAppFn = .const T' ust)
    (hg : T' = T ∧ tmaj.getAppArgs.length = cnP ∧
      cvj.levelParams.length = ust.length ∧
      ConLeche.andRescueSlots env rl.ctor cnP ust = true)
    (hgd : ((Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])).wscopedB d &&
      (Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])).looseBVarsBounded 0 &&
      (Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])).fvarLeaves.all
        (fun l => x.fvarLeaves.contains l)) = true)
    (h3 : ConLeche.iotaCertsFueled mode env F d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x]) = .ok b3)
    (h4 : b3 = true → ConLeche.inferTypeIO mode env F d
      (Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])) = .ok tf)
    (h5 : b3 = true → ConLeche.isDefEqCore mode env F d tmaj tf = .ok b5)
    (h6 : b3 = true → b5 = true → ConLeche.proofIrrelFueled mode env F d
      (Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])) x = .ok b6) :
    mtcAnd mode env F d rl cvj cnP T x = .ok (if b3 && b5 && b6 then
      Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x]) else x) := by
  have e1' : (ConLeche.pureFns mode env F).inferIO d x = .ok tm := e1
  have e2' : (ConLeche.pureFns mode env F).whnf d tm = .ok tmaj := e2
  have h3' : ConLeche.iotaCerts (ConLeche.pureFns mode env F) env d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x]) = .ok b3 := h3
  simp only [mtcAnd, e1', e2', bind, Except.bind, hgf]
  rw [if_pos hg]
  simp only [hgd, if_true, h3']
  cases b3
  · rfl
  · have h4' : (ConLeche.pureFns mode env F).inferIO d
        (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])) = .ok tf := h4 rfl
    have h5' : (ConLeche.pureFns mode env F).defeq d tmaj tf = .ok b5 := h5 rfl
    simp only [if_true, h4', h5']
    cases b5
    · rfl
    · have h6' : ConLeche.proofIrrel (ConLeche.pureFns mode env F) env d
          (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])) x = .ok b6 := h6 rfl rfl
      simp only [if_true, h6']
      cases b6 <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:618-658 majorToCtor — **the η
rescue** (`to_cnstr_when_structure`): the constructor of the major's
projections, fabricated at an instantiated-never-`Prop` structure, certified
by the synthetic spine's telescope (a family, gated on `mode.certs`) and the
structure-η certificate, or — at the 0-field basis `PUnit` — proof
irrelevance. -/
theorem majorEta_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (rl' : RecRule) (major : EIdx) (x : Expr)
    (icvj : IConstantVal) (dcvj : ConstantVal) (cnP cnF : Nat)
    (icvT : IConstantVal) (dcvT : ConstantVal) (icaps : IIndCaps)
    (dcaps : IndCaps) (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₁)
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hdcvT : Frontend.denoteCV s₁.store icvT = some dcvT)
    (hcaps : Frontend.denoteCaps s₁.store icaps = some dcaps)
    (hT : denoteN s₁.store.ns T = some Tn)
    (hcj : denoteN s₁.store.ns icvj.name = some rl'.ctor)
    (hfj : env.find? rl'.ctor = some (.ctorInfo dcvj cnP cnF)) :
    ⦃fun s => ⌜s = s₁⌝⦄ (do
      let tmaj ← (coreKnot mode fe id fuel).whnf d
        (← (coreKnot mode fe id fuel).inferIO d major)
      match ← view (← getAppFn coreWalkFuel tmaj) with
      | .const T' ust => do
        let ustl ← viewLs ust
        let targs ← getAppArgs coreWalkFuel tmaj
        let nz ← capsNeverZero icvT.levelParams ust icaps
        if T' = T ∧ targs.length = icaps.etaParams ∧
            ustl.length = icvT.levelParams.length ∧ nz = true then do
          let fabArgs ← etaFabArgsE fe T ust targs major icaps.etaFields
          let hd ← internE (.const icaps.etaCtor ust)
          let fab ← mkAppN hd fabArgs
          if ← fabScopeOk d fab major then do
            let famE ←
              if mode.certs then
                ConRon.Arena.iotaCerts (coreKnot mode fe id fuel) fe d false
                  (← constTyAt icvj ust) fabArgs
              else pure true
            if famE then do
              if ← ConRon.Arena.structEtaCertWith mode (coreKnot mode fe id fuel) fe d
                  fab major tmaj then
                pure fab
              else if icaps.etaFields = 0 then do
                if ← ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d fab major
                then pure fab
                else pure major
              else pure major
            else pure major
          else pure major
        else pure major
      | _ => pure major : AM EIdx)
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (fun F => mtcEta mode env F d dcvj dcvT dcaps Tn x) d s'.store r⌝⦄ := by
  have hcert : mode.certs = true := ConLeche.certs_of_verifiedChecks hμ
  obtain ⟨_, hlpsT, _⟩ := denoteCV_inv hdcvT
  obtain ⟨_, hctor, hep, hef, _⟩ := denoteCaps_fields hcaps
  -- stage: the major's io-grade type, head-normalised
  refine triple_seq (hsim.inferIO s₁ d major x hok hmaj hw) ?_
  rintro tm s2 ⟨hok2, hx2, hp2, vtm, hvtm, hwvtm, F1, hF1⟩
  refine triple_seq (hsim.whnf s2 d tm vtm hok2 hvtm hwvtm) ?_
  rintro tmaj s3 ⟨hok3, hx3, hp3, vtmaj, hvtmaj, hwvtmaj, F2, hF2⟩
  have hx13 := hx2.trans hx3
  have hp13 : s3.pins = s₁.pins := hp3.trans hp2
  have hwf3 := hok3.state.wf
  have hA : ∀ G, max F1 F2 ≤ G →
      ConLeche.inferTypeIO mode env G d x = .ok vtm ∧
      ConLeche.whnf mode env G d vtm = .ok vtmaj := fun G hG =>
    ⟨ConLeche.inferTypeIO_mono (by omega) hF1, ConLeche.whnf_mono (by omega) hF2⟩
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s3 tmaj hok3.state
    (by rw [hvtmaj]; rfl)) ?_
  rintro hh s4 ⟨hs4, hrelF⟩
  subst s4
  have hdd := hrelF vtmaj hvtmaj
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine view_bind_triple hvh ?_
  cases vh
  case const T' ust =>
    obtain ⟨Tn', lsu, hgf, hTn', hlsu⟩ := denote_const_inv hwf3 hvh hdd
    dsimp only
    refine triple_seq (viewLs_spec s3 ust) ?_
    rintro ustl s5 ⟨hs5, hustl⟩
    subst s5
    have hul := view_len_of_denoteLs hlsu hustl
    refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s3 tmaj hok3.state
      (by rw [hvtmaj]; rfl)) ?_
    rintro targs s6 ⟨hs6, hrelA⟩
    subst s6
    have htargs := hrelA vtmaj hvtmaj
    have htl := denoteEList_len htargs
    refine triple_seq (capsNeverZero_spec s3 icvT.levelParams ust icaps
      dcvT.levelParams lsu dcaps hok3 (denoteNListE_ext hx13 _ _ hlpsT) hlsu
      (by
        simp only [Frontend.denoteCaps] at hcaps ⊢
        rw [denoteN_ext hctor hx13]
        split at hcaps
        · rename_i ct hct
          rw [hctor] at hct; cases hct; exact hcaps
        · simp at hcaps)) ?_
    rintro nz s7 ⟨hok7, hst7, hp7, hnz⟩
    have hx37 : Ext s3.store s7.store := by rw [hst7]; exact Ext.refl _
    have hcond : (T' = T ∧ targs.length = icaps.etaParams ∧
        ustl.length = icvT.levelParams.length ∧ nz = true) ↔
        (Tn' = Tn ∧ vtmaj.getAppArgs.length = dcaps.etaParams ∧
          lsu.length = dcvT.levelParams.length ∧
          ConLeche.capsNeverZero dcvT.levelParams lsu dcaps = true) := by
      rw [nidx_eq_iff hwf3 hTn' (denoteN_ext hT hx13), ← htl, hep, hul,
        ← denoteNList_len hlpsT, hnz]
    by_cases hg : T' = T ∧ targs.length = icaps.etaParams ∧
        ustl.length = icvT.levelParams.length ∧ nz = true
    · rw [if_pos hg]
      have hgP := hcond.mp hg
      have htargs7 := denoteEList_ext hx37 _ _ htargs
      refine triple_seq (etaFabArgsE_spec s7 T ust targs major icaps.etaFields Tn lsu
        vtmaj.getAppArgs x hok7 (denoteN_ext hT (hx13.trans hx37))
        (denoteLs_ext hlsu hx37) htargs7 (denote_ext hmaj (hx13.trans hx37))) ?_
      rintro fabArgs s8 ⟨hok8, hx8, hp8, hfa⟩
      rw [← hef] at hfa
      refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
        s8 (.const icaps.etaCtor ust) hok8 (viewOK_const
          (nview_isSome_of_denote (denoteN_ext hctor (hx13.trans (hx37.trans hx8))))
          (by obtain ⟨w, hw', _⟩ := denoteLs_view (denoteLs_ext hlsu (hx37.trans hx8))
              rw [hw']; rfl))) ?_
      rintro hd s9 ⟨hok9, hx9, hp9, hhd⟩
      have hhd' : denoteE s9.store hd = some (.const dcaps.etaCtor lsu) := by
        rw [hhd]
        simp only [denoteEView, denoteN_ext hctor (hx13.trans (hx37.trans (hx8.trans hx9))),
          denoteLs_ext hlsu (hx37.trans (hx8.trans hx9)), opt2]
      have hfa9 := denoteEList_ext hx9 _ _ hfa
      refine triple_seq (ExprOps.mkAppN_spec fabArgs s9 hd hok9.state
        (by rw [hhd']; rfl) (by rw [hfa9]; rfl)) ?_
      rintro fab s10 ⟨hst10, hx10, _, _, hc10, hp10, hrel⟩
      have hok10 : CheckOK mode env fe s10 := hok9.mono hst10 hx10 hc10 hp10
      have hfab := hrel _ _ hhd' hfa9
      have hx110 := hx13.trans (hx37.trans (hx8.trans (hx9.trans hx10)))
      have hp110 : s10.pins = s₁.pins :=
        hp10.trans (hp9.trans (hp8.trans (hp7.trans hp13)))
      refine triple_seq (fabScopeOk_spec s10 d fab major _ x hok10 hfab
        (denote_ext hmaj hx110)) ?_
      rintro gd s11 ⟨hok11, hst11, hp11, hgd⟩
      have hx111 : Ext s₁.store s11.store := by rw [hst11]; exact hx110
      have hp111 : s11.pins = s₁.pins := hp11.trans hp110
      have hTs : ∀ {b3 b4 b5 : Bool} {G : Nat}, max F1 F2 ≤ G →
          (gd = true) →
          ConLeche.iotaCertsFueled mode env G d false
            (dcvj.type.instantiateLevelParams dcvj.levelParams lsu)
            (ConLeche.etaFabArgsE env Tn lsu vtmaj.getAppArgs x dcaps.etaFields) = .ok b3 →
          (b3 = true → ConLeche.structEtaCertWithFueled mode env G d
            (Expr.mkAppN (.const dcaps.etaCtor lsu)
              (ConLeche.etaFabArgsE env Tn lsu vtmaj.getAppArgs x dcaps.etaFields))
            x vtmaj = .ok b4) →
          (b3 = true → b4 = false → dcaps.etaFields = 0 →
            ConLeche.proofIrrelFueled mode env G d
              (Expr.mkAppN (.const dcaps.etaCtor lsu)
                (ConLeche.etaFabArgsE env Tn lsu vtmaj.getAppArgs x dcaps.etaFields))
              x = .ok b5) →
          mtcEta mode env G d dcvj dcvT dcaps Tn x = .ok
            (if b3 && (b4 || (decide (dcaps.etaFields = 0) && b5)) then
              Expr.mkAppN (.const dcaps.etaCtor lsu)
                (ConLeche.etaFabArgsE env Tn lsu vtmaj.getAppArgs x dcaps.etaFields)
            else x) := by
        intro b3 b4 b5 G hG hgt h3 h4 h5
        obtain ⟨e1, e2⟩ := hA G hG
        obtain ⟨hTT, hr⟩ := hgP
        subst hTT
        exact mtcEta_fire e1 e2 hgf ⟨rfl, hr⟩ (hgd ▸ hgt) h3 h4 h5
      by_cases hgt : gd = true
      · rw [if_pos hgt]
        have hgP' := hgd ▸ hgt
        have hwfab : Expr.WScoped d (Expr.mkAppN (.const dcaps.etaCtor lsu)
            (ConLeche.etaFabArgsE env Tn lsu vtmaj.getAppArgs x dcaps.etaFields)) := by
          simp only [Bool.and_eq_true] at hgP'
          exact Expr.WScoped.of_wscopedB hgP'.1.1
        have hwargs : ∀ z ∈ ConLeche.etaFabArgsE env Tn lsu vtmaj.getAppArgs x
            dcaps.etaFields, Expr.WScoped d z := fun z hz =>
          Expr.WScoped.getAppArgs hwfab z (by
            rw [Expr.getAppArgs_mkAppN]; simpa [Expr.getAppArgs] using hz)
        have hx311 : Ext s3.store s11.store := by
          rw [hst11]; exact hx37.trans (hx8.trans (hx9.trans hx10))
        rw [if_pos hcert]
        refine triple_seq (constTyAt_spec s11 icvj ust rl'.ctor lsu
          (.ctorInfo dcvj cnP cnF) hok11 (denoteN_ext hcj hx111)
          (denoteLs_ext hlsu hx311)
          hfj (by
            have := denoteCV_ext hdcvj hx111
            exact this)) ?_
        rintro tyC s12 ⟨hok12, hx12, hp12, htyC⟩
        have hwtyC : Expr.WScoped d
            (dcvj.type.instantiateLevelParams dcvj.levelParams lsu) :=
          Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfj lsu)
        have hfa12 := denoteEList_ext (hx10.trans (by rw [← hst11]; exact hx12)) _ _ hfa9
        refine triple_seq (iotaCerts_spec hsim d false tyC fabArgs s12 hok12
          ⟨_, _, htyC, hwtyC, hfa12, hwargs⟩) ?_
        rintro c1 s13 ⟨hok13, hx13', hp13', hc1⟩
        obtain ⟨F3, hF3⟩ := hc1 _ _ htyC hfa12
        have hx113 := hx111.trans (hx12.trans hx13')
        have hp113 : s13.pins = s₁.pins := hp13'.trans (hp12.trans hp111)
        have hfab13 := denote_ext hfab (by rw [← hst11]; exact hx12.trans hx13')
        by_cases hc1t : c1 = true
        · rw [if_pos hc1t]
          subst hc1t
          refine triple_seq (structEtaCertWith_spec hμ henv hsim s13 d fab major tmaj
            _ x vtmaj hok13 hfab13 (denote_ext hmaj hx113)
            (denote_ext hvtmaj (hx311.trans (hx12.trans hx13')))
            hwfab hw hwvtmaj) ?_
          rintro b4 s14 ⟨hok14, hx14, hp14, F4, hF4⟩
          have hx114 := hx113.trans hx14
          have hp114 : s14.pins = s₁.pins := hp14.trans hp113
          have hfab14 := denote_ext hfab13 hx14
          by_cases hb4 : b4 = true
          · rw [if_pos hb4]
            subst hb4
            have hv := hTs (b3 := true) (b4 := true) (b5 := false)
              (G := max (max F1 F2) (max F3 F4)) (by omega) hgt
              (iotaCertsFueled_mono (by omega) hF3)
              (fun _ => structEtaCertWithFueled_mono (by omega) hF4)
              (fun _ h => by cases h)
            mvcgen
            bridge_peel; subst_vars
            exact ⟨hok14, hx114, hp114, _, hfab14, hwfab, _, hv⟩
          · rw [if_neg hb4]
            have hb4f : b4 = false := by simpa using hb4
            subst hb4f
            by_cases hz : icaps.etaFields = 0
            · rw [if_pos hz]
              have hz' : dcaps.etaFields = 0 := by rw [hef]; exact hz
              refine triple_seq (proofIrrel_spec hsim s14 d fab major _ x hok14
                hfab14 (denote_ext hmaj hx114) hwfab hw) ?_
              rintro ir s15 ⟨hok15, hx15, hp15, F5, hF5⟩
              have hv := hTs (b3 := true) (b4 := false) (b5 := ir)
                (G := max (max F1 F2) (max F3 (max F4 F5))) (by omega) hgt
                (iotaCertsFueled_mono (by omega) hF3)
                (fun _ => structEtaCertWithFueled_mono (by omega) hF4)
                (fun _ _ _ => proofIrrelFueled_mono (by omega) hF5)
              have hfab15 := denote_ext hfab14 hx15
              have hmaj15 := denote_ext hmaj (hx114.trans hx15)
              cases ir
              · simp [hz'] at hv
                mvcgen
                bridge_peel; subst_vars
                exact ⟨hok15, hx114.trans hx15, hp15.trans hp114, x, hmaj15, hw, _, hv⟩
              · rw [if_pos (by simp [hz'] : (true && (false ||
                  (decide (dcaps.etaFields = 0) && true))) = true)] at hv
                mvcgen
                bridge_peel; subst_vars
                exact ⟨hok15, hx114.trans hx15, hp15.trans hp114, _, hfab15, hwfab,
                  _, hv⟩
            · rw [if_neg hz]
              have hz' : dcaps.etaFields ≠ 0 := by rw [hef]; exact hz
              have hv := hTs (b3 := true) (b4 := false) (b5 := false)
                (G := max (max F1 F2) (max F3 F4)) (by omega) hgt
                (iotaCertsFueled_mono (by omega) hF3)
                (fun _ => structEtaCertWithFueled_mono (by omega) hF4)
                (fun _ _ h => absurd h hz')
              simp at hv
              mvcgen
              bridge_peel; subst_vars
              exact ⟨hok14, hx114, hp114, x, denote_ext hmaj hx114, hw, _, hv⟩
        · rw [if_neg hc1t]
          have hc1f : c1 = false := by simpa using hc1t
          subst hc1f
          have hv := hTs (b3 := false) (b4 := false) (b5 := false)
            (G := max (max F1 F2) F3) (by omega) hgt
            (iotaCertsFueled_mono (by omega) hF3)
            (fun h => by cases h) (fun h => by cases h)
          mvcgen
          bridge_peel; subst_vars
          exact ⟨hok13, hx113, hp113, x, denote_ext hmaj hx113, hw, _, hv⟩
      · rw [if_neg hgt]
        have hgf' : gd = false := by simpa using hgt
        have hres : ∀ G, max F1 F2 ≤ G →
            mtcEta mode env G d dcvj dcvT dcaps Tn x = .ok x := by
          intro G hG
          obtain ⟨e1, e2⟩ := hA G hG
          have e1' : (ConLeche.pureFns mode env G).inferIO d x = .ok vtm := e1
          have e2' : (ConLeche.pureFns mode env G).whnf d vtm = .ok vtmaj := e2
          obtain ⟨hTT, hr⟩ := hgP
          subst hTT
          simp only [mtcEta, e1', e2', bind, Except.bind, hgf]
          rw [if_pos (by first | exact ⟨rfl, hr⟩ | exact ⟨trivial, hr⟩)]
          simp only [← hgd, hgf']
          rfl
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok11, hx111, hp111, x, denote_ext hmaj hx111, hw, _,
          hres _ (Nat.le_refl _)⟩
    · rw [if_neg hg]
      have hres : ∀ G, max F1 F2 ≤ G →
          mtcEta mode env G d dcvj dcvT dcaps Tn x = .ok x := by
        intro G hG
        obtain ⟨e1, e2⟩ := hA G hG
        have e1' : (ConLeche.pureFns mode env G).inferIO d x = .ok vtm := e1
        have e2' : (ConLeche.pureFns mode env G).whnf d vtm = .ok vtmaj := e2
        simp only [mtcEta, e1', e2', bind, Except.bind, hgf]
        rw [if_neg (fun h => hg (hcond.mpr h))]
        rfl
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok7, by rw [hst7]; exact hx13, hp7.trans hp13, x,
        denote_ext hmaj (by rw [hst7]; exact hx13), hw, _, hres _ (Nat.le_refl _)⟩
  all_goals
    dsimp only
    have hnc := denote_not_const hwf3 hvh hdd (by intro c us h; cases h)
    have hres : ∀ G, max F1 F2 ≤ G →
        mtcEta mode env G d dcvj dcvT dcaps Tn x = .ok x := by
      intro G hG
      obtain ⟨e1, e2⟩ := hA G hG
      have e1' : (ConLeche.pureFns mode env G).inferIO d x = .ok vtm := e1
      have e2' : (ConLeche.pureFns mode env G).whnf d vtm = .ok vtmaj := e2
      simp only [mtcEta, e1', e2', bind, Except.bind]
      first
        | rfl
        | (split
           · rename_i c us heq; exact absurd heq (hnc c us)
           · rfl)
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok3, hx13, hp13, x, denote_ext hmaj hx13, hw, _, hres _ (Nat.le_refl _)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:659-721 majorToCtor — **the pinned
`And` rescue**: `And.intro` of the major's two projections, certified the K
branch's way (the synthetic spine, the type check, proof irrelevance; the two
families gated on `mode.certs`). -/
theorem majorAnd_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (rl : IRecRule) (rl' : RecRule) (major : EIdx)
    (x : Expr) (icvj : IConstantVal) (dcvj : ConstantVal) (cnP cnF : Nat)
    (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₁) (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hT : denoteN s₁.store.ns T = some Tn)
    (hfj : env.find? rl'.ctor = some (.ctorInfo dcvj cnP cnF)) :
    ⦃fun s => ⌜s = s₁⌝⦄ (do
      let tmaj ← (coreKnot mode fe id fuel).whnf d
        (← (coreKnot mode fe id fuel).inferIO d major)
      match ← view (← getAppFn coreWalkFuel tmaj) with
      | .const T' ust => do
        match ← viewLsLen ust with
        | none => failDanglingLs
        | some ustl =>
        let targs ← getAppArgs coreWalkFuel tmaj
        let ars ← andRescueSlots fe rl.ctor cnP ust
        if T' = T ∧ targs.length = cnP ∧
            icvj.levelParams.length = ustl ∧ ars = true then do
          let p0 ← internE (.proj T 0 major)
          let p1 ← internE (.proj T 1 major)
          let fabArgs := targs ++ [p0, p1]
          let hd ← internE (.const rl.ctor ust)
          let fab ← mkAppN hd fabArgs
          if ← fabScopeOk d fab major then do
            let famA ←
              if mode.certs then
                ConRon.Arena.iotaCerts (coreKnot mode fe id fuel) fe d false
                  (← constTyAt icvj ust) fabArgs
              else pure true
            if famA then do
              if ← (coreKnot mode fe id fuel).defeq d tmaj
                  (← (coreKnot mode fe id fuel).inferIO d fab) then do
                let irA ←
                  if mode.certs then
                    ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d fab major
                  else pure true
                if irA then pure fab else pure major
              else pure major
            else pure major
          else pure major
        else pure major
      | _ => pure major : AM EIdx)
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (fun F => mtcAnd mode env F d rl' dcvj cnP Tn x) d s'.store r⌝⦄ := by
  have hcert : mode.certs = true := ConLeche.certs_of_verifiedChecks hμ
  obtain ⟨_, _, _, _, hrlc, _, _⟩ := rule_denote hrl'
  obtain ⟨_, hlpsj, _⟩ := denoteCV_inv hdcvj
  have hnamej : dcvj.name = rl'.ctor := env_find_name hfj
  refine triple_seq (hsim.inferIO s₁ d major x hok hmaj hw) ?_
  rintro tm s2 ⟨hok2, hx2, hp2, vtm, hvtm, hwvtm, F1, hF1⟩
  refine triple_seq (hsim.whnf s2 d tm vtm hok2 hvtm hwvtm) ?_
  rintro tmaj s3 ⟨hok3, hx3, hp3, vtmaj, hvtmaj, hwvtmaj, F2, hF2⟩
  have hx13 := hx2.trans hx3
  have hp13 : s3.pins = s₁.pins := hp3.trans hp2
  have hwf3 := hok3.state.wf
  have hA : ∀ G, max F1 F2 ≤ G →
      ConLeche.inferTypeIO mode env G d x = .ok vtm ∧
      ConLeche.whnf mode env G d vtm = .ok vtmaj := fun G hG =>
    ⟨ConLeche.inferTypeIO_mono (by omega) hF1, ConLeche.whnf_mono (by omega) hF2⟩
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s3 tmaj hok3.state
    (by rw [hvtmaj]; rfl)) ?_
  rintro hh s4 ⟨hs4, hrelF⟩
  subst s4
  have hdd := hrelF vtmaj hvtmaj
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine view_bind_triple hvh ?_
  cases vh
  case const T' ust =>
    obtain ⟨Tn', lsu, hgf, hTn', hlsu⟩ := denote_const_inv hwf3 hvh hdd
    dsimp only
    refine triple_seq (viewLsLen_spec s3 ust) ?_
    rintro ol s5 ⟨hs5, hol⟩
    subst s5
    rw [viewLen_of_denoteLs hlsu] at hol
    subst hol
    dsimp only
    refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s3 tmaj hok3.state
      (by rw [hvtmaj]; rfl)) ?_
    rintro targs s6 ⟨hs6, hrelA⟩
    subst s6
    have htargs := hrelA vtmaj hvtmaj
    have htl := denoteEList_len htargs
    refine triple_seq (andRescueSlots_spec s3 rl.ctor cnP ust rl'.ctor lsu hok3
      (denoteN_ext hrlc hx13) hlsu) ?_
    rintro ars s7 ⟨hok7, hx7, hp7, hars⟩
    have hx17 := hx13.trans hx7
    have hp17 : s7.pins = s₁.pins := hp7.trans hp13
    have hcond : (T' = T ∧ targs.length = cnP ∧ icvj.levelParams.length = lsu.length ∧
        ars = true) ↔ (Tn' = Tn ∧ vtmaj.getAppArgs.length = cnP ∧
          dcvj.levelParams.length = lsu.length ∧
          ConLeche.andRescueSlots env rl'.ctor cnP lsu = true) := by
      rw [nidx_eq_iff hwf3 hTn' (denoteN_ext hT hx13), ← htl,
        ← denoteNList_len hlpsj, hars]
    by_cases hg : T' = T ∧ targs.length = cnP ∧ icvj.levelParams.length = lsu.length ∧
        ars = true
    · rw [if_pos hg]
      have hgP := hcond.mp hg
      have hwf7 := hok7.state.wf
      refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
        s7 (.proj T 0 major) hok7 (viewOK_proj
          (nview_isSome_of_denote (denoteN_ext hT hx17))
          (by rw [denote_ext hmaj hx17]; rfl))) ?_
      rintro p0 s8 ⟨hok8, hx8, hp8, hp0⟩
      have hx18 := hx17.trans hx8
      have hp0' : denoteE s8.store p0 = some (.proj Tn 0 x) := by
        rw [hp0]; simp only [denoteEView, denoteN_ext hT hx18, denote_ext hmaj hx18, opt2]
      refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
        s8 (.proj T 1 major) hok8 (viewOK_proj
          (nview_isSome_of_denote (denoteN_ext hT hx18))
          (by rw [denote_ext hmaj hx18]; rfl))) ?_
      rintro p1 s9 ⟨hok9, hx9, hp9, hp1⟩
      have hx19 := hx18.trans hx9
      have hp1' : denoteE s9.store p1 = some (.proj Tn 1 x) := by
        rw [hp1]; simp only [denoteEView, denoteN_ext hT hx19, denote_ext hmaj hx19, opt2]
      try dsimp only
      refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
        s9 (.const rl.ctor ust) hok9 (viewOK_const
          (nview_isSome_of_denote (denoteN_ext hrlc hx19))
          (by obtain ⟨w, hw', _⟩ := denoteLs_view (denoteLs_ext hlsu (hx7.trans (hx8.trans hx9)))
              rw [hw']; rfl))) ?_
      rintro hd s10 ⟨hok10, hx10, hp10, hhd⟩
      have hx110 := hx19.trans hx10
      have hhd' : denoteE s10.store hd = some (.const rl'.ctor lsu) := by
        rw [hhd]
        simp only [denoteEView, denoteN_ext hrlc hx110,
          denoteLs_ext hlsu (hx7.trans (hx8.trans (hx9.trans hx10))), opt2]
      have hfa : Frontend.denoteEList s10.store (targs ++ [p0, p1]) =
          some (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x]) :=
        denoteEList_appendI
          (denoteEList_ext (hx7.trans (hx8.trans (hx9.trans hx10))) _ _ htargs)
          (by simp [Frontend.denoteEList, denote_ext hp0' (hx9.trans hx10),
                denote_ext hp1' hx10])
      refine triple_seq (ExprOps.mkAppN_spec _ s10 hd hok10.state
        (by rw [hhd']; rfl) (by rw [hfa]; rfl)) ?_
      rintro fab s11 ⟨hst11, hx11, _, _, hc11, hp11, hrel⟩
      have hok11 : CheckOK mode env fe s11 := hok10.mono hst11 hx11 hc11 hp11
      have hfab := hrel _ _ hhd' hfa
      have hx111 := hx110.trans hx11
      have hp111 : s11.pins = s₁.pins :=
        hp11.trans (hp10.trans (hp9.trans (hp8.trans hp17)))
      refine triple_seq (fabScopeOk_spec s11 d fab major _ x hok11 hfab
        (denote_ext hmaj hx111)) ?_
      rintro gd s12 ⟨hok12, hst12, hp12, hgd⟩
      have hx112 : Ext s₁.store s12.store := by rw [hst12]; exact hx111
      have hp112 : s12.pins = s₁.pins := hp12.trans hp111
      have hTs : ∀ {b3 b5 b6 : Bool} {tf : Expr} {G : Nat}, max F1 F2 ≤ G →
          gd = true →
          ConLeche.iotaCertsFueled mode env G d false
            (dcvj.type.instantiateLevelParams dcvj.levelParams lsu)
            (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x]) = .ok b3 →
          (b3 = true → ConLeche.inferTypeIO mode env G d
            (Expr.mkAppN (.const rl'.ctor lsu)
              (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x])) = .ok tf) →
          (b3 = true → ConLeche.isDefEqCore mode env G d vtmaj tf = .ok b5) →
          (b3 = true → b5 = true → ConLeche.proofIrrelFueled mode env G d
            (Expr.mkAppN (.const rl'.ctor lsu)
              (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x])) x = .ok b6) →
          mtcAnd mode env G d rl' dcvj cnP Tn x = .ok (if b3 && b5 && b6 then
            Expr.mkAppN (.const rl'.ctor lsu)
              (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x]) else x) := by
        intro b3 b5 b6 tf G hG hgt h3 h4 h5 h6
        obtain ⟨e1, e2⟩ := hA G hG
        obtain ⟨hTT, hr⟩ := hgP
        subst hTT
        exact mtcAnd_fire e1 e2 hgf ⟨rfl, hr⟩ (hgd ▸ hgt) h3 h4 h5 h6
      by_cases hgt : gd = true
      · rw [if_pos hgt]
        have hgP' := hgd ▸ hgt
        have hwfab : Expr.WScoped d (Expr.mkAppN (.const rl'.ctor lsu)
            (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x])) := by
          simp only [Bool.and_eq_true] at hgP'
          exact Expr.WScoped.of_wscopedB hgP'.1.1
        have hwargs : ∀ z ∈ vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x],
            Expr.WScoped d z := fun z hz =>
          Expr.WScoped.getAppArgs hwfab z (by
            rw [Expr.getAppArgs_mkAppN]; simpa [Expr.getAppArgs] using hz)
        have hx312 : Ext s3.store s12.store := by
          rw [hst12]; exact hx7.trans (hx8.trans (hx9.trans (hx10.trans hx11)))
        rw [if_pos hcert]
        refine triple_seq (constTyAt_spec s12 icvj ust rl'.ctor lsu
          (.ctorInfo dcvj cnP cnF) hok12
          (by rw [denoteCV_name (denoteCV_ext hdcvj hx112), hnamej])
          (denoteLs_ext hlsu hx312) hfj (denoteCV_ext hdcvj hx112)) ?_
        rintro tyC s13 ⟨hok13, hx13', hp13', htyC⟩
        have hwtyC : Expr.WScoped d
            (dcvj.type.instantiateLevelParams dcvj.levelParams lsu) :=
          Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfj lsu)
        have hfa13 := denoteEList_ext (hx11.trans (by rw [← hst12]; exact hx13')) _ _ hfa
        refine triple_seq (iotaCerts_spec hsim d false tyC _ s13 hok13
          ⟨_, _, htyC, hwtyC, hfa13, hwargs⟩) ?_
        rintro c1 s14 ⟨hok14, hx14, hp14, hc1⟩
        obtain ⟨F3, hF3⟩ := hc1 _ _ htyC hfa13
        have hx114 := hx112.trans (hx13'.trans hx14)
        have hp114 : s14.pins = s₁.pins := hp14.trans (hp13'.trans hp112)
        have hfab14 := denote_ext hfab (by rw [← hst12]; exact hx13'.trans hx14)
        by_cases hc1t : c1 = true
        · rw [if_pos hc1t]
          subst hc1t
          refine triple_seq (hsim.inferIO s14 d fab _ hok14 hfab14 hwfab) ?_
          rintro tf s15 ⟨hok15, hx15, hp15, vtf, hvtf, hwvtf, F4, hF4⟩
          refine triple_seq (hsim.defeq s15 d tmaj tf vtmaj vtf hok15
            (denote_ext hvtmaj (hx312.trans (hx13'.trans (hx14.trans hx15)))) hvtf
            hwvtmaj hwvtf) ?_
          rintro rd s16 ⟨hok16, hx16, hp16, F5, hF5⟩
          have hx116 := hx114.trans (hx15.trans hx16)
          have hp116 : s16.pins = s₁.pins := hp16.trans (hp15.trans hp114)
          by_cases hrd : rd = true
          · rw [if_pos hrd]
            subst hrd
            rw [if_pos hcert]
            refine triple_seq (proofIrrel_spec hsim s16 d fab major _ x hok16
              (denote_ext hfab14 (hx15.trans hx16)) (denote_ext hmaj hx116) hwfab hw) ?_
            rintro ir s17 ⟨hok17, hx17', hp17', F6, hF6⟩
            have hv := hTs (b3 := true) (b5 := true) (b6 := ir)
              (G := max (max F1 F2) (max F3 (max F4 (max F5 F6)))) (by omega) hgt
              (iotaCertsFueled_mono (by omega) hF3)
              (fun _ => ConLeche.inferTypeIO_mono (by omega) hF4)
              (fun _ => ConLeche.isDefEqCore_mono (by omega) hF5)
              (fun _ _ => proofIrrelFueled_mono (by omega) hF6)
            have hfab17 := denote_ext hfab14 (hx15.trans (hx16.trans hx17'))
            have hmaj17 := denote_ext hmaj (hx116.trans hx17')
            cases ir
            · mvcgen
              bridge_peel; subst_vars
              exact ⟨hok17, hx116.trans hx17', hp17'.trans hp116, x, hmaj17, hw, _, hv⟩
            · mvcgen
              bridge_peel; subst_vars
              exact ⟨hok17, hx116.trans hx17', hp17'.trans hp116, _, hfab17, hwfab, _,
                hv⟩
          · rw [if_neg hrd]
            have hrdf : rd = false := by simpa using hrd
            subst hrdf
            have hv := hTs (b3 := true) (b5 := false) (b6 := false)
              (G := max (max F1 F2) (max F3 (max F4 F5))) (by omega) hgt
              (iotaCertsFueled_mono (by omega) hF3)
              (fun _ => ConLeche.inferTypeIO_mono (by omega) hF4)
              (fun _ => ConLeche.isDefEqCore_mono (by omega) hF5)
              (fun _ h => by cases h)
            mvcgen
            bridge_peel; subst_vars
            exact ⟨hok16, hx116, hp116, x, denote_ext hmaj hx116, hw, _, hv⟩
        · rw [if_neg hc1t]
          have hc1f : c1 = false := by simpa using hc1t
          subst hc1f
          have hv := hTs (b3 := false) (b5 := false) (b6 := false) (tf := x)
            (G := max (max F1 F2) F3) (by omega) hgt
            (iotaCertsFueled_mono (by omega) hF3)
            (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
          mvcgen
          bridge_peel; subst_vars
          exact ⟨hok14, hx114, hp114, x, denote_ext hmaj hx114, hw, _, hv⟩
      · rw [if_neg hgt]
        have hgf' : gd = false := by simpa using hgt
        have hres : ∀ G, max F1 F2 ≤ G →
            mtcAnd mode env G d rl' dcvj cnP Tn x = .ok x := by
          intro G hG
          obtain ⟨e1, e2⟩ := hA G hG
          have e1' : (ConLeche.pureFns mode env G).inferIO d x = .ok vtm := e1
          have e2' : (ConLeche.pureFns mode env G).whnf d vtm = .ok vtmaj := e2
          obtain ⟨hTT, hr⟩ := hgP
          subst hTT
          simp only [mtcAnd, e1', e2', bind, Except.bind, hgf]
          rw [if_pos (by first | exact ⟨rfl, hr⟩ | exact ⟨trivial, hr⟩)]
          simp only [← hgd, hgf']
          rfl
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok12, hx112, hp112, x, denote_ext hmaj hx112, hw, _,
          hres _ (Nat.le_refl _)⟩
    · rw [if_neg hg]
      have hres : ∀ G, max F1 F2 ≤ G →
          mtcAnd mode env G d rl' dcvj cnP Tn x = .ok x := by
        intro G hG
        obtain ⟨e1, e2⟩ := hA G hG
        have e1' : (ConLeche.pureFns mode env G).inferIO d x = .ok vtm := e1
        have e2' : (ConLeche.pureFns mode env G).whnf d vtm = .ok vtmaj := e2
        simp only [mtcAnd, e1', e2', bind, Except.bind, hgf]
        rw [if_neg (fun h => hg (hcond.mpr h))]
        rfl
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok7, hx17, hp17, x, denote_ext hmaj hx17, hw, _, hres _ (Nat.le_refl _)⟩
  all_goals
    dsimp only
    have hnc := denote_not_const hwf3 hvh hdd (by intro c us h; cases h)
    have hres : ∀ G, max F1 F2 ≤ G →
        mtcAnd mode env G d rl' dcvj cnP Tn x = .ok x := by
      intro G hG
      obtain ⟨e1, e2⟩ := hA G hG
      have e1' : (ConLeche.pureFns mode env G).inferIO d x = .ok vtm := e1
      have e2' : (ConLeche.pureFns mode env G).whnf d vtm = .ok vtmaj := e2
      simp only [mtcAnd, e1', e2', bind, Except.bind]
      first
        | rfl
        | (split
           · rename_i c us heq; exact absurd heq (hnc c us)
           · rfl)
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok3, hx13, hp13, x, denote_ext hmaj hx13, hw, _, hres _ (Nat.le_refl _)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — **THEOREM 1
for `majorToCtor`**, the stuck-major rescue: K, η, and the pinned `And`.
The recursor's name is unused on both sides (`_recName`). -/
theorem majorToCtor_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (c : NIdx) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK mode env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.majorToCtor mode (coreKnot mode fe id fuel) fe d c rules
        major
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.majorToCtorFueled mode env F d cn rules' x) d
          s'.store r⌝⦄ := by
  sorry

/-- con-leche: none — a denoting rule list has the same K bit. -/
theorem recRuleK_denote {st : EStore} {rules : List IRecRule}
    {rules' : List RecRule} (h : Frontend.denoteRules st rules = some rules') :
    ConRon.Arena.recRuleK rules = ConLeche.recRuleK rules' := by
  match rules, h with
  | [], h =>
    simp only [Frontend.denoteRules] at h; cases h; rfl
  | [r], h =>
    simp only [Frontend.denoteRules] at h
    split at h
    · rename_i x xs hx hxs
      obtain rfl : xs = [] := by
        simp only [Frontend.denoteRules, Option.some.injEq] at hxs; exact hxs.symm
      cases h
      simp only [Frontend.denoteRule] at hx
      split at hx
      · cases hx; rfl
      · simp at hx
    · simp at h
  | r1 :: r2 :: rs, h =>
    have hl := denoteRules_len h
    match rules', hl with
    | a :: b :: cs, _ => rfl

/-- con-leche: ConLeche/Kernel/Core.lean:758-795 prepareMajor — at a
K-flagged recursor: the rescue on the raw major, then `whnf`, then the literal
conversion. -/
theorem prepareMajorFueled_k {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x m1 m2 m3 : Expr}
    (hk : ConLeche.recRuleK rules' = true)
    (h1 : ConLeche.majorToCtorFueled mode env F d cn rules' x = .ok m1)
    (h2 : ConLeche.whnf mode env F d m1 = .ok m2)
    (h3 : ConLeche.litMajorToCtorFueled mode env F d m2 = .ok m3) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m3 := by
  have e1 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' x = .ok m1 := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d m1 = .ok m2 := h2
  have e3 : ConLeche.litMajorToCtor (ConLeche.pureFns mode env F) env d m2 =
      .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk, if_true,
    e1, e2, e3, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:758-795 prepareMajor — elsewhere:
`whnf`, the literal conversion, then the rescue. -/
theorem prepareMajorFueled_nk {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x m1 m2 m3 : Expr}
    (hk : ConLeche.recRuleK rules' = false)
    (h1 : ConLeche.whnf mode env F d x = .ok m1)
    (h2 : ConLeche.litMajorToCtorFueled mode env F d m1 = .ok m2)
    (h3 : ConLeche.majorToCtorFueled mode env F d cn rules' m2 = .ok m3) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m3 := by
  have e1 : (ConLeche.pureFns mode env F).whnf d x = .ok m1 := h1
  have e2 : ConLeche.litMajorToCtor (ConLeche.pureFns mode env F) env d m1 =
      .ok m2 := h2
  have e3 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' m2 = .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk,
    Bool.false_eq_true, if_false, e1, e2, e3, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:758-795 prepareMajor — **THEOREM 1
for `prepareMajor`**: the official kernel's order, K rescue on the raw major
or head normalisation first. -/
theorem prepareMajor_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (c : NIdx) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK mode env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.prepareMajor mode (coreKnot mode fe id fuel) fe d c rules
        major
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.prepareMajorFueled mode env F d cn rules' x) d
          s'.store r⌝⦄ := by
  unfold ConRon.Arena.prepareMajor
  rw [recRuleK_denote hr]
  split
  next hk =>
    refine triple_seq (majorToCtor_spec hμ henv hsim s₀ d c rules major cn
      rules' x hok hr hden hw) ?_
    rintro m1 s1 ⟨hok1, hx1, hp1, v1, hv1, hwv1, F1, hF1⟩
    refine triple_seq (hsim.whnf s1 d m1 v1 hok1 hv1 hwv1) ?_
    rintro m2 s2 ⟨hok2, hx2, hp2, v2, hv2, hwv2, F2, hF2⟩
    refine triple_mono (litMajorToCtor_spec hsim s2 d m2 v2 hok2 hv2 hwv2) ?_
    rintro m3 s3 ⟨hok3, hx3, hp3, v3, hv3, hwv3, F3, hF3⟩
    refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1), v3, hv3,
      hwv3, max F1 (max F2 F3), prepareMajorFueled_k hk
        (majorToCtorFueled_mono (by omega) hF1) (ConLeche.whnf_mono (by omega) hF2)
        (litMajorToCtorFueled_mono (by omega) hF3)⟩
  next hk =>
    have hk' : ConLeche.recRuleK rules' = false := by simpa using hk
    refine triple_seq (hsim.whnf s₀ d major x hok hden hw) ?_
    rintro m1 s1 ⟨hok1, hx1, hp1, v1, hv1, hwv1, F1, hF1⟩
    refine triple_seq (litMajorToCtor_spec hsim s1 d m1 v1 hok1 hv1 hwv1) ?_
    rintro m2 s2 ⟨hok2, hx2, hp2, v2, hv2, hwv2, F2, hF2⟩
    refine triple_mono (majorToCtor_spec hμ henv hsim s2 d c rules m2 cn rules'
      v2 hok2 (denoteRules_ext (hx1.trans hx2) _ _ hr) hv2 hwv2) ?_
    rintro m3 s3 ⟨hok3, hx3, hp3, v3, hv3, hwv3, F3, hF3⟩
    refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1), v3, hv3,
      hwv3, max F1 (max F2 F3), prepareMajorFueled_nk hk'
        (ConLeche.whnf_mono (by omega) hF1)
        (litMajorToCtorFueled_mono (by omega) hF2)
        (majorToCtorFueled_mono (by omega) hF3)⟩


end ConRon.Bridge.Core
