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
          sorry
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
