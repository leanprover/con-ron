/-
# `ConRon.Bridge.Core.Walks.IotaMajor` — the ι major's preparation

Task #97-P3-Core round 6 (lane `iota`): `litMajorToCtor`, the stuck-major
rescue `majorToCtor` (K, η, the pinned `And`) and `prepareMajor`, which runs
them in the official kernel's order (lean4#15351; restated at con-leche
e74d32ad by task #119: the η rescue is uncertified, K and `And` check the
fabricated constructor's type and, at the verified mode, proof irrelevance).
-/
import ConRon.Bridge.Core.Walks.IotaLeaves

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

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
    ⦃fun s => s = s₀⦄
      ConRon.Arena.litMajorToCtor (coreKnot mode fe id fuel) fe d h
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.litMajorToCtorFueled mode env F d x) d
          s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  unfold ConRon.Arena.litMajorToCtor
  refine tag_view_bind_triple hv ?_
    (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
  -- every major but a string literal: the `Nat` conversion
  have hnat : (∀ str, x ≠ .lit (.strVal str)) →
      ⦃fun s => s = s₀⦄ ConRon.Arena.litToCtorIfNat fe h
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          SimEOp (fun F => ConLeche.litMajorToCtorFueled mode env F d x) d
            s'.store r; ⊤⦄ := by
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
          ite_true]
        exact hF
      next hsupf =>
        have hS : ConLeche.strLitSupported env = false := by
          rw [← hsup]; simpa using hsupf
        vcgen
        bridge_peel; subst_vars
        refine ⟨hok1, hx1, hp1, .lit (.strVal str), denote_ext hden hx1, hw, 0,
          ?_⟩
        simp only [ConLeche.litMajorToCtor, hS, Bool.false_eq_true, ite_false]
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

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch. -/
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
          (ConLeche.pureFns mode env F).inferIO d fab >>= fun tfab =>
          (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
          if rd then
            (if mode.verifiedChecks then
              ConLeche.proofIrrel (ConLeche.pureFns mode env F) d fab major
            else pure true) >>= fun r => if r then pure fab else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the η branch
(no certificate on the fabricated spine, con-leche's task #342 L11b). -/
def mtcEta (mode : CheckMode) (env : Env) (F d : Nat) (cvT : ConstantVal)
    (caps : IndCaps) (T : ConLeche.Name) (major : Expr) : CheckM Expr :=
  (ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        ConLeche.capsNeverZero cvT.levelParams ust caps = true ∧
        ConLeche.reservedBasisNames.contains T = false ∧
        ConLeche.reservedBasisNames.contains caps.etaCtor = false ∧
        ConLeche.towerSlotsAll env T caps.etaFields = true then
      let fab := Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE T tmaj.getAppArgs major caps.etaFields)
      if fab.wscopedB d && fab.looseBVarsBounded 0 &&
          fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
        pure fab
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the pinned
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
        (ConLeche.pureFns mode env F).inferIO d fab >>= fun tfab =>
        (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
        if rd then
          (if mode.verifiedChecks then
            ConLeche.proofIrrel (ConLeche.pureFns mode env F) d fab major
          else pure true) >>= fun r => if r then pure fab else pure major
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
      else if rl.eta = true then mtcEta mode env F d cvT caps T x
      else if T = ConLeche.andName then mtcAnd mode env F d rl cvj cnP T x
      else pure x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hfj, hpr,
    hfT, Bool.false_eq_true, ite_false]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — a constructor
application stays. -/
theorem majorToCtorFueled_ctor {F d : Nat} {cn : ConLeche.Name}
    {rules : List RecRule} {x : Expr} (h : ConLeche.isCtorApp env x = true) :
    ConLeche.majorToCtorFueled mode env F d cn rules x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, h, ite_true]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — every prefix
miss leaves the major alone. -/
theorem majorToCtorFueled_nrules {F d : Nat} {cn : ConLeche.Name}
    {rules : List RecRule} {x : Expr} (hnc : ConLeche.isCtorApp env x = false)
    (h : ∀ rl, rules ≠ [rl]) :
    ConLeche.majorToCtorFueled mode env F d cn rules x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc,
    Bool.false_eq_true, ite_false]
  match rules, h with
  | [], _ => rfl
  | [rl], h => exact absurd rfl (h rl)
  | _ :: _ :: _, _ => rfl

theorem majorToCtorFueled_nctor {F d : Nat} {cn : ConLeche.Name} {rl : RecRule}
    {x : Expr} (hnc : ConLeche.isCtorApp env x = false)
    (h : ∀ cvj cnP cnF, env.find? rl.ctor ≠ some (.ctorInfo cvj cnP cnF)) :
    ConLeche.majorToCtorFueled mode env F d cn [rl] x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc,
    Bool.false_eq_true, ite_false]
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
    Bool.false_eq_true, ite_false]
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
    Bool.false_eq_true, ite_false]
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

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch
past its three syntactic guards, as a function of the two verdicts. -/
theorem mtcK_fire {F d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T T' : ConLeche.Name} {x tm tmaj tf : Expr} {ust : List Level}
    {b5 b6 : Bool}
    (e1 : ConLeche.inferTypeIO mode env F d x = .ok tm)
    (e2 : ConLeche.whnf mode env F d tm = .ok tmaj)
    (hgf : tmaj.getAppFn = .const T' ust)
    (hg1 : T' = T ∧ cvj.levelParams.length = ust.length)
    (hg2 : cnP ≤ tmaj.getAppArgs.length)
    (hgd : ((Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).wscopedB d &&
      (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).looseBVarsBounded 0 &&
      (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).fvarLeaves.all
        (fun l => x.fvarLeaves.contains l)) = true)
    (h4 : ConLeche.inferTypeIO mode env F d (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) = .ok tf)
    (h5 : ConLeche.isDefEqCore mode env F d tmaj tf = .ok b5)
    (h6 : b5 = true → (if mode.verifiedChecks then ConLeche.proofIrrelFueled mode env F d
      (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) x else .ok true) = .ok b6) :
    mtcK mode env F d rl cvj cnP T x = .ok (if b5 && b6 then
      (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) else x) := by
  have e1' : (ConLeche.pureFns mode env F).inferIO d x = .ok tm := e1
  have e2' : (ConLeche.pureFns mode env F).whnf d tm = .ok tmaj := e2
  have h4' : (ConLeche.pureFns mode env F).inferIO d (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) = .ok tf := h4
  have h5' : (ConLeche.pureFns mode env F).defeq d tmaj tf = .ok b5 := h5
  simp only [mtcK, e1', e2', bind, Except.bind, hgf]
  rw [ite_eq_left hg1, ite_eq_left hg2]
  simp only [hgd, ite_true, h4', h5']
  cases b5
  · rfl
  · have h6' := h6 rfl
    simp only [ite_true]
    cases hv : mode.verifiedChecks
    · simp only [hv, Bool.false_eq_true, ite_false] at h6' ⊢
      cases h6'; rfl
    · simp only [hv, ite_true] at h6' ⊢
      have h6'' : ConLeche.proofIrrel (ConLeche.pureFns mode env F) d (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) x =
          .ok b6 := h6'
      rw [h6'']
      cases b6 <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:571-617 majorToCtor — **the K
rescue** (`to_cnstr_when_K`): the parameters-only constructor application
fabricated from the major's type, certified by the official type check and,
at verified mode, proof irrelevance. -/
theorem majorK_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (rl : IRecRule) (rl' : RecRule) (major : EIdx)
    (x : Expr) (icvj : IConstantVal) (dcvj : ConstantVal) (cnP cnF : Nat)
    (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₁) (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hT : denoteN s₁.store.ns T = some Tn)
    (hfj : env.find? rl'.ctor = some (.ctorInfo dcvj cnP cnF)) :
    ⦃fun s => s = s₁⦄ (do
      let tmaj ← (coreKnot mode fe id fuel).whnf d
        (← (coreKnot mode fe id fuel).inferIO d major)
      let hh ← getAppFn coreWalkFuel tmaj
      if hh.tag == ETag.const then
        match ← view hh with
        | .const T' ust => do
          let ustl ← viewLs ust
          if T' = T ∧ icvj.levelParams.length = ustl.length then do
            let targs ← getAppArgs coreWalkFuel tmaj
            if cnP ≤ targs.length then do
              let hd ← internE (.const rl.ctor ust)
              let fab ← mkAppN hd (targs.take cnP)
              if ← fabScopeOk d fab major then do
                if ← (coreKnot mode fe id fuel).defeq d tmaj
                    (← (coreKnot mode fe id fuel).inferIO d fab) then do
                  let irK ←
                    if mode.verifiedChecks then
                      ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d fab major
                    else pure true
                  if irK then pure fab else pure major
                else pure major
              else pure major
            else pure major
          else pure major
        | _ => pure major
      else pure major : AM EIdx)
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (fun F => mtcK mode env F d rl' dcvj cnP Tn x) d s'.store r; ⊤⦄ := by
  obtain ⟨_, _, hrlc, _, _, _, _⟩ := rule_denote hrl'
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
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
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
    · rw [ite_eq_left hg1]
      have hg1P := hcond.mp hg1
      refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s3 tmaj hok3.state
        (by rw [hvtmaj]; rfl)) ?_
      rintro targs s6 ⟨hs6, hrelA⟩
      subst s6
      have htargs := hrelA vtmaj hvtmaj
      have htl := denoteEList_len htargs
      by_cases hg2 : cnP ≤ targs.length
      · rw [ite_eq_left hg2]
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
        rintro fab s8 ⟨hst8, hx8, _, hc8, hp8, hrel⟩
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
        · rw [ite_eq_left hgt]
          have hgP := hgd ▸ hgt
          have hwfab : Expr.WScoped d (Expr.mkAppN (.const rl'.ctor lsu)
              (vtmaj.getAppArgs.take cnP)) := by
            simp only [Bool.and_eq_true] at hgP
            exact Expr.WScoped.of_wscopedB hgP.1.1
          have hx39 : Ext s3.store s9.store := hx7.trans (by rw [hst9]; exact hx8)
          have hTs : ∀ {b5 b6 : Bool} {tf : Expr} {G : Nat}, max F1 F2 ≤ G →
              ConLeche.inferTypeIO mode env G d
                (Expr.mkAppN (.const rl'.ctor lsu) (vtmaj.getAppArgs.take cnP)) = .ok tf →
              ConLeche.isDefEqCore mode env G d vtmaj tf = .ok b5 →
              (b5 = true → (if mode.verifiedChecks then ConLeche.proofIrrelFueled mode env G d
                (Expr.mkAppN (.const rl'.ctor lsu) (vtmaj.getAppArgs.take cnP)) x
                else .ok true) = .ok b6) →
              mtcK mode env G d rl' dcvj cnP Tn x = .ok (if b5 && b6 then
                Expr.mkAppN (.const rl'.ctor lsu) (vtmaj.getAppArgs.take cnP) else x) := by
            intro b5 b6 tf G hG h4 h5 h6
            obtain ⟨e1, e2⟩ := hA G hG
            have hg1' : Tn' = Tn ∧ dcvj.levelParams.length = lsu.length := hg1P
            rw [← hg1'.1]
            exact mtcK_fire e1 e2 hgf ⟨rfl, hg1'.2⟩ hg2P hgP h4 h5 h6
          have hfab9 : denoteE s9.store fab = some (Expr.mkAppN (.const rl'.ctor lsu)
              (vtmaj.getAppArgs.take cnP)) := by rw [hst9]; exact hfab
          refine triple_seq (hsim.inferIO s9 d fab _ hok9 hfab9 hwfab) ?_
          rintro tf s12 ⟨hok12, hx12, hp12, vtf, hvtf, hwvtf, F4, hF4⟩
          refine triple_seq (hsim.defeq s12 d tmaj tf vtmaj vtf hok12
            (denote_ext hvtmaj (hx39.trans hx12)) hvtf hwvtmaj hwvtf) ?_
          rintro rd s13 ⟨hok13, hx13', hp13', F5, hF5⟩
          have hx113 := hx19.trans (hx12.trans hx13')
          have hp113 : s13.pins = s₁.pins := hp13'.trans (hp12.trans hp19)
          by_cases hrd : rd = true
          · rw [ite_eq_left hrd]
            subst hrd
            rw [ite_eq_left hμ]
            refine triple_seq (proofIrrel_spec hsim s13 d fab major _ x hok13
              (denote_ext hfab9 (hx12.trans hx13')) (denote_ext hmaj hx113) hwfab hw) ?_
            rintro ir s14 ⟨hok14, hx14, hp14, F6, hF6⟩
            have hv := hTs (b5 := true) (b6 := ir)
              (G := max (max F1 F2) (max F4 (max F5 F6))) (by omega)
              (ConLeche.inferTypeIO_mono (by omega) hF4)
              (ConLeche.isDefEqCore_mono (by omega) hF5)
              (fun _ => by rw [ite_eq_left hμ]; exact proofIrrelFueled_mono (by omega) hF6)
            have hfab14 := denote_ext hfab9 (hx12.trans (hx13'.trans hx14))
            have hmaj14 := denote_ext hmaj (hx113.trans hx14)
            cases ir <;> simp only [Bool.false_eq_true, ↓reduceIte]
            · vcgen
              bridge_peel; subst_vars
              exact ⟨hok14, hx113.trans hx14, hp14.trans hp113, x, hmaj14, hw, _, hv⟩
            · vcgen
              bridge_peel; subst_vars
              exact ⟨hok14, hx113.trans hx14, hp14.trans hp113, _, hfab14, hwfab, _, hv⟩
          · rw [ite_eq_right hrd]
            have hrdf : rd = false := by simpa using hrd
            subst hrdf
            have hv := hTs (b5 := false) (b6 := false)
              (G := max (max F1 F2) (max F4 F5)) (by omega)
              (ConLeche.inferTypeIO_mono (by omega) hF4)
              (ConLeche.isDefEqCore_mono (by omega) hF5)
              (fun h => by cases h)
            vcgen
            bridge_peel; subst_vars
            exact ⟨hok13, hx113, hp113, x, denote_ext hmaj hx113, hw, _, hv⟩
        · rw [ite_eq_right hgt]
          have hgf' : gd = false := by simpa using hgt
          have hres : ∀ G, max F1 F2 ≤ G →
              mtcK mode env G d rl' dcvj cnP Tn x = .ok x := by
            intro G hG
            obtain ⟨e1, e2⟩ := hA G hG
            simp only [mtcK, e1, e2, bind, Except.bind, hgf]
            rw [ite_eq_left hg1P, ite_eq_left hg2P]
            simp only [← hgd, hgf']
            rfl
          vcgen
          bridge_peel; subst_vars
          exact ⟨hok9, hx19, hp19, x, denote_ext hmaj hx19, hw, _,
            hres _ (Nat.le_refl _)⟩
      · rw [ite_eq_right hg2]
        have hres : ∀ G, max F1 F2 ≤ G →
            mtcK mode env G d rl' dcvj cnP Tn x = .ok x := by
          intro G hG
          obtain ⟨e1, e2⟩ := hA G hG
          simp only [mtcK, e1, e2, bind, Except.bind, hgf]
          rw [ite_eq_left hg1P, ite_eq_right (by rw [htl]; exact hg2)]
          rfl
        vcgen
        bridge_peel; subst_vars
        exact ⟨hok3, hx13, hp13, x, denote_ext hmaj hx13, hw, _,
          hres _ (Nat.le_refl _)⟩
    · rw [ite_eq_right hg1]
      have hres : ∀ G, max F1 F2 ≤ G →
          mtcK mode env G d rl' dcvj cnP Tn x = .ok x := by
        intro G hG
        obtain ⟨e1, e2⟩ := hA G hG
        simp only [mtcK, e1, e2, bind, Except.bind, hgf]
        rw [ite_eq_right (fun h => hg1 (hcond.mpr h))]
        rfl
      vcgen
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
    vcgen
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
  · rename_i ct _ _ hct _ _; cases h; exact ⟨rfl, hct, rfl, rfl, rfl⟩
  · simp at h

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the η branch
past its guards: the fabricated constructor, uncertified (con-leche task
#342). -/
theorem mtcEta_fire {F d : Nat} {cvT : ConstantVal} {caps : IndCaps}
    {T T' : ConLeche.Name} {x tm tmaj : Expr} {ust : List Level}
    (e1 : ConLeche.inferTypeIO mode env F d x = .ok tm)
    (e2 : ConLeche.whnf mode env F d tm = .ok tmaj)
    (hgf : tmaj.getAppFn = .const T' ust)
    (hg : T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
      ust.length = cvT.levelParams.length ∧
      ConLeche.capsNeverZero cvT.levelParams ust caps = true ∧
      ConLeche.reservedBasisNames.contains T = false ∧
      ConLeche.reservedBasisNames.contains caps.etaCtor = false ∧
      ConLeche.towerSlotsAll env T caps.etaFields = true)
    (hgd : ((Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE T tmaj.getAppArgs x caps.etaFields)).wscopedB d &&
      (Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE T tmaj.getAppArgs x caps.etaFields)).looseBVarsBounded 0 &&
      (Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE T tmaj.getAppArgs x caps.etaFields)).fvarLeaves.all
        (fun l => x.fvarLeaves.contains l)) = true) :
    mtcEta mode env F d cvT caps T x = .ok (Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE T tmaj.getAppArgs x caps.etaFields)) := by
  have e1' : (ConLeche.pureFns mode env F).inferIO d x = .ok tm := e1
  have e2' : (ConLeche.pureFns mode env F).whnf d tm = .ok tmaj := e2
  simp only [mtcEta, e1', e2', bind, Except.bind, hgf]
  rw [ite_eq_left hg]
  simp only [hgd, ite_true]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And`
branch past its guards, as a function of the two verdicts. -/
theorem mtcAnd_fire {F d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T T' : ConLeche.Name} {x tm tmaj tf : Expr} {ust : List Level}
    {b5 b6 : Bool}
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
    (h4 : ConLeche.inferTypeIO mode env F d (Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])) = .ok tf)
    (h5 : ConLeche.isDefEqCore mode env F d tmaj tf = .ok b5)
    (h6 : b5 = true → (if mode.verifiedChecks then ConLeche.proofIrrelFueled mode env F d
      (Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])) x else .ok true) = .ok b6) :
    mtcAnd mode env F d rl cvj cnP T x = .ok (if b5 && b6 then
      (Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])) else x) := by
  have e1' : (ConLeche.pureFns mode env F).inferIO d x = .ok tm := e1
  have e2' : (ConLeche.pureFns mode env F).whnf d tm = .ok tmaj := e2
  have h4' : (ConLeche.pureFns mode env F).inferIO d (Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])) = .ok tf := h4
  have h5' : (ConLeche.pureFns mode env F).defeq d tmaj tf = .ok b5 := h5
  simp only [mtcAnd, e1', e2', bind, Except.bind, hgf]
  rw [ite_eq_left hg]
  simp only [hgd, ite_true, h4', h5']
  cases b5
  · rfl
  · have h6' := h6 rfl
    simp only [ite_true]
    cases hv : mode.verifiedChecks
    · simp only [hv, Bool.false_eq_true, ite_false] at h6' ⊢
      cases h6'; rfl
    · simp only [hv, ite_true] at h6' ⊢
      have h6'' : ConLeche.proofIrrel (ConLeche.pureFns mode env F) d (Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])) x =
          .ok b6 := h6'
      rw [h6'']
      cases b6 <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:618-658 majorToCtor — **the η
rescue** (`to_cnstr_when_structure`): the constructor of the major's
projections, fabricated at an instantiated-never-`Prop` structure outside the
reserved basis whose field slots are all tower slots, with no certificate
(con-leche task #342 L11b). -/
theorem majorEta_spec {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (major : EIdx) (x : Expr)
    (icvT : IConstantVal) (dcvT : ConstantVal) (icaps : IIndCaps)
    (dcaps : IndCaps) (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₁)
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvT : Frontend.denoteCV s₁.store icvT = some dcvT)
    (hcaps : Frontend.denoteCaps s₁.store icaps = some dcaps)
    (hT : denoteN s₁.store.ns T = some Tn) :
    ⦃fun s => s = s₁⦄ (do
      let tmaj ← (coreKnot mode fe id fuel).whnf d
        (← (coreKnot mode fe id fuel).inferIO d major)
      let hh ← getAppFn coreWalkFuel tmaj
      if hh.tag == ETag.const then
        match ← view hh with
        | .const T' ust => do
          let ustl ← viewLs ust
          let targs ← getAppArgs coreWalkFuel tmaj
          let nz ← capsNeverZero icvT.levelParams ust icaps
          if T' = T ∧ targs.length = icaps.etaParams ∧
              ustl.length = icvT.levelParams.length ∧ nz = true then do
            let reserved ← reservedBasisNames
            if reserved.contains T = false ∧
                reserved.contains icaps.etaCtor = false then do
              if ← towerSlotsAll fe T icaps.etaFields then do
                let fabArgs ← etaFabArgsE T targs major icaps.etaFields
                let hd ← internE (.const icaps.etaCtor ust)
                let fab ← mkAppN hd fabArgs
                if ← fabScopeOk d fab major then pure fab
                else pure major
              else pure major
            else pure major
          else pure major
        | _ => pure major
      else pure major : AM EIdx)
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (fun F => mtcEta mode env F d dcvT dcaps Tn x) d s'.store r; ⊤⦄ := by
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
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
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
      (denoteCaps_ext hcaps hx13)) ?_
    rintro nz s7 ⟨hok7, hst7, hp7, hnz⟩
    have hx37 : Ext s3.store s7.store := by rw [hst7]; exact Ext.refl _
    have hx17 : Ext s₁.store s7.store := hx13.trans hx37
    have hp17 : s7.pins = s₁.pins := hp7.trans hp13
    have hcond : (T' = T ∧ targs.length = icaps.etaParams ∧
        ustl.length = icvT.levelParams.length ∧ nz = true) ↔
        (Tn' = Tn ∧ vtmaj.getAppArgs.length = dcaps.etaParams ∧
          lsu.length = dcvT.levelParams.length ∧
          ConLeche.capsNeverZero dcvT.levelParams lsu dcaps = true) := by
      rw [nidx_eq_iff hwf3 hTn' (denoteN_ext hT hx13), ← htl, hep, hul,
        ← denoteNList_len hlpsT, hnz]
    -- every failed guard leaves the major
    have hno : ∀ G, max F1 F2 ≤ G →
        ¬ (Tn' = Tn ∧ vtmaj.getAppArgs.length = dcaps.etaParams ∧
          lsu.length = dcvT.levelParams.length ∧
          ConLeche.capsNeverZero dcvT.levelParams lsu dcaps = true ∧
          ConLeche.reservedBasisNames.contains Tn = false ∧
          ConLeche.reservedBasisNames.contains dcaps.etaCtor = false ∧
          ConLeche.towerSlotsAll env Tn dcaps.etaFields = true) →
        mtcEta mode env G d dcvT dcaps Tn x = .ok x := by
      intro G hG hng
      obtain ⟨e1, e2⟩ := hA G hG
      have e1' : (ConLeche.pureFns mode env G).inferIO d x = .ok vtm := e1
      have e2' : (ConLeche.pureFns mode env G).whnf d vtm = .ok vtmaj := e2
      simp only [mtcEta, e1', e2', bind, Except.bind, hgf]
      rw [ite_eq_right hng]
      rfl
    by_cases hg : T' = T ∧ targs.length = icaps.etaParams ∧
        ustl.length = icvT.levelParams.length ∧ nz = true
    case neg =>
      rw [ite_eq_right hg]
      vcgen
      bridge_peel; subst_vars
      exact ⟨hok7, hx17, hp17, x, denote_ext hmaj hx17, hw, _,
        hno _ (Nat.le_refl _) (fun h => hg (hcond.mpr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩))⟩
    rw [ite_eq_left hg]
    have hgP := hcond.mp hg
    refine triple_seq (reservedBasisNames_spec s7 hok7) ?_
    rintro res s8 ⟨hok8, hx8, hp8, hres⟩
    have hx18 := hx17.trans hx8
    have hp18 : s8.pins = s₁.pins := hp8.trans hp17
    have hc1 := denoteNList_containsC hok8.state.wf res _ hres T Tn (denoteN_ext hT hx18)
    have hc2 := denoteNList_containsC hok8.state.wf res _ hres icaps.etaCtor dcaps.etaCtor
      (denoteN_ext hctor hx18)
    by_cases hgr : res.contains T = false ∧ res.contains icaps.etaCtor = false
    case neg =>
      rw [ite_eq_right hgr]
      vcgen
      bridge_peel; subst_vars
      exact ⟨hok8, hx18, hp18, x, denote_ext hmaj hx18, hw, _,
        hno _ (Nat.le_refl _) (fun h => hgr ⟨by rw [hc1]; exact h.2.2.2.2.1,
          by rw [hc2]; exact h.2.2.2.2.2.1⟩)⟩
    rw [ite_eq_left hgr]
    have hgrP : ConLeche.reservedBasisNames.contains Tn = false ∧
        ConLeche.reservedBasisNames.contains dcaps.etaCtor = false :=
      ⟨by rw [← hc1]; exact hgr.1, by rw [← hc2]; exact hgr.2⟩
    refine triple_seq (towerSlotsAll_spec s8 T Tn icaps.etaFields hok8
      (denoteN_ext hT hx18)) ?_
    rintro tsa s9 ⟨hok9, hx9, hp9, htsa⟩
    have hx19 := hx18.trans hx9
    have hp19 : s9.pins = s₁.pins := hp9.trans hp18
    by_cases hts : tsa = true
    case neg =>
      rw [ite_eq_right hts]
      have htsF : ConLeche.towerSlotsAll env Tn dcaps.etaFields ≠ true := by
        rw [hef, ← htsa]; exact hts
      vcgen
      bridge_peel; subst_vars
      exact ⟨hok9, hx19, hp19, x, denote_ext hmaj hx19, hw, _,
        hno _ (Nat.le_refl _) (fun h => htsF h.2.2.2.2.2.2)⟩
    rw [ite_eq_left hts]
    have htsP : ConLeche.towerSlotsAll env Tn dcaps.etaFields = true := by
      rw [hef, ← htsa]; exact hts
    have hgAll : Tn' = Tn ∧ vtmaj.getAppArgs.length = dcaps.etaParams ∧
        lsu.length = dcvT.levelParams.length ∧
        ConLeche.capsNeverZero dcvT.levelParams lsu dcaps = true ∧
        ConLeche.reservedBasisNames.contains Tn = false ∧
        ConLeche.reservedBasisNames.contains dcaps.etaCtor = false ∧
        ConLeche.towerSlotsAll env Tn dcaps.etaFields = true :=
      ⟨hgP.1, hgP.2.1, hgP.2.2.1, hgP.2.2.2, hgrP.1, hgrP.2, htsP⟩
    have hx39 : Ext s3.store s9.store := hx37.trans (hx8.trans hx9)
    have htargs9 := denoteEList_ext hx39 _ _ htargs
    refine triple_seq (etaFabArgsE_spec s9 T targs major icaps.etaFields Tn
      vtmaj.getAppArgs x hok9 (denoteN_ext hT hx19) htargs9
      (denote_ext hmaj hx19)) ?_
    rintro fabArgs s10 ⟨hok10, hx10, hp10, hfa⟩
    rw [← hef] at hfa
    have hx110 := hx19.trans hx10
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s10 (.const icaps.etaCtor ust) hok10 (viewOK_const
        (nview_isSome_of_denote (denoteN_ext hctor hx110))
        (by obtain ⟨w, hw', _⟩ := denoteLs_view (denoteLs_ext hlsu (hx39.trans hx10))
            rw [hw']; rfl))) ?_
    rintro hd s11 ⟨hok11, hx11, hp11, hhd⟩
    have hhd' : denoteE s11.store hd = some (.const dcaps.etaCtor lsu) := by
      rw [hhd]
      simp only [denoteEView, denoteN_ext hctor (hx110.trans hx11),
        denoteLs_ext hlsu (hx39.trans (hx10.trans hx11)), opt2]
    have hfa11 := denoteEList_ext hx11 _ _ hfa
    refine triple_seq (ExprOps.mkAppN_spec fabArgs s11 hd hok11.state
      (by rw [hhd']; rfl) (by rw [hfa11]; rfl)) ?_
    rintro fab s12 ⟨hst12, hx12, _, hc12, hp12, hrel⟩
    have hok12 : CheckOK mode env fe s12 := hok11.mono hst12 hx12 hc12 hp12
    have hfab := hrel _ _ hhd' hfa11
    have hx112 := hx110.trans (hx11.trans hx12)
    have hp112 : s12.pins = s₁.pins := hp12.trans (hp11.trans (hp10.trans hp19))
    refine triple_seq (fabScopeOk_spec s12 d fab major _ x hok12 hfab
      (denote_ext hmaj hx112)) ?_
    rintro gd s13 ⟨hok13, hst13, hp13', hgd⟩
    have hx113 : Ext s₁.store s13.store := by rw [hst13]; exact hx112
    have hp113 : s13.pins = s₁.pins := hp13'.trans hp112
    by_cases hgt : gd = true
    · rw [ite_eq_left hgt]
      have hgP' := hgd ▸ hgt
      have hwfab : Expr.WScoped d (Expr.mkAppN (.const dcaps.etaCtor lsu)
          (ConLeche.etaFabArgsE Tn vtmaj.getAppArgs x dcaps.etaFields)) := by
        simp only [Bool.and_eq_true] at hgP'
        exact Expr.WScoped.of_wscopedB hgP'.1.1
      have hv : mtcEta mode env (max F1 F2) d dcvT dcaps Tn x = .ok
          (Expr.mkAppN (.const dcaps.etaCtor lsu)
            (ConLeche.etaFabArgsE Tn vtmaj.getAppArgs x dcaps.etaFields)) := by
        obtain ⟨e1, e2⟩ := hA _ (Nat.le_refl _)
        obtain ⟨hTT, hr⟩ := hgAll
        subst hTT
        exact mtcEta_fire e1 e2 hgf ⟨rfl, hr⟩ hgP'
      vcgen
      bridge_peel; subst_vars
      exact ⟨hok13, hx113, hp113, _, by rw [hst13]; exact hfab, hwfab, _, hv⟩
    · rw [ite_eq_right hgt]
      have hgf' : gd = false := by simpa using hgt
      have hres : mtcEta mode env (max F1 F2) d dcvT dcaps Tn x = .ok x := by
        obtain ⟨e1, e2⟩ := hA _ (Nat.le_refl _)
        have e1' : (ConLeche.pureFns mode env (max F1 F2)).inferIO d x = .ok vtm := e1
        have e2' : (ConLeche.pureFns mode env (max F1 F2)).whnf d vtm = .ok vtmaj := e2
        obtain ⟨hTT, hr⟩ := hgAll
        subst hTT
        simp only [mtcEta, e1', e2', bind, Except.bind, hgf]
        rw [ite_eq_left (by first | exact ⟨rfl, hr⟩ | exact ⟨trivial, hr⟩)]
        simp only [← hgd, hgf']
        rfl
      vcgen
      bridge_peel; subst_vars
      exact ⟨hok13, hx113, hp113, x, denote_ext hmaj hx113, hw, _, hres⟩
  all_goals
    dsimp only
    have hnc := denote_not_const hwf3 hvh hdd (by intro c us h; cases h)
    have hres : ∀ G, max F1 F2 ≤ G →
        mtcEta mode env G d dcvT dcaps Tn x = .ok x := by
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
    vcgen
    bridge_peel; subst_vars
    exact ⟨hok3, hx13, hp13, x, denote_ext hmaj hx13, hw, _, hres _ (Nat.le_refl _)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:659-721 majorToCtor — **the pinned
`And` rescue**: `And.intro` of the major's two projections, certified the K
branch's way (the type check, and proof irrelevance at verified mode). -/
theorem majorAnd_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (rl : IRecRule) (rl' : RecRule) (major : EIdx)
    (x : Expr) (icvj : IConstantVal) (dcvj : ConstantVal) (cnP cnF : Nat)
    (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₁) (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hT : denoteN s₁.store.ns T = some Tn)
    (hfj : env.find? rl'.ctor = some (.ctorInfo dcvj cnP cnF)) :
    ⦃fun s => s = s₁⦄ (do
      let tmaj ← (coreKnot mode fe id fuel).whnf d
        (← (coreKnot mode fe id fuel).inferIO d major)
      let hh ← getAppFn coreWalkFuel tmaj
      if hh.tag == ETag.const then
        match ← view hh with
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
              if ← (coreKnot mode fe id fuel).defeq d tmaj
                  (← (coreKnot mode fe id fuel).inferIO d fab) then do
                let irA ←
                  if mode.verifiedChecks then
                    ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d fab major
                  else pure true
                if irA then pure fab else pure major
              else pure major
            else pure major
          else pure major
        | _ => pure major
      else pure major : AM EIdx)
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (fun F => mtcAnd mode env F d rl' dcvj cnP Tn x) d s'.store r; ⊤⦄ := by
  obtain ⟨_, _, hrlc, _, _, _, _⟩ := rule_denote hrl'
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
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
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
    · rw [ite_eq_left hg]
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
      rintro fab s11 ⟨hst11, hx11, _, hc11, hp11, hrel⟩
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
      have hTs : ∀ {b5 b6 : Bool} {tf : Expr} {G : Nat}, max F1 F2 ≤ G →
          gd = true →
          ConLeche.inferTypeIO mode env G d (Expr.mkAppN (.const rl'.ctor lsu)
              (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x])) = .ok tf →
          ConLeche.isDefEqCore mode env G d vtmaj tf = .ok b5 →
          (b5 = true → (if mode.verifiedChecks then ConLeche.proofIrrelFueled mode env G d
            (Expr.mkAppN (.const rl'.ctor lsu)
              (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x])) x else .ok true) = .ok b6) →
          mtcAnd mode env G d rl' dcvj cnP Tn x = .ok (if b5 && b6 then
            Expr.mkAppN (.const rl'.ctor lsu)
              (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x]) else x) := by
        intro b5 b6 tf G hG hgt h4 h5 h6
        obtain ⟨e1, e2⟩ := hA G hG
        obtain ⟨hTT, hr⟩ := hgP
        subst hTT
        exact mtcAnd_fire e1 e2 hgf ⟨rfl, hr⟩ (hgd ▸ hgt) h4 h5 h6
      by_cases hgt : gd = true
      · rw [ite_eq_left hgt]
        have hgP' := hgd ▸ hgt
        have hwfab : Expr.WScoped d (Expr.mkAppN (.const rl'.ctor lsu)
            (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x])) := by
          simp only [Bool.and_eq_true] at hgP'
          exact Expr.WScoped.of_wscopedB hgP'.1.1
        have hx312 : Ext s3.store s12.store := by
          rw [hst12]; exact hx7.trans (hx8.trans (hx9.trans (hx10.trans hx11)))
        have hfab12 : denoteE s12.store fab = some (Expr.mkAppN (.const rl'.ctor lsu)
            (vtmaj.getAppArgs ++ [.proj Tn 0 x, .proj Tn 1 x])) := by rw [hst12]; exact hfab
        refine triple_seq (hsim.inferIO s12 d fab _ hok12 hfab12 hwfab) ?_
        rintro tf s15 ⟨hok15, hx15, hp15, vtf, hvtf, hwvtf, F4, hF4⟩
        refine triple_seq (hsim.defeq s15 d tmaj tf vtmaj vtf hok15
          (denote_ext hvtmaj (hx312.trans hx15)) hvtf hwvtmaj hwvtf) ?_
        rintro rd s16 ⟨hok16, hx16, hp16, F5, hF5⟩
        have hx116 := hx112.trans (hx15.trans hx16)
        have hp116 : s16.pins = s₁.pins := hp16.trans (hp15.trans hp112)
        by_cases hrd : rd = true
        · rw [ite_eq_left hrd]
          subst hrd
          rw [ite_eq_left hμ]
          refine triple_seq (proofIrrel_spec hsim s16 d fab major _ x hok16
            (denote_ext hfab12 (hx15.trans hx16)) (denote_ext hmaj hx116) hwfab hw) ?_
          rintro ir s17 ⟨hok17, hx17', hp17', F6, hF6⟩
          have hv := hTs (b5 := true) (b6 := ir)
            (G := max (max F1 F2) (max F4 (max F5 F6))) (by omega) hgt
            (ConLeche.inferTypeIO_mono (by omega) hF4)
            (ConLeche.isDefEqCore_mono (by omega) hF5)
            (fun _ => by rw [ite_eq_left hμ]; exact proofIrrelFueled_mono (by omega) hF6)
          have hfab17 := denote_ext hfab12 (hx15.trans (hx16.trans hx17'))
          have hmaj17 := denote_ext hmaj (hx116.trans hx17')
          cases ir <;> simp only [Bool.false_eq_true, ↓reduceIte]
          · vcgen
            bridge_peel; subst_vars
            exact ⟨hok17, hx116.trans hx17', hp17'.trans hp116, x, hmaj17, hw, _, hv⟩
          · vcgen
            bridge_peel; subst_vars
            exact ⟨hok17, hx116.trans hx17', hp17'.trans hp116, _, hfab17, hwfab, _,
              hv⟩
        · rw [ite_eq_right hrd]
          have hrdf : rd = false := by simpa using hrd
          subst hrdf
          have hv := hTs (b5 := false) (b6 := false)
            (G := max (max F1 F2) (max F4 F5)) (by omega) hgt
            (ConLeche.inferTypeIO_mono (by omega) hF4)
            (ConLeche.isDefEqCore_mono (by omega) hF5)
            (fun h => by cases h)
          vcgen
          bridge_peel; subst_vars
          exact ⟨hok16, hx116, hp116, x, denote_ext hmaj hx116, hw, _, hv⟩
      · rw [ite_eq_right hgt]
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
          rw [ite_eq_left (by first | exact ⟨rfl, hr⟩ | exact ⟨trivial, hr⟩)]
          simp only [← hgd, hgf']
          rfl
        vcgen
        bridge_peel; subst_vars
        exact ⟨hok12, hx112, hp112, x, denote_ext hmaj hx112, hw, _,
          hres _ (Nat.le_refl _)⟩
    · rw [ite_eq_right hg]
      have hres : ∀ G, max F1 F2 ≤ G →
          mtcAnd mode env G d rl' dcvj cnP Tn x = .ok x := by
        intro G hG
        obtain ⟨e1, e2⟩ := hA G hG
        have e1' : (ConLeche.pureFns mode env G).inferIO d x = .ok vtm := e1
        have e2' : (ConLeche.pureFns mode env G).whnf d vtm = .ok vtmaj := e2
        simp only [mtcAnd, e1', e2', bind, Except.bind, hgf]
        rw [ite_eq_right (fun h => hg (hcond.mpr h))]
        rfl
      vcgen
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
    vcgen
    bridge_peel; subst_vars
    exact ⟨hok3, hx13, hp13, x, denote_ext hmaj hx13, hw, _, hres _ (Nat.le_refl _)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — **THEOREM 1
for `majorToCtor`**, the stuck-major rescue: K, η, and the pinned `And`.
The recursor's name is unused on both sides (`_recName`). -/
theorem majorToCtor_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (c : NIdx) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK mode env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.majorToCtor mode (coreKnot mode fe id fuel) fe d c rules
        major
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.majorToCtorFueled mode env F d cn rules' x) d
          s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  have hxit : ∀ (s' : AState), CheckOK mode env fe s' → Ext s₀.store s'.store →
      s'.pins = s₀.pins →
      (∀ F, ConLeche.majorToCtorFueled mode env F d cn rules' x = .ok x) →
      CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.majorToCtorFueled mode env F d cn rules' x) d
          s'.store major :=
    fun s' h1 h2 h3 h4 => ⟨h1, h2, h3, x, denote_ext hden h2, hw, 0, h4 0⟩
  unfold ConRon.Arena.majorToCtor
  refine triple_seq (isCtorApp_spec s₀ major x hok hden) ?_
  rintro ic s1 ⟨hs1, hic⟩
  subst s1
  by_cases hict : ic = true
  · rw [ite_eq_left hict]
    have hc : ConLeche.isCtorApp env x = true := hic ▸ hict
    have hF : ∀ F, ConLeche.majorToCtorFueled mode env F d cn rules' x = .ok x := (fun F => majorToCtorFueled_ctor hc)
    vcgen
    bridge_peel; subst_vars
    exact hxit _ hok (Ext.refl _) rfl hF
  · rw [ite_eq_right hict]
    have hnc : ConLeche.isCtorApp env x = false := by rw [← hic]; simpa using hict
    split
    next rl =>
      obtain ⟨rl', hrl', rfl⟩ : ∃ rl', Frontend.denoteRule s₀.store rl = some rl' ∧
          rules' = [rl'] := by
        simp only [Frontend.denoteRules] at hr
        split at hr
        · rename_i y ys hy hys
          simp only [Option.some.injEq] at hys
          subst hys
          cases hr
          exact ⟨y, hy, rfl⟩
        · simp at hr
      obtain ⟨_, _, hrlc, _, _, _, _⟩ := rule_denote hrl'
      obtain ⟨hk', he'⟩ : rl'.k = rl.k ∧ rl'.eta = rl.eta := by
        simp only [Frontend.denoteRule] at hrl'
        split at hrl'
        · cases hrl'; exact ⟨rfl, rfl⟩
        · simp at hrl'
      split
      next icvj cnP cnF hfj =>
        obtain ⟨dcvj, hdcvj, hfindj⟩ := env_ctor_of_index hok hrlc hfj
        obtain ⟨_, _, htyj⟩ := denoteCV_inv hdcvj
        have hcj : denoteN s₀.store.ns icvj.name = some rl'.ctor := by
          rw [denoteCV_name hdcvj]; exact congrArg some (env_find_name hfindj)
        refine triple_seq (ExprOps.piResult_spec coreWalkFuel s₀ icvj.type hok.state
          (by rw [htyj]; rfl)) ?_
        rintro pr s2 ⟨hs2, hrelP⟩
        subst s2
        have hpr := hrelP dcvj.type htyj
        refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ pr hok.state
          (by rw [hpr]; rfl)) ?_
        rintro ph s3 ⟨hs3, hrelF⟩
        subst s3
        have hph := hrelF _ hpr
        obtain ⟨vh, hvh⟩ := denoteE_view hph
        refine tag_view_bind_triple hvh ?_
          (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
        cases vh
        case const T lus =>
          obtain ⟨Tn, lusv, hgf, hTn, _⟩ := denote_const_inv hwf hvh hph
          dsimp only
          split
          next icvT icaps hfT =>
            obtain ⟨dcvT, dcaps, hdcvT, hdcaps, hfindT⟩ := env_ind_of_index hok hTn hfT
            have hpre := fun F => majorToCtorFueled_pre (F := F) (d := d) (cn := cn)
              (mode := mode) hnc hfindj hgf hfindT
            by_cases hk : rl.k = true
            · rw [ite_eq_left hk]
              refine triple_mono (majorK_spec hμ hsim s₀ d rl rl' major x icvj dcvj
                cnP cnF T Tn hok hrl' hden hw hdcvj hTn hfindj) ?_
              rintro r s' ⟨h1, h2, h3, v, hv, hwv, F, hF⟩
              exact ⟨h1, h2, h3, v, hv, hwv, F, by dsimp only; rw [hpre, ite_eq_left (hk' ▸ hk)]; exact hF⟩
            · rw [ite_eq_right hk]
              have hkf : (rl'.k = true) = False := by rw [hk']; simpa using hk
              by_cases he : rl.eta = true
              · rw [ite_eq_left he]
                refine triple_mono (majorEta_spec hsim s₀ d major x
                  icvT dcvT icaps dcaps T Tn hok hden hw hdcvT hdcaps hTn) ?_
                rintro r s' ⟨h1, h2, h3, v, hv, hwv, F, hF⟩
                exact ⟨h1, h2, h3, v, hv, hwv, F, by
                  dsimp only; rw [hpre, ite_eq_right (by rw [hk']; exact hk), ite_eq_left (he' ▸ he)]; exact hF⟩
              · rw [ite_eq_right he]
                unfold ConRon.Arena.pinAnd
                refine triple_seq (pinAt_spec s₀ PIN_AND hok.pins) ?_
                rintro an s4 ⟨hs4, han⟩
                subst s4
                have hTan := nidx_eq_iff hwf hTn (han _ rfl)
                by_cases hta : T = an
                · rw [ite_eq_left hta]
                  have hta' : Tn = ConLeche.andName := hTan.mp hta
                  refine triple_mono (majorAnd_spec hμ hsim s₀ d rl rl' major x icvj
                    dcvj cnP cnF T Tn hok hrl' hden hw hdcvj hTn hfindj) ?_
                  rintro r s' ⟨h1, h2, h3, v, hv, hwv, F, hF⟩
                  exact ⟨h1, h2, h3, v, hv, hwv, F, by
                    dsimp only; rw [hpre, ite_eq_right (by rw [hk']; exact hk),
                      ite_eq_right (by rw [he']; exact he), ite_eq_left hta']; exact hF⟩
                · rw [ite_eq_right hta]
                  have hta' : ¬ Tn = ConLeche.andName := fun h => hta (hTan.mpr h)
                  have hF : ∀ F, ConLeche.majorToCtorFueled mode env F d cn [rl'] x = .ok x := (fun F => by
                    rw [hpre, ite_eq_right (by rw [hk']; exact hk),
                      ite_eq_right (by rw [he']; exact he), ite_eq_right hta']; rfl)
                  vcgen
                  bridge_peel; subst_vars
                  exact hxit _ hok (Ext.refl _) rfl hF
          next hnd =>
            have hni := env_not_ind_of_index hok hTn (fun v c h => hnd v c h)
            have hF : ∀ F, ConLeche.majorToCtorFueled mode env F d cn [rl'] x = .ok x := (fun F =>
              majorToCtorFueled_nind hnc hfindj hgf hni)
            vcgen
            bridge_peel; subst_vars
            exact hxit _ hok (Ext.refl _) rfl hF
        all_goals
          dsimp only
          have hncT := denote_not_const hwf hvh hph (by intro c us h; cases h)
          have hF : ∀ F, ConLeche.majorToCtorFueled mode env F d cn [rl'] x = .ok x := (fun F =>
            majorToCtorFueled_nhead hnc hfindj hncT)
          vcgen
          bridge_peel; subst_vars
          exact hxit _ hok (Ext.refl _) rfl hF
      next hnd =>
        have hnc' := env_not_ctor_of_index hok hrlc (fun v p q h => hnd v p q h)
        have hF : ∀ F, ConLeche.majorToCtorFueled mode env F d cn [rl'] x = .ok x := (fun F =>
          majorToCtorFueled_nctor hnc hnc')
        vcgen
        bridge_peel; subst_vars
        exact hxit _ hok (Ext.refl _) rfl hF
    next hnr =>
      have hns : ∀ rl, rules' ≠ [rl] := by
        intro rl h
        subst h
        have hl := denoteRules_len hr
        match rules, hl, hnr with
        | [r], _, hnr => exact hnr r rfl
      have hF : ∀ F, ConLeche.majorToCtorFueled mode env F d cn rules' x = .ok x := (fun F =>
        majorToCtorFueled_nrules hnc hns)
      vcgen
      bridge_peel; subst_vars
      exact hxit _ hok (Ext.refl _) rfl hF

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
        simp only [Option.some.injEq] at hxs; exact hxs.symm
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

/-- con-leche: ConLeche/Kernel/Core.lean:782-834 prepareMajor — at a
K-flagged recursor whose rescue produced a constructor application: the
literal conversion of the rescued major. -/
theorem prepareMajorFueled_k {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x m1 m3 : Expr}
    (hk : ConLeche.recRuleK rules' = true)
    (h1 : ConLeche.majorToCtorFueled mode env F d cn rules' x = .ok m1)
    (hc : ConLeche.isCtorApp env m1 = true)
    (h3 : ConLeche.litMajorToCtorFueled mode env F d m1 = .ok m3) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m3 := by
  have e1 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' x = .ok m1 := h1
  have e3 : ConLeche.litMajorToCtor (ConLeche.pureFns mode env F) env d m1 =
      .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk, ite_true,
    e1, hc, e3, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:782-834 prepareMajor — at a
K-flagged recursor whose rescue did not produce a constructor application:
the major as the rescue left it (con-leche task #334). -/
theorem prepareMajorFueled_kStuck {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x m1 : Expr}
    (hk : ConLeche.recRuleK rules' = true)
    (h1 : ConLeche.majorToCtorFueled mode env F d cn rules' x = .ok m1)
    (hc : ConLeche.isCtorApp env m1 = false) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m1 := by
  have e1 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' x = .ok m1 := h1
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk, ite_true,
    e1, hc, Bool.false_eq_true, ite_false, bind, Except.bind]
  rfl

/-- con-leche: none — the converse of the `lit` arm of `ETables.get`: a tier
that decodes a handle to a literal view projects that literal. -/
theorem ETables.getLit_of_get {t : ETables} {i : EIdx} {l : ConLeche.Literal}
    (h : t.get i = some (.lit l)) : t.getLit i = some l := by
  simp only [ETables.get] at h
  simp only [ETables.getLit]
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (obtain ⟨r, hr, hh⟩ := Option.map_eq_some_iff.mp h
       cases hh; simp_all)

/-- con-leche: none — a handle that views to a literal is read by `viewLit`
as that literal. -/
theorem viewLit_of_view {st : EStore} {i : EIdx} {l : ConLeche.Literal}
    (h : st.view i = some (.lit l)) : st.viewLit i = some l := by
  rw [EStore.view_eq_tier] at h
  simp only [EStore.viewLit, EStore.persGetLit]
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at h ⊢; exact ETables.getLit_of_get h
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢; simp only [Bool.false_eq_true, ite_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at h ⊢; exact ETables.getLit_of_get h
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

/-- con-leche: ConLeche/Kernel/Core.lean:689-692 Expr.isStrLit — **THEOREM 1
for the twin's `isStrLit`**: a read-only test that agrees with the
denotation's. -/
theorem isStrLit_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isStrLit h
    ⦃fun b s' => s' = s₀ ∧ b = x.isStrLit; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  unfold ConRon.Arena.isStrLit
  by_cases ht : (h.tag == ETag.lit) = true
  · rw [ite_eq_left ht]
    have htag : h.tag = v.tagOf := EStore.tagOf_of_view hv
    cases v
    case lit l =>
      obtain rfl := denote_lit_inv hwf hv hden
      have hl := viewLit_of_view hv
      cases l <;>
        (simp only [ConRon.Arena.viewLit]
         vcgen
         all_goals first
           | (bridge_peel; subst_vars; simp_all [Expr.isStrLit]; done)
           | (bridge_peel; subst_vars; rename_i h1 h2; rw [hl] at h2; cases h2
              exact (h1 _ rfl).elim))
    all_goals
      exfalso
      simp only [ENodeView.tagOf] at htag
      rw [htag] at ht
      revert ht; decide
  · rw [ite_eq_right ht]
    have hns : x.isStrLit = false := by
      cases x with
      | lit l =>
        cases l with
        | natVal _ => rfl
        | strVal _ =>
          exfalso
          obtain rfl := view_of_denote_lit hwf hv hden
          have := EStore.tagOf_of_view hv
          simp only [ENodeView.tagOf] at this
          exact ht (by rw [this]; rfl)
      | _ => rfl
    vcgen
    bridge_peel; subst_vars
    exact ⟨rfl, hns.symm⟩

/-- con-leche: ConLeche/Kernel/Core.lean:751-769 prepareMajor — elsewhere,
the structure rescues on the major AS FOUND (lean4#15351; a `String` literal
skips them) produced a constructor application: that is the major. -/
theorem prepareMajorFueled_nkCtor {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x mE : Expr}
    (hk : ConLeche.recRuleK rules' = false)
    (h0 : (if x.isStrLit then .ok x
      else ConLeche.majorToCtorFueled mode env F d cn rules' x : CheckM Expr)
        = .ok mE)
    (hc : ConLeche.isCtorApp env mE = true) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok mE := by
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk,
    Bool.false_eq_true, ite_false]
  cases hs : x.isStrLit
  · simp only [hs, Bool.false_eq_true, ite_false] at h0
    have e0 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
        rules' x = .ok mE := h0
    simp only [Bool.false_eq_true, ite_false, e0, hc, ite_true, bind,
      Except.bind]
    rfl
  · simp only [hs, ite_true] at h0
    cases h0
    simp only [ite_true, hc, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:751-769 prepareMajor — elsewhere,
no constructor yet: `whnf`, the literal conversion, then the rescues once
more on the reduct. -/
theorem prepareMajorFueled_nk {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x mE m1 m2 m3 : Expr}
    (hk : ConLeche.recRuleK rules' = false)
    (h0 : (if x.isStrLit then .ok x
      else ConLeche.majorToCtorFueled mode env F d cn rules' x : CheckM Expr)
        = .ok mE)
    (hc : ConLeche.isCtorApp env mE = false)
    (h1 : ConLeche.whnf mode env F d mE = .ok m1)
    (h2 : ConLeche.litMajorToCtorFueled mode env F d m1 = .ok m2)
    (h3 : ConLeche.majorToCtorFueled mode env F d cn rules' m2 = .ok m3) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m3 := by
  have e1 : (ConLeche.pureFns mode env F).whnf d mE = .ok m1 := h1
  have e2 : ConLeche.litMajorToCtor (ConLeche.pureFns mode env F) env d m1 =
      .ok m2 := h2
  have e3 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' m2 = .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk,
    Bool.false_eq_true, ite_false]
  cases hs : x.isStrLit
  · simp only [hs, Bool.false_eq_true, ite_false] at h0
    have e0 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
        rules' x = .ok mE := h0
    simp only [Bool.false_eq_true, ite_false, e0, hc, e1, e2, e3, bind,
      Except.bind]
  · simp only [hs, ite_true] at h0
    cases h0
    simp only [ite_true, hc, Bool.false_eq_true, ite_false, e1, e2, e3, bind,
      Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:751-769 prepareMajor — **THEOREM 1
for `prepareMajor`**: the K rescue on the raw major, then only the literal
conversion of a rescued constructor (con-leche task #334); elsewhere the
structure rescues on the major as found, then head normalisation, the
literal conversion and the rescues once more (lean4#15351). -/
theorem prepareMajor_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (c : NIdx) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK mode env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.prepareMajor mode (coreKnot mode fe id fuel) fe d c rules
        major
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.prepareMajorFueled mode env F d cn rules' x) d
          s'.store r; ⊤⦄ := by
  unfold ConRon.Arena.prepareMajor
  rw [recRuleK_denote hr]
  split
  next hk =>
    refine triple_seq (majorToCtor_spec hμ hsim s₀ d c rules major cn
      rules' x hok hr hden hw) ?_
    rintro m1 s1 ⟨hok1, hx1, hp1, v1, hv1, hwv1, F1, hF1⟩
    refine triple_seq (isCtorApp_spec s1 m1 v1 hok1 hv1) ?_
    rintro ic s2 ⟨hs2, hic⟩
    subst s2
    by_cases hict : ic = true
    · rw [ite_eq_left hict]
      have hc : ConLeche.isCtorApp env v1 = true := hic ▸ hict
      refine triple_mono (litMajorToCtor_spec hsim s1 d m1 v1 hok1 hv1 hwv1) ?_
      rintro m3 s3 ⟨hok3, hx3, hp3, v3, hv3, hwv3, F3, hF3⟩
      refine ⟨hok3, hx1.trans hx3, hp3.trans hp1, v3, hv3,
        hwv3, max F1 F3, prepareMajorFueled_k hk
          (majorToCtorFueled_mono (by omega) hF1) hc
          (litMajorToCtorFueled_mono (by omega) hF3)⟩
    · rw [ite_eq_right hict]
      have hnc : ConLeche.isCtorApp env v1 = false := by rw [← hic]; simpa using hict
      have hpost : CheckOK mode env fe s1 ∧ Ext s₀.store s1.store ∧
          s1.pins = s₀.pins ∧
          SimEOp (fun F => ConLeche.prepareMajorFueled mode env F d cn rules' x) d
            s1.store m1 :=
        ⟨hok1, hx1, hp1, v1, hv1, hwv1, F1, prepareMajorFueled_kStuck hk hF1 hnc⟩
      vcgen
      subst_vars
      exact hpost
  next hk =>
    have hk' : ConLeche.recRuleK rules' = false := by simpa using hk
    -- the continuation, at whatever the structure rescues on the major as
    -- found produced (a `String` literal skips them)
    have hK : ∀ mE s1, (CheckOK mode env fe s1 ∧ Ext s₀.store s1.store ∧
          s1.pins = s₀.pins ∧
          SimEOp (fun F => (if x.isStrLit then .ok x
            else ConLeche.majorToCtorFueled mode env F d cn rules' x : CheckM Expr))
            d s1.store mE) →
        ⦃fun s => s = s1⦄ (do
          if ← ConRon.Arena.isCtorApp fe mE then pure mE
          else do
            let major₀ ← (coreKnot mode fe id fuel).whnf d mE
            let major₁ ← ConRon.Arena.litMajorToCtor (coreKnot mode fe id fuel) fe d
              major₀
            ConRon.Arena.majorToCtor mode (coreKnot mode fe id fuel) fe d c rules
              major₁ : AM EIdx)
        ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          SimEOp (fun F => ConLeche.prepareMajorFueled mode env F d cn rules' x) d
            s'.store r; ⊤⦄ := by
      rintro mE s1 ⟨hok1, hx1, hp1, vE, hvE, hwvE, F0, hF0⟩
      refine triple_seq (isCtorApp_spec s1 mE vE hok1 hvE) ?_
      rintro ic s2 ⟨hs2, hic⟩
      subst s2
      by_cases hict : ic = true
      · rw [ite_eq_left hict]
        have hc : ConLeche.isCtorApp env vE = true := hic ▸ hict
        have hpost : CheckOK mode env fe s1 ∧ Ext s₀.store s1.store ∧
            s1.pins = s₀.pins ∧
            SimEOp (fun F => ConLeche.prepareMajorFueled mode env F d cn rules' x) d
              s1.store mE :=
          ⟨hok1, hx1, hp1, vE, hvE, hwvE, F0, prepareMajorFueled_nkCtor hk' hF0 hc⟩
        vcgen
        subst_vars
        exact hpost
      · rw [ite_eq_right hict]
        have hnc : ConLeche.isCtorApp env vE = false := by rw [← hic]; simpa using hict
        refine triple_seq (hsim.whnf s1 d mE vE hok1 hvE hwvE) ?_
        rintro m1 s2 ⟨hok2, hx2, hp2, v1, hv1, hwv1, F1, hF1⟩
        refine triple_seq (litMajorToCtor_spec hsim s2 d m1 v1 hok2 hv1 hwv1) ?_
        rintro m2 s3 ⟨hok3, hx3, hp3, v2, hv2, hwv2, F2, hF2⟩
        have hx13 := hx1.trans (hx2.trans hx3)
        refine triple_mono (majorToCtor_spec hμ hsim s3 d c rules m2 cn rules'
          v2 hok3 (denoteRules_ext hx13 _ _ hr) hv2 hwv2) ?_
        rintro m3 s4 ⟨hok4, hx4, hp4, v3, hv3, hwv3, F3, hF3⟩
        refine ⟨hok4, hx13.trans hx4, hp4.trans (hp3.trans (hp2.trans hp1)), v3, hv3,
          hwv3, max F0 (max F1 (max F2 F3)), prepareMajorFueled_nk hk'
            ?_ hnc
            (ConLeche.whnf_mono (by omega) hF1)
            (litMajorToCtorFueled_mono (by omega) hF2)
            (majorToCtorFueled_mono (by omega) hF3)⟩
        cases hs : x.isStrLit
        · simp only [hs, Bool.false_eq_true, ite_false] at hF0 ⊢
          exact majorToCtorFueled_mono (by omega) hF0
        · simp only [hs, ite_true] at hF0 ⊢
          exact hF0
    refine triple_seq (isStrLit_spec s₀ major x hok hden) ?_
    rintro b s1 ⟨hs1, rfl⟩
    subst s1
    dsimp only
    cases hs : x.isStrLit
    · simp only [Bool.false_eq_true, ite_false]
      refine triple_seq (majorToCtor_spec hμ hsim s₀ d c rules major cn rules'
        x hok hr hden hw) ?_
      intro mE s1 hpost
      refine hK mE s1 ?_
      simpa only [hs, Bool.false_eq_true, ite_false] using hpost
    · simp only [ite_true, pure_bind]
      exact hK major s₀ ⟨hok, Ext.refl _, rfl, x, hden, hw, 0, by simp [hs]⟩

end ConRon.Bridge.Core
