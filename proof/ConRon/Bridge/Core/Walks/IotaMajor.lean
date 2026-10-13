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
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
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
    sorry
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
theorem majorEta_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
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
    sorry
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
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
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
    sorry
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
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
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
      sorry
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
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
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
    refine triple_seq (majorToCtor_spec hμ henv hsim s₀ d c rules major cn
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
        refine triple_mono (majorToCtor_spec hμ henv hsim s3 d c rules m2 cn rules'
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
      refine triple_seq (majorToCtor_spec hμ henv hsim s₀ d c rules major cn rules'
        x hok hr hden hw) ?_
      intro mE s1 hpost
      refine hK mE s1 ?_
      simpa only [hs, Bool.false_eq_true, ite_false] using hpost
    · simp only [ite_true, pure_bind]
      exact hK major s₀ ⟨hok, Ext.refl _, rfl, x, hden, hw, 0, by simp [hs]⟩

end ConRon.Bridge.Core
