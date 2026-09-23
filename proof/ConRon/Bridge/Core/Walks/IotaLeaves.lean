/-
# `ConRon.Bridge.Core.Walks.IotaLeaves` — the state-only readers under `iotaRec`

Task #97-P3-Core round 6 (lane `iota`): the six readers the stuck-major rescue
and the ι step consult, each an equation with con-leche's function.  The
walks that call the knot are `Walks/IotaMajor.lean` and `Walks/Iota.lean`.
-/
import ConRon.Bridge.Core.Walks.Stuck
import ConRon.Bridge.Core.Walks.ProjLit
import ConRon.Bridge.ExprOps.Guards
import ConRon.Bridge.ExprOps.Ranges

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. State-only readers -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:46-53 isCtorApp — **THEOREM 1
for `isCtorApp`**: an equation with con-leche's reader. -/
theorem isCtorApp_spec (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.isCtorApp fe a
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = ConLeche.isCtorApp env x⌝⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.isCtorApp
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ a hok.state
    (by rw [hda]; rfl)) ?_
  rintro hd s1 ⟨hs1, hrelF⟩
  subst s1
  have hdd : denoteE s₀.store hd = some x.getAppFn := hrelF x hda
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine view_bind_triple hvh ?_
  cases vh
  case const c us =>
    obtain ⟨cn, ls, hgf, hcn, _⟩ := denote_const_inv hwf hvh hdd
    dsimp only
    split
    next icv cnP cnF hfd =>
      obtain ⟨dcv, _hdcv, hfind⟩ := env_ctor_of_index hok hcn hfd
      mvcgen
      bridge_peel; subst_vars
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.isCtorApp, hgf, hfind]
    next hnd =>
      have hnc := env_not_ctor_of_index hok hcn (fun v p q h => hnd v p q h)
      mvcgen
      bridge_peel; subst_vars
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.isCtorApp, hgf]
      try (split
           · rename_i cv p q heq; exact absurd heq (hnc cv p q)
           · rfl)
  all_goals
    dsimp only
    mvcgen
    bridge_peel; subst_vars
    refine ⟨rfl, ?_⟩
    have hnc := denote_not_const hwf hvh hdd (by intro c us h; cases h)
    simp only [ConLeche.isCtorApp]
    try (split
         · rename_i c us heq; exact absurd heq (hnc c us)
         · rfl)

/-- con-leche: none — only a `Nat` literal converts. -/
theorem litToCtorIfNat_of_not_nat (x : Expr)
    (hx : ∀ n, x ≠ .lit (.natVal n)) : ConLeche.litToCtorIfNat env x = x := by
  cases x with
  | lit l =>
    cases l with
    | natVal n => exact absurd rfl (hx n)
    | strVal _ => rfl
  | _ => rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:197-200 natLitToConstructor —
**THEOREM 1 for `natLitToConstructor`**: `Nat.zero`, or `Nat.succ` applied to
the predecessor literal. -/
theorem natLitToConstructor_spec (s₀ : AState) (n : Nat)
    (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natLitToConstructor n
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (ConLeche.natLitToConstructor n)⌝⦄ := by
  unfold ConRon.Arena.natLitToConstructor
  cases n with
  | zero =>
    dsimp only
    unfold ConRon.Arena.pinNatZero
    refine triple_seq (pinAt_spec s₀ PIN_NAT_ZERO hok.pins) ?_
    rintro z s1 ⟨hs1, hz⟩
    subst s1
    exact constE_spec s₀ z ConLeche.natZeroName hok (hz _ rfl)
  | succ k =>
    dsimp only
    unfold ConRon.Arena.pinNatSucc
    refine triple_seq (pinAt_spec s₀ PIN_NAT_SUCC hok.pins) ?_
    rintro sn s1 ⟨hs1, hsn⟩
    subst s1
    refine triple_seq (constE_spec s₀ sn ConLeche.natSuccName hok (hsn _ rfl)) ?_
    rintro sc s2 ⟨hok2, hx2, hp2, hsc⟩
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s2 (.lit (.natVal k)) hok2 viewOK_lit) ?_
    rintro l s3 ⟨hok3, hx3, hp3, hl⟩
    have hl' : denoteE s3.store l = some (.lit (.natVal k)) := by rw [hl]; rfl
    have hsc3 := denote_ext hsc hx3
    refine triple_mono (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s3 (.app sc l) hok3 (viewOK_app (by rw [hsc3]; rfl) (by rw [hl']; rfl))) ?_
    rintro r s4 ⟨hok4, hx4, hp4, hr⟩
    refine ⟨hok4, hx2.trans (hx3.trans hx4), hp4.trans (hp3.trans hp2), ?_⟩
    rw [hr]
    simp only [denoteEView, denote_ext hsc3 hx4, denote_ext hl' hx4, opt2,
      ConLeche.natLitToConstructor]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:264-268 litToCtorIfNat —
**THEOREM 1 for `litToCtorIfNat`**: a supported `Nat` literal one layer. -/
theorem litToCtorIfNat_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store h = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.litToCtorIfNat fe h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (ConLeche.litToCtorIfNat env x)⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hda
  unfold ConRon.Arena.litToCtorIfNat
  refine view_bind_triple hv ?_
  have hpass : ConLeche.litToCtorIfNat env x = x →
      ⦃fun s => ⌜s = s₀⌝⦄ (pure h : AM EIdx)
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          denoteE s'.store r = some (ConLeche.litToCtorIfNat env x)⌝⦄ := by
    intro hx
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, by rw [hx]; exact hda⟩
  cases v
  case lit l =>
    obtain rfl := denote_lit_inv hwf hv hda
    cases l with
    | strVal str => exact hpass rfl
    | natVal n =>
      dsimp only
      refine triple_seq (natLitSupported_spec s₀ hok) ?_
      rintro sup s1 ⟨hok1, hx1, hp1, hsup⟩
      split
      next hsupt =>
        have hS : ConLeche.natLitSupported env = true := hsup ▸ hsupt
        refine triple_mono (natLitToConstructor_spec s1 n hok1) ?_
        rintro r s2 ⟨hok2, hx2, hp2, hr⟩
        refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
        rw [hr]
        simp only [ConLeche.litToCtorIfNat, hS, if_true]
      next hsupf =>
        have hS : ConLeche.natLitSupported env = false := by
          rw [← hsup]; simpa using hsupf
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok1, hx1, hp1, ?_⟩
        simp only [ConLeche.litToCtorIfNat, hS, Bool.false_eq_true, if_false]
        exact denote_ext hda hx1
  all_goals
    dsimp only
    refine hpass (litToCtorIfNat_of_not_nat _ ?_)
    intro n hx
    subst hx
    have := view_of_denote_lit hwf hv hda
    cases this

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:93-95 capsNeverZero —
**THEOREM 1 for `capsNeverZero`**. -/
theorem capsNeverZero_spec (s₀ : AState) (lps : List NIdx) (us : LsIdx)
    (icaps : IIndCaps) (ks : List ConLeche.Name) (vs : List Level)
    (caps : IndCaps) (hok : CheckOK mode env fe s₀)
    (hks : Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : denoteLs s₀.store.lss us = some vs)
    (hcaps : Frontend.denoteCaps s₀.store icaps = some caps) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.capsNeverZero lps us icaps
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.capsNeverZero ks vs caps⌝⦄ := by
  unfold ConRon.Arena.capsNeverZero
  refine triple_seq (ExprOps.readNamesM_specF s₀ lps hok.caches.readN) ?_
  rintro ks' s1 ⟨hst1, hm1, hp1, hc1, hks1, hN1⟩
  have hf1 := ReadbackFrame.ofReadN hst1 hm1 hp1 hc1 hN1
  have hok1 := CheckOK.ofReadbackFrame hok hf1
  refine triple_seq (ExprOps.readLevelsM_specF s1 us hok1.caches.readLs) ?_
  rintro vs' s2 ⟨hst2, hm2, hp2, hc2, hvs2, hLs2⟩
  have hf2 := ReadbackFrame.ofReadLs hst2 hm2 hp2 hc2 hLs2
  have hok2 := CheckOK.ofReadbackFrame hok1 hf2
  rw [hks] at hks1
  obtain rfl := Option.some.inj hks1
  rw [hst1, hvs] at hvs2
  obtain rfl := Option.some.inj hvs2
  have hsz : caps.sortZ = icaps.sortZ := by
    simp only [Frontend.denoteCaps] at hcaps
    split at hcaps
    · cases hcaps; rfl
    · simp at hcaps
  mvcgen
  bridge_peel; subst_vars
  refine ⟨hok2, hst2.trans hst1, hp2.trans hp1, ?_⟩
  simp only [ConLeche.capsNeverZero, hsz]

/-- con-leche: ConLeche/Kernel/Core.lean:586-588 majorToCtor (the scope
guard) — **THEOREM 1 for `fabScopeOk`**: the executed tier's three memoised
walks decide con-leche's syntactic guard. -/
theorem fabScopeOk_spec (s₀ : AState) (d : Nat) (fab major : EIdx)
    (ef em : Expr) (hok : CheckOK mode env fe s₀)
    (hf : denoteE s₀.store fab = some ef) (hm : denoteE s₀.store major = some em) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.fabScopeOk d fab major
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        r = (ef.wscopedB d && ef.looseBVarsBounded 0 &&
          ef.fvarLeaves.all (fun l => em.fvarLeaves.contains l))⌝⦄ := by
  unfold ConRon.Arena.fabScopeOk
  refine triple_seq (ExprOps.wscopedBFast_spec coreWalkFuel d s₀ fab hok.state
    (by rw [hf]; rfl)) ?_
  rintro w s1 ⟨hs1, hw⟩
  subst s1
  have hw' : w = ef.wscopedB d := hw ef hf
  split
  next hwn =>
    have hwf0 : ef.wscopedB d = false := by simpa [hw'] using hwn
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok, rfl, rfl, ?_⟩
    simp [hwf0]
  next hwy =>
    have hwt : ef.wscopedB d = true := by simpa [hw'] using hwy
    refine triple_seq (ExprOps.looseBVarsBoundedFast_spec coreWalkFuel 0 s₀ fab
      hok.state (by rw [hf]; rfl)) ?_
    rintro lb s2 ⟨hst2, hc2, hp2, hlb⟩
    have hlb' : lb = ef.looseBVarsBounded 0 := hlb ef hf
    have hok2 : CheckOK mode env fe s2 :=
      hok.mono ⟨by rw [hst2]; exact hok.state.wf⟩ (by rw [hst2]; exact Ext.refl _)
        hc2 hp2
    split
    next hln =>
      have hlf : ef.looseBVarsBounded 0 = false := by simpa [hlb'] using hln
      mvcgen
      bridge_peel; subst_vars
      refine ⟨hok2, hst2, hp2, ?_⟩
      simp [hlf]
    next hly =>
      have hlt : ef.looseBVarsBounded 0 = true := by simpa [hlb'] using hly
      refine triple_mono (ExprOps.leafGuard_spec coreWalkFuel s2 fab major
        hok2.state (by rw [hst2, hf]; rfl) (by rw [hst2, hm]; rfl)) ?_
      rintro r s3 ⟨hs3, hr⟩
      subst hs3
      refine ⟨hok2, hst2, hp2, ?_⟩
      have := hr em (by rw [hst2]; exact hm) ef (by rw [hst2]; exact hf)
      rw [this, hwt, hlt]
      simp [ExprOps.leavesSubSpec]

/-- con-leche: none — the denotation of an appended handle list. -/
theorem denoteEList_appendI {st : EStore} :
    ∀ {as bs : List EIdx} {xs ys : List Expr},
      Frontend.denoteEList st as = some xs →
      Frontend.denoteEList st bs = some ys →
      Frontend.denoteEList st (as ++ bs) = some (xs ++ ys)
  | [], bs, xs, ys, ha, hb => by
    simp only [Frontend.denoteEList, Option.some.injEq] at ha
    subst ha; simpa using hb
  | a :: as, bs, xs, ys, ha, hb => by
    obtain ⟨x, xs', hx, hxs, rfl⟩ := denoteEList_cons_inv ha
    simp only [List.cons_append, Frontend.denoteEList, hx,
      denoteEList_appendI hxs hb]

/-- con-leche: ConLeche/Kernel/Env.lean:629 projFnName — **THEOREM 1 for
`projFnName`** (the `I` suffix: a lane-local copy; the η lane's module may
carry the same statement). -/
theorem projFnName_specI (s₀ : AState) (T : NIdx) (i : Nat) (Tn : ConLeche.Name)
    (hwf : StoreWF s₀.store) (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.projFnName T i
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteN s'.store.ns h = some (ConLeche.projFnName Tn i)⌝⦄ := by
  mvcgen [ConRon.Arena.projFnName, internNNode_spec]
  all_goals (bridge_peel; subst_vars
             grind [denoteNView, Arena.NStore.ViewOK, NNodeView.children,
               nview_isSome_of_denote, Ext.trans, ConLeche.projFnName])

/-- con-leche: none — `CheckOK` past `projFnName` (an arena-growing call). -/
theorem projFnName_ok (s₀ : AState) (T : NIdx) (i : Nat) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.projFnName T i
    ⦃⇓? h s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteN s'.store.ns h = some (ConLeche.projFnName Tn i)⌝⦄ :=
  triple_mono (projFnName_specI s₀ T i Tn hok.state.wf hT)
    (fun _ _ ⟨hwf', hx', _, hc', hp', hd⟩ =>
      ⟨hok.mono ⟨hwf'⟩ hx' hc' hp', hx', hp', hd⟩)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:709-714 towerSlotsAll — the
counted slot walk, from slot `j` for `n` slots. -/
theorem towerSlotsAllGo_specI (T : NIdx) (Tn : ConLeche.Name) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.towerSlotsAllGo fe T n j
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          r = (List.range' j n).all (fun k => (env.findProj? Tn k).isSome)⌝⦄ := by
  intro n
  induction n with
  | zero =>
    intro j s₀ hok _
    mvcgen [ConRon.Arena.towerSlotsAllGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | succ n ih =>
    intro j s₀ hok hT
    unfold ConRon.Arena.towerSlotsAllGo
    refine triple_seq (IFEnv.findProj?_spec s₀ T j Tn hok hT) ?_
    rintro o s1 ⟨hok1, hx1, _, _, hp1, hsome, hnone⟩
    have hiff : o.isSome = (env.findProj? Tn j).isSome := by
      cases o with
      | none => rw [hnone rfl]; rfl
      | some e => obtain ⟨p, _, hp⟩ := hsome e rfl; rw [hp]; rfl
    split
    next hy =>
      refine triple_mono (ih (j + 1) s1 hok1 (denoteN_ext hT hx1)) ?_
      rintro r s2 ⟨hok2, hx2, hp2, hr⟩
      refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
      rw [hr, List.range'_succ, List.all_cons, ← hiff, hy, Bool.true_and]
    next hn =>
      have hf : (env.findProj? Tn j).isSome = false := by
        rw [← hiff]; simpa using hn
      mvcgen
      bridge_peel; subst_vars
      refine ⟨hok1, hx1, hp1, ?_⟩
      rw [List.range'_succ, List.all_cons, hf, Bool.false_and]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs — the `.proj`
nodes, from slot `j` for `n` slots. -/
theorem projNodesGo_specI (T : NIdx) (b : EIdx) (Tn : ConLeche.Name) (x : Expr) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn → denoteE s₀.store b = some x →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.projNodesGo T b n j
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          Frontend.denoteEList s'.store r =
            some ((List.range' j n).map (fun k => Expr.proj Tn k x))⌝⦄ := by
  intro n
  induction n with
  | zero =>
    intro j s₀ hok _ _
    mvcgen [ConRon.Arena.projNodesGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | succ n ih =>
    intro j s₀ hok hT hb
    unfold ConRon.Arena.projNodesGo
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s₀ (.proj T j b) hok (viewOK_proj (nview_isSome_of_denote hT)
        (by rw [hb]; rfl))) ?_
    rintro p s1 ⟨hok1, hx1, hp1, hpd⟩
    have hpd' : denoteE s1.store p = some (.proj Tn j x) := by
      rw [hpd]; simp only [denoteEView, denoteN_ext hT hx1, denote_ext hb hx1, opt2]
    refine triple_seq (ih (j + 1) s1 hok1 (denoteN_ext hT hx1)
      (denote_ext hb hx1)) ?_
    rintro rest s2 ⟨hok2, hx2, hp2, hrest⟩
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    rw [List.range'_succ, List.map_cons]
    simp only [Frontend.denoteEList, denote_ext hpd' hx2, hrest]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs — the
projection-function applications, from slot `j` for `n` slots. -/
theorem projAppsGo_specI (T : NIdx) (us : LsIdx) (targs : List EIdx) (b : EIdx)
    (Tn : ConLeche.Name) (ls : List Level) (ts : List Expr) (x : Expr) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn → denoteLs s₀.store.lss us = some ls →
      Frontend.denoteEList s₀.store targs = some ts →
      denoteE s₀.store b = some x →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.projAppsGo T us targs b n j
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          Frontend.denoteEList s'.store r =
            some ((List.range' j n).map (fun k =>
              Expr.mkAppN (.const (ConLeche.projFnName Tn k) ls)
                (ts ++ [x])))⌝⦄ := by
  intro n
  induction n with
  | zero =>
    intro j s₀ hok _ _ _ _
    mvcgen [ConRon.Arena.projAppsGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | succ n ih =>
    intro j s₀ hok hT hus hts hb
    unfold ConRon.Arena.projAppsGo
    refine triple_seq (projFnName_ok s₀ T j Tn hok hT) ?_
    rintro pn s1 ⟨hok1, hx1, hp1, hpn⟩
    have hus1 := denoteLs_ext hus hx1
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s1 (.const pn us) hok1 (viewOK_const (nview_isSome_of_denote hpn)
        (by obtain ⟨w, hw, _⟩ := denoteLs_view hus1; rw [hw]; rfl))) ?_
    rintro f s2 ⟨hok2, hx2, hp2, hf⟩
    have hf' : denoteE s2.store f = some (.const (ConLeche.projFnName Tn j) ls) := by
      rw [hf]; simp only [denoteEView, denoteN_ext hpn hx2, denoteLs_ext hus1 hx2, opt2]
    have hx02 := hx1.trans hx2
    have hargs2 : Frontend.denoteEList s2.store (targs ++ [b]) = some (ts ++ [x]) :=
      denoteEList_appendI (denoteEList_ext hx02 _ _ hts)
        (by simp [Frontend.denoteEList, denote_ext hb hx02])
    refine triple_seq (ExprOps.mkAppN_spec (targs ++ [b]) s2 f hok2.state
      (by rw [hf']; rfl) (by rw [hargs2]; rfl)) ?_
    rintro p s3 ⟨hst3, hx3, _, _, hc3, hp3, hrel⟩
    have hok3 : CheckOK mode env fe s3 := hok2.mono hst3 hx3 hc3 hp3
    have hpd := hrel _ _ hf' hargs2
    have hx03 := hx02.trans hx3
    refine triple_seq (ih (j + 1) s3 hok3 (denoteN_ext hT hx03)
      (denoteLs_ext hus hx03) (denoteEList_ext hx03 _ _ hts) (denote_ext hb hx03)) ?_
    rintro rest s4 ⟨hok4, hx4, hp4, hrest⟩
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok4, hx03.trans hx4, hp4.trans (hp3.trans (hp2.trans hp1)), ?_⟩
    rw [List.range'_succ, List.map_cons]
    simp only [Frontend.denoteEList, denote_ext hpd hx4, hrest]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs — **THEOREM 1
for `etaProjs`**. -/
theorem etaProjs_specI (s₀ : AState) (T : NIdx) (ust : LsIdx)
    (targs : List EIdx) (major : EIdx) (nF : Nat) (Tn : ConLeche.Name)
    (ls : List Level) (ts : List Expr) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hus : denoteLs s₀.store.lss ust = some ls)
    (hts : Frontend.denoteEList s₀.store targs = some ts)
    (hx : denoteE s₀.store major = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.etaProjs fe T ust targs major nF
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.etaProjs env Tn ls ts x nF)⌝⦄ := by
  unfold ConRon.Arena.etaProjs ConRon.Arena.towerSlotsAll
  refine triple_seq (towerSlotsAllGo_specI T Tn nF 0 s₀ hok hT) ?_
  rintro tw s1 ⟨hok1, hx1, hp1, htw⟩
  have htw' : tw = ConLeche.towerSlotsAll env Tn nF := by
    rw [htw, ConLeche.towerSlotsAll, List.range_eq_range']
  split
  next hy =>
    refine triple_mono (projNodesGo_specI T major Tn x nF 0 s1 hok1
      (denoteN_ext hT hx1) (denote_ext hx hx1)) ?_
    rintro r s2 ⟨hok2, hx2, hp2, hr⟩
    refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    rw [hr, ConLeche.etaProjs, ← htw', hy]
    simp [List.range_eq_range']
  next hn =>
    have hf : tw = false := by simpa using hn
    refine triple_mono (projAppsGo_specI T ust targs major Tn ls ts x nF 0 s1 hok1
      (denoteN_ext hT hx1) (denoteLs_ext hus hx1) (denoteEList_ext hx1 _ _ hts)
      (denote_ext hx hx1)) ?_
    rintro r s2 ⟨hok2, hx2, hp2, hr⟩
    refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    rw [hr, ConLeche.etaProjs, ← htw', hf]
    simp [List.range_eq_range']

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:761-766 etaFabArgsE — **THEOREM
1 for `etaFabArgsE`**: the η rescue's fabricated argument spine. -/
theorem etaFabArgsE_spec (s₀ : AState) (T : NIdx) (ust : LsIdx)
    (targs : List EIdx) (major : EIdx) (nF : Nat) (Tn : ConLeche.Name)
    (ls : List Level) (ts : List Expr) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hus : denoteLs s₀.store.lss ust = some ls)
    (hts : Frontend.denoteEList s₀.store targs = some ts)
    (hx : denoteE s₀.store major = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.etaFabArgsE fe T ust targs major nF
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.etaFabArgsE env Tn ls ts x nF)⌝⦄ := by
  unfold ConRon.Arena.etaFabArgsE
  refine triple_seq (etaProjs_specI s₀ T ust targs major nF Tn ls ts x hok hT hus
    hts hx) ?_
  rintro ps s1 ⟨hok1, hx1, hp1, hps⟩
  mvcgen
  bridge_peel; subst_vars
  refine ⟨hok1, hx1, hp1, ?_⟩
  rw [denoteEList_appendI (denoteEList_ext hx1 _ _ hts) hps]
  rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:796-809 andRescueSlotsOf — the
two-slot walk, from slot `j` for `n` slots. -/
theorem andRescueSlotsGo_specI (ctor : NIdx) (nP : Nat) (ust : LsIdx)
    (cn : ConLeche.Name) (ls : List Level) (an : NIdx) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns an = some ConLeche.andName →
      denoteN s₀.store.ns ctor = some cn → denoteLs s₀.store.lss ust = some ls →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.andRescueSlotsGo fe an ctor nP ust n j
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          r = (List.range' j n).all (fun k =>
            match env.findProj? ConLeche.andName k with
            | some e => e.ctor == cn && e.numParams == nP && e.numFields == 2 &&
                e.fireOk ls
            | none => false)⌝⦄ := by
  intro n
  induction n with
  | zero =>
    intro j s₀ hok _ _ _
    mvcgen [ConRon.Arena.andRescueSlotsGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | succ n ih =>
    intro j s₀ hok han hc hus
    unfold ConRon.Arena.andRescueSlotsGo
    refine triple_seq (IFEnv.findProj?_spec s₀ an j ConLeche.andName hok han) ?_
    rintro o s1 ⟨hok1, hx1, _, _, hp1, hsome, hnone⟩
    cases o with
    | none =>
      have hf := hnone rfl
      mvcgen
      bridge_peel; subst_vars
      refine ⟨hok1, hx1, hp1, ?_⟩
      rw [List.range'_succ, List.all_cons, hf]; rfl
    | some e =>
      obtain ⟨p, hpe, hfp⟩ := hsome e rfl
      obtain ⟨_, _, hct, _, _, _, _, hnp, hnf, _⟩ := denoteProjEntry_inv hpe
      dsimp only
      refine triple_seq (IProjEntry.fireOk_spec s1 e ust p ls hok1 hpe
        (denoteLs_ext hus hx1)) ?_
      rintro fo s2 ⟨hok2, hst2, hp2, hfo⟩
      have hcond : (e.ctor == ctor && e.numParams == nP && e.numFields == 2 && fo) =
          (p.ctor == cn && p.numParams == nP && p.numFields == 2 && p.fireOk ls) := by
        obtain ⟨rk, hrk⟩ := hok1.state.wf
        rw [beq_of_denoteN hrk.nsWF hct (denoteN_ext hc hx1), hnp, hnf, hfo]
      have hx12 : Ext s1.store s2.store := by rw [hst2]; exact Ext.refl _
      split
      next hy =>
        have hy' : (p.ctor == cn && p.numParams == nP && p.numFields == 2 &&
            p.fireOk ls) = true := hcond ▸ hy
        refine triple_mono (ih (j + 1) s2 hok2 (denoteN_ext han (hx1.trans hx12))
          (denoteN_ext hc (hx1.trans hx12)) (denoteLs_ext hus (hx1.trans hx12))) ?_
        rintro r s3 ⟨hok3, hx3, hp3, hr⟩
        refine ⟨hok3, hx1.trans (hx12.trans hx3), hp3.trans (hp2.trans hp1), ?_⟩
        rw [hr, List.range'_succ, List.all_cons, hfp]
        simp only [hy', Bool.true_and]
      next hn =>
        have hn' : (p.ctor == cn && p.numParams == nP && p.numFields == 2 &&
            p.fireOk ls) = false := by rw [← hcond]; simpa using hn
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok2, hx1.trans hx12, hp2.trans hp1, ?_⟩
        rw [List.range'_succ, List.all_cons, hfp]
        simp only [hn', Bool.false_and]
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:796-813 andRescueSlots —
**THEOREM 1 for `andRescueSlots`**: the pinned `And`'s two slots, ready to
fire. -/
theorem andRescueSlots_spec (s₀ : AState) (ctor : NIdx) (nP : Nat)
    (ust : LsIdx) (cn : ConLeche.Name) (ls : List Level)
    (hok : CheckOK mode env fe s₀) (hc : denoteN s₀.store.ns ctor = some cn)
    (hus : denoteLs s₀.store.lss ust = some ls) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.andRescueSlots fe ctor nP ust
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.andRescueSlots env cn nP ls⌝⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.andRescueSlots ConRon.Arena.pinAnd
  refine triple_seq (pinAt_spec s₀ PIN_AND hok.pins) ?_
  rintro an s1 ⟨hs1, han⟩
  subst s1
  refine triple_mono (andRescueSlotsGo_specI ctor nP ust cn ls an 2 0 s₀ hok
    (han _ rfl) hc hus) ?_
  rintro r s' ⟨hok', hst, hp, hr⟩
  refine ⟨hok', hst, hp, ?_⟩
  rw [hr, ConLeche.andRescueSlots, ConLeche.andRescueSlotsOf, List.range_eq_range']
  rfl


end ConRon.Bridge.Core
