/-
# `ConRon.Bridge.Core.Walks.Iota` — the ι step, `iotaRec`

Task #97-P3-Core round 6 (lane `iota`).  `iotaRec` is `whnfCoreBody`'s ι
step: at a stored recursor applied to exactly its telescope, the major premise
is PREPARED (the K rescue on the raw major, or head normalisation, the literal
conversion and the η / `And` rescue), and a matching rule of a fully applied
constructor fires after the level and parameter comparison and the three
certificate runs.  Round 4 left it in `Walks/Owed.lean` as one statement over
the whole tower; it moved here because the η rescue calls
`structEtaCertWith` (`Walks/Stuck.lean`), which `Owed.lean` cannot import.

The module is top-down, one theorem per twin function:

| walk | twin (`Arena/Core.lean`) | con-leche |
|---|---|---|
| `iotaRec_spec` | `:2049` | `Kernel/Core.lean:797-910` |
| `iotaRecAt_spec` | `:1959` | the same clause at a held spine |
| `prepareMajor_spec` | `:1871` | `:758-795` |
| `majorToCtor_spec` | `:1660` | `:544-726` |
| `litMajorToCtor_spec` | `:1774` | `:728-740` |
| `recFireComparands_spec` | `:1920` | `CoreDefs.lean:948-968` |
| `iotaIndexOk_spec` | `:1252` | `Core.lean:255-265` |

and the state-only readers under them (`isCtorApp`, `litToCtorIfNat`,
`capsNeverZero`, `fabScopeOk`, `etaFabArgsE`, `andRescueSlots`).

**Preconditions added to `iotaRec_spec`** (it had neither): `hμ :
mode.verifiedChecks = true` — the twin gates the rescue certificates and the
ι certificate family on `mode.certs` (`Cached/CoreC.lean:576/588/621/654/658/
797/814`) where con-leche's spec body runs them unconditionally, the same
repair round 5 made to `stuckIrrel_spec` — and `henv : EnvWF env`, the
hypothesis of con-leche's own `iotaRec_WScoped` / `prepareMajorFueled_WScoped`
(the answer's scoping, which `SimOOp` states) and of `const_ty_hasFvar` (the
certificate runs' subjects).
-/
import ConRon.Bridge.Core.Walks.IotaMajor

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 3. The firing rule's comparands and the index comparison -/

/-- con-leche: none — a denoting level-handle list is a valid list node. -/
theorem lsViewOK_of_denote {st : LsStore} :
    ∀ {v : List LIdx} {L : List Level}, denoteLList st.ls v = some L → st.ViewOK v
  | [], _, _ => by intro c hc; simp at hc
  | u :: us, L, h => by
    simp only [denoteLList] at h
    cases h1 : denoteL st.ls u with
    | none => rw [h1] at h; simp [opt2] at h
    | some l =>
      cases h2 : denoteLList st.ls us with
      | none => rw [h1, h2] at h; simp [opt2] at h
      | some L' =>
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact lview_isSome_of_denote h1
        · exact lsViewOK_of_denote h2 c hc

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands — the
nested rule's level comparands, `lvls.map (Level.subst lps us)`. -/
theorem substLevelsAt_spec (ks : List ConLeche.Name) (vs : List Level) :
    ∀ (lvls : List LIdx) (s₀ : AState) (L : List Level),
      CheckOK mode env fe s₀ → denoteLList s₀.store.ls lvls = some L →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.substLevelsAt ks vs lvls
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          denoteLList s'.store.ls r = some (L.map (Level.subst ks vs))⌝⦄ := by
  intro lvls
  induction lvls with
  | nil =>
    intro s₀ L hok hL
    simp only [denoteLList, Option.some.injEq] at hL
    subst hL
    mvcgen [ConRon.Arena.substLevelsAt]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | cons u us ih =>
    intro s₀ L hok hL
    obtain ⟨l0, L', hu, hus, rfl⟩ : ∃ l0 L', denoteL s₀.store.ls u = some l0 ∧
        denoteLList s₀.store.ls us = some L' ∧ L = l0 :: L' := by
      simp only [denoteLList] at hL
      cases h1 : denoteL s₀.store.ls u with
      | none => rw [h1] at hL; simp [opt2] at hL
      | some l =>
        cases h2 : denoteLList s₀.store.ls us with
        | none => rw [h1, h2] at hL; simp [opt2] at hL
        | some L' =>
          rw [h1, h2] at hL
          simp only [opt2, Option.some.injEq] at hL
          exact ⟨l, L', rfl, rfl, hL.symm⟩
    unfold ConRon.Arena.substLevelsAt
    refine triple_seq (ExprOps.readLevelM_specF s₀ u hok.caches.readL) ?_
    rintro l s1 ⟨hst1, hm1, hp1, hc1, hl1, hL1⟩
    have hok1 := CheckOK.ofReadbackFrame hok
      (ReadbackFrame.ofReadL hst1 hm1 hp1 hc1 hL1)
    have hle : l0 = l := Option.some.inj (hu.symm.trans hl1)
    subst hle
    refine triple_seq (internLevel_spec s1 (Level.subst ks vs l0)
      hok1.state.wf) ?_
    rintro h s2 ⟨hwf2, hx2, _, _, _, _, hc2, hp2, hh⟩
    have hok2 : CheckOK mode env fe s2 := hok1.mono ⟨hwf2⟩ hx2 hc2 hp2
    have hx02 : Ext s₀.store s2.store := by rw [← hst1]; exact hx2
    refine triple_seq (ih s2 L' hok2 (denoteLListE_ext hx02 _ _ hus)) ?_
    rintro rest s3 ⟨hok3, hx3, hp3, hrest⟩
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok3, hx02.trans hx3, hp3.trans (hp2.trans hp1), ?_⟩
    simp only [List.map_cons]
    exact denoteLList_cons_of (denoteL_ext hh hx3) hrest

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands — the
canonical rule's level comparands, `cvjLps.map fun p => Level.subst lps us
(.param p)`. -/
theorem substParamLevels_spec (ks : List ConLeche.Name) (vs : List Level) :
    ∀ (ps : List NIdx) (s₀ : AState) (cs : List ConLeche.Name),
      CheckOK mode env fe s₀ → Frontend.denoteNList s₀.store.ns ps = some cs →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.substParamLevels ks vs ps
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          denoteLList s'.store.ls r =
            some (cs.map fun p => Level.subst ks vs (.param p))⌝⦄ := by
  intro ps
  induction ps with
  | nil =>
    intro s₀ cs hok hcs
    simp only [Frontend.denoteNList, Option.some.injEq] at hcs
    subst hcs
    mvcgen [ConRon.Arena.substParamLevels]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | cons p ps ih =>
    intro s₀ cs hok hcs
    obtain ⟨c0, cs', hp0, hps, rfl⟩ : ∃ c0 cs', denoteN s₀.store.ns p = some c0 ∧
        Frontend.denoteNList s₀.store.ns ps = some cs' ∧ cs = c0 :: cs' := by
      simp only [Frontend.denoteNList] at hcs
      cases h1 : denoteN s₀.store.ns p with
      | none => rw [h1] at hcs; simp at hcs
      | some c =>
        cases h2 : Frontend.denoteNList s₀.store.ns ps with
        | none => rw [h1, h2] at hcs; simp at hcs
        | some cs' =>
          rw [h1, h2] at hcs
          simp only [Option.some.injEq] at hcs
          exact ⟨c, cs', rfl, rfl, hcs.symm⟩
    unfold ConRon.Arena.substParamLevels
    refine triple_seq (ExprOps.readNameM_specF s₀ p hok.caches.readN) ?_
    rintro pn s1 ⟨hst1, hm1, hp1, hc1, hpn1, hN1⟩
    have hok1 := CheckOK.ofReadbackFrame hok
      (ReadbackFrame.ofReadN hst1 hm1 hp1 hc1 hN1)
    have hle : c0 = pn := Option.some.inj (hp0.symm.trans hpn1)
    subst hle
    refine triple_seq (internLevel_spec s1 (Level.subst ks vs (.param c0))
      hok1.state.wf) ?_
    rintro h s2 ⟨hwf2, hx2, _, _, _, _, hc2, hp2, hh⟩
    have hok2 : CheckOK mode env fe s2 := hok1.mono ⟨hwf2⟩ hx2 hc2 hp2
    have hx02 : Ext s₀.store s2.store := by rw [← hst1]; exact hx2
    refine triple_seq (ih s2 cs' hok2 (denoteNListE_ext hx02 _ _ hps)) ?_
    rintro rest s3 ⟨hok3, hx3, hp3, hrest⟩
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok3, hx02.trans hx3, hp3.trans (hp2.trans hp1), ?_⟩
    simp only [List.map_cons]
    exact denoteLList_cons_of (denoteL_ext hh hx3) hrest

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands — the
nested rule's parameter pins, level-instantiated and instantiated at the
recursor's leading-argument spine. -/
theorem instSpinePins_spec (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (rP : Nat) (ksv : List ConLeche.Name) (usv : List Level) (xs : List Expr) :
    ∀ (pins : List EIdx) (s₀ : AState) (Ps : List Expr),
      CheckOK mode env fe s₀ →
      Frontend.denoteNList s₀.store.ns lps = some ksv →
      denoteLs s₀.store.lss us = some usv →
      Frontend.denoteEList s₀.store args = some xs →
      Frontend.denoteEList s₀.store pins = some Ps →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.instSpinePins lps us args rP pins
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          Frontend.denoteEList s'.store r = some (Ps.map fun p =>
            Expr.instSpine (xs.take rP) (rP - 1)
              (p.instantiateLevelParams ksv usv))⌝⦄ := by
  intro pins
  induction pins with
  | nil =>
    intro s₀ Ps hok _ _ _ hPs
    obtain rfl := denoteEList_nil_inv hPs
    mvcgen [ConRon.Arena.instSpinePins]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | cons p ps ih =>
    intro s₀ Ps hok hks hus hxs hPs
    obtain ⟨P, Ps', hP, hPs', rfl⟩ := denoteEList_cons_inv hPs
    unfold ConRon.Arena.instSpinePins
    refine triple_seq (ExprOps.instLPFast_spec coreWalkFuel s₀ lps us p ksv usv
      hok.state hok.caches.readN hok.caches.readL hok.caches.readLs hks hus
      (by rw [hP]; rfl)) ?_
    rintro q s1 ⟨hst1, hx1, _, hL1, hLs1, hN1, hc1, hp1, _, hrel1⟩
    have hok1 := CheckOK.ofInstLP hok hst1 hx1 hL1 hLs1 hN1 hc1 hp1
    have hq := hrel1 P hP
    have hxs1 := ExprOps.denoteEList_take rP _ _ (denoteEList_ext hx1 _ _ hxs)
    refine triple_seq (ExprOps.instSpine_spec coreWalkFuel (args.take rP) s1
      (rP - 1) q hok1.state (by rw [hq]; rfl) (by rw [hxs1]; rfl)) ?_
    rintro sp s2 ⟨hst2, hx2, _, hc2, hp2, hrel2⟩
    have hok2 : CheckOK mode env fe s2 := hok1.mono hst2 hx2 hc2 hp2
    have hsp := hrel2 _ _ hq hxs1
    have hx02 := hx1.trans hx2
    refine triple_seq (ih s2 Ps' hok2 (denoteNListE_ext hx02 _ _ hks)
      (denoteLs_ext hus hx02) (denoteEList_ext hx02 _ _ hxs)
      (denoteEList_ext hx02 _ _ hPs')) ?_
    rintro rest s3 ⟨hok3, hx3, hp3, hrest⟩
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok3, hx02.trans hx3, hp3.trans (hp2.trans hp1), ?_⟩
    simp only [List.map_cons, Frontend.denoteEList, denote_ext hsp hx3, hrest]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands —
**THEOREM 1 for `recFireComparands`**: both comparand lists, substituted and
re-interned. -/
theorem recFireComparands_spec (s₀ : AState) (rl : IRecRule) (rl' : RecRule)
    (lps : List NIdx) (us : LsIdx) (cvjLps : List NIdx) (args : List EIdx)
    (rP : Nat) (ks : List ConLeche.Name) (vs : List Level)
    (cs : List ConLeche.Name) (xs : List Expr)
    (hok : CheckOK mode env fe s₀)
    (hrl : Frontend.denoteRule s₀.store rl = some rl')
    (hks : Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : denoteLs s₀.store.lss us = some vs)
    (hcs : Frontend.denoteNList s₀.store.ns cvjLps = some cs)
    (hxs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.recFireComparands rl lps us cvjLps args rP
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteLs s'.store.lss r.1 =
          some (ConLeche.recFireComparands rl' ks vs cs xs rP).1 ∧
        Frontend.denoteEList s'.store r.2 =
          some (ConLeche.recFireComparands rl' ks vs cs xs rP).2⌝⦄ := by
  obtain ⟨c, f, rr, _hc, hf, _hr, rfl⟩ : ∃ c f rr,
      denoteN s₀.store.ns rl.ctor = some c ∧
      Frontend.denoteFire s₀.store rl.fire = some f ∧
      denoteE s₀.store rl.rhs = some rr ∧
      rl' = ⟨c, rl.nfields, rl.ctorParams, f, rr, rl.k, rl.eta,
        rl.paramsBlind⟩ := by
    simp only [Frontend.denoteRule] at hrl
    split at hrl
    · rename_i c f rr hc hf hr; cases hrl; exact ⟨c, f, rr, hc, hf, hr, rfl⟩
    · simp at hrl
  unfold ConRon.Arena.recFireComparands
  -- the two readbacks every branch starts with
  have hread : ∀ {β : Type} (k : List ConLeche.Name → List Level → AM β)
      (Q : β → AState → Prop),
      (∀ s2, CheckOK mode env fe s2 → s2.store = s₀.store → s2.pins = s₀.pins →
        ⦃fun s => ⌜s = s2⌝⦄ k ks vs ⦃⇓? r s' => ⌜Q r s'⌝⦄) →
      ⦃fun s => ⌜s = s₀⌝⦄ (do
        let a ← readNamesM lps
        let b ← readLevelsM us
        k a b) ⦃⇓? r s' => ⌜Q r s'⌝⦄ := by
    intro β k Q hk
    refine triple_seq (ExprOps.readNamesM_specF s₀ lps hok.caches.readN) ?_
    rintro ks' s1 ⟨hst1, hm1, hp1, hc1, hks1, hN1⟩
    have hok1 := CheckOK.ofReadbackFrame hok (ReadbackFrame.ofReadN hst1 hm1 hp1 hc1 hN1)
    refine triple_seq (ExprOps.readLevelsM_specF s1 us hok1.caches.readLs) ?_
    rintro vs' s2 ⟨hst2, hm2, hp2, hc2, hvs2, hLs2⟩
    have hok2 := CheckOK.ofReadbackFrame hok1
      (ReadbackFrame.ofReadLs hst2 hm2 hp2 hc2 hLs2)
    rw [hks] at hks1
    obtain rfl := Option.some.inj hks1
    rw [hst1, hvs] at hvs2
    obtain rfl := Option.some.inj hvs2
    exact hk s2 hok2 (hst2.trans hst1) (hp2.trans hp1)
  cases hfire : rl.fire
  case nested lvls pins =>
    rw [hfire] at hf
    obtain ⟨Lv, Ps, hLv, hPs, rfl⟩ : ∃ Lv Ps,
        denoteLList s₀.store.ls lvls = some Lv ∧
        Frontend.denoteEList s₀.store pins = some Ps ∧ f = .nested Lv Ps := by
      simp only [Frontend.denoteFire] at hf
      split at hf
      · rename_i Lv Ps h1 h2; cases hf; exact ⟨Lv, Ps, h1, h2, rfl⟩
      · simp at hf
    dsimp only
    refine hread _ _ (fun s2 hok2 hst2 hp2 => ?_)
    have hx02 : Ext s₀.store s2.store := by rw [hst2]; exact Ext.refl _
    refine triple_seq (substLevelsAt_spec ks vs lvls s2 Lv hok2
      (by rw [hst2]; exact hLv)) ?_
    rintro ls s3 ⟨hok3, hx3, hp3, hls⟩
    refine triple_seq (internLsNode_spec s3 ls hok3.state.wf
      (lsViewOK_of_denote hls)) ?_
    rintro lsh s4 ⟨hwf4, hx4, _, _, _, _, hc4, hp4, _, hlsh⟩
    have hok4 : CheckOK mode env fe s4 := hok3.mono ⟨hwf4⟩ hx4 hc4 hp4
    have hx04 : Ext s₀.store s4.store := hx02.trans (hx3.trans hx4)
    refine triple_seq (instSpinePins_spec lps us args rP ks vs xs pins s4 Ps hok4
      (denoteNListE_ext hx04 _ _ hks) (denoteLs_ext hvs hx04)
      (denoteEList_ext hx04 _ _ hxs) (denoteEList_ext hx04 _ _ hPs)) ?_
    rintro ps s5 ⟨hok5, hx5, hp5, hps⟩
    have hlsh4 : denoteLs s4.store.lss lsh = some (Lv.map (Level.subst ks vs)) :=
      denoteLs_of_list_ext hx4 hls hlsh
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok5, hx04.trans hx5, hp5.trans (hp4.trans (hp3.trans hp2)), ?_, ?_⟩
    · rw [denoteLs_ext hlsh4 hx5]; simp [ConLeche.recFireComparands]
    · rw [hps]; simp [ConLeche.recFireComparands]
  all_goals
    rw [hfire] at hf
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    subst hf
    dsimp only
    refine hread _ _ (fun s2 hok2 hst2 hp2 => ?_)
    have hx02 : Ext s₀.store s2.store := by rw [hst2]; exact Ext.refl _
    refine triple_seq (substParamLevels_spec ks vs cvjLps s2 cs hok2
      (by rw [hst2]; exact hcs)) ?_
    rintro ls s3 ⟨hok3, hx3, hp3, hls⟩
    refine triple_seq (internLsNode_spec s3 ls hok3.state.wf
      (lsViewOK_of_denote hls)) ?_
    rintro lsh s4 ⟨hwf4, hx4, _, _, _, _, hc4, hp4, _, hlsh⟩
    have hok4 : CheckOK mode env fe s4 := hok3.mono ⟨hwf4⟩ hx4 hc4 hp4
    have hx04 : Ext s₀.store s4.store := hx02.trans (hx3.trans hx4)
    have hlsh4 := denoteLs_of_list_ext hx4 hls hlsh
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok4, hx04, hp4.trans (hp3.trans hp2), ?_, ?_⟩
    · rw [hlsh4]; simp [ConLeche.recFireComparands]
    · rw [ExprOps.denoteEList_take _ _ _ (denoteEList_ext hx04 _ _ hxs)]
      simp [ConLeche.recFireComparands]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:704-707 piResidual — a non-∀
telescope has no residual along a non-empty spine. -/
theorem piResidual_cons_none {e x : Expr} {xs : List Expr}
    (h : ∀ p q m, e ≠ .forallE p q m) : ConLeche.piResidual e (x :: xs) = none := by
  cases e with
  | forallE p q m => exact absurd rfl (h p q m)
  | _ => rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:704-707 piResidual — **THEOREM 1
for `piResidual`**: the telescope residual along an argument spine. -/
theorem piResidual_spec : ∀ (as : List EIdx) (s₀ : AState) (h : EIdx) (e : Expr)
    (xs : List Expr), CheckOK mode env fe s₀ → denoteE s₀.store h = some e →
    Frontend.denoteEList s₀.store as = some xs →
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.piResidual h as
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteEO s'.store r = some (ConLeche.piResidual e xs)⌝⦄ := by
  intro as
  induction as with
  | nil =>
    intro s₀ h e xs hok he hxs
    obtain rfl := denoteEList_nil_inv hxs
    mvcgen [ConRon.Arena.piResidual]
    bridge_peel; subst_vars
    refine ⟨hok, Ext.refl _, rfl, ?_⟩
    simp [denoteEO, he, ConLeche.piResidual]
  | cons a as ih =>
    intro s₀ h e xs hok he hxs
    have hwf := hok.state.wf
    obtain ⟨x, xs', hx, hxs', rfl⟩ := denoteEList_cons_inv hxs
    obtain ⟨v, hv⟩ := denoteE_view he
    unfold ConRon.Arena.piResidual
    refine view_bind_triple hv ?_
    cases v
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, _, hb⟩ := denote_forallE_inv hwf hv he
      dsimp only
      refine triple_seq (instantiate1Fast_specE coreWalkFuel s₀ b a 0 hok.state
        (by rw [hx]; rfl) (by rw [hb]; rfl)) ?_
      rintro b' s1 ⟨hst1, hx1, hc1, hp1, _, hrel⟩
      have hok1 : CheckOK mode env fe s1 := hok.mono hst1 hx1 hc1 hp1
      have hb' := hrel x hx eb hb
      refine triple_mono (ih s1 b' _ xs' hok1 hb' (denoteEList_ext hx1 _ _ hxs')) ?_
      rintro r s2 ⟨hok2, hx2, hp2, hr⟩
      exact ⟨hok2, hx1.trans hx2, hp2.trans hp1, hr⟩
    all_goals
      dsimp only
      have hnf := denote_not_forallE hwf hv he (by intro ty b m h; cases h)
      mvcgen
      bridge_peel; subst_vars
      refine ⟨hok, Ext.refl _, rfl, ?_⟩
      rw [piResidual_cons_none hnf]
      rfl

/-- con-leche: ConLeche/Kernel/Core.lean:255-265 iotaIndexOk — **THEOREM 1
for `iotaIndexOk`**: the canonical-index comparison of a firing redex. -/
theorem iotaIndexOk_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d mI rP cnP : Nat) (tyC : EIdx) (margs idx : List EIdx)
    (ty : Expr) (ms is : List Expr)
    (hok : CheckOK mode env fe s₀) (hty : denoteE s₀.store tyC = some ty)
    (hms : Frontend.denoteEList s₀.store margs = some ms)
    (his : Frontend.denoteEList s₀.store idx = some is)
    (hwty : Expr.WScoped d ty) (hwms : ∀ z ∈ ms, Expr.WScoped d z)
    (hwis : ∀ z ∈ is, Expr.WScoped d z) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.iotaIndexOk (coreKnot mode fe id fuel) fe d mI rP cnP tyC
        margs idx
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.iotaIndexOkFueled mode env F d mI rP cnP ty
          ms is) r⌝⦄ := by
  unfold ConRon.Arena.iotaIndexOk
  split
  next hm =>
    have hres : ConLeche.iotaIndexOkFueled mode env 0 d mI rP cnP ty ms is =
        .ok true := by
      simp only [ConLeche.iotaIndexOkFueled, ConLeche.iotaIndexOk, if_pos hm]; rfl
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, 0, hres⟩
  next hm =>
    refine triple_seq (piResidual_spec margs s₀ tyC ty ms hok hty hms) ?_
    rintro o s1 ⟨hok1, hx1, hp1, ho⟩
    cases o with
    | none =>
      have hn : ConLeche.piResidual ty ms = none := by
        simp only [denoteEO, Option.some.injEq] at ho; exact ho.symm
      have hres : ConLeche.iotaIndexOkFueled mode env 0 d mI rP cnP ty ms is =
          .ok false := by
        simp only [ConLeche.iotaIndexOkFueled, ConLeche.iotaIndexOk, if_neg hm, hn]
        rfl
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok1, hx1, hp1, 0, hres⟩
    | some res =>
      obtain ⟨e', hres, hpe⟩ : ∃ e', denoteE s1.store res = some e' ∧
          ConLeche.piResidual ty ms = some e' := by
        simp only [denoteEO, Option.map_eq_some_iff] at ho
        obtain ⟨e', h1, h2⟩ := ho
        exact ⟨e', h1, by rw [← h2]⟩
      have hwe' : Expr.WScoped d e' := ConLeche.piResidual_WScoped hpe hwty hwms
      dsimp only
      refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s1 res hok1.state
        (by rw [hres]; rfl)) ?_
      rintro args s2 ⟨hs2, hrelA⟩
      subst s2
      have hargs := ExprOps.denoteEList_drop cnP _ _ (hrelA e' hres)
      refine triple_mono (defEqList_spec hsim s1 d (args.drop cnP) idx _ is hok1
        hargs (denoteEList_ext hx1 _ _ his)
        (fun z hz => Expr.WScoped.getAppArgs hwe' z (List.mem_of_mem_drop hz))
        hwis) ?_
      rintro r s3 ⟨hok3, hx3, hp3, F, hF⟩
      refine ⟨hok3, hx1.trans hx3, hp3.trans hp1, F, ?_⟩
      have hF' : ConLeche.defEqList (ConLeche.pureFns mode env F) env d
          (e'.getAppArgs.drop cnP) is = .ok r := hF
      simp [ConLeche.iotaIndexOkFueled, ConLeche.iotaIndexOk, hm, hpe, hF']

/-! ## 4. The ι step -/

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — **THEOREM 1 for
`iotaRecAt`**: one ι step at a spine the caller already holds (task
#97-P6-9's hoist).  The held head `h` is not an application (it is a spine
head), so `getAppFn`/`getAppArgs` of `Expr.mkAppN h xs` are `h` and `xs`,
which is the equation the hoist owes.  The count `n` is the whole held
vector (`hn`): both callers pass `size`, and at a larger `n` the twin's
arity guard reads `n` where con-leche's reads the spine. -/
theorem iotaRecAt_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (hd : EIdx) (sargs : Array EIdx) (n : Nat)
    (h : Expr) (xs : List Expr)
    (hok : CheckOK mode env fe s₀) (hdh : denoteE s₀.store hd = some h)
    (hnapp : ∀ f a, h ≠ .app f a)
    (hn : n = sargs.size)
    (hxs : Frontend.denoteEList s₀.store sargs.toList = some xs)
    (hw : Expr.WScoped d (Expr.mkAppN h xs)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.iotaRecAt mode (coreKnot mode fe id fuel) fe d hd sargs n
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled mode env F d (Expr.mkAppN h xs))
          d s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — **THEOREM 1 for
`iotaRec`**: one ι step at a recursor application, with the stuck-major
machinery under it.  Moved here from `Walks/Owed.lean` (round 6); **the
preconditions `hμ` and `henv` are new** (module note). -/
theorem iotaRec_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.iotaRec mode (coreKnot mode fe id fuel) fe d e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled mode env F d x) d
          s'.store r⌝⦄ := by
  unfold ConRon.Arena.iotaRec
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ e hok.state
    (by rw [hden]; rfl)) ?_
  rintro hd s1 ⟨hs1, hrelF⟩
  subst s1
  refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ e hok.state
    (by rw [hden]; rfl)) ?_
  rintro args s2 ⟨hs2, hrelA⟩
  subst s2
  have hmk : Expr.mkAppN x.getAppFn x.getAppArgs = x := Expr.mkAppN_getApp x
  refine triple_mono (iotaRecAt_spec hμ henv hsim s₀ d hd args.toArray
    args.length x.getAppFn x.getAppArgs hok (hrelF x hden)
    (fun f a => ConLeche.Expr.getAppFn_not_app x f a) (by simp)
    (by simpa using hrelA x hden) (by rw [hmk]; exact hw)) ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  rw [hmk] at h4
  exact ⟨h1, h2, h3, h4⟩

section Census