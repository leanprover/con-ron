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
    refine tag_view_bind_triple hv ?_
      (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
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

/-! ## 4. The ι step

`iotaRecAt_spec` is staged over the twin's `do` block; past the parameter
comparison the legacy `do` elaborator inlines the certificate-family
continuation into each of the comparison's three branches, so that
continuation is one lemma (`iotaFam_spec`, stated at the same `do` text) and
the three branches `exact` it.  The pure side is `iotaTail`, a copy of
con-leche's clause past the major's preparation that `iotaRecFueled_pre` ties
to the original by `rfl`, and `iotaTail_fire` evaluates it at the five
verdicts. -/

/-! ### `iotaRec`'s pure side at its exits

Each exit is con-leche's `iotaRec` at a subject `E` whose spine head and
arguments are known (`hE1`, `hE2`), with the facts the twin's stages name. -/

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — the head is not a
constant. -/
theorem iotaRecFueled_nohead {F d : Nat} {E : Expr}
    (hE1 : ∀ c us, E.getAppFn ≠ .const c us) :
    ConLeche.iotaRecFueled mode env F d E = .ok none := by
  simp only [ConLeche.iotaRecFueled, ConLeche.iotaRec]
  first
    | rfl
    | (split
       · rename_i c us heq; exact absurd heq (hE1 c us)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — the head is not a
stored recursor. -/
theorem iotaRecFueled_norec {F d : Nat} {E : Expr} {c : ConLeche.Name}
    {us : List Level} (hE1 : E.getAppFn = .const c us)
    (hf : ∀ cv mI rP rules, env.find? c ≠ some (.recInfo cv mI rP rules)) :
    ConLeche.iotaRecFueled mode env F d E = .ok none := by
  simp only [ConLeche.iotaRecFueled, ConLeche.iotaRec, hE1]
  first
    | rfl
    | (split
       · rename_i cv mI rP rules heq; exact absurd heq (hf cv mI rP rules)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — the arity or level
guard fails. -/
theorem iotaRecFueled_guard {F d : Nat} {E : Expr} {c : ConLeche.Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hE1 : E.getAppFn = .const c us)
    (hf : env.find? c = some (.recInfo cv mI rP rules))
    (hg : ¬ (E.getAppArgs.length = mI + 1 ∧ us.length = cv.levelParams.length)) :
    ConLeche.iotaRecFueled mode env F d E = .ok none := by
  simp only [ConLeche.iotaRecFueled, ConLeche.iotaRec, hE1, hf]
  rw [if_neg hg]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — past the guard and
the major's preparation, as a function of the prepared major: every later exit
is a statement about this tail. -/
def iotaTail (mode : CheckMode) (env : Env) (F d : Nat) (us : List Level)
    (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule) (args : List Expr)
    (major : Expr) : CheckM (Option Expr) :=
  match major.getAppFn with
  | .const cj usj =>
    match env.find? cj with
    | some (.ctorInfo cvj _ _) =>
      match rules.find? (fun r' => r'.ctor == cj) with
      | some rl =>
        let margs := major.getAppArgs
        if margs.length = rl.ctorParams + rl.nfields then
          if rl.fire = .inert then
            throw (.notImplemented
              "iota reduction over a nested auxiliary recursor rule")
          else do
            if ← ConLeche.liftFueled "level comparison" (Level.isEquivList usj
                (ConLeche.recFireComparands rl cv.levelParams us
                  cvj.levelParams args rP).1) then
              if ← (if rl.compareParams then
                  ConLeche.defEqListFueled mode env F d
                    (margs.take rl.ctorParams)
                    (ConLeche.recFireComparands rl cv.levelParams us
                      cvj.levelParams args rP).2
                  else pure true) then
                if ← ConLeche.iotaCertsFueled mode env F d mode.betaGate
                    (cv.type.instantiateLevelParams cv.levelParams us)
                    (args.take mI ++ [major]) then
                  if ← ConLeche.iotaCertsFueled mode env F d mode.betaGate
                      (cvj.type.instantiateLevelParams cvj.levelParams usj)
                      margs then
                    if ← ConLeche.iotaIndexOkFueled mode env F d mI rP
                        rl.ctorParams
                        (cvj.type.instantiateLevelParams cvj.levelParams usj)
                        margs ((args.take mI).drop rP) then
                      pure (some (Expr.mkAppN
                        (rl.rhs.instantiateLevelParams cv.levelParams us)
                        (args.take rP ++ margs.drop rl.ctorParams)))
                    else pure none
                  else pure none
                else pure none
              else pure none
            else pure none
        else pure none
      | none => pure none
    | _ => pure none
  | _ => pure none

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — the prefix: head,
recursor, guard, the prepared major; the rest is `iotaTail`. -/
theorem iotaRecFueled_pre {F d : Nat} {E : Expr} {c : ConLeche.Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {major : Expr}
    (hE1 : E.getAppFn = .const c us)
    (hf : env.find? c = some (.recInfo cv mI rP rules))
    (hg : E.getAppArgs.length = mI + 1 ∧ us.length = cv.levelParams.length)
    (hpm : ConLeche.prepareMajorFueled mode env F d c rules
      (E.getAppArgs.getD mI (.bvar 0)) = .ok major) :
    ConLeche.iotaRecFueled mode env F d E =
      iotaTail mode env F d us cv mI rP rules E.getAppArgs major := by
  have hpm' : ConLeche.prepareMajor mode (ConLeche.pureFns mode env F) env d c
      rules (E.getAppArgs.getD mI (.bvar 0)) = .ok major := hpm
  simp only [ConLeche.iotaRecFueled, ConLeche.iotaRec, hE1, hf]
  rw [if_pos hg]
  simp only [hpm', bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — the prepared
major's head is not a constant. -/
theorem iotaTail_nohead {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {args : List Expr} {major : Expr}
    (hm : ∀ cj usj, major.getAppFn ≠ .const cj usj) :
    iotaTail mode env F d us cv mI rP rules args major = .ok none := by
  simp only [iotaTail]
  first
    | rfl
    | (split
       · rename_i c us heq; exact absurd heq (hm c us)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — the head is not a
stored constructor. -/
theorem iotaTail_noctor {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {args : List Expr} {major : Expr}
    {cj : ConLeche.Name} {usj : List Level}
    (hm : major.getAppFn = .const cj usj)
    (hf : ∀ cvj a b, env.find? cj ≠ some (.ctorInfo cvj a b)) :
    iotaTail mode env F d us cv mI rP rules args major = .ok none := by
  simp only [iotaTail, hm]
  first
    | rfl
    | (split
       · rename_i cvj a b heq; exact absurd heq (hf cvj a b)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — no rule matches the
constructor. -/
theorem iotaTail_norule {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {args : List Expr} {major : Expr}
    {cj : ConLeche.Name} {usj : List Level} {cvj : ConstantVal} {a b : Nat}
    (hm : major.getAppFn = .const cj usj)
    (hf : env.find? cj = some (.ctorInfo cvj a b))
    (hr : rules.find? (fun r' => r'.ctor == cj) = none) :
    iotaTail mode env F d us cv mI rP rules args major = .ok none := by
  simp only [iotaTail, hm, hf, hr]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — the constructor is
not fully applied. -/
theorem iotaTail_len {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {args : List Expr} {major : Expr}
    {cj : ConLeche.Name} {usj : List Level} {cvj : ConstantVal} {a b : Nat}
    {rl : RecRule}
    (hm : major.getAppFn = .const cj usj)
    (hf : env.find? cj = some (.ctorInfo cvj a b))
    (hr : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hl : ¬ major.getAppArgs.length = rl.ctorParams + rl.nfields) :
    iotaTail mode env F d us cv mI rP rules args major = .ok none := by
  simp only [iotaTail, hm, hf, hr]
  rw [if_neg hl]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — **the firing
block**, as a function of the five verdicts: the level comparison, the
parameter comparison, the two telescope runs and the index comparison, each
needed only once the ones before it passed. -/
theorem iotaTail_fire {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {args : List Expr} {major : Expr}
    {cj : ConLeche.Name} {usj : List Level} {cvj : ConstantVal} {a b : Nat}
    {rl : RecRule} {b1 b2 b3 b4 b5 : Bool}
    (hm : major.getAppFn = .const cj usj)
    (hf : env.find? cj = some (.ctorInfo cvj a b))
    (hr : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hl : major.getAppArgs.length = rl.ctorParams + rl.nfields)
    (hin : rl.fire ≠ .inert)
    (h1 : Level.isEquivList usj (ConLeche.recFireComparands rl cv.levelParams us
      cvj.levelParams args rP).1 = some b1)
    (h2 : b1 = true → (if rl.compareParams then
        ConLeche.defEqListFueled mode env F d
          (major.getAppArgs.take rl.ctorParams)
          (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams args
            rP).2
        else pure true : CheckM Bool) = .ok b2)
    (h3 : b1 = true → b2 = true → ConLeche.iotaCertsFueled mode env F d
      mode.betaGate (cv.type.instantiateLevelParams cv.levelParams us)
      (args.take mI ++ [major]) = .ok b3)
    (h4 : b1 = true → b2 = true → b3 = true → ConLeche.iotaCertsFueled mode env
      F d mode.betaGate (cvj.type.instantiateLevelParams cvj.levelParams usj)
      major.getAppArgs = .ok b4)
    (h5 : b1 = true → b2 = true → b3 = true → b4 = true →
      ConLeche.iotaIndexOkFueled mode env F d mI rP rl.ctorParams
        (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs ((args.take mI).drop rP) = .ok b5) :
    iotaTail mode env F d us cv mI rP rules args major =
      .ok (if b1 && b2 && b3 && b4 && b5 then
        some (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
          (args.take rP ++ major.getAppArgs.drop rl.ctorParams))
      else none) := by
  simp only [iotaTail, hm, hf, hr]
  rw [if_pos hl, if_neg hin]
  simp only [ConLeche.liftFueled, h1, bind, Except.bind, pure, Except.pure]
  simp only [pure, Except.pure] at h2
  cases b1
  · rfl
  · simp only [h2 rfl, if_true]
    cases b2
    · rfl
    · simp only [h3 rfl rfl, if_true]
      cases b3
      · rfl
      · simp only [h4 rfl rfl rfl, if_true]
        cases b4
        · rfl
        · simp only [h5 rfl rfl rfl rfl, if_true]
          cases b5 <;> rfl

/-! ### The twin side's index and rule facts -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the index's HIT half at a
recursor. -/
theorem env_rec_of_index {s : AState} (hok : CheckOK mode env fe s)
    {c : NIdx} {cn : ConLeche.Name} {icv : IConstantVal} {mI rP : Nat}
    {rules : List IRecRule} (hn : denoteN s.store.ns c = some cn)
    (hfd : fe.find? c = some (.recInfo icv mI rP rules)) :
    ∃ dcv drules, Frontend.denoteCV s.store icv = some dcv ∧
      Frontend.denoteRules s.store rules = some drules ∧
      env.find? cn = some (.recInfo dcv mI rP drules) := by
  obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c _ hfd
  obtain rfl := Option.some.inj (hn'.symm.trans hn)
  simp only [Frontend.denoteCI] at hci
  split at hci
  · rename_i dcv dr hdcv hdr
    cases hci
    exact ⟨dcv, dr, hdcv, hdr, hfind⟩
  · simp at hci

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the MISS half at a
recursor. -/
theorem env_not_rec_of_index {s : AState} (hok : CheckOK mode env fe s)
    {c : NIdx} {cn : ConLeche.Name} (hn : denoteN s.store.ns c = some cn)
    (hnd : ∀ v mI rP rs, fe.find? c ≠ some (.recInfo v mI rP rs)) :
    ∀ cv mI rP rs, env.find? cn ≠ some (.recInfo cv mI rP rs) := by
  intro cv mI rP rs hcon
  cases hf : fe.find? c with
  | none => rw [IFEnvOK.miss hok.state hok.ienv hn hf] at hcon; simp at hcon
  | some ci =>
    obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c ci hf
    obtain rfl := Option.some.inj (hn'.symm.trans hn)
    rw [hfind] at hcon
    obtain rfl := Option.some.inj hcon
    cases ci with
    | recInfo v mI' rP' rs' => exact hnd v mI' rP' rs' hf
    | _ =>
      simp only [Frontend.denoteCI] at hci
      first
        | (simp at hci)
        | (split at hci <;> simp at hci)

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — `findRule` IS the
rule lookup `rules.find? (fun r' => r'.ctor == cj)`, across the denotation. -/
theorem findRule_denote {st : EStore} (hwf : StoreWF st) {cj : NIdx}
    {cjn : ConLeche.Name} (hcj : denoteN st.ns cj = some cjn) :
    ∀ {rules : List IRecRule} {rules' : List RecRule},
      Frontend.denoteRules st rules = some rules' →
      (∀ rl, ConRon.Arena.findRule rules cj = some rl →
        ∃ rl', Frontend.denoteRule st rl = some rl' ∧
          rules'.find? (fun r => r.ctor == cjn) = some rl') ∧
      (ConRon.Arena.findRule rules cj = none →
        rules'.find? (fun r => r.ctor == cjn) = none)
  | [], rules', h => by
    simp only [Frontend.denoteRules, Option.some.injEq] at h
    subst h
    exact ⟨fun rl h => by simp [ConRon.Arena.findRule] at h, fun _ => rfl⟩
  | r :: rs, rules', h => by
    simp only [Frontend.denoteRules] at h
    split at h
    · rename_i x xs hx hxs
      cases h
      obtain ⟨hr1, hr2⟩ := findRule_denote hwf hcj hxs
      obtain ⟨_, _, _, _, hc, _, _⟩ := rule_denote hx
      obtain ⟨rk, hrk⟩ := hwf
      have hbeq : (r.ctor == cj) = (x.ctor == cjn) := beq_of_denoteN hrk.nsWF hc hcj
      by_cases hb : (r.ctor == cj) = true
      · have hb' : (x.ctor == cjn) = true := hbeq ▸ hb
        refine ⟨fun rl hrl => ?_, fun hn => ?_⟩
        · simp only [ConRon.Arena.findRule, hb, if_true, Option.some.injEq] at hrl
          subst hrl
          exact ⟨x, hx, by simp [List.find?, hb']⟩
        · simp [ConRon.Arena.findRule, hb] at hn
      · have hb' : (x.ctor == cjn) = false := by rw [← hbeq]; simpa using hb
        have hbf : (r.ctor == cj) = false := by simpa using hb
        refine ⟨fun rl hrl => ?_, fun hn => ?_⟩
        · simp only [ConRon.Arena.findRule, hbf, Bool.false_eq_true, if_false] at hrl
          obtain ⟨rl', h1, h2⟩ := hr1 rl hrl
          exact ⟨rl', h1, by simp [List.find?, hb', h2]⟩
        · simp only [ConRon.Arena.findRule, hbf, Bool.false_eq_true, if_false] at hn
          simp [List.find?, hb', hr2 hn]
    · simp at h

/-- con-leche: none — an in-range `getD` of a denoting list denotes the
`getD` of the denotation, whatever the two defaults. -/
theorem denoteEList_getD_lt {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr}, Frontend.denoteEList st hs = some xs →
      ∀ {i : Nat}, i < hs.length → ∀ (a : EIdx) (b : Expr),
        denoteE st (hs.getD i a) = some (xs.getD i b)
  | [], _, _, _, hi, _, _ => by simp at hi
  | h :: hs, xs, hd, i, hi, a, b => by
    obtain ⟨x, xs', hx, hxs, rfl⟩ := denoteEList_cons_inv hd
    cases i with
    | zero => simpa using hx
    | succ i =>
      simp only [List.getD_cons_succ]
      exact denoteEList_getD_lt hxs (by simp at hi; omega) a b

/-- con-leche: none — the parameter comparison's pure side is fuel-monotone
(`defEqListFueled_mono` under the `compareParams` gate). -/
theorem ifDefEq_mono {c : Bool} {F G d : Nat} {as bs : List Expr} {r : Bool}
    (hle : F ≤ G)
    (h : (if c then ConLeche.defEqListFueled mode env F d as bs
      else pure true : CheckM Bool) = .ok r) :
    (if c then ConLeche.defEqListFueled mode env G d as bs
      else pure true : CheckM Bool) = .ok r := by
  cases c
  · exact h
  · exact defEqListFueled_mono hle h

/-- con-leche: none — `SimOOp` at a `none` answer. -/
theorem simOOp_none {P : Nat → CheckM (Option Expr)} {d F : Nat} {st : EStore}
    (h : P F = .ok none) : SimOOp P d st none :=
  ⟨none, rfl, fun _ hx => absurd hx (by simp), F, h⟩

/-- con-leche: ConLeche/Kernel/Core.lean:880-905 iotaRec — **the firing
rule's certificate family and the reduct**, past the level and parameter
comparisons: the two licensed telescope runs, the index comparison (one
family, gated on `mode.certs`, `Cached/CoreC.lean:814`), then the rule's
right-hand side applied to the parameters and the fields.  Stated at the
continuation the twin's `do` block inlines at every branch of the parameter
comparison, so the three branches share this proof. -/
theorem iotaFam_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (c : NIdx) (icv icvj : IConstantVal)
    (us usj : LsIdx) (rl : IRecRule) (args margs : List EIdx) (major : EIdx)
    (mI rP : Nat) (cn cjn : ConLeche.Name) (ls lsj : List Level)
    (dcv dcvj : ConstantVal) (cnP cnF : Nat) (drules : List RecRule)
    (rl' : RecRule) (xs : List Expr) (vmaj : Expr) (Fp Fq : Nat)
    (hok : CheckOK mode env fe s₁)
    (hcn : denoteN s₁.store.ns c = some cn)
    (hls : denoteLs s₁.store.lss us = some ls)
    (hlsj : denoteLs s₁.store.lss usj = some lsj)
    (hdcv : Frontend.denoteCV s₁.store icv = some dcv)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hmaj : denoteE s₁.store major = some vmaj)
    (hmargs : Frontend.denoteEList s₁.store margs = some vmaj.getAppArgs)
    (hargs : Frontend.denoteEList s₁.store args = some xs)
    (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hfind : env.find? cn = some (.recInfo dcv mI rP drules))
    (hfindj : env.find? cjn = some (.ctorInfo dcvj cnP cnF))
    (hfind' : drules.find? (fun r => r.ctor == cjn) = some rl')
    (hgfm : vmaj.getAppFn = .const cjn lsj)
    (hlP : vmaj.getAppArgs.length = rl'.ctorParams + rl'.nfields)
    (hin' : rl'.fire ≠ .inert)
    (hwargs : ∀ z ∈ xs, Expr.WScoped d z) (hwvmaj : Expr.WScoped d vmaj)
    (hw : Expr.WScoped d (Expr.mkAppN (.const cn ls) xs))
    (hT : ∀ G, Fp ≤ G → ConLeche.iotaRecFueled mode env G d
      (Expr.mkAppN (.const cn ls) xs) =
      iotaTail mode env G d ls dcv mI rP drules xs vmaj)
    (h1 : Level.isEquivList lsj (ConLeche.recFireComparands rl' dcv.levelParams
      ls dcvj.levelParams xs rP).1 = some true)
    (hq : (if rl'.compareParams then
        ConLeche.defEqListFueled mode env Fq d
          (vmaj.getAppArgs.take rl'.ctorParams)
          (ConLeche.recFireComparands rl' dcv.levelParams ls dcvj.levelParams xs
            rP).2
      else pure true : CheckM Bool) = .ok true) :
    ⦃fun s => ⌜s = s₁⌝⦄ (do
      let fam ←
        if mode.certs then do
          let tyR ← constTyAt icv us
          if ← ConRon.Arena.iotaCerts (coreKnot mode fe id fuel) fe d
              mode.betaGate tyR (args.take mI ++ [major]) then do
            let tyC ← constTyAt icvj usj
            if ← ConRon.Arena.iotaCerts (coreKnot mode fe id fuel) fe d
                mode.betaGate tyC margs then
              ConRon.Arena.iotaIndexOk (coreKnot mode fe id fuel) fe d mI rP
                rl.ctorParams tyC margs ((args.take mI).drop rP)
            else pure false
          else pure false
        else pure true
      if fam then do
        let rhs ← ruleRhsAt c rl.ctor icv.levelParams rl.rhs us
        let x ← mkAppN rhs (args.take rP ++ margs.drop rl.ctorParams)
        pure (some x)
      else pure none : AM (Option EIdx))
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
          (Expr.mkAppN (.const cn ls) xs)) d s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨_hcp, _hinert, hctp, _hnf, hrlc, hrlrhs, _⟩ := rule_denote hrl'
  obtain ⟨_, hlps, _⟩ := denoteCV_inv hdcv
  have hname : dcv.name = cn := env_find_name hfind
  have hnamej : dcvj.name = cjn := env_find_name hfindj
  have hctor : rl'.ctor = cjn := by
    have := List.find?_some hfind'
    simpa using this
  have hwtyR : Expr.WScoped d (dcv.type.instantiateLevelParams dcv.levelParams ls) :=
    Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfind ls)
  have hwtyC : Expr.WScoped d
      (dcvj.type.instantiateLevelParams dcvj.levelParams lsj) :=
    Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfindj lsj)
  have hwA : ∀ z ∈ xs.take mI ++ [vmaj], Expr.WScoped d z := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hwargs z (List.mem_of_mem_take hz)
    · rw [List.mem_singleton.mp hz]; exact hwvmaj
  have hwM : ∀ z ∈ vmaj.getAppArgs, Expr.WScoped d z := Expr.WScoped.getAppArgs hwvmaj
  rw [if_pos (ConLeche.certs_of_verifiedChecks hμ)]
  -- stage: the recursor's instantiated type, and its telescope run
  refine triple_seq (constTyAt_spec s₁ icv us cn ls (.recInfo dcv mI rP drules) hok
    (by rw [denoteCV_name hdcv, hname]) hls hfind hdcv) ?_
  rintro tyR s2 ⟨hok2, hx2, hp2, htyR⟩
  have hA : Frontend.denoteEList s2.store (args.take mI ++ [major]) =
      some (xs.take mI ++ [vmaj]) :=
    denoteEList_appendI (ExprOps.denoteEList_take mI _ _ (denoteEList_ext hx2 _ _ hargs))
      (by simp [Frontend.denoteEList, denote_ext hmaj hx2])
  refine triple_seq (iotaCerts_spec hsim d mode.betaGate tyR _ s2 hok2
    ⟨_, _, htyR, hwtyR, hA, hwA⟩) ?_
  rintro c1 s3 ⟨hok3, hx3, hp3, hc1⟩
  obtain ⟨F1, hF1⟩ := hc1 _ _ htyR hA
  have hx13 := hx2.trans hx3
  have hp13 : s3.pins = s₁.pins := hp3.trans hp2
  by_cases hc1t : c1 = true
  · rw [if_pos hc1t]
    subst hc1t
    refine triple_seq (constTyAt_spec s3 icvj usj cjn lsj (.ctorInfo dcvj cnP cnF) hok3
      (by rw [denoteCV_name (denoteCV_ext hdcvj hx13), hnamej])
      (denoteLs_ext hlsj hx13) hfindj (denoteCV_ext hdcvj hx13)) ?_
    rintro tyC s4 ⟨hok4, hx4, hp4, htyC⟩
    have hM4 := denoteEList_ext (hx13.trans hx4) _ _ hmargs
    refine triple_seq (iotaCerts_spec hsim d mode.betaGate tyC _ s4 hok4
      ⟨_, _, htyC, hwtyC, hM4, hwM⟩) ?_
    rintro c2 s5 ⟨hok5, hx5, hp5, hc2⟩
    obtain ⟨F2, hF2⟩ := hc2 _ _ htyC hM4
    have hx15 := hx13.trans (hx4.trans hx5)
    have hp15 : s5.pins = s₁.pins := hp5.trans (hp4.trans hp13)
    by_cases hc2t : c2 = true
    · rw [if_pos hc2t]
      subst hc2t
      have hI := ExprOps.denoteEList_drop rP _ _
        (ExprOps.denoteEList_take mI _ _ (denoteEList_ext hx15 _ _ hargs))
      refine triple_seq (iotaIndexOk_spec hsim s5 d mI rP rl.ctorParams tyC margs
        ((args.take mI).drop rP) _ _ _ hok5 (denote_ext htyC hx5)
        (denoteEList_ext hx5 _ _ hM4) hI hwtyC hwM
        (fun z hz => hwargs z (List.mem_of_mem_take (List.mem_of_mem_drop hz)))) ?_
      rintro c3 s6 ⟨hok6, hx6, hp6, F3, hF3⟩
      have hx16 := hx15.trans hx6
      have hp16 : s6.pins = s₁.pins := hp6.trans hp15
      have hval : ∀ b5, ConLeche.iotaIndexOkFueled mode env F3 d mI rP rl.ctorParams
          (dcvj.type.instantiateLevelParams dcvj.levelParams lsj) vmaj.getAppArgs
          ((xs.take mI).drop rP) = .ok b5 →
          ConLeche.iotaRecFueled mode env (max Fp (max Fq (max F1 (max F2 F3)))) d
            (Expr.mkAppN (.const cn ls) xs) = .ok (if b5 then
              some (Expr.mkAppN (rl'.rhs.instantiateLevelParams dcv.levelParams ls)
                (xs.take rP ++ vmaj.getAppArgs.drop rl'.ctorParams)) else none) := by
        intro b5 hb5
        rw [hT _ (by omega), iotaTail_fire (b2 := true) (b3 := true) (b4 := true)
          (b5 := b5) hgfm hfindj hfind' hlP hin' h1
          (fun _ => ifDefEq_mono (by omega) hq)
          (fun _ _ => iotaCertsFueled_mono (by omega) hF1)
          (fun _ _ _ => iotaCertsFueled_mono (by omega) hF2)
          (fun _ _ _ _ => by rw [hctp]; exact iotaIndexOkFueled_mono (by omega) hb5)]
        cases b5 <;> rfl
      dsimp only
      by_cases hc3t : c3 = true
      · rw [if_pos hc3t]
        subst hc3t
        have hv := hval true hF3
        refine triple_seq (ruleRhsAt_spec s6 c rl.ctor icv.levelParams rl.rhs us cn
          cjn ls dcv mI rP drules rl' hok6 (denoteN_ext hcn hx16)
          (by rw [← hctor]; exact denoteN_ext hrlc hx16) (denoteLs_ext hls hx16)
          (denoteNListE_ext hx16 _ _ hlps)
          (denote_ext hrlrhs hx16) hfind hfind') ?_
        rintro rhs s7 ⟨hok7, hx7, hp7, hrhs⟩
        have hB : Frontend.denoteEList s7.store (args.take rP ++ margs.drop rl.ctorParams) =
            some (xs.take rP ++ vmaj.getAppArgs.drop rl'.ctorParams) := by
          rw [hctp]
          exact denoteEList_appendI
            (ExprOps.denoteEList_take rP _ _ (denoteEList_ext (hx16.trans hx7) _ _ hargs))
            (ExprOps.denoteEList_drop _ _ _ (denoteEList_ext (hx16.trans hx7) _ _ hmargs))
        refine triple_seq (ExprOps.mkAppN_spec _ s7 rhs hok7.state (by rw [hrhs]; rfl)
          (by rw [hB]; rfl)) ?_
        rintro x s8 ⟨hst8, hx8, _, _, hc8, hp8, hrel⟩
        have hok8 : CheckOK mode env fe s8 := hok7.mono hst8 hx8 hc8 hp8
        have hxd := hrel _ _ hrhs hB
        have hvw := ConLeche.iotaRec_WScoped henv hv hw
        have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
            (Expr.mkAppN (.const cn ls) xs)) d s8.store (some x) :=
          ⟨_, by simp [denoteEO, hxd], fun y hy => by
            cases hy; exact hvw, _, hv⟩
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok8, hx16.trans (hx7.trans hx8), hp8.trans (hp7.trans hp16), hfin⟩
      · rw [if_neg hc3t]
        have hc3f : c3 = false := by simpa using hc3t
        subst hc3f
        have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
            (Expr.mkAppN (.const cn ls) xs)) d s6.store none :=
          simOOp_none (hval false hF3)
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok6, hx16, hp16, hfin⟩
    · rw [if_neg hc2t]
      have hc2f : c2 = false := by simpa using hc2t
      subst hc2f
      have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
          (Expr.mkAppN (.const cn ls) xs)) d s5.store none := by
        refine simOOp_none (F := max Fp (max Fq (max F1 F2))) ?_
        rw [hT _ (by omega), iotaTail_fire (b2 := true) (b3 := true) (b4 := false)
          (b5 := false) hgfm hfindj hfind' hlP hin' h1
          (fun _ => ifDefEq_mono (by omega) hq)
          (fun _ _ => iotaCertsFueled_mono (by omega) hF1)
          (fun _ _ _ => iotaCertsFueled_mono (by omega) hF2)
          (fun _ _ _ h => by cases h)]
        rfl
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok5, hx15, hp15, hfin⟩
  · rw [if_neg hc1t]
    have hc1f : c1 = false := by simpa using hc1t
    subst hc1f
    have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
        (Expr.mkAppN (.const cn ls) xs)) d s3.store none := by
      refine simOOp_none (F := max Fp (max Fq F1)) ?_
      rw [hT _ (by omega), iotaTail_fire (b2 := true) (b3 := false) (b4 := false)
        (b5 := false) hgfm hfindj hfind' hlP hin' h1
        (fun _ => ifDefEq_mono (by omega) hq)
        (fun _ _ => iotaCertsFueled_mono (by omega) hF1)
        (fun _ _ h => by cases h) (fun _ _ h => by cases h)]
      rfl
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok3, hx13, hp13, hfin⟩

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
  have hwf := hok.state.wf
  subst hn
  have hxl : xs.length = sargs.size := by rw [denoteEList_len hxs]; simp
  unfold ConRon.Arena.iotaRecAt
  by_cases htag : (hd.tag == ETag.const) = true
  · rw [if_pos htag]
    refine triple_seq (viewConst_spec s₀ hd) ?_
    rintro oc s1 ⟨hs1, hoc⟩
    subst s1
    cases oc with
    | none => exact triple_failDanglingE
    | some cu =>
      obtain ⟨c, us⟩ := cu
      have hv := view_of_viewConst_tag htag hoc.symm
      obtain ⟨cn, ls, rfl, hcn, hls⟩ := denote_const_inv hwf hv hdh
      have hE1 : (Expr.mkAppN (.const cn ls) xs).getAppFn = .const cn ls := by
        rw [Expr.getAppFn_mkAppN]; rfl
      have hE2 : (Expr.mkAppN (.const cn ls) xs).getAppArgs = xs := by
        rw [Expr.getAppArgs_mkAppN]; rfl
      have hwargs : ∀ z ∈ xs, Expr.WScoped d z := fun z hz =>
        Expr.WScoped.getAppArgs hw z (by rw [hE2]; exact hz)
      dsimp only
      split
      next icv mI rP rules hfc =>
        obtain ⟨dcv, drules, hdcv, hdr, hfind⟩ := env_rec_of_index hok hcn hfc
        obtain ⟨_, hlps, _⟩ := denoteCV_inv hdcv
        have hlenlps := denoteNList_len hlps
        by_cases hne : sargs.size ≠ mI + 1
        · rw [if_pos hne]
          have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
              (Expr.mkAppN (.const cn ls) xs)) d s₀.store none :=
            simOOp_none (F := 0) (iotaRecFueled_guard hE1 hfind (by
              rw [hE2]; intro hg; exact hne (by rw [← hxl, hg.1])))
          mvcgen
          bridge_peel; subst_vars
          exact ⟨hok, Ext.refl _, rfl, hfin⟩
        · rw [if_neg hne]
          have hmI : sargs.size = mI + 1 := by simpa using hne
          have hargs : Frontend.denoteEList s₀.store
              (takeEidx sargs sargs.size).toList = some xs := by
            rw [ExprOps.takeEidx_toList, List.take_of_length_le (by simp)]
            exact hxs
          have hal : (takeEidx sargs sargs.size).toList.length = mI + 1 := by
            rw [← denoteEList_len hargs, hxl, hmI]
          refine triple_seq (viewLsLen_spec s₀ us) ?_
          rintro ol s2 ⟨hs2, hol⟩
          subst s2
          rw [viewLen_of_denoteLs hls] at hol
          subst hol
          dsimp only
          by_cases hg : (takeEidx sargs sargs.size).toList.length = mI + 1 ∧
              ls.length = icv.levelParams.length
          · rw [if_pos hg]
            have hgP : xs.length = mI + 1 ∧ ls.length = dcv.levelParams.length :=
              ⟨by rw [hxl, hmI], by rw [hg.2, hlenlps]⟩
            refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
              s₀ (.bvar 0) hok viewOK_bvar) ?_
            rintro b0 s3 ⟨hok3, hx3, hp3, _⟩
            have hargs3 := denoteEList_ext hx3 _ _ hargs
            have hmaj := denoteEList_getD_lt hargs3 (i := mI) (by rw [hal]; omega) b0
              (.bvar 0)
            have hmI' : mI < xs.length := by omega
            have hwmaj : Expr.WScoped d (xs.getD mI (.bvar 0)) := by
              simp only [List.getD, List.getElem?_eq_getElem hmI', Option.getD_some]
              exact hwargs _ (List.getElem_mem hmI')
            refine triple_seq (prepareMajor_spec hμ henv hsim s3 d c rules _ cn drules _
              hok3 (denoteRules_ext hx3 _ _ hdr) hmaj hwmaj) ?_
            rintro major s4 ⟨hok4, hx4, hp4, vmaj, hvmaj, hwvmaj, Fp, hFp⟩
            have hx04 := hx3.trans hx4
            have hp04 : s4.pins = s₀.pins := hp4.trans hp3
            have hwf4 := hok4.state.wf
            have hT : ∀ G, Fp ≤ G → ConLeche.iotaRecFueled mode env G d
                (Expr.mkAppN (.const cn ls) xs) =
                iotaTail mode env G d ls dcv mI rP drules xs vmaj := by
              intro G hG
              rw [iotaRecFueled_pre hE1 hfind (by rw [hE2]; exact hgP)
                (by rw [hE2]; exact prepareMajorFueled_mono hG hFp), hE2]
            refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s4 major hok4.state
              (by rw [hvmaj]; rfl)) ?_
            rintro mh s5 ⟨hs5, hrelF⟩
            subst s5
            have hmh := hrelF vmaj hvmaj
            obtain ⟨vh, hvh⟩ := denoteE_view hmh
            refine tag_view_bind_triple hvh ?_
              (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
            cases vh
            case const cj usj =>
              obtain ⟨cjn, lsj, hgfm, hcjn, hlsj⟩ := denote_const_inv hwf4 hvh hmh
              dsimp only
              split
              next icvj cnP cnF hfj =>
                obtain ⟨dcvj, hdcvj, hfindj⟩ := env_ctor_of_index hok4 hcjn hfj
                obtain ⟨_, hlpsj, _⟩ := denoteCV_inv hdcvj
                have hdr4 := denoteRules_ext hx04 _ _ hdr
                obtain ⟨hfr1, hfr2⟩ := findRule_denote hwf4 hcjn hdr4
                split
                next rl hrl =>
                  obtain ⟨rl', hrl', hfind'⟩ := hfr1 rl hrl
                  obtain ⟨hcp, hinert, hctp, hnf, hrlc, hrlrhs, hnest⟩ := rule_denote hrl'
                  refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s4 major
                    hok4.state (by rw [hvmaj]; rfl)) ?_
                  rintro margs s6 ⟨hs6, hrelA⟩
                  subst s6
                  have hmargs := hrelA vmaj hvmaj
                  have hmlen := denoteEList_len hmargs
                  by_cases hl : margs.length = rl.ctorParams + rl.nfields
                  · rw [if_pos hl]
                    have hlP : vmaj.getAppArgs.length = rl'.ctorParams + rl'.nfields := by
                      rw [hmlen, hl, hctp, hnf]
                    by_cases hin : rl.fire = .inert
                    · rw [if_pos hin]; exact triple_fail
                    · rw [if_neg hin]
                      have hin' : rl'.fire ≠ .inert := fun h => hin (hinert.mpr h)
                      have hwmargs : ∀ z ∈ vmaj.getAppArgs, Expr.WScoped d z :=
                        Expr.WScoped.getAppArgs hwvmaj
                      have hpinsW : ∀ lvls pins, rl'.fire = .nested lvls pins →
                          ∀ pin ∈ pins, pin.hasFvar = false := by
                        intro lvls pins hf' pin hpin
                        obtain ⟨-, -, -, -, -, hrules, -⟩ :=
                          henv _ (ConLeche.find?_mem hfind)
                        obtain ⟨-, -, -, -, g5⟩ := hrules dcv mI rP drules rfl rl'
                          (List.mem_of_find?_eq_some hfind')
                        exact ((g5 lvls pins hf').2.2.1 pin hpin).1
                      have hcmpW := ConLeche.recFireComparands_snd_WScoped rl'
                        dcv.levelParams ls dcvj.levelParams xs rP hwargs hpinsW
                      refine triple_seq (recFireComparands_spec s4 rl rl' icv.levelParams us
                        icvj.levelParams (takeEidx sargs sargs.size).toList rP
                        dcv.levelParams ls dcvj.levelParams xs hok4 hrl'
                        (denoteNListE_ext hx04 _ _ hlps) (denoteLs_ext hls hx04) hlpsj
                        (denoteEList_ext hx04 _ _ hargs)) ?_
                      rintro cmp s7 ⟨hok7, hx7, hp7, hcm1, hcm2⟩
                      refine triple_seq (lvlsEq?_spec s7 usj cmp.1 hok7) ?_
                      rintro rq s8 ⟨hok8, hst8, hp8, lu, lv, hlu, hlv, hrq⟩
                      rw [denoteLs_ext hlsj hx7] at hlu
                      obtain rfl := Option.some.inj hlu
                      rw [hcm1] at hlv
                      obtain rfl := Option.some.inj hlv
                      refine triple_seq (liftFueled_spec s8 _ rq) ?_
                      rintro b1 s9 ⟨hs9, hb1⟩
                      subst s9
                      have h1 : Level.isEquivList lsj (ConLeche.recFireComparands rl'
                          dcv.levelParams ls dcvj.levelParams xs rP).1 = some b1 := by
                        rw [← hrq, hb1]
                      have hx48 : Ext s4.store s8.store := by rw [hst8]; exact hx7
                      have hp48 : s8.pins = s4.pins := hp8.trans hp7
                      by_cases hb1t : b1 = true
                      · rw [if_pos hb1t]
                        subst hb1t
                        have hcert : mode.certs = true :=
                          ConLeche.certs_of_verifiedChecks hμ
                        have hst87 : s8.store = s7.store := hst8
                        have hmt := ExprOps.denoteEList_take rl.ctorParams _ _
                          (denoteEList_ext hx48 _ _ hmargs)
                        have hcm2' : Frontend.denoteEList s8.store cmp.2 = some
                            (ConLeche.recFireComparands rl' dcv.levelParams ls
                              dcvj.levelParams xs rP).2 := by rw [hst87]; exact hcm2
                        -- stage: the parameter comparison (the twin's `do` inlines the rest at
                        -- each of its three branches; `iotaFam_spec` is that rest)
                        by_cases hcpt : rl.compareParams = true
                        · rw [if_pos hcpt]
                          have hcpt' : rl'.compareParams = true := hcp ▸ hcpt
                          split
                          · refine triple_seq (Q := fun _ s' => CheckOK mode env fe s' ∧
                              s'.store = s8.store ∧ s'.pins = s8.pins) ?_ ?_
                            · mvcgen
                              bridge_peel; subst_vars
                              exact ⟨hok8, rfl, rfl⟩
                            rintro kp sk ⟨hokk, hstk, hpk⟩
                            rw [if_pos (by rw [hcert]; rfl : (mode.certs || kp) = true)]
                            refine triple_seq (defEqList_spec hsim sk d _ _ _ _ hokk
                              (by rw [hstk]; exact hmt) (by rw [hstk]; exact hcm2')
                              (fun z hz => hwmargs z (List.mem_of_mem_take hz)) hcmpW) ?_
                            rintro y s10 ⟨hok10, hx10, hp10, Fq, hFq⟩
                            have hx410 : Ext s4.store s10.store := hx48.trans (by rw [← hstk]; exact hx10)
                            have hp410 : s10.pins = s4.pins := hp10.trans (hpk.trans hp48)
                            have hq : (if rl'.compareParams then
                                ConLeche.defEqListFueled mode env Fq d
                                  (vmaj.getAppArgs.take rl'.ctorParams)
                                  (ConLeche.recFireComparands rl' dcv.levelParams ls dcvj.levelParams xs rP).2
                                else pure true : CheckM Bool) = .ok y := by
                              rw [if_pos hcpt', hctp]; exact hFq
                            by_cases hyt : y = true
                            · rw [if_pos hyt]
                              subst hyt
                              refine triple_mono (iotaFam_spec hμ henv hsim s10 d c icv icvj us usj rl
                                (takeEidx sargs sargs.size).toList margs major mI rP cn cjn ls lsj dcv dcvj
                                cnP cnF drules rl' xs vmaj Fp Fq hok10
                                (denoteN_ext hcn (hx04.trans hx410)) (denoteLs_ext hls (hx04.trans hx410))
                                (denoteLs_ext hlsj hx410) (denoteCV_ext hdcv (hx04.trans hx410))
                                (denoteCV_ext hdcvj hx410) (denote_ext hvmaj hx410)
                                (denoteEList_ext hx410 _ _ hmargs) (denoteEList_ext (hx04.trans hx410) _ _ hargs)
                                (denoteRule_ext hrl' hx410) hfind hfindj hfind' hgfm hlP hin' hwargs hwvmaj hw
                                hT h1 hq) ?_
                              rintro r s' ⟨ha, hb, hc, hd'⟩
                              exact ⟨ha, hx04.trans (hx410.trans hb), hc.trans (hp410.trans hp04), hd'⟩
                            · rw [if_neg hyt]
                              have hyf : y = false := by simpa using hyt
                              subst hyf
                              have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
                                  (Expr.mkAppN (.const cn ls) xs)) d s10.store none := by
                                refine simOOp_none (F := max Fp Fq) ?_
                                rw [hT _ (Nat.le_max_left _ _), iotaTail_fire (b2 := false)
                                  (b3 := false) (b4 := false) (b5 := false) hgfm hfindj hfind'
                                  hlP hin' h1 (fun _ => ifDefEq_mono (Nat.le_max_right _ _) hq)
                                  (fun _ h => by cases h) (fun _ h => by cases h)
                                  (fun _ h => by cases h)]
                                rfl
                              mvcgen
                              bridge_peel; subst_vars
                              exact ⟨hok10, hx04.trans hx410, hp410.trans hp04, hfin⟩
                          · refine triple_seq (Q := fun _ s' => CheckOK mode env fe s' ∧
                              s'.store = s8.store ∧ s'.pins = s8.pins) ?_ ?_
                            · refine triple_mono (ExprOps.readNameM_specF s8 c hok8.caches.readN) ?_
                              rintro nm s' ⟨hst, hm, hp, hc, _, hN⟩
                              exact ⟨CheckOK.ofReadbackFrame hok8 (ReadbackFrame.ofReadN hst hm hp hc hN),
                                hst, hp⟩
                            rintro nm sk0 ⟨hokk0, hstk0, hpk0⟩
                            refine triple_seq (Q := fun _ s' => CheckOK mode env fe s' ∧
                              s'.store = s8.store ∧ s'.pins = s8.pins) ?_ ?_
                            · mvcgen
                              bridge_peel; subst_vars
                              exact ⟨hokk0, hstk0, hpk0⟩
                            rintro kp sk ⟨hokk, hstk, hpk⟩
                            rw [if_pos (by rw [hcert]; rfl : (mode.certs || kp) = true)]
                            refine triple_seq (defEqList_spec hsim sk d _ _ _ _ hokk
                              (by rw [hstk]; exact hmt) (by rw [hstk]; exact hcm2')
                              (fun z hz => hwmargs z (List.mem_of_mem_take hz)) hcmpW) ?_
                            rintro y s10 ⟨hok10, hx10, hp10, Fq, hFq⟩
                            have hx410 : Ext s4.store s10.store := hx48.trans (by rw [← hstk]; exact hx10)
                            have hp410 : s10.pins = s4.pins := hp10.trans (hpk.trans hp48)
                            have hq : (if rl'.compareParams then
                                ConLeche.defEqListFueled mode env Fq d
                                  (vmaj.getAppArgs.take rl'.ctorParams)
                                  (ConLeche.recFireComparands rl' dcv.levelParams ls dcvj.levelParams xs rP).2
                                else pure true : CheckM Bool) = .ok y := by
                              rw [if_pos hcpt', hctp]; exact hFq
                            by_cases hyt : y = true
                            · rw [if_pos hyt]
                              subst hyt
                              refine triple_mono (iotaFam_spec hμ henv hsim s10 d c icv icvj us usj rl
                                (takeEidx sargs sargs.size).toList margs major mI rP cn cjn ls lsj dcv dcvj
                                cnP cnF drules rl' xs vmaj Fp Fq hok10
                                (denoteN_ext hcn (hx04.trans hx410)) (denoteLs_ext hls (hx04.trans hx410))
                                (denoteLs_ext hlsj hx410) (denoteCV_ext hdcv (hx04.trans hx410))
                                (denoteCV_ext hdcvj hx410) (denote_ext hvmaj hx410)
                                (denoteEList_ext hx410 _ _ hmargs) (denoteEList_ext (hx04.trans hx410) _ _ hargs)
                                (denoteRule_ext hrl' hx410) hfind hfindj hfind' hgfm hlP hin' hwargs hwvmaj hw
                                hT h1 hq) ?_
                              rintro r s' ⟨ha, hb, hc, hd'⟩
                              exact ⟨ha, hx04.trans (hx410.trans hb), hc.trans (hp410.trans hp04), hd'⟩
                            · rw [if_neg hyt]
                              have hyf : y = false := by simpa using hyt
                              subst hyf
                              have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
                                  (Expr.mkAppN (.const cn ls) xs)) d s10.store none := by
                                refine simOOp_none (F := max Fp Fq) ?_
                                rw [hT _ (Nat.le_max_left _ _), iotaTail_fire (b2 := false)
                                  (b3 := false) (b4 := false) (b5 := false) hgfm hfindj hfind'
                                  hlP hin' h1 (fun _ => ifDefEq_mono (Nat.le_max_right _ _) hq)
                                  (fun _ h => by cases h) (fun _ h => by cases h)
                                  (fun _ h => by cases h)]
                                rfl
                              mvcgen
                              bridge_peel; subst_vars
                              exact ⟨hok10, hx04.trans hx410, hp410.trans hp04, hfin⟩
                        · rw [if_neg hcpt]
                          have hcpf : rl'.compareParams = false := by rw [← hcp]; simpa using hcpt
                          have hq : (if rl'.compareParams then
                              ConLeche.defEqListFueled mode env 0 d
                                (vmaj.getAppArgs.take rl'.ctorParams)
                                (ConLeche.recFireComparands rl' dcv.levelParams ls dcvj.levelParams xs rP).2
                              else pure true : CheckM Bool) = .ok true := by rw [hcpf]; rfl
                          refine triple_seq (Q := fun y s' => s' = s8 ∧ y = true) ?_ ?_
                          · mvcgen
                          rintro y s10 ⟨hs10, rfl⟩
                          subst s10
                          rw [if_pos rfl]
                          refine triple_mono (iotaFam_spec hμ henv hsim s8 d c icv icvj us usj rl
                            (takeEidx sargs sargs.size).toList margs major mI rP cn cjn ls lsj dcv dcvj
                            cnP cnF drules rl' xs vmaj Fp 0 hok8
                            (denoteN_ext hcn (hx04.trans hx48)) (denoteLs_ext hls (hx04.trans hx48))
                            (denoteLs_ext hlsj hx48) (denoteCV_ext hdcv (hx04.trans hx48))
                            (denoteCV_ext hdcvj hx48) (denote_ext hvmaj hx48)
                            (denoteEList_ext hx48 _ _ hmargs) (denoteEList_ext (hx04.trans hx48) _ _ hargs)
                            (denoteRule_ext hrl' hx48) hfind hfindj hfind' hgfm hlP hin' hwargs hwvmaj hw
                            hT h1 hq) ?_
                          rintro r s' ⟨ha, hb, hc, hd'⟩
                          exact ⟨ha, hx04.trans (hx48.trans hb), hc.trans (hp48.trans hp04), hd'⟩
                      · rw [if_neg hb1t]
                        have hb1f : b1 = false := by simpa using hb1t
                        have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
                            (Expr.mkAppN (.const cn ls) xs)) d s8.store none := by
                          refine simOOp_none (F := Fp) ?_
                          rw [hT _ (Nat.le_refl _), iotaTail_fire (b2 := false) (b3 := false)
                            (b4 := false) (b5 := false) hgfm hfindj hfind' hlP hin' h1
                            (fun h => by rw [hb1f] at h; cases h)
                            (fun h => by rw [hb1f] at h; cases h)
                            (fun h => by rw [hb1f] at h; cases h)
                            (fun h => by rw [hb1f] at h; cases h)]
                          simp [hb1f]
                        mvcgen
                        bridge_peel; subst_vars
                        exact ⟨hok8, hx04.trans hx48, hp48.trans hp04, hfin⟩
                  · rw [if_neg hl]
                    have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
                        (Expr.mkAppN (.const cn ls) xs)) d s4.store none :=
                      simOOp_none (F := Fp) (by
                        rw [hT _ (Nat.le_refl _)]
                        exact iotaTail_len hgfm hfindj hfind' (by rw [hmlen, hctp, hnf]; exact hl))
                    mvcgen
                    bridge_peel; subst_vars
                    exact ⟨hok4, hx04, hp04, hfin⟩
                next hrl =>
                  have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
                      (Expr.mkAppN (.const cn ls) xs)) d s4.store none :=
                    simOOp_none (F := Fp) (by
                      rw [hT _ (Nat.le_refl _)]
                      exact iotaTail_norule hgfm hfindj (hfr2 hrl))
                  mvcgen
                  bridge_peel; subst_vars
                  exact ⟨hok4, hx04, hp04, hfin⟩
              next hnd =>
                have hnc := env_not_ctor_of_index hok4 hcjn (fun v p q h => hnd v p q h)
                have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
                    (Expr.mkAppN (.const cn ls) xs)) d s4.store none :=
                  simOOp_none (F := Fp) (by rw [hT _ (Nat.le_refl _)]
                                            exact iotaTail_noctor hgfm hnc)
                mvcgen
                bridge_peel; subst_vars
                exact ⟨hok4, hx04, hp04, hfin⟩
            all_goals
              dsimp only
              have hnc := denote_not_const hwf4 hvh hmh (by intro c us h; cases h)
              have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
                  (Expr.mkAppN (.const cn ls) xs)) d s4.store none :=
                simOOp_none (F := Fp) (by rw [hT _ (Nat.le_refl _)]
                                          exact iotaTail_nohead hnc)
              mvcgen
              bridge_peel; subst_vars
              exact ⟨hok4, hx04, hp04, hfin⟩
          · rw [if_neg hg]
            have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
                (Expr.mkAppN (.const cn ls) xs)) d s₀.store none :=
              simOOp_none (F := 0) (iotaRecFueled_guard hE1 hfind (by
                rw [hE2]; intro hg'; exact hg ⟨hal, by rw [hg'.2, hlenlps]⟩))
            mvcgen
            bridge_peel; subst_vars
            exact ⟨hok, Ext.refl _, rfl, hfin⟩
      next hnd =>
        have hnr := env_not_rec_of_index hok hcn (fun v mI rP rs h => hnd v mI rP rs h)
        have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
            (Expr.mkAppN (.const cn ls) xs)) d s₀.store none :=
          simOOp_none (F := 0) (iotaRecFueled_norec hE1 hnr)
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok, Ext.refl _, rfl, hfin⟩
  · rw [if_neg htag]
    obtain ⟨v, hv⟩ := denoteE_view hdh
    have hvt := EStore.tagOf_of_view hv
    have hnc := denote_not_const hwf hv hdh (by
      intro c us h; subst h; exact htag (by rw [hvt]; rfl))
    have hfin : SimOOp (fun F => ConLeche.iotaRecFueled mode env F d
        (Expr.mkAppN h xs)) d s₀.store none :=
      simOOp_none (F := 0) (iotaRecFueled_nohead (by
        rw [Expr.getAppFn_mkAppN]
        cases h with
        | app f a => exact absurd rfl (hnapp f a)
        | _ => exact hnc))
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hfin⟩

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
#print axioms isCtorApp_spec
#print axioms litToCtorIfNat_spec
#print axioms capsNeverZero_spec
#print axioms fabScopeOk_spec
#print axioms etaFabArgsE_spec
#print axioms andRescueSlots_spec
#print axioms litMajorToCtor_spec
#print axioms majorK_spec
#print axioms majorEta_spec
#print axioms majorAnd_spec
#print axioms majorToCtor_spec
#print axioms prepareMajor_spec
#print axioms recFireComparands_spec
#print axioms piResidual_spec
#print axioms iotaIndexOk_spec
#print axioms iotaFam_spec
#print axioms iotaRecAt_spec
#print axioms iotaRec_spec

end Census

end ConRon.Bridge.Core
