/-
# `ConRon.Bridge.Modular.ReachParts` — a part's reads, Theorem 1 (task #166)

A read of a part with its memo (`takePart`, the read, `putPart`: upstream's `withPart`), a part's
region and table off one read of its files (`loadPart`), a copy's statement (`stmtAt`), one or
several constants (`partEntry`, `partEntries`), a copy in its module's private part (`privSpot`):
each twin accept is upstream's answer, the caches related after.  Run style, not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.ReachCache
public import ConRon.Bridge.Modular.ReachMemo
import ConRon.Bridge.Frontend.Lines

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM)
open ConLeche.Frontend.Olean (Region Roots OLeanLevel ModFiles CEntryF CKindF entryAt)

/-- con-leche: ConLeche/Driver/Reach.lean:262-282 withPart — **a read of a part with its
memo**: the twin's `takePart`, a read `g` of the region with the memo, `putPart`, is
upstream's `withPart` at a read `f` answering alike from any good memo. -/
theorem partRead_run {α β : Type} {R : EStore → α → β → Prop}
    {g : Region → SM → AM (SM × Option α)}
    {f : Region → ConLeche.Frontend.Olean.SM → Option (ConLeche.Frontend.Olean.SM × β)}
    {pk : OleanPins}
    (hg : ∀ (r : Region) (m m' : SM) (a : α) (s s' : AState), Ctx pk s → SMGood s.store r m →
      g r m s = .ok ((m', some a), s') →
      ParseStep s s' ∧ SMGood s'.store r m' ∧ ∀ mC : ConLeche.Frontend.Olean.SM, mC.Good r →
        ∃ mC' b, f r mC = some (mC', b) ∧ mC'.Good r ∧ R s'.store a b)
    {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} {a : α} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hk : PKRel s.store k kC)
    (h : (do
        let (c, r, st) ← ConRon.Arena.Modular.takePart (modelFs F) pk sp c k
        ConRon.Arena.Modular.putPart c k r (← g r st)) s = .ok ((c', a), s')) :
    DStep s s' ∧ ∃ cC' b, ModelIO.Gives (ConLeche.Driver.withPart envC cC kC f) F (cC', .ok b) ∧
      CacheRel s'.store c' cC' ∧ R s'.store a b := by
  have hw := hctx.wf
  obtain ⟨⟨c₁, r, st⟩, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨⟨m', o⟩, s₂, h2, h3⟩ := AM.bind_ok h
  -- the part: cached, or read off its files
  obtain ⟨hs1, stC, hgot, hst, hgC, hc1⟩ : s₁ = s ∧ ∃ (stC : ConLeche.Frontend.Olean.SM),
      (cC.parts[kC]? = some (r, stC) ∨ (cC.parts[kC]? = none ∧ stC = {} ∧ ∃ fv a',
        ModelIO.Gives (envC.rd.files kC.mod kC.level) F (.ok fv) ∧
        fv.viewRegion kC.level = some (r, a'))) ∧
      SMGood s.store r st ∧ stC.Good r ∧
      CacheRel s.store c₁ { cC with parts := cC.parts.erase kC } := by
    have hp := hc.parts.get hw hk
    generalize hT : ConRon.Arena.Modular.takePart (modelFs F) pk sp c k = tk at h1
    unfold ConRon.Arena.Modular.takePart at hT
    split at hT
    · rename_i r' st' hr
      subst hT
      obtain ⟨hv, rfl⟩ := AM.pure_ok h1
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      rw [hr] at hp
      rcases optRel_cases hp with ⟨g1, -⟩ | ⟨p, q, g1, g2, g3⟩
      · cases g1
      cases g1
      obtain ⟨q1, q2⟩ := q
      obtain ⟨rfl, g4, g5⟩ := g3
      exact ⟨rfl, q2, .inl g2, g4, g5, { hc with parts := hc.parts.erase hw hk }⟩
    · rename_i hr
      subst hT
      obtain ⟨mn, t₁, g1, k1⟩ := AM.bind_ok h1
      obtain ⟨e1, hmn⟩ := readName_run g1
      rw [e1] at k1
      obtain ⟨fv, t₂, g2, k2⟩ := AM.bind_ok k1
      cases hf : ConRon.Arena.Frontend.Olean.readFiles (modelFs F) sp mn k.level with
      | error e =>
        simp only [hf, ConRon.Arena.Frontend.Olean.liftE] at g2; exact (AM.fail_ok g2).elim
      | ok fv' =>
      simp only [hf, ConRon.Arena.Frontend.Olean.liftE] at g2
      obtain ⟨e2, e3⟩ := AM.pure_ok g2
      subst e2
      rcases hv : fv.viewRegion k.level with _ | ⟨r', a'⟩
      · rw [hv] at k2
        obtain ⟨_, _, _, g3⟩ := AM.bind_ok k2
        exact (AM.fail_ok g3).elim
      · rw [hv] at k2
        obtain ⟨hv', e4⟩ := AM.pure_ok k2
        simp only [Prod.mk.injEq] at hv'
        obtain ⟨rfl, rfl, rfl⟩ := hv'
        refine ⟨e4.trans e3, ?_⟩
        rw [hr] at hp
        have hpC : cC.parts[kC]? = none := by
          rcases optRel_cases hp with ⟨-, g⟩ | ⟨p, q, g, -, -⟩
          · exact g
          · cases g
        obtain rfl : mn = kC.mod := Option.some.inj (hmn.symm.trans hk.1)
        refine ⟨{}, .inr ⟨hpC, rfl, fv, a', ?_, hk.2 ▸ hv⟩, SMGood.empty _ _,
          ConLeche.Frontend.Olean.SM.good_empty _, ?_⟩
        · rw [he.rd, ← hk.2]
          exact readFiles_sim (roots_ok_of_bare hsp) rfl hf
        · refine { hc with parts := ⟨fun x a hx => ?_, fun xC b hx => ?_⟩ }
          · obtain ⟨xC, b, h1, h2, h3⟩ := hc.parts.fwd x a hx
            refine ⟨xC, b, h1, ?_, h3⟩
            rw [Std.HashMap.getElem?_erase]
            split
            · rename_i hxe
              obtain rfl := eq_of_beq hxe
              rw [hpC] at h2; cases h2
            · exact h2
          · rw [Std.HashMap.getElem?_erase] at hx
            split at hx
            · cases hx
            · exact hc.parts.bwd xC b hx
  rw [hs1] at h2
  obtain ⟨hst2, hg2, hf⟩ := hg r st m' a s s₂ hctx.ctx hst (by
    -- the read's answer is `some`: `putPart` accepted
    cases o with
    | none =>
      unfold ConRon.Arena.Modular.putPart at h3
      obtain ⟨_, _, _, g⟩ := AM.bind_ok h3
      exact (AM.fail_ok g).elim
    | some a' =>
      unfold ConRon.Arena.Modular.putPart at h3
      obtain ⟨hv, rfl⟩ := AM.pure_ok h3
      simp only [Prod.mk.injEq] at hv
      obtain ⟨-, rfl⟩ := hv
      exact h2)
  cases o with
  | none =>
    unfold ConRon.Arena.Modular.putPart at h3
    obtain ⟨_, _, _, g⟩ := AM.bind_ok h3
    exact (AM.fail_ok g).elim
  | some a' =>
  unfold ConRon.Arena.Modular.putPart at h3
  obtain ⟨hv, rfl⟩ := AM.pure_ok h3
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  obtain ⟨mC', b, hfb, hgC', hR⟩ := hf stC hgC
  have hds := DStep.of_parse hctx.ok hctx.off hst2
  have hw2 := nsWF_of_StateOK hst2.ok
  have hc2 := hc1.ext hst2.ext
  refine ⟨hds, { cC with parts := (cC.parts.erase kC).insert kC (r, mC') }, b, ?_,
    { hc2 with parts := hc2.parts.insert hw2 (hk.ext hst2.ext) ⟨rfl, hg2, hgC'⟩ }, hR⟩
  unfold ConLeche.Driver.withPart
  rcases hgot with hhit | ⟨hmiss, rfl, fv, a', hfv, hvr⟩
  · simp only [hhit]
    refine (ModelIO.gives_pure _ _).bind ?_
    simp only [hfb]
    exact ModelIO.gives_pure _ _
  · simp only [hmiss]
    refine hfv.bind ?_
    simp only [hvr]
    refine (ModelIO.gives_pure _ _).bind ?_
    simp only [hfb]
    exact ModelIO.gives_pure _ _

/-- con-leche: ConLeche/Driver/Reach.lean:311-314 stmtAt — **a copy's statement and kind**,
upstream's, read back. -/
theorem stmtAt_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {sp₀ : ConRon.Arena.Modular.Spot} {spC : ConLeche.Driver.Spot}
    {cv : ConRon.Arena.Frontend.Olean.StmtRec} {k : CKindF NIdx Unit} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hs : SpotRel s.store sp₀ spC)
    (h : ConRon.Arena.Modular.stmtAt (modelFs F) pk sp c sp₀ s = .ok ((c', cv, k), s')) :
    DStep s s' ∧ ∃ cC' cvC kC, ModelIO.Gives (ConLeche.Driver.stmtAt envC cC spC) F
        (cC', .ok (cvC, kC)) ∧ CacheRel s'.store c' cC' ∧ denoteStmt s'.store cv = some cvC ∧
      denoteKindN s'.store k = some kC := by
  unfold ConRon.Arena.Modular.stmtAt at h
  obtain ⟨hst, cC', ⟨cvC, kC⟩, hg, hc', hR⟩ := partRead_run
    (R := fun st (a : ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)
      (b : ConstantVal × CKindF ConLeche.Name Unit) => denoteStmt st a.1 = some b.1 ∧
        denoteKindN st a.2 = some b.2)
    (g := fun r st => ConRon.Arena.Frontend.Olean.stmtWith pk r st sp₀.pos.loc)
    (f := fun r st => ConLeche.Frontend.Olean.stmtWith r st spC.pos.loc)
    (fun r m m' a s s' hc hm h => by
      obtain ⟨cv, k⟩ := a
      obtain ⟨hst, hg, cvC, kC, hsk, hd1, hd2⟩ := stmtWith_runR hc hm h
      refine ⟨hst, hg, fun mC hG => ?_⟩
      obtain ⟨mC', hw, hG'⟩ := stmtWith_complete hG (hs.2.loc ▸ hsk)
      exact ⟨mC', (cvC, kC), hw, hG', hd1, hd2⟩) hsp hctx he hc hs.1 h
  exact ⟨hst, cC', cvC, kC, hg, hc', hR⟩

/-- con-leche: ConLeche/Driver/Reach.lean:262-282 withPart — **one constant of a part**,
upstream's, read back. -/
theorem partEntry_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} {l : Nat}
    {e : CEntryF NIdx EIdx} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hk : PKRel s.store k kC)
    (h : ConRon.Arena.Modular.partEntry (modelFs F) pk sp c k l s = .ok ((c', e), s')) :
    DStep s s' ∧ ∃ cC' eC, ModelIO.Gives (ConLeche.Driver.withPart envC cC kC
        fun r st => ConLeche.Frontend.Olean.entryWith r st l) F (cC', .ok eC) ∧
      CacheRel s'.store c' cC' ∧ denoteEntry s'.store e = some eC := by
  unfold ConRon.Arena.Modular.partEntry at h
  exact partRead_run (R := fun st (a : CEntryF NIdx EIdx) (b : CEntryF ConLeche.Name Expr) =>
      denoteEntry st a = some b)
    (g := fun r st => ConRon.Arena.Frontend.Olean.entryWith pk r st l)
    (fun r m m' a s s' hc hm h => by
      obtain ⟨hst, hg, eC, heC, hd⟩ := entryWith_runR hc hm h
      refine ⟨hst, hg, fun mC hG => ?_⟩
      obtain ⟨mC', hw, hG'⟩ := entryWith_complete hG heC
      exact ⟨mC', eC, hw, hG', hd⟩) hsp hctx he hc hk h

/-- con-leche: ConLeche/Driver/Reach.lean:262-282 withPart — **several constants of a part**,
upstream's, read back. -/
theorem partEntries_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} {ls : List Nat}
    {es : List (CEntryF NIdx EIdx)} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hk : PKRel s.store k kC)
    (h : ConRon.Arena.Modular.partEntries (modelFs F) pk sp c k ls s = .ok ((c', es), s')) :
    DStep s s' ∧ ∃ cC' esC, ModelIO.Gives (ConLeche.Driver.withPart envC cC kC
        fun r st => ConLeche.Driver.entriesWith r st ls) F (cC', .ok esC) ∧
      CacheRel s'.store c' cC' ∧ es.mapM (denoteEntry s'.store) = some esC := by
  unfold ConRon.Arena.Modular.partEntries at h
  exact partRead_run (R := fun st (a : List (CEntryF NIdx EIdx)) (b : List (CEntryF ConLeche.Name Expr)) =>
      a.mapM (denoteEntry st) = some b)
    (g := fun r st => ConRon.Arena.Modular.entriesWith pk r st ls)
    (fun r m m' a s s' hc hm h => by
      obtain ⟨hst, hg, esC, hes, hd⟩ := entriesWith_runR ls hc hm h
      refine ⟨hst, hg, fun mC hG => ?_⟩
      obtain ⟨mC', hw, hG'⟩ := entriesWith_complete ls hG hes
      exact ⟨mC', esC, hw, hG', hd⟩) hsp hctx he hc hk h

end ConRon.Bridge.Modular
