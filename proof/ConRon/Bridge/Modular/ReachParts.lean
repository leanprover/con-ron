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

/-- A run that ends in a failure, after any reads: no accept. -/
theorem AM.bind_fail_never {α β : Type} {x : AM α} {f : α → Arena.CheckError} {s s' : AState}
    {b : β} (h : (x >>= fun a => fail (f a)) s = .ok (b, s')) : False := by
  obtain ⟨_, _, _, h2⟩ := AM.bind_ok h
  exact AM.fail_ok h2

/-- A failure's message read name by name: no accept. -/
macro "am_never " h:ident : tactic => `(tactic| first
  | exact (AM.fail_ok $h).elim
  | exact (AM.bind_fail_never $h).elim
  | (obtain ⟨_, _, _, h'⟩ := AM.bind_ok $h
     first
     | exact (AM.fail_ok h').elim
     | exact (AM.bind_fail_never h').elim
     | (obtain ⟨_, _, _, h''⟩ := AM.bind_ok h'
        first
        | exact (AM.fail_ok h'').elim
        | exact (AM.bind_fail_never h'').elim)))

/-- con-leche: ConLeche/Driver/Reach.lean:262-282 withPart — **a read of a part with its
memo**: the twin's `takePart`, a read `g` of the region with the memo, `putPart`, is
upstream's `withPart` at a read `f` answering alike from any good memo. -/
theorem partRead_run {α β : Type} {R : EStore → α → β → Prop}
    {g : Region → SM → AM (SM × Option α)}
    {f : Region → ConLeche.Frontend.Olean.SM → Option (ConLeche.Frontend.Olean.SM × β)}
    {pk : OleanPins} {st₀ : EStore}
    (hg : ∀ (r : Region) (m m' : SM) (a : α) (s s' : AState), Ext st₀ s.store → Ctx pk s →
      SparseGood s.store r m →
      g r m s = .ok ((m', some a), s') →
      ParseStep s s' ∧ SparseGood s'.store r m' ∧ ∀ mC : ConLeche.Frontend.Olean.SM, mC.Good r →
        ∃ mC' b, f r mC = some (mC', b) ∧ mC'.Good r ∧ R s'.store a b)
    {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} {a : α} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hk : PKRel s.store k kC) (hx₀ : Ext st₀ s.store)
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
      SparseGood s.store r st ∧ stC.Good r ∧
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
        refine ⟨{}, .inr ⟨hpC, rfl, fv, a', ?_, hk.2 ▸ hv⟩, SparseGood.empty _ _,
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
  obtain ⟨hst2, hg2, hf⟩ := hg r st m' a s s₂ hx₀ hctx.ctx hst (by
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
    (fun r m m' a s s' _ hc hm h => by
      obtain ⟨cv, k⟩ := a
      obtain ⟨hst, hg, cvC, kC, hsk, hd1, hd2⟩ := stmtWith_runR hc hm h
      refine ⟨hst, hg, fun mC hG => ?_⟩
      obtain ⟨mC', hw, hG'⟩ := stmtWith_complete hG (hs.2.loc ▸ hsk)
      exact ⟨mC', (cvC, kC), hw, hG', hd1, hd2⟩) hsp hctx he hc hs.1 (Ext.refl _) h
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
    (fun r m m' a s s' _ hc hm h => by
      obtain ⟨hst, hg, eC, heC, hd⟩ := entryWith_runR hc hm h
      refine ⟨hst, hg, fun mC hG => ?_⟩
      obtain ⟨mC', hw, hG'⟩ := entryWith_complete hG heC
      exact ⟨mC', eC, hw, hG', hd⟩) hsp hctx he hc hk (Ext.refl _) h

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
    (fun r m m' a s s' _ hc hm h => by
      obtain ⟨hst, hg, esC, hes, hd⟩ := entriesWith_runR ls hc hm h
      refine ⟨hst, hg, fun mC hG => ?_⟩
      obtain ⟨mC', hw, hG'⟩ := entriesWith_complete ls hG hes
      exact ⟨mC', esC, hw, hG', hd⟩) hsp hctx he hc hk (Ext.refl _) h

/-! ## A part's region and table, one read of its files -/

/-- con-leche: ConLeche/Driver/Reach.lean:284-301 loadPart — **a part's region and table off one
read of its files**: upstream's accept, the caches related after. -/
theorem loadPart_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hk : PKRel s.store k kC)
    (h : ConRon.Arena.Modular.loadPart (modelFs F) pk sp c k s = .ok (c', s')) :
    DStep s s' ∧ ∃ cC', ModelIO.Gives (ConLeche.Driver.loadPart envC cC kC) F (cC', .ok ()) ∧
      CacheRel s'.store c' cC' := by
  have hw := hctx.wf
  have hpc := hc.parts.contains hw hk
  have htc := hc.tables.contains hw hk
  unfold ConRon.Arena.Modular.loadPart at h
  by_cases h1 : c.parts.contains k = true
  · simp only [h1, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    refine ⟨DStep.refl hctx.ok hctx.off, cC, ?_, hc⟩
    unfold ConLeche.Driver.loadPart
    simp only [← hpc, h1, ↓reduceIte]
    exact ModelIO.gives_pure _ _
  simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  obtain ⟨mn, t₁, g1, k1⟩ := AM.bind_ok h
  obtain ⟨e1, hmn⟩ := readName_run g1
  rw [e1] at k1
  obtain rfl : mn = kC.mod := Option.some.inj (hmn.symm.trans hk.1)
  obtain ⟨fv, t₂, g2, k2⟩ := AM.bind_ok k1
  cases hf : ConRon.Arena.Frontend.Olean.readFiles (modelFs F) sp kC.mod k.level with
  | error e =>
    simp only [hf, ConRon.Arena.Frontend.Olean.liftE] at g2; exact (AM.fail_ok g2).elim
  | ok fv' =>
  simp only [hf, ConRon.Arena.Frontend.Olean.liftE] at g2
  obtain ⟨e2, e3⟩ := AM.pure_ok g2
  subst e2
  rw [e3] at k2
  have hgf : ModelIO.Gives (envC.rd.files kC.mod kC.level) F (.ok fv) := by
    rw [he.rd, ← hk.2]
    exact readFiles_sim (roots_ok_of_bare hsp) rfl hf
  rcases hv : fv.viewRegion k.level with _ | ⟨r, a⟩
  · rw [hv] at k2
    obtain ⟨_, _, _, g3⟩ := AM.bind_ok k2
    exact (AM.fail_ok g3).elim
  rw [hv] at k2
  have hpkC : (cC.parts.contains kC) = false := by rw [← hpc]; simpa using h1
  have hcP : CacheRel s.store { c with parts := c.parts.insert k (r, {}) }
      { cC with parts := cC.parts.insert kC (r, {}) } :=
    { hc with parts := hc.parts.insert hw hk ⟨rfl, SparseGood.empty _ _,
      ConLeche.Frontend.Olean.SM.good_empty _⟩ }
  by_cases h2 : c.tables.contains k = true
  · simp only [h2, ↓reduceIte] at k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
    refine ⟨DStep.refl hctx.ok hctx.off, _, ?_, hcP⟩
    unfold ConLeche.Driver.loadPart
    simp only [hpkC, Bool.false_eq_true, ↓reduceIte]
    refine hgf.bind ?_
    simp only [← hk.2, hv, ← htc, h2, ↓reduceIte]
    exact ModelIO.gives_pure _ _
  simp only [h2, Bool.false_eq_true, ↓reduceIte] at k2
  obtain ⟨o, t₃, g4, k3⟩ := AM.bind_ok k2
  cases o with
  | none =>
    obtain ⟨_, _, _, g5⟩ := AM.bind_ok k3
    exact (AM.fail_ok g5).elim
  | some t =>
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
  obtain ⟨hst, tC, htC, hrel⟩ := namePositionsAt_run hctx.ctx g4
  have hds := DStep.of_parse hctx.ok hctx.off hst
  have hcP' := hcP.ext hst.ext
  have hT := hcP'.tables.insert (nsWF_of_StateOK hst.ok) (hk.ext hst.ext) hrel
  refine ⟨hds, { cC with parts := cC.parts.insert kC (r, {}), tables := cC.tables.insert kC tC }, ?_,
    { hcP' with tables := hT }⟩
  unfold ConLeche.Driver.loadPart
  simp only [hpkC, Bool.false_eq_true, ↓reduceIte]
  refine hgf.bind ?_
  have htC' : (cC.tables.contains kC) = false := by rw [← htc]; simpa using h2
  simp only [← hk.2, hv, htC', Bool.false_eq_true, ↓reduceIte, htC]
  exact ModelIO.gives_pure _ _

/-! ## A copy in its module's private part -/

/-- con-leche: ConLeche/Driver/Reach.lean:316-328 privSpot — **a copy in its module's private
part**: upstream's, the caches related after. -/
theorem privSpot_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {sp₀ p : ConRon.Arena.Modular.Spot} {spC : ConLeche.Driver.Spot} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hs : SpotRel s.store sp₀ spC)
    (h : ConRon.Arena.Modular.privSpot (modelFs F) pk sp env c sp₀ s = .ok ((c', p), s')) :
    DStep s s' ∧ ∃ cC' pC, ModelIO.Gives (ConLeche.Driver.privSpot envC cC spC) F (cC', .ok pC) ∧
      CacheRel s'.store c' cC' ∧ SpotRel s'.store p pC := by
  unfold ConRon.Arena.Modular.privSpot at h
  by_cases h1 : (sp₀.part.level == .private) = true
  · simp only [h1, ↓reduceIte] at h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    refine ⟨DStep.refl hctx.ok hctx.off, cC, spC, ?_, hc, hs⟩
    unfold ConLeche.Driver.privSpot
    simp only [← hs.1.2, h1, ↓reduceIte]
    exact ModelIO.gives_pure _ _
  simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  have hkp : PKRel s.store (ConRon.Arena.Modular.privKey sp₀.part.mod)
      (⟨spC.part.mod, .private⟩ : ConLeche.Driver.PartKey) := ⟨hs.1.1, rfl⟩
  obtain ⟨c₁, s₁, g1, k1⟩ := AM.bind_ok h
  obtain ⟨hst1, cC₁, lC, l, hgl, hc1, hl, hlr⟩ := lookOf_run hsp hctx he hc hkp g1
  obtain ⟨o, s₂, g2, k2⟩ := AM.bind_ok k1
  rw [lookAt_eq hl] at g2
  obtain ⟨ho, e2⟩ := AM.pure_ok g2
  subst ho e2
  have hw1 := nsWF_of_StateOK hst1.ok.state
  have hq := hlr.get hw1 (denoteN_ext hs.2.name hst1.ext)
  rcases optRel_cases hq with ⟨g4, -⟩ | ⟨q, qC, g4, g5, g6⟩
  · rw [g4] at k2
    am_never k2
  rw [g4] at k2
  obtain ⟨hv, rfl⟩ := AM.pure_ok k2
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  refine ⟨hst1, cC₁, ⟨⟨spC.part.mod, .private⟩, qC⟩, ?_, hc1, ⟨hkp.ext hst1.ext, g6⟩⟩
  unfold ConLeche.Driver.privSpot
  have h1C : (spC.part.level == .private) = false := by rw [← hs.1.2]; simpa using h1
  simp only [h1C, Bool.false_eq_true, ↓reduceIte]
  refine hgl.bind ?_
  simp only [g5]
  exact ModelIO.gives_pure _ _

/-! ## A home's view -/

theorem hmrel_contains {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap NIdx α} {MC : Std.HashMap ConLeche.Name β} (h : HMRel R st M MC) {x : NIdx}
    {n : ConLeche.Name} (hd : denoteN st.ns x = some n) : M.contains x = MC.contains n := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?]
  rcases optRel_cases (h.get hw hd) with ⟨h1, h2⟩ | ⟨a, b, h1, h2, -⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2]; rfl

theorem viewFold_rel {st : EStore} (hw : NStoreWF st.ns) {k : ConRon.Arena.Modular.PartKey}
    {kC : ConLeche.Driver.PartKey} (hk : PKRel st k kC) :
    ∀ {qs : List ConRon.Arena.Frontend.Olean.NamePosition}
      {qsC : List ConLeche.Frontend.Olean.NamePosition}
      {v : Std.HashMap NIdx ConRon.Arena.Modular.Spot}
      {vC : Std.HashMap ConLeche.Name ConLeche.Driver.Spot},
      ListRel (NPRel st) qs qsC → HMRel (SpotRel st) st v vC →
      HMRel (SpotRel st) st
        (qs.foldl (fun (v : Std.HashMap NIdx ConRon.Arena.Modular.Spot) q =>
          if v.contains q.name then v else v.insert q.name ⟨k, q⟩) v)
        (qsC.foldl (fun (v : Std.HashMap ConLeche.Name ConLeche.Driver.Spot) q =>
          if v.contains q.name then v else v.insert q.name ⟨kC, q⟩) vC)
  | [], [], _, _, .nil, h => h
  | q :: qs, qC :: qsC, v, vC, .cons hq hqs, h => by
    simp only [List.foldl_cons]
    refine viewFold_rel hw hk hqs ?_
    rw [hmrel_contains hw h hq.name]
    split
    · exact h
    · exact h.insert hw hq.name ⟨hk, hq⟩

/-- con-leche: ConLeche/Driver/Reach.lean:218-222 viewStep — one part's names into a view,
upstream's. -/
theorem viewStep_rel {st : EStore} (hw : NStoreWF st.ns) {v : Std.HashMap NIdx ConRon.Arena.Modular.Spot}
    {vC : Std.HashMap ConLeche.Name ConLeche.Driver.Spot} (hv : HMRel (SpotRel st) st v vC)
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} (hk : PKRel st k kC)
    {t : ConRon.Arena.Frontend.Olean.NamePositions} {tC : ConLeche.Frontend.Olean.NamePositions}
    (ht : NPsRel st t tC) :
    HMRel (SpotRel st) st (ConRon.Arena.Modular.viewStep v k t) (ConLeche.Driver.viewStep vC kC tC) := by
  unfold ConRon.Arena.Modular.viewStep ConLeche.Driver.viewStep
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact viewFold_rel hw hk ht.consts hv

/-- con-leche: ConLeche/Driver/Reach.lean:332-340 viewAdd — **some parts' names into a view**,
upstream's, the caches related after. -/
theorem viewAdd_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO} :
    ∀ (ks : List ConRon.Arena.Modular.PartKey) {ksC : List ConLeche.Driver.PartKey}
      {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
      {v v' : Std.HashMap NIdx ConRon.Arena.Modular.Spot}
      {vC : Std.HashMap ConLeche.Name ConLeche.Driver.Spot} {s s' : AState},
      RCtx pk s → EnvRel sp s.store env envC → CacheRel s.store c cC →
      ListRel (PKRel s.store) ks ksC → HMRel (SpotRel s.store) s.store v vC →
      ConRon.Arena.Modular.viewAdd (modelFs F) pk sp env c v ks s = .ok ((c', v'), s') →
      DStep s s' ∧ ∃ cC' vC', ModelIO.Gives (ConLeche.Driver.viewAdd envC cC vC ksC) F
          (cC', .ok vC') ∧ CacheRel s'.store c' cC' ∧ HMRel (SpotRel s'.store) s'.store v' vC'
  | [], _, c, c', cC, v, v', vC, s, s', hctx, _, hc, .nil, hv, h => by
    rw [ConRon.Arena.Modular.viewAdd] at h
    obtain ⟨hv', rfl⟩ := AM.pure_ok h
    simp only [Prod.mk.injEq] at hv'
    obtain ⟨rfl, rfl⟩ := hv'
    exact ⟨DStep.refl hctx.ok hctx.off, cC, vC, ModelIO.gives_pure _ _, hc, hv⟩
  | k :: ks, _, c, c', cC, v, v', vC, s, s', hctx, he, hc, .cons hk hks, hv, h => by
    rw [ConRon.Arena.Modular.viewAdd] at h
    obtain ⟨⟨c₁, v₁⟩, s₁, h1, h2⟩ := AM.bind_ok h
    unfold ConRon.Arena.Modular.viewAddOne at h1
    obtain ⟨c₀, s₀, g1, g2⟩ := AM.bind_ok h1
    obtain ⟨hst0, cC₀, tC, t, hgt, hc0, ht, htr⟩ := tableOf_run hsp hctx he hc hk g1
    rw [ht] at g2
    obtain ⟨hv1, rfl⟩ := AM.pure_ok g2
    simp only [Prod.mk.injEq] at hv1
    obtain ⟨rfl, rfl⟩ := hv1
    have hw0 := nsWF_of_StateOK hst0.ok.state
    have hv₁ := viewStep_rel hw0 (hv.ext hst0.ext (fun _ _ h => h.ext hst0.ext)) (hk.ext hst0.ext) htr
    obtain ⟨hst1, cC', vC', hg, hc', hv'⟩ := viewAdd_run hsp ks (hctx.step hst0)
      (he.ext hst0.ext hw0) hc0 (ListRel.mono' (fun _ _ h => h.ext hst0.ext) hks) hv₁ h2
    refine ⟨hst0.trans hst1, cC', vC', ?_, hc', hv'⟩
    rw [ConLeche.Driver.viewAdd]
    refine hgt.bind ?_
    exact hg

/-- con-leche: ConLeche/Driver/Reach.lean:213-216 viewKeys — the parts of a home's view,
upstream's. -/
theorem viewKeys_rel {st : EStore} {h : NIdx} {hC : ConLeche.Name} (hh : denoteN st.ns h = some hC)
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    (hl : LoadsRel st ld ldC) :
    ListRel (PKRel st) (ConRon.Arena.Modular.viewKeys h ld) (ConLeche.Driver.viewKeys hC ldC) := by
  unfold ConRon.Arena.Modular.viewKeys ConLeche.Driver.viewKeys
  refine .cons ⟨hh, rfl⟩ ?_
  have ho := hl.order
  have hf := hl.flags
  rw [Array.toList_zip, Array.toList_zip, ← hf]
  generalize ld.order.toList = os at ho
  generalize ldC.order.toList = osC at ho
  generalize ld.flags.toList = fs
  induction ho generalizing fs with
  | nil => simp; exact .nil
  | cons ha _ ih =>
    cases fs with
    | nil => simp; exact .nil
    | cons f fs => simp only [List.zip_cons_cons, List.map_cons]; exact .cons ⟨ha, rfl⟩ (ih fs)


/-- con-leche: ConLeche/Driver/Reach.lean:342-357 viewOf — **a home's view**, upstream's, cached
in the related caches after. -/
theorem viewOf_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {h : NIdx} {hC : ConLeche.Name} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hh : denoteN s.store.ns h = some hC)
    (hrun : ConRon.Arena.Modular.viewOf (modelFs F) pk sp env c h s = .ok (c', s')) :
    DStep s s' ∧ ∃ cC' vC v, ModelIO.Gives (ConLeche.Driver.viewOf envC cC hC) F (cC', .ok vC) ∧
      CacheRel s'.store c' cC' ∧ c'.views[h]? = some v ∧ HMRel (SpotRel s'.store) s'.store v vC := by
  have hw := hctx.wf
  have hvw := hc.views.get hw hh
  unfold ConRon.Arena.Modular.viewOf at hrun
  by_cases h1 : c.views.contains h = true
  · simp only [h1, ↓reduceIte] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    rw [Std.HashMap.contains_eq_isSome_getElem?] at h1
    rcases optRel_cases hvw with ⟨g1, -⟩ | ⟨v, vC, g1, g2, g3⟩
    · rw [g1] at h1; cases h1
    refine ⟨DStep.refl hctx.ok hctx.off, cC, vC, v, ?_, hc, g1, g3⟩
    unfold ConLeche.Driver.viewOf
    simp only [g2]
    exact ModelIO.gives_pure _ _
  simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind] at hrun
  have hmissC : cC.views[hC]? = none := by
    have hm : c.views[h]? = none := by
      rw [Std.HashMap.contains_eq_isSome_getElem?] at h1
      cases hh' : c.views[h]? with
      | none => rfl
      | some _ => rw [hh'] at h1; exact absurd rfl h1
    rw [hm] at hvw
    rcases optRel_cases hvw with ⟨-, g⟩ | ⟨a, b, g, -, -⟩
    · exact g
    · cases g
  have hk : PKRel s.store (ConRon.Arena.Modular.privKey h) (⟨hC, .private⟩ : ConLeche.Driver.PartKey) :=
    ⟨hh, rfl⟩
  obtain ⟨c₁, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, cC₁, tC, t, hgt, hc1, ht, htr⟩ := tableOf_run hsp hctx he hc hk g1
  obtain ⟨ld, s₂, g2, k2⟩ := AM.bind_ok k1
  unfold ConRon.Arena.Modular.homeLoads at g2
  rw [ht] at g2
  have hctx1 := hctx.step hst1
  obtain ⟨hst2, ldC, hgl, hlr, -⟩ := headerFixpoint_gives hsp hctx1.ctx htr.imports g2
  have hds2 := DStep.of_parse hctx1.ok hctx1.off hst2
  have hctx2 := hctx1.step hds2
  have hw2 := hctx2.wf
  obtain ⟨⟨c₃, v⟩, s₃, g3, k3⟩ := AM.bind_ok k2
  obtain ⟨hst3, cC₃, vC, hgv, hc3, hvr⟩ := viewAdd_run hsp _ hctx2
    ((he.ext hst1.ext (nsWF_of_StateOK hst1.ok.state)).ext hds2.ext hw2) (hc1.ext hds2.ext)
    (viewKeys_rel (denoteN_ext hh (hst1.trans hds2).ext) hlr) (HMRel.empty _ _) g3
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
  have hw3 := nsWF_of_StateOK hst3.ok.state
  refine ⟨(hst1.trans hds2).trans hst3, { cC₃ with views := cC₃.views.insert hC vC }, vC, v, ?_,
    { hc3 with views := hc3.views.insert hw3 (denoteN_ext hh ((hst1.trans hds2).trans hst3).ext) hvr },
    by simp, hvr⟩
  unfold ConLeche.Driver.viewOf
  simp only [hmissC]
  refine hgt.bind ?_
  simp only [he.rd]
  rw [htr.isModule] at hgl
  exact hgl.bind (hgv.bind (ModelIO.gives_pure _ _))

/-- con-leche: ConLeche/Driver/Reach.lean:359-364 locate — **`y` located in `h`'s view**,
upstream's, the search counted on both sides. -/
theorem locate_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {h y : NIdx} {hC yC : ConLeche.Name} {o : Option ConRon.Arena.Modular.Spot} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hh : denoteN s.store.ns h = some hC) (hy : denoteN s.store.ns y = some yC)
    (hrun : ConRon.Arena.Modular.locate (modelFs F) pk sp env c h y s = .ok ((c', o), s')) :
    DStep s s' ∧ ∃ cC' oC, ModelIO.Gives (ConLeche.Driver.locate envC cC hC yC) F (cC', .ok oC) ∧
      CacheRel s'.store c' cC' ∧ Option.Rel (SpotRel s'.store) o oC := by
  unfold ConRon.Arena.Modular.locate at hrun
  obtain ⟨c₁, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, cC₁, vC, v, hgv, hc1, hv, hvr⟩ := viewOf_run hsp hctx he hc hh g1
  obtain ⟨o', s₂, g2, k2⟩ := AM.bind_ok k1
  have hva : ConRon.Arena.Modular.viewAt { c₁ with searches := c₁.searches + 1 } h y s₁ =
      .ok (v[y]?, s₁) := by
    simp [ConRon.Arena.Modular.viewAt, hv]; rfl
  rw [hva] at g2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok g2
  obtain ⟨hv', rfl⟩ := AM.pure_ok k2
  simp only [Prod.mk.injEq] at hv'
  obtain ⟨rfl, rfl⟩ := hv'
  refine ⟨hst1, { cC₁ with searches := cC₁.searches + 1 }, vC[yC]?, ?_,
    { hc1 with searches := by simp [hc1.searches] },
    hvr.get (nsWF_of_StateOK hst1.ok.state) (denoteN_ext hy hst1.ext)⟩
  unfold ConLeche.Driver.locate
  refine hgv.bind ?_
  exact ModelIO.gives_pure _ _

end ConRon.Bridge.Modular
