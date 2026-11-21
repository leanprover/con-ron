/-
# `ConRon.Bridge.Modular.ReachStored` — the reach's stored names and clash rule, Theorem 1 (task #166)

The names a record stores, against the importer's copies (`storedNamesOk_run`, one name at a time:
`storedNameOk_step`), and the clashing names' copies as reads (`clashPartners_run`).  Run style.
-/
module

public import ConRon.Bridge.Modular.ReachCapture

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM)
open ConLeche.Frontend.Olean (Region Roots OLeanLevel ModFiles CEntryF CKindF Copy)

/-- A cache with its completions replaced. -/
theorem CacheRel.withLocated {st : EStore} {c : ConRon.Arena.Modular.ReachCache}
    {cC : ConLeche.Driver.ReachCache} (h : CacheRel st c cC)
    {L : Std.HashMap NIdx ConRon.Arena.Modular.Spot} {LC : Std.HashMap ConLeche.Name ConLeche.Driver.Spot}
    (hL : HMRel (SpotRel st) st L LC) :
    CacheRel st { c with located := L } { cC with located := LC } :=
  ⟨h.tables, h.looks, h.parts, h.recBlocks, h.views, hL, h.completed, h.pending, h.partners,
    h.searches⟩

/-- con-leche: ConLeche/Driver/Reach.lean:533-558 storedNamesOk — **one stored name, against the
importer's copies**: the twin's step accepting, upstream's run of the names from it on is the run
of the rest from the related cache. -/
theorem storedNameOk_step {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {h : NIdx} {hC : ConLeche.Name} {n : NIdx} {nC : ConLeche.Name} {nsC : List ConLeche.Name}
    {c c₁ : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache} {s s₁ : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hh : denoteN s.store.ns h = some hC) (hn : denoteN s.store.ns n = some nC)
    (g1 : ConRon.Arena.Modular.storedNameOk (modelFs F) pk sp env c h n s = .ok (c₁, s₁)) :
    DStep s s₁ ∧ ∃ cC₁, CacheRel s₁.store c₁ cC₁ ∧
      ∀ R, ModelIO.Gives (ConLeche.Driver.storedNamesOk envC cC₁ hC nsC) F R →
        ModelIO.Gives (ConLeche.Driver.storedNamesOk envC cC hC (nC :: nsC)) F R := by
  have hw := hctx.wf
  unfold ConRon.Arena.Modular.storedNameOk at g1
  rw [ConLeche.Driver.storedNamesOk]
  rcases optRel_cases (importerSpot_rel hw hctx.nulls he hn) with ⟨i1, i2⟩ |
      ⟨⟨i, sq⟩, ⟨iC, sqC⟩, i1, i2, ⟨-, hsq⟩⟩
  · rw [i1] at g1
    rw [i2]
    dsimp only at g1 ⊢
    rcases optRel_cases (hc.located.get hw hn) with ⟨l1, l2⟩ | ⟨sq, sqC, l1, l2, hsq⟩
    · simp only [ConRon.Arena.Modular.locatedAt, l1] at g1
      simp only [l2]
      have hk : PKRel s.store (ConRon.Arena.Modular.privKey h)
          (⟨hC, .private⟩ : ConLeche.Driver.PartKey) := ⟨hh, rfl⟩
      obtain ⟨c₀, t₀, f1, r1⟩ := AM.bind_ok g1
      obtain ⟨hst0, cC₀, lC, l, hgl, hc0, hl, hlr⟩ := lookOf_run hsp hctx he hc hk f1
      obtain ⟨o, t₁, f2, r2⟩ := AM.bind_ok r1
      rw [lookAt_eq hl] at f2
      obtain ⟨ho, e2⟩ := AM.pure_ok f2
      subst ho e2
      have hq := hlr.get (nsWF_of_StateOK hst0.ok.state) (denoteN_ext hn hst0.ext)
      rcases optRel_cases hq with ⟨q1, -⟩ | ⟨q, qC, q1, q2, q3⟩
      · rw [q1] at r2; am_never r2
      rw [q1] at r2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
      have hw0 := nsWF_of_StateOK hst0.ok.state
      have hL := hc0.located.insert hw0 (denoteN_ext hn hst0.ext)
        (a := (⟨ConRon.Arena.Modular.privKey h, q⟩ : ConRon.Arena.Modular.Spot))
        (b := (⟨⟨hC, .private⟩, qC⟩ : ConLeche.Driver.Spot)) ⟨hk.ext hst0.ext, q3⟩
      refine ⟨hst0, { cC₀ with located := cC₀.located.insert nC ⟨⟨hC, .private⟩, qC⟩ },
        hc0.withLocated hL, fun R hR => hgl.bind ?_⟩
      simp only [q2]
      exact hR
    · simp only [ConRon.Arena.Modular.locatedAt, l1] at g1
      simp only [l2]
      have hmods := nidx_beq_iff hw hsq.1.1 hh
      by_cases hm : (sq.part.mod == h) = true
      · simp only [hm, ↓reduceIte] at g1
        obtain ⟨rfl, rfl⟩ := AM.pure_ok g1
        rw [hmods] at hm
        simp only [hm, ↓reduceIte]
        exact ⟨DStep.refl hctx.ok hctx.off, cC, hc, fun R hR => hR⟩
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at g1
        am_never g1
  · rw [i1] at g1
    rw [i2]
    dsimp only at g1 ⊢
    have hmods := nidx_beq_iff hw hsq.1.1 hh
    by_cases hm : (sq.part.mod == h) = true
    · simp only [hm, ↓reduceIte] at g1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok g1
      rw [hmods] at hm
      simp only [hm, ↓reduceIte]
      exact ⟨DStep.refl hctx.ok hctx.off, cC, hc, fun R hR => hR⟩
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at g1
      am_never g1

/-- con-leche: ConLeche/Driver/Reach.lean:533-558 storedNamesOk — **the names a record stores,
against the importer's copies**: upstream's accept, the caches related after. -/
theorem storedNamesOk_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {h : NIdx} {hC : ConLeche.Name} :
    ∀ (ns : List NIdx) {nsC : List ConLeche.Name}
      {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache} {s s' : AState},
      RCtx pk s → EnvRel sp s.store env envC → CacheRel s.store c cC →
      denoteN s.store.ns h = some hC → ListRel (NR s.store) ns nsC →
      ConRon.Arena.Modular.storedNamesOk (modelFs F) pk sp env h c ns s = .ok (c', s') →
      DStep s s' ∧ ∃ cC', ModelIO.Gives (ConLeche.Driver.storedNamesOk envC cC hC nsC) F (cC', .ok ()) ∧
        CacheRel s'.store c' cC'
  | [], _, c, c', cC, s, s', hctx, _, hc, _, .nil, hrun => by
    rw [ConRon.Arena.Modular.storedNamesOk] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨DStep.refl hctx.ok hctx.off, cC, by rw [ConLeche.Driver.storedNamesOk]; exact ModelIO.gives_pure _ _, hc⟩
  | n :: ns, _, c, c', cC, s, s', hctx, he, hc, hh, .cons hn hns, hrun => by
    rw [ConRon.Arena.Modular.storedNamesOk] at hrun
    obtain ⟨c₁, s₁, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hst1, cC₁, hc1, hstep⟩ := storedNameOk_step hsp hctx he hc hh hn g1
    have hctx1 := hctx.step hst1
    obtain ⟨hst2, cC', hg2, hc'⟩ := storedNamesOk_run hsp ns hctx1 (he.ext hst1.ext hctx1.wf) hc1
      (denoteN_ext hh hst1.ext) (ListRel.mono' (fun _ _ h => denoteN_ext h hst1.ext) hns) k1
    exact ⟨hst1.trans hst2, cC', hstep _ hg2, hc'⟩

end ConRon.Bridge.Modular
