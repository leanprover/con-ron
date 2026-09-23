/-
# `ConRon.Bridge.Checker.Phased` — Theorem 1 at the fold the driver runs

**Task #97-P5-Driver.**  `Arena/Phased.lean`'s `installThenCheckPhased` is the
twin of `arena::checker::check_decls_phased`, the Rust driver's sequential
projection: phase A, then phase B on one WORKER whose state is the phase-A
state with the scratch tier emptied and the memos and caches fresh
(`AState.worker`), the phase-A state handed back at the end.

It is `installThenCheck` in everything Theorem 1 asks about, because
`annotFold_bridge` already says phase A leaves the caches empty whenever it
installed anything — the fact `installThenCheck_bridge` itself uses to enter
phase B — and `Arena.checkPendingList_worker` turns a worker's accepting walk
into the phase-A state's.  So this module adds no argument: it is
`installThenCheck_bridge` with phase B routed through that equation, and its
one change of letter is the state the environment denotes in — the PHASE-A
state `s'` the driver's fold returns, where `installThenCheck_bridge` names
the state phase B ended in.
-/
import ConRon.Bridge.Checker.Split
import ConRon.Arena.Phased

open ConLeche ConRon.Arena

namespace ConRon.Bridge

/-- An `AM` bind whose first half is known to accept is its second half at
the first half's result (`Capstone.lean`'s `AM.bind_of_ok`, which this tier
cannot import). -/
private theorem bind_of_ok {α β : Type} {x : AM α} {f : α → AM β} {s s₁ : AState}
    {a : α} (h : x s = .ok (a, s₁)) : (x >>= f) s = f a s₁ := by
  rw [AM.bind_apply, h]; rfl

/-- con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls — **the
driver's fold is one accept with `installThenCheck`, and with the pure
fold**.  From an accepting `installThenCheckPhased` run: an accepting
`installThenCheck` run from the same state, and con-leche's `checkDeclsPure`
accepting the denoted stream at the environment `fe'` denotes in the
returned (phase-A) state.

`Arena.installThenCheck_bridge`'s proof, phase B routed through
`Arena.checkPendingList_worker`; its hypotheses verbatim. -/
theorem Arena.installThenCheckPhased_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {fe' : IFEnv}
    {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hpp : PersPinSets pins)
    (hok : FoldOK μ Env.empty (mkIFEnv IEnv.empty) s)
    (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hden : denoteDecls s.store ds.toList = some dsP)
    (hrun : Arena.installThenCheckPhased μ pins ds s = .ok (.ok fe', s')) :
    (∃ s'', Arena.installThenCheck μ pins ds s = .ok (.ok fe', s'')) ∧
      ∃ env' F', denoteFEnv s'.store fe' = some env' ∧
        ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F') pinsP dsP
          = .ok env' := by
  have hnd0 : NodupNames Env.empty := List.nodup_nil
  simp only [Arena.installThenCheckPhased] at hrun
  obtain ⟨r1, s₁, hA, hrest⟩ := AM.bind_ok hrun
  cases r1 with
  | error e =>
    obtain ⟨hbad, -⟩ := AM.pure_ok hrest
    exact absurd hbad (by simp)
  | ok p =>
    obtain ⟨n, fe₁, pend⟩ := p
    obtain ⟨env₁, pendP, hok₁, -, hPA, hrel, hnil, hc₁⟩ :=
      Arena.annotFold_bridge hμ hk hind hpp ds.toList dsP Env.empty 0 n
        (mkIFEnv IEnv.empty) fe₁ #[] pend [] s s₁ hok hnd0 hpins hpd hden .nil hA
    simp only [List.nil_append] at hrel
    obtain ⟨r2, s₂, hB, hrest2⟩ := AM.bind_ok hrest
    cases r2 with
    | error e =>
      obtain ⟨hbad, -⟩ := AM.pure_ok hrest2
      exact absurd hbad (by simp)
    | ok u =>
      obtain ⟨he, hs'⟩ := AM.pure_ok hrest2
      simp only [Except.ok.injEq] at he
      -- the worker's walk hands the phase-A state back
      have hW : ∃ s₃, Arena.checkPendingList μ fe₁ pend.toList s₁.worker
          = .ok (.ok (), s₃) ∧ s₂ = s₁ := by
        simp only [Arena.checkPendingWorker] at hB
        split at hB
        · rename_i r s₃ hw
          simp only [Except.ok.injEq, Prod.mk.injEq] at hB
          obtain ⟨hr, hs⟩ := hB
          subst hr
          exact ⟨s₃, hw, hs.symm⟩
        · exact absurd hB (by simp)
      obtain ⟨s₃, hw, hs₂⟩ := hW
      have hc : pend.toList ≠ [] → s₁.caches = Caches.empty := by
        intro hne
        by_cases hds : ds.toList = []
        · exfalso
          rw [hds] at hden
          simp only [denoteDecls, Option.some.injEq] at hden
          subst hden
          cases hPA
          exact hne (ListRel.nil_right hrel)
        · exact hc₁ hds
      obtain ⟨s₄, hB'⟩ := Arena.checkPendingList_worker hc hw
      obtain ⟨hok₂, -, hall⟩ :=
        Arena.checkPendingList_bridge hμ hk (hPA.nodup hnd0) pend.toList pendP s₁ s₄
          hok₁ hrel hc hB'
      obtain ⟨F, hF⟩ := hPA.foldlM hall
      have e1 : fe' = fe₁ := by first | exact he | exact he.symm
      have e2 : s' = s₁ := by rw [← hs₂]; first | exact hs' | exact hs'.symm
      rw [e1, e2]
      refine ⟨⟨s₄, ?_⟩, env₁, F, hok₁.denote, hF F (Nat.le_refl _)⟩
      simp only [Arena.installThenCheck]
      rw [bind_of_ok hA]
      dsimp only
      rw [bind_of_ok hB']
      rfl

end ConRon.Bridge
