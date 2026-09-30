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
import ConRon.Arena.Pooled

open ConLeche ConRon.Arena

namespace ConRon.Bridge

/-! ## The pool (task #97-P5-POOL)

`Arena.PooledAccepts` is the binary's phase B: record lists, one per worker,
covering the pending records, each accepted from the phase-A state's worker.
Theorem 1 needs no argument that a worker's history is invisible: every
list is a `checkPendingList` run from `s'.worker`, hence (by
`Arena.checkPendingList_worker`) one from the phase-A state, and
`Arena.checkPendingList_bridge` — stated for ANY list related to its pure
records — turns it into con-leche's pure accept of each of its records, at
that record's own prefix environment.  Covering is all `PhaseA.foldlM` then
asks for. -/

private theorem listRel_exists_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel R xs ys → ∀ x ∈ xs, ∃ y, R x y
  | _, _, .nil, _, hx => absurd hx (by simp)
  | _, _, .cons hab hr, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hab⟩
    · exact listRel_exists_right hr x hx

private theorem listRel_exists_left {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil, _, hy => absurd hy (by simp)
  | _, _, .cons hab hr, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨x, hx, h⟩ := listRel_exists_left hr y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

private theorem listRel_total {α β : Type} {R : α → β → Prop} :
    ∀ (w : List α), (∀ x ∈ w, ∃ y, R x y) → ∃ wy, ListRel R w wy
  | [], _ => ⟨[], .nil⟩
  | a :: as, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨bs, hbs⟩ := listRel_total as (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨b :: bs, .cons hb hbs⟩

/-- A related list can be chosen to contain any one partner of any one of
its elements. -/
private theorem listRel_through {α β : Type} {R : α → β → Prop} :
    ∀ (w : List α), (∀ x ∈ w, ∃ y, R x y) → ∀ {x y}, x ∈ w → R x y →
      ∃ wy, ListRel R w wy ∧ y ∈ wy
  | [], _, _, _, hx, _ => absurd hx (by simp)
  | a :: as, h, x, y, hx, hxy => by
    have has : ∀ z ∈ as, ∃ y, R z y := fun z hz => h z (List.mem_cons_of_mem _ hz)
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨bs, hbs⟩ := listRel_total as has
      exact ⟨y :: bs, .cons hxy hbs, List.mem_cons_self⟩
    · obtain ⟨b, hb⟩ := h a List.mem_cons_self
      obtain ⟨wy, hwy, hy⟩ := listRel_through as has hx hxy
      exact ⟨b :: wy, .cons hb hwy, List.mem_cons_of_mem _ hy⟩

/-- con-leche: Main.lean:289-316 checkPool — **the pooled fold is the pure
fold's accept**.  From an accepting `Arena.PooledAccepts` — phase A, and
record lists covering the pending records, each accepted by a worker —
con-leche's `checkDeclsPure` accepts the denoted stream at the environment
`fe'` denotes in the phase-A state `s'`.  `installThenCheckPhased_bridge`'s
hypotheses verbatim; phase B is the per-list `checkPendingList_bridge`,
gathered record by record. -/
theorem Arena.pooledAccepts_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {fe' : IFEnv}
    {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hpp : PersPinSets pins)
    (hok : FoldOK μ Env.empty (mkIFEnv IEnv.empty) s)
    (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hden : denoteDecls s.store ds.toList = some dsP)
    (hrun : Arena.PooledAccepts μ pins ds s fe' s') :
    ∃ env' F', denoteFEnv s'.store fe' = some env' ∧
      ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F') pinsP dsP = .ok env' := by
  have hnd0 : NodupNames Env.empty := List.nodup_nil
  obtain ⟨n, pend, parts, hA, hcov, hsub, hw⟩ := hrun
  obtain ⟨env₁, pendP, hok₁, -, hPA, hrel, -, hc₁⟩ :=
    Arena.annotFold_bridge hμ hk hind hpp ds.toList dsP Env.empty 0 n
      (mkIFEnv IEnv.empty) fe' #[] pend [] s s' hok hnd0 hpins hpd hden .nil hA
  simp only [List.nil_append] at hrel
  have hc : pend.toList ≠ [] → s'.caches = Caches.empty := by
    intro hne
    by_cases hds : ds.toList = []
    · exfalso
      rw [hds] at hden
      simp only [denoteDecls, Option.some.injEq] at hden
      subst hden
      cases hPA
      exact hne (ListRel.nil_right hrel)
    · exact hc₁ hds
  have hall : ∀ p ∈ pendP, ∃ F,
      ConLeche.checkValueGroup (ConLeche.fueledOps μ F) p.1 p.2 = .ok () := by
    intro p hp
    obtain ⟨pc, hpc, hR⟩ := listRel_exists_left hrel p hp
    obtain ⟨w, hwm, hpcw⟩ := hcov pc hpc
    have hwsub := hsub w hwm
    obtain ⟨wP, hwP, hpw⟩ := listRel_through w
      (fun x hx => listRel_exists_right hrel x (hwsub x hx)) hpcw hR
    have hcw : w ≠ [] → s'.caches = Caches.empty := fun _ =>
      hc (List.ne_nil_of_mem (hwsub pc hpcw))
    obtain ⟨s₃, hrun3⟩ := hw w hwm
    obtain ⟨s₄, hB'⟩ := Arena.checkPendingList_worker hcw hrun3
    obtain ⟨-, -, hallw⟩ :=
      Arena.checkPendingList_bridge hμ hk (hPA.nodup hnd0) w wP s' s₄ hok₁ hwP hcw hB'
    exact hallw p hpw
  obtain ⟨F, hF⟩ := hPA.foldlM hall
  exact ⟨env₁, F, hok₁.denote, hF F (Nat.le_refl _)⟩

end ConRon.Bridge
