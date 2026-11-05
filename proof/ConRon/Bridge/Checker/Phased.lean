/-
# `ConRon.Bridge.Checker.Phased` — Theorem 1 at the fold the driver runs

`Arena.PooledAccepts` is the binary's two phases: phase A, then job lists, one per worker,
covering the jobs, each accepted from the phase-A state's worker.  A worker's history is
invisible by construction (`Bridge/Checker/Frame.lean`'s `checkJobList_worker_each`): every
job of a list is an accept from the worker itself.  So the jobs are facts about one state.
The block jobs among them are `Arena.installFold_bridge`'s premise, which gives
`PhaseA` and the pending records' relation; the value checks are
`Arena.checkPending_prefix` at their own prefix environments, and `PhaseA.foldlM` pays
them.
-/
module

import ConRon.Bridge.Checker.Split
public import ConRon.Arena.Pooled
public import ConRon.Bridge.Checker.Frame
public import ConRon.Bridge.Checker.Decl
public import ConRon.Bridge.Checker.Hyp

public section

open ConLeche ConRon.Arena

namespace ConRon.Bridge

private theorem listRel_exists_left {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil, _, hy => absurd hy (by simp)
  | _, _, .cons hab hr, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨x, hx, h⟩ := listRel_exists_left hr y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:281-292 jobOrder — the merge drops no job
it has and reaches every job from its positions on. -/
private theorem jobOrderGo_mem (pend : Array PendingCheck) (D : Array BlockCheck) :
    ∀ (k a b : Nat) (acc : Array Job), (pend.size - a) + (D.size - b) = k →
      (∀ j ∈ acc, j ∈ jobOrderGo pend D a b acc) ∧
      (∀ i, a ≤ i → i < pend.size → (false, i) ∈ jobOrderGo pend D a b acc) ∧
      (∀ i, b ≤ i → i < D.size → (true, i) ∈ jobOrderGo pend D a b acc) := by
  intro k
  induction k with
  | zero =>
    intro a b acc hk
    have ha : ¬ a < pend.size := by omega
    have hb : ¬ b < D.size := by omega
    rw [jobOrderGo]
    simp only [ha, hb, ↓reduceDIte, ↓reduceIte]
    exact ⟨fun _ h => h, fun i _ _ => by omega, fun i _ _ => by omega⟩
  | succ k ih =>
    intro a b acc hk
    have stepA : a < pend.size →
        ((∀ j ∈ acc, j ∈ jobOrderGo pend D (a + 1) b (acc.push (false, a))) ∧
         (∀ i, a ≤ i → i < pend.size → (false, i) ∈ jobOrderGo pend D (a + 1) b (acc.push (false, a))) ∧
         (∀ i, b ≤ i → i < D.size → (true, i) ∈ jobOrderGo pend D (a + 1) b (acc.push (false, a)))) := by
      intro ha
      obtain ⟨h1, h2, h3⟩ := ih (a + 1) b (acc.push (false, a)) (by omega)
      refine ⟨fun j hj => h1 j (by simp [hj]), fun i hi hs => ?_, h3⟩
      by_cases hia : i = a
      · subst hia; exact h1 _ (by simp)
      · exact h2 i (by omega) hs
    have stepB : b < D.size →
        ((∀ j ∈ acc, j ∈ jobOrderGo pend D a (b + 1) (acc.push (true, b))) ∧
         (∀ i, a ≤ i → i < pend.size → (false, i) ∈ jobOrderGo pend D a (b + 1) (acc.push (true, b))) ∧
         (∀ i, b ≤ i → i < D.size → (true, i) ∈ jobOrderGo pend D a (b + 1) (acc.push (true, b)))) := by
      intro hb
      obtain ⟨h1, h2, h3⟩ := ih a (b + 1) (acc.push (true, b)) (by omega)
      refine ⟨fun j hj => h1 j (by simp [hj]), h2, fun i hi hs => ?_⟩
      by_cases hib : i = b
      · subst hib; exact h1 _ (by simp)
      · exact h3 i (by omega) hs
    rw [jobOrderGo]
    split
    · rename_i ha
      split
      · rename_i hb
        split
        · exact stepB hb
        · exact stepA ha
      · exact stepA ha
    · rename_i ha
      split
      · rename_i hb
        exact stepB hb
      · omega

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:281-292 jobOrder — every record's check is a
job. -/
theorem mem_jobOrder_false {pend : Array PendingCheck} {D : Array BlockCheck} {i : Nat}
    (h : i < pend.size) : (false, i) ∈ (jobOrder pend D).toList := by
  have := (jobOrderGo_mem pend D _ 0 0 (Array.mkEmpty (pend.size + D.size)) rfl).2.1 i (by omega) h
  simpa [jobOrder] using this

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:281-292 jobOrder — every block's check is a
job. -/
theorem mem_jobOrder_true {pend : Array PendingCheck} {D : Array BlockCheck} {i : Nat}
    (h : i < D.size) : (true, i) ∈ (jobOrder pend D).toList := by
  have := (jobOrderGo_mem pend D _ 0 0 (Array.mkEmpty (pend.size + D.size)) rfl).2.2 i (by omega) h
  simpa [jobOrder] using this

/-- con-leche: Main.lean:289-316 checkPool — **the pooled fold is the pure fold's accept**.
From an accepting `Arena.PooledAccepts`, con-leche's `checkDeclsPure` accepts the denoted
stream at the environment `fe'` denotes in the phase-A state `s'`. -/
theorem Arena.pooledAccepts_bridge
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {fe' : IFEnv}
    {s s' : AState}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    (hpp : PersPinSets pins)
    (hok : FoldOK Env.empty (mkIFEnv IEnv.empty) s)
    (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hden : denoteDecls s.store ds.toList = some dsP)
    (hrun : Arena.PooledAccepts .verified pins ds s fe' s') :
    ∃ env' F', denoteFEnv s'.store fe' = some env' ∧
      ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F') pinsP dsP = .ok env' := by
  have hnd0 : NodupNames Env.empty := List.nodup_nil
  obtain ⟨n, pend, D, parts, hA, hcov, -, hw⟩ := hrun
  -- every job, from the worker
  have hjob : ∀ j ∈ (jobOrder pend D).toList, ∃ t,
      runJob .verified pins fe' pend D j s'.worker = .ok (.ok (), t) := by
    intro j hj
    obtain ⟨w, hwm, hjw⟩ := hcov j hj
    obtain ⟨s₃, hrun3⟩ := hw w hwm
    exact checkJobList_worker_each hrun3 j hjw
  have hblocks : ∀ b ∈ D.toList, ∃ t, blockCheck .verified pins b s'.worker = .ok ((), t) := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hb)
    obtain ⟨t, ht⟩ := hjob _ (mem_jobOrder_true hi)
    obtain ⟨b', hb', hc⟩ := runJob_block rfl ht
    simp only [Array.getElem?_eq_getElem hi, Option.some.injEq] at hb'
    subst hb'
    exact ⟨t, hc⟩
  obtain ⟨env₁, pendP, hok₁, -, hPA, hrel, -, -⟩ :=
    Arena.installFold_bridge hk hind hpp ds.toList dsP Env.empty 0 n
      (mkIFEnv IEnv.empty) fe' #[] pend #[] D [] s s' hok hnd0 hpins hpd hden .nil hA hblocks
  simp only [List.nil_append] at hrel
  -- the worker over phase A's final store
  have hwf := hok₁.check.state.wf
  have hxw : PExt s'.store s'.worker.store := PExt.dropScratch hwf
  have hokw : FoldOK env₁ fe' s'.worker :=
    hok₁.pmono hxw (EStore.dropScratch_spec hwf).1 rfl rfl
  have hnd₁ := hPA.nodup hnd0
  have hall : ∀ p ∈ pendP, ∃ F,
      ConLeche.checkValueGroup (ConLeche.fueledOps .verified F) p.1 p.2 = .ok () := by
    intro p hp
    obtain ⟨pc, hpc, hR⟩ := listRel_exists_left hrel p hp
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hpc)
    obtain ⟨t, ht⟩ := hjob _ (mem_jobOrder_false hi)
    obtain ⟨pc', hpc', hc⟩ := runJob_pending rfl ht
    simp only [Array.getElem?_eq_getElem hi, Option.some.injEq] at hpc'
    subst hpc'
    have hRw := hR.mono hxw ⟨[], rfl⟩ (TblExt.of_eq rfl)
    exact Arena.checkPending_prefix hk hokw hRw.pers hnd₁ rfl hRw.envWF hRw.prefix_find?
      hRw.prefix_findTable? hRw.kind hRw.cv hRw.jv hRw.wsty hRw.wsjv hc
  obtain ⟨F, hF⟩ := hPA.foldlM hall
  exact ⟨env₁, F, hok₁.denote, hF F (Nat.le_refl _)⟩

end ConRon.Bridge
