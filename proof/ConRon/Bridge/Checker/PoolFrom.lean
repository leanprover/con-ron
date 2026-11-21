/-
# `ConRon.Bridge.Checker.PoolFrom` — a worker's own jobs passing are a run from its context

The check phase of a modular worker (`Arena/OleanJobs.lean`'s `PooledOleanAcceptsFromJ` at no
solution): the index of the context's records followed by the own records, and job lists
claiming the own positions `start ≤ t < ds.size` only.  `Arena.pooledOleanAcceptsFrom_bridge`:
every own job passing is a run of con-leche's pure fold (`PureRun`) of the own records, filled,
from the environment of the context to that of all the records — upstream's
`checkDecls_of_jobs_from` over the pure fold, as `WorkerAccepted` states it.

`Bridge/Checker/Pooled.lean`'s argument at a prefix predicate (`pooled_foldP`) with the
positions shifted by `start`: the context's records are never checked, so the induction starts
at `start` from what the context gives (`FromOK.start`: its environment well formed, its names
distinct, both hypotheses of the headline), and each own job extends it (`FromOK.step`, a job's
accept at a well-formed prefix being the fold's step, `oleanJob_spec`).
-/
module

public import ConRon.Bridge.Checker.Pool
public import ConLeche.Verify.Cached.PureRun
public import ConLeche.Verify.Driver.Oleans
import all ConLeche.Verify.Driver.Oleans
import all ConLeche.Verify.Cached.StreamIndex
import all ConRon.Bridge.Checker.PooledOleans
import ConLeche.Semantics.DeclWF
import ConRon.Bridge.Checker.Install

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The prefixes from `start` -/

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:461 jobs_run_from — **the prefix of length
`k` from `start`**: its environment well formed, its names distinct, and its records past `start`
a run of the pure fold from the environment of the first `start`. -/
@[expose] def FromOK (pinsP : List NatOpPinSet) (dsP : List Declaration) (start k : Nat) : Prop :=
  EnvWF (streamEnv (dsP.take k)) ∧
    ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup ∧
    PureRun pinsP ((dsP.take k).drop start) (streamEnv (dsP.take start)) (streamEnv (dsP.take k))

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:461 jobs_run_from — the empty run at
`start`. -/
theorem FromOK.start {pinsP : List NatOpPinSet} {dsP : List Declaration} {start : Nat}
    (hwf : EnvWF (streamEnv (dsP.take start)))
    (hnd : ((ConLeche.Cached.recsConsts (dsP.take start)).map (·.name)).Nodup) :
    FromOK pinsP dsP start start := by
  refine ⟨hwf, hnd, ?_⟩
  rw [List.drop_eq_nil_of_le (by rw [List.length_take]; exact Nat.min_le_left _ _)]
  exact .nil _

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:461 jobs_run_from — **the step**: record `k`
(at or past `start`) accepted at the prefix's environment extends the run. -/
theorem FromOK.step {pinsP : List NatOpPinSet} {dsP : List Declaration} {start k : Nat}
    (hpush : KernelPushes pinsP) (hs : start ≤ k) (hk : k < dsP.length)
    (h : FromOK pinsP dsP start k) {F : Nat} {env' : Env}
    (hd : checkDecl .verified (fueledOps .verified F) pinsP (streamEnv (dsP.take k)) dsP[k] =
      .ok env') :
    FromOK pinsP dsP start (k + 1) := by
  obtain ⟨hwf, hnd, hrun⟩ := h
  obtain ⟨henv', hndD, hfr⟩ := hpush hd
  obtain ⟨hstream, hnd'⟩ := prefix_step hk henv' hndD hfr hnd
  refine ⟨hstream ▸ ConLeche.Semantics.checkDecl_envWF hwf hd, hnd', ?_⟩
  have hdrop : (dsP.take (k + 1)).drop start = (dsP.take k).drop start ++ [dsP[k]] := by
    rw [take_succ_eq hk, List.drop_append_of_le_length (by simp; omega)]
  rw [hdrop, hstream]
  exact hrun.append (.cons ⟨F, hd⟩ (.nil _))

/-! ## The jobs, shifted by `start` -/

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:461-484 parWorker — a worker's chain of jobs at or
past `start`, renumbered from `start`. -/
theorem jobChain_shift {σ : Type} {Run : Nat → σ → σ → Prop} {start : Nat} :
    ∀ (l : List Nat) (w : σ), (∀ t ∈ l, start ≤ t) → JobChain Run w l →
      JobChain (fun j => Run (start + j)) w (l.map (· - start))
  | [], w, _, _ => .nil w
  | t :: l, w, hl, .cons hr hrest => by
    have ht : start + (t - start) = t := by have := hl t (List.mem_cons_self ..); omega
    exact .cons (by rw [ht]; exact hr)
      (jobChain_shift l _ (fun u hu => hl u (List.mem_cons_of_mem _ hu)) hrest)

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:461-484 parWorker — claims at or past `start`,
increasing, stay increasing renumbered. -/
theorem pairwise_shift {start : Nat} :
    ∀ (l : List Nat), (∀ t ∈ l, start ≤ t) → l.Pairwise (· < ·) →
      (l.map (· - start)).Pairwise (· < ·)
  | [], _, _ => .nil
  | t :: l, hl, hp => by
    rw [List.pairwise_cons] at hp
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, pairwise_shift l
      (fun u hu => hl u (List.mem_cons_of_mem _ hu)) hp.2⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
    have h1 := hp.1 u hu
    have h2 := hl u (List.mem_cons_of_mem _ hu)
    have h3 := hl t (List.mem_cons_self ..)
    show t - start < u - start
    omega

/-! ## The pool from `start` -/

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:527 checkDecls_of_jobs_from — **the own
jobs of an `--olean` worker passing**: from a context whose environment is well formed with
distinct names, every job at or past `start` passing is a run of the pure fold of the FILLED
records past `start` from the context's environment. -/
theorem pooled_from_oleans
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {F : FS}
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {sp : ConLeche.Frontend.Olean.Roots}
    {values : Array ConRon.Arena.Frontend.Olean.ModRef}
    {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    {ds : Array IDeclaration} {dsP : List Declaration} {I : IStreamIndex} {s₀ s₁ : AState}
    (hrec : RecordSpec pins pinsP) (hpush : KernelPushes pinsP) (hpp : PersPinSets pins)
    (hst : StateOK s₁) (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁)
    (hpins : PinsDenote s₁.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x) (hlen : dsP.length = ds.size)
    (hden : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s₁.store ds[i] = some dsP[i])
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base)
    (hwf₀ : StoreWF s₀.store) (hoff₀ : s₀.store.scratchOn = false) (hx₀ : PExt s₀.store s₁.store)
    (hv₀ : Frontend.Olean.ValuesRel sp F s₀.store values valuesP)
    (hnu₀ : Frontend.Olean.NullsRel s₀.store pk) (hsp : sp.bare = sp)
    {start : Nat} (hsl : start ≤ ds.size)
    (hwfC : EnvWF (streamEnv (dsP.take start)))
    (hndC : ((ConLeche.Cached.recsConsts (dsP.take start)).map (·.name)).Nodup)
    (parts : List (List Nat))
    (hcov : ∀ t, start ≤ t → t < ds.size → ∃ w ∈ parts, t ∈ w)
    (hrng : ∀ w ∈ parts, ∀ t ∈ w, start ≤ t ∧ t < ds.size)
    (hinc : ∀ w ∈ parts, w.Pairwise (· < ·))
    (hacc : ∀ w ∈ parts, ∃ s'', checkOleanJobList (Frontend.Olean.modelFs F) pk sp values
      .verified pins I ds w {} s₁.worker = .ok (.ok (), s'')) :
    PureRun pinsP ((fillStream sp F valuesP dsP).drop start) (streamEnv (dsP.take start))
      (streamEnv (fillStream sp F valuesP dsP)) := by
  have hlenF : (fillStream sp F valuesP dsP).length = ds.size := by simp [fillStream, hlen]
  -- the fill changes neither the environments nor the names
  have htakeF : ∀ k, (fillStream sp F valuesP dsP).take k = (dsP.take k).map
      (ConLeche.Cached.fillDecl (fillRef (valueOf sp F valuesP))) := fun k => by
    simp [fillStream, List.map_take]
  have henvF : ∀ k, streamEnv ((fillStream sp F valuesP dsP).take k) = streamEnv (dsP.take k) := fun k => by
    rw [htakeF]; exact ConLeche.Cached.streamEnv_fill _ _ _
  have hrecsF : ∀ k, ConLeche.Cached.recsConsts ((fillStream sp F valuesP dsP).take k) =
      ConLeche.Cached.recsConsts (dsP.take k) := fun k => by
    rw [htakeF]
    unfold ConLeche.Cached.recsConsts
    generalize dsP.take k = l
    induction l with
    | nil => rfl
    | cons d l ih =>
      simp only [List.map_cons, List.flatMap_cons, ConLeche.Cached.declConstants_fillDecl, ih]
  have hspec : JobSpecAt (fun w => WorkerOK s₁ w.1 ∧ Frontend.Olean.CacheOK sp F valuesP w.2)
      (OleanRun (Frontend.Olean.modelFs F) pk sp values pins I ds) pinsP
      (fillStream sp F valuesP dsP) := oleanJob_spec hrec hpp hpinsOK hpersPins hpins hpd hden hI hpI hwf₀ hoff₀ hx₀
    hv₀ hnu₀ hsp
  have hfin := pooled_foldP
    (Inv := fun w => WorkerOK s₁ w.1 ∧ Frontend.Olean.CacheOK sp F valuesP w.2)
    (Run := fun j => OleanRun (Frontend.Olean.modelFs F) pk sp values pins I ds (start + j))
    (N := ds.size - start)
    (P := fun j => FromOK pinsP (fillStream sp F valuesP dsP) start (start + j))
    (by
      have h0 := FromOK.start (pinsP := pinsP) (dsP := fillStream sp F valuesP dsP)
        ((henvF start).symm ▸ hwfC) ((hrecsF start).symm ▸ hndC)
      simpa using h0)
    (fun {j} {w} {w'} hj hw hP hr => by
      have hk : start + j < (fillStream sp F valuesP dsP).length := by omega
      obtain ⟨hw', env', Fu, hFu⟩ := hspec hk hw hP.1 hP.2.1 hr
      exact ⟨hw', by
        rw [show start + (j + 1) = start + j + 1 by omega]
        exact FromOK.step hpush (by omega) hk hP hFu⟩)
    (fun {t} {w} {w'} hr => by obtain ⟨hk, -⟩ := hr; omega)
    (parts.map (·.map (· - start)))
    (fun j hj => by
      obtain ⟨wl, hwl, hm⟩ := hcov (start + j) (by omega) (by omega)
      exact ⟨_, List.mem_map_of_mem hwl, List.mem_map.mpr ⟨start + j, hm, by omega⟩⟩)
    (fun wl hwl => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hwl
      exact pairwise_shift w (fun t ht => (hrng w hw t ht).1) (hinc w hw))
    (fun wl hwl => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hwl
      obtain ⟨s'', h⟩ := hacc w hw
      exact ⟨(s₁.worker, {}), ⟨WorkerOK.start hst, Frontend.Olean.CacheOK.empty sp F valuesP⟩,
        jobChain_shift w _ (fun t ht => (hrng w hw t ht).1) (checkOleanJobList_chain w {} _ _ h)⟩)
  obtain ⟨-, -, hrun⟩ := hfin
  rw [show start + (ds.size - start) = (fillStream sp F valuesP dsP).length by omega, List.take_length, henvF] at hrun
  exact hrun

/-! ## Theorem 1 of the check phase from `start` -/

/-- con-leche: ConLeche/Verify/Driver/Oleans.lean:36 fillOf — the reference fill at the snapshot's
values is upstream's `fillOf`. -/
theorem fillRef_valueOf (sp : ConLeche.Frontend.Olean.Roots) (F : FS)
    (valuesP : Array ConLeche.Frontend.Olean.ModRef) :
    fillRef (valueOf sp F valuesP) = ConLeche.Driver.fillOf sp F valuesP := by
  funext e
  cases e <;> simp only [fillRef, ConLeche.Driver.fillOf, valueOf]

open ConRon.Arena.Frontend.Olean (OleanPins ModRef) in
/-- con-leche: ConLeche/Driver/CheckMain.lean:152-170 checkOleansG
con-leche: ConLeche/Verify/Driver/Worker.lean:234 WorkerAccepted — **THEOREM 1 at a worker's
check phase**: from an accepting `Arena.PooledOleanAcceptsFromJ` at no solution on a snapshot
`F`, over the context's records followed by the own records, claiming the own positions
(`start` the context's length), the own records with their theorems' values in place
(`fillOf` at the snapshot's module references) are a run of con-leche's pure fold from the
context's environment to the environment of the context and the own records:
`WorkerAccepted`'s `PureRun`.  What the context gives is a hypothesis: its environment well
formed (`hwfC`) and its names distinct (`hndC`), upstream's `worker_ctx`/`ImportOk` facts. -/
theorem Arena.pooledOleanAcceptsFrom_bridge
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {ctxC ownC : List Declaration} {s₀ s s' : AState}
    {I : IStreamIndex}
    {F : FS} {pk : OleanPins} {sp : ConLeche.Frontend.Olean.Roots}
    {values : Array ModRef} {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    (hst : DriverOK s) (hoff : s.store.scratchOn = false)
    (hpersPins : PersPins s) (hpp : PersPinSets pins) (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x) (hden : denoteDecls s.store ds.toList = some (ctxC ++ ownC))
    (hwf₀ : StoreWF s₀.store) (hoff₀ : s₀.store.scratchOn = false) (hx₀ : PExt s₀.store s.store)
    (hv₀ : Frontend.Olean.ValuesRel sp F s₀.store values valuesP)
    (hnu₀ : Frontend.Olean.NullsRel s₀.store pk) (hsp : sp.bare = sp)
    (hwfC : EnvWF (streamEnv ctxC))
    (hndC : ((ConLeche.Cached.recsConsts ctxC).map (·.name)).Nodup)
    (hrun : Arena.PooledOleanAcceptsFromJ (Frontend.Olean.modelFs F) pk sp values .verified pins
      none ctxC.length ds s I s') :
    PureRun pinsP (ownC.map (ConLeche.Cached.fillDecl (ConLeche.Driver.fillOf sp F valuesP)))
      (streamEnv ctxC)
      (streamEnv (ownC.map (ConLeche.Cached.fillDecl (ConLeche.Driver.fillOf sp F valuesP)))
        (streamEnv ctxC)) := by
  obtain ⟨parts, hidx, hcov, hrng, hinc, hacc⟩ := hrun
  obtain ⟨hst', hx, hp', -, hI, hpI⟩ :=
    buildIndex_run constsSpec tablesSpec hst hpersPins hoff hpd hden hidx
  have hx' := PExt.of_ext hx
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hden
  have hden' : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < (ctxC ++ ownC).length,
      Frontend.denoteDecl s'.store ds[i] = some (ctxC ++ ownC)[i] := fun i hi => by
    obtain ⟨hi', h⟩ := hget i (by simpa using hi)
    exact ⟨hi', Frontend.denoteDecl_ext hx (by simpa using h)⟩
  have hlen' : (ctxC ++ ownC).length = ds.size := by simpa using hlen
  have htake : (ctxC ++ ownC).take ctxC.length = ctxC := List.take_left' rfl
  have hacc' : ∀ w ∈ parts, ∃ s'', checkOleanJobList (Frontend.Olean.modelFs F) pk sp values
      .verified pins I ds w {} s'.worker = .ok (.ok (), s'') := fun w hw => by
    rw [checkOleanJobList_eq_J]; exact hacc w hw
  have h := pooled_from_oleans (recordSpec hk hind) (kernelPushes pinsP) hpp hst'.state
    (hst.pins.pmono hpersPins hx' hp') (hpersPins.mono hp') (PinsDenote.mono hx pins pinsP hpins)
    hpd hlen' hden' hI hpI hwf₀ hoff₀ (hx₀.trans hx') hv₀ hnu₀ hsp
    (by simp at hlen'; omega) (by rw [htake]; exact hwfC) (by rw [htake]; exact hndC)
    parts hcov hrng hinc hacc'
  rw [htake] at h
  have hd : (fillStream sp F valuesP (ctxC ++ ownC)).drop ctxC.length =
      ownC.map (ConLeche.Cached.fillDecl (ConLeche.Driver.fillOf sp F valuesP)) := by
    simp [fillStream, fillRef_valueOf]
  have he : streamEnv (fillStream sp F valuesP (ctxC ++ ownC)) =
      streamEnv (ownC.map (ConLeche.Cached.fillDecl (ConLeche.Driver.fillOf sp F valuesP)))
        (streamEnv ctxC) := by
    have happ : ∀ (A B : List Declaration) (E : Env), streamEnv (A ++ B) E =
        streamEnv B (streamEnv A E) := fun A B E => by simp [streamEnv, List.foldl_append]
    simp only [fillStream, fillRef_valueOf, List.map_append]
    rw [happ, ConLeche.Cached.streamEnv_fill _ ctxC]
  rw [hd, he] at h
  exact h

end ConRon.Bridge
