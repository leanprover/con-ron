/-
# `ConRon.Bridge.Compare.Pooled` — every job passing with a solution is a mixed run

The challenge's check phase of a compared run: the challenge's records indexed, then job lists,
one per worker, covering every position, each strictly increasing, each accepted by
`checkJobList` at the solution `J` from the driver's state's worker.  `pooledAcceptsJ_bridge`:
the records' denotation is a mixed run (`Compare/Model.lean`'s `MixedRun`) from the empty
environment to the one they denote, against con-leche's solution `⟨mkFEnv envS, matesU⟩`.

`Bridge/Checker/Pooled.lean`'s argument with the prefix predicate replaced: the fold's prefix of
length `k` is a mixed run with distinct names (`MixedPrefix`); a job at `k` is one mixed step at
the prefix's environment (`RecordSpecC`), which extends the prefix (`MixedPrefix.step`).  The
solution's index is read at every job through its view past its last record (`SolView`), which
denotes `envS` by `view_ok`, and its mates by `MatesRel`, both persistent, so a job's scratch
tier does not disturb them.
-/
module

public import ConRon.Bridge.Compare.Record
public import ConRon.Bridge.Compare.Mates
public import ConRon.Bridge.Checker.Pooled
public import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Install
import ConLeche.Semantics.DeclWF
import ConLeche.Verify.Cached.StreamIndex

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The prefix -/

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:461 jobs_run_from — **the prefix of length
`k`, checked with the solution**: a mixed run from the empty environment to the one its records
denote, its names distinct. -/
@[expose] def MixedPrefix (pinsP : List NatOpPinSet) (JS : ConLeche.Cached.Solution)
    (dsP : List Declaration) (k : Nat) : Prop :=
  Compare.MixedRun pinsP JS (dsP.take k) Env.empty (ConLeche.streamEnv (dsP.take k)) ∧
    ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:461 jobs_run_from — the empty prefix. -/
theorem MixedPrefix.zero (pinsP : List NatOpPinSet) (JS : ConLeche.Cached.Solution)
    (dsP : List Declaration) : MixedPrefix pinsP JS dsP 0 := by
  have h0 : (ConLeche.Cached.recsConsts ([] : List Declaration)).length = 0 := by
    have := (ConLeche.Cached.buildIndex_spec (#[] : Array Declaration)).next
    simpa [ConLeche.Cached.buildIndex] using this.symm
  refine ⟨by rw [List.take_zero]; exact Compare.MixedRun.nil _, ?_⟩
  rw [List.take_zero, List.eq_nil_of_length_eq_zero h0]
  exact List.nodup_nil

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:461 jobs_run_from — **the step**: the
prefix of length `k` and a mixed step of record `k` at its environment give the prefix of length
`k + 1`. -/
theorem MixedPrefix.step {pinsP : List NatOpPinSet} {JS : ConLeche.Cached.Solution}
    {dsP : List Declaration} {k : Nat} (hk : k < dsP.length) (hP : MixedPrefix pinsP JS dsP k)
    {env' : Env}
    (hd : Compare.MixedStep pinsP JS (ConLeche.streamEnv (dsP.take k)) dsP[k] env') :
    MixedPrefix pinsP JS dsP (k + 1) := by
  obtain ⟨hrun, hnd⟩ := hP
  obtain ⟨henv', hndD, hfr⟩ := hd.pushes
  obtain ⟨hstream, hnd'⟩ := prefix_step hk henv' hndD hfr hnd
  refine ⟨?_, hnd'⟩
  rw [hstream, take_succ_eq hk]
  exact hrun.snoc hd

/-! ## One job, with a solution -/

/-- con-leche: ConLeche/Cached/Justify.lean:144-146 solutionOf — **the solution at a job's state**:
its index, built from `dsS` and persistent, read through its view past its last record, denotes
the environment of `dsS`. -/
theorem solView_ok {dsS : List Declaration} {J : ISolution} {s₁ s : AState}
    (hIS : IndexDenotes s₁.store J.idx (ConLeche.Cached.buildIndex dsS.toArray))
    (hpIS : PersIFBase J.idx.base)
    (hndS : ((ConLeche.Cached.recsConsts dsS).map (·.name)).Nodup)
    (hst : StateOK s) (hx : PExt s₁.store s.store) :
    IFEnvOK (ConLeche.streamEnv dsS) (SolView J) s := by
  have hIj := hIS.pmono hpIS hx
  have hspec : ConLeche.Cached.IndexSpec (dsS ++ [])
      (ConLeche.Cached.buildIndex dsS.toArray) := by
    simpa using ConLeche.Cached.buildIndex_spec dsS.toArray
  obtain ⟨hienv, -⟩ := view_ok hst hIj hspec hndS
  have hsz : J.idx.firsts.size = dsS.length := by
    rw [hIS.firsts]; simpa using (ConLeche.Cached.buildIndex_spec dsS.toArray).size
  simpa [SolView, hsz] using hienv

/-- con-leche: ConLeche/Cached/StreamIndex.lean:95-104 recordJob — **one job with a solution, from
a worker's state**: at a position whose prefix is a mixed run with distinct names, record `k`'s
job accepting leaves a worker's state and is a mixed step at the prefix's environment. -/
theorem job_specC
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {J : ISolution} {dsS : List Declaration}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    {ds : Array IDeclaration} {dsP : List Declaration} {I : IStreamIndex} {s₁ w w' : AState}
    {k : Nat}
    (hrec : RecordSpecC pins pinsP J (ConLeche.streamEnv dsS) matesU) (hpp : PersPinSets pins)
    (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁) (hpins : PinsDenote s₁.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base)
    (hIS : IndexDenotes s₁.store J.idx (ConLeche.Cached.buildIndex dsS.toArray))
    (hpIS : PersIFBase J.idx.base)
    (hndS : ((ConLeche.Cached.recsConsts dsS).map (·.name)).Nodup)
    (hmates : MatesRel s₁.store J.mates matesU)
    (hw : WorkerOK s₁ w) (hk : k < ds.size) (hk' : k < dsP.length)
    (hdk : Frontend.denoteDecl s₁.store ds[k] = some dsP[k])
    (hP : MixedPrefix pinsP ⟨mkFEnv (ConLeche.streamEnv dsS), matesU⟩ dsP k)
    (hjob : recordJob .verified pins (some J) I k ds[k] w = .ok ((), w')) :
    WorkerOK s₁ w' ∧ ∃ env', Compare.MixedStep pinsP ⟨mkFEnv (ConLeche.streamEnv dsS), matesU⟩
      (ConLeche.streamEnv (dsP.take k)) dsP[k] env' := by
  simp only [recordJob, Bind.bind, StateT.bind, Except.bind] at hjob
  have henter : enterScratch w =
      .ok ((), AState.mk w.store.enableScratch Memos.empty w.caches w.pins) := rfl
  generalize hsj : AState.mk w.store.enableScratch Memos.empty w.caches w.pins = sj at henter
  rw [henter] at hjob
  simp only at hjob
  cases hrc : recordCheck .verified pins (some J) I k ds[k] sj with
  | error e => rw [hrc] at hjob; exact nomatch hjob
  | ok r =>
    obtain ⟨u, s'⟩ := r
    rw [hrc] at hjob
    simp only at hjob
    have hdrop : dropScratch s' =
        .ok ((), AState.mk s'.store.dropScratch s'.memos Caches.empty s'.pins) := rfl
    rw [hdrop] at hjob
    simp only [Except.ok.injEq, Prod.mk.injEq] at hjob
    obtain ⟨-, rfl⟩ := hjob
    have hxj : PExt s₁.store sj.store := by
      rw [← hsj]; exact hw.pext.trans (PExt.enterScratch hw.state.wf)
    have hstj : StateOK sj := by rw [← hsj]; exact ⟨EStore.enableScratch_wf hw.state.wf⟩
    have hpj : sj.pins = s₁.pins := by rw [← hsj]; exact hw.pins
    have hcj : sj.caches = Caches.empty := by rw [← hsj]; exact hw.caches
    obtain ⟨hrunP, hnd⟩ := hP
    have hok := view_foldOK hpinsOK hpersPins hI hpI hk'
      (hrunP.envWF ConLeche.Semantics.EnvWF.empty) hnd hstj hxj (CacheOK.of_empty hcj) hpj
    have hpinsj := PinsDenote.pmono hxj pins pinsP hpp hpins
    have hdj := denoteDecl_pext hxj (hpd _ (Array.getElem_mem_toList hk)) hdk
    have hsolj := solView_ok hIS hpIS hndS hstj hxj
    have hmj := (hmates.pmono hxj).toDen hstj.wf
    obtain ⟨hst', hx', hp', env', hstep⟩ := hrec hok hpinsj hdj hsolj hmj (by cases u; exact hrc)
    refine ⟨{ state := ⟨EStore.dropScratch_wf hst'.wf⟩
              pext := (hxj.trans (PExt.of_ext hx')).trans (PExt.dropScratch hst'.wf)
              caches := rfl
              pins := hp'.trans hpj }, env', hstep⟩

/-! ## The pool -/

/-- con-leche: ConLeche/Cached/StreamIndex.lean:95-104 recordJob — the challenge's step: record
`k`'s job with the solution, at a position of the records. -/
@[expose] def RecordRunJ (pins : List INatOpPinSet) (J : Option ISolution) (I : IStreamIndex)
    (ds : Array IDeclaration) (k : Nat) (w w' : AState) : Prop :=
  ∃ hk : k < ds.size, recordJob .verified pins J I k ds[k] w = .ok ((), w')

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:461-484 parWorker — a worker's accepted list with
a solution is a chain of record jobs. -/
theorem checkJobList_chainJ {pins : List INatOpPinSet} {J : Option ISolution} {I : IStreamIndex}
    {ds : Array IDeclaration} :
    ∀ (l : List Nat) (w w'' : AState),
      checkJobList .verified pins J I ds l w = .ok (.ok (), w'') →
      JobChain (RecordRunJ pins J I ds) w l := by
  intro l
  induction l with
  | nil => intro w _ _; exact .nil w
  | cons t rest ih =>
    intro w w'' hl
    simp only [checkJobList] at hl
    cases hr : runJob .verified pins J I ds t w with
    | error e => rw [hr] at hl; exact nomatch hl
    | ok r =>
      obtain ⟨res, w₁⟩ := r
      rw [hr] at hl
      cases res with
      | error e => simp at hl
      | ok u =>
        simp only at hl
        unfold runJob at hr
        cases hdt : ds[t]? with
        | none => rw [hdt] at hr; simp at hr
        | some dt =>
          rw [hdt] at hr
          simp only at hr
          cases hj : recordJob .verified pins J I t dt w with
          | error e => rw [hj] at hr; simp at hr
          | ok q =>
            obtain ⟨u', w₁'⟩ := q
            rw [hj] at hr
            simp only [Except.ok.injEq, Prod.mk.injEq] at hr
            obtain ⟨-, rfl⟩ := hr
            obtain ⟨ht, rfl⟩ := Array.getElem?_eq_some_iff.mp hdt
            exact .cons ⟨ht, by cases u'; exact hj⟩ (ih _ w'' hl)

/-- con-leche: ConLeche/Driver/CheckPool.lean:211-239 checkPool
con-leche: ConLeche/Model/Solution/Fold.lean:98 sideFold — **THEOREM 1 at the challenge's check
phase**: from the challenge's pooled check accepting at the solution `J` (its index built,
job lists covering the records, each increasing, each accepted at `J` from the driver's
state's worker), the denoted records are a mixed run from the empty environment to the one
they denote, against con-leche's solution: the solution stream's environment (`J`'s index
denotes its index, persistently, with distinct names) and the mates `J` holds. -/
theorem Arena.pooledAcceptsJ_bridge
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {s s' : AState} {I : IStreamIndex}
    {J : ISolution} {dsS : List Declaration}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    (hst : DriverOK s) (hoff : s.store.scratchOn = false)
    (hpersPins : PersPins s) (hpp : PersPinSets pins) (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x) (hden : denoteDecls s.store ds.toList = some dsP)
    (hIS : IndexDenotes s.store J.idx (ConLeche.Cached.buildIndex dsS.toArray))
    (hpIS : PersIFBase J.idx.base)
    (hndS : ((ConLeche.Cached.recsConsts dsS).map (·.name)).Nodup)
    (hmates : MatesRel s.store J.mates matesU)
    (hrun : ∃ (parts : List (List Nat)),
      buildIndex ds s = .ok (.ok I, s') ∧
      (∀ t < ds.size, ∃ w ∈ parts, t ∈ w) ∧
      (∀ w ∈ parts, ∀ t ∈ w, t < ds.size) ∧
      (∀ w ∈ parts, w.Pairwise (· < ·)) ∧
      (∀ w ∈ parts, ∃ s'', checkJobList .verified pins (some J) I ds w s'.worker =
        .ok (.ok (), s''))) :
    Compare.MixedRun pinsP ⟨mkFEnv (ConLeche.streamEnv dsS), matesU⟩ dsP Env.empty
      (ConLeche.streamEnv dsP) := by
  obtain ⟨parts, hidx, hcov, -, hinc, hacc⟩ := hrun
  obtain ⟨hst', hx, hp', -, hI, hpI⟩ :=
    buildIndex_run constsSpec tablesSpec hst hpersPins hoff hpd hden hidx
  have hx' := PExt.of_ext hx
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hden
  have hden' : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s'.store ds[i] = some dsP[i] := fun i hi => by
    obtain ⟨hi', h⟩ := hget i (by simpa using hi)
    exact ⟨hi', Frontend.denoteDecl_ext hx (by simpa using h)⟩
  have hlen' : dsP.length = ds.size := by simpa using hlen
  have hrec : RecordSpecC pins pinsP J (ConLeche.streamEnv dsS) matesU := recordSpecC hk hind
  have hpinsOK := hst.pins.pmono hpersPins hx' hp'
  have hpersPins' := hpersPins.mono hp'
  have hpins' := PinsDenote.mono hx pins pinsP hpins
  have hIS' := hIS.pmono hpIS hx'
  have hmates' := hmates.mono hx
  have hfin := pooled_foldP (Inv := WorkerOK s') (Run := RecordRunJ pins (some J) I ds)
    (N := dsP.length) (P := MixedPrefix pinsP ⟨mkFEnv (ConLeche.streamEnv dsS), matesU⟩ dsP)
    (MixedPrefix.zero _ _ _)
    (fun {k w w'} hkN hw hP hr => by
      obtain ⟨hk, hj⟩ := hr
      obtain ⟨hk', hdk⟩ := hden' k hk
      obtain ⟨hw', env', hstep⟩ := job_specC hrec hpp hpinsOK hpersPins' hpins' hpd hI hpI
        hIS' hpIS hndS hmates' hw hk hk' hdk hP hj
      exact ⟨hw', MixedPrefix.step hk' hP hstep⟩)
    (fun {t w w'} hr => by obtain ⟨hk, -⟩ := hr; omega) parts
    (fun t ht => hcov t (by omega)) hinc
    (fun w hw => by
      obtain ⟨s'', h⟩ := hacc w hw
      exact ⟨s'.worker, WorkerOK.start hst'.state, checkJobList_chainJ w _ _ h⟩)
  obtain ⟨hrunF, -⟩ := hfin
  rw [List.take_of_length_le (Nat.le_refl _)] at hrunF
  exact hrunF

end ConRon.Bridge
