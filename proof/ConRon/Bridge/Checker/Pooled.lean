/-
# `ConRon.Bridge.Checker.Pooled` — every job passing is con-leche's fold accepting

The twin's check phase (`Arena/Pooled.lean`'s `PooledAccepts`): the stream's index built, then
job lists, one per worker, covering every position, each strictly increasing, each accepted by
`checkJobList` from the driver's state's worker.  A job is a record's check at the index's view
of its position (`recordJob`), from an empty scratch tier and fresh memos.

`pooled_fold`: if the index denotes con-leche's index of the denoted stream, every job passing
is an accept of con-leche's pure fold `checkDeclsPure`.  This is con-leche's
`checkDecls_of_jobs` (`ConLeche/Verify/Cached/StreamIndex.lean`) with the store threaded:

* **Induction in fold order.**  At position `k` the prefix's fold has accepted with the
  environment the records denote (`streamEnv`, con-leche's `checkDecl` pushes what the record says:
  `KernelPushes`), so the names so far are distinct (`KernelPushes`' freshness) and the view of
  `k` is that environment (`view_ok`).  con-leche's model of the accepted prefix supplies its
  `EnvWF` (`ConLeche.Model.foldPM`), as upstream's `declsRun_model` does.  Then job `k`'s accept is
  the fold's step (`RecordSpec`).
* **A worker's state.**  A job runs from the state its worker reached through the jobs it ran
  before.  Their specifications need the fold up to THEIR positions, and a worker's jobs increase,
  so those positions are below `k` and the induction already has them (`worker_reaches`).  Each job
  leaves the store a persistent extension of the driver's, the caches flushed and the pins as they
  were (`WorkerOK`), whatever its environment was: a job's own pushes go with its scratch tier.

The per-record facts are hypotheses here, discharged in `Bridge/Checker/Pool.lean`:
`RecordSpec` (the per-declaration bridge `Arena.checkDecl_bridge` and the `And` pin's frame) and
`KernelPushes` (`Bridge/Checker/Pushes.lean`).  Nothing here unfolds a check.
-/
module

public import ConRon.Bridge.Checker.StreamIndex
public import ConRon.Bridge.Checker.Decl
public import ConRon.Arena.Pooled
public import ConLeche.Model.Fold
import ConLeche.Verify.BridgeDecl
import ConRon.Bridge.Specs
import ConLeche.Verify.Cached.BridgeCS4

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

universe w

/-! ## The pin variants across a drop -/

/-- con-leche: none — a persistent type-pin list keeps denoting across a persistent extension. -/
theorem TypePinsDenote.pmono {st st' : EStore} (hx : PExt st st') :
    ∀ ps qs, PersTypePins ps → TypePinsDenote st ps qs → TypePinsDenote st' ps qs
  | [], [], _, _ => trivial
  | p :: ps, _ :: qs, hp, ⟨h1, h2, h3⟩ =>
    ⟨denoteN_pext hx (hp p (by simp)).1 h1, denoteE_pext hx (hp p (by simp)).2 h2,
      TypePinsDenote.pmono hx ps qs (fun c hc => hp c (by simp [hc])) h3⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- con-leche: none — the interned pin variants keep denoting across a persistent extension:
`internAllPins` ran before the parse with the scratch tier closed, so every pin handle is
persistent. -/
theorem PinsDenote.pmono {st st' : EStore} (hx : PExt st st') :
    ∀ ps qs, PersPinSets ps → PinsDenote st ps qs → PinsDenote st' ps qs := by
  intro ps
  induction ps with
  | nil => intro qs _ h; cases qs <;> exact h
  | cons a as ih =>
    intro qs hp h
    cases qs with
    | nil => exact h
    | cons b bs =>
      obtain ⟨h1, h2⟩ := h
      have hpa : PersPinSet a := hp a (by simp)
      have hpp := hpa.pins
      have hpr := hpa.proofs
      simp only [PersEList, List.mem_cons] at hpp
      refine ⟨?_, ih bs (fun c hc => hp c (by simp [hc])) h2⟩
      refine {
        toolchain := h1.toolchain
        divPin := denoteE_pext hx (hpp _ (by simp)) h1.divPin
        modPin := denoteE_pext hx (hpp _ (by simp)) h1.modPin
        gcdPin := denoteE_pext hx (hpp _ (by simp)) h1.gcdPin
        landPin := denoteE_pext hx (hpp _ (by simp)) h1.landPin
        lorPin := denoteE_pext hx (hpp _ (by simp)) h1.lorPin
        xorPin := denoteE_pext hx (hpp _ (by simp)) h1.xorPin
        shiftLeftPin := denoteE_pext hx (hpp _ (by simp)) h1.shiftLeftPin
        shiftRightPin := denoteE_pext hx (hpp _ (by simp)) h1.shiftRightPin
        divProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.divProofs
        modProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.modProofs
        gcdProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.gcdProofs
        landProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.landProofs
        lorProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.lorProofs
        xorProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.xorProofs
        shiftLeftProofs := denoteEList_pext hx _ _
          (fun c hc => hpr c (by simp [hc])) h1.shiftLeftProofs
        shiftRightProofs := denoteEList_pext hx _ _
          (fun c hc => hpr c (by simp [hc])) h1.shiftRightProofs
        divTypePins := TypePinsDenote.pmono hx _ _
          (fun c hc => hpa.typePins c (by simp [hc])) h1.divTypePins
        modTypePins := TypePinsDenote.pmono hx _ _
          (fun c hc => hpa.typePins c (by simp [hc])) h1.modTypePins
        gcdTypePins := TypePinsDenote.pmono hx _ _
          (fun c hc => hpa.typePins c (by simp [hc])) h1.gcdTypePins
        landTypePins := TypePinsDenote.pmono hx _ _
          (fun c hc => hpa.typePins c (by simp [hc])) h1.landTypePins
        lorTypePins := TypePinsDenote.pmono hx _ _
          (fun c hc => hpa.typePins c (by simp [hc])) h1.lorTypePins
        xorTypePins := TypePinsDenote.pmono hx _ _
          (fun c hc => hpa.typePins c (by simp [hc])) h1.xorTypePins
        shiftLeftTypePins := TypePinsDenote.pmono hx _ _
          (fun c hc => hpa.typePins c (by simp [hc])) h1.shiftLeftTypePins
        shiftRightTypePins := TypePinsDenote.pmono hx _ _
          (fun c hc => hpa.typePins c (by simp [hc])) h1.shiftRightTypePins }

/-! ## The per-record facts this module takes -/

/-- con-leche: ConLeche/Cached/StreamIndex.lean:74-81 recordJob — **a record's check at a view,
bridged**: from the invariant at the view, the record's check (the `And` pin, then `checkDecl`)
accepting leaves the store invariant, an append and the pins, and con-leche's pure `checkDecl`
accepts the denoted record at the environment the view stands for.  `Bridge/Checker/Pool.lean`
proves it from `Arena.checkDecl_bridge`. -/
@[expose] def RecordSpec (pins : List INatOpPinSet) (pinsP : List NatOpPinSet) : Prop :=
  ∀ {env : Env} {I : IStreamIndex} {k : Nat} {pd : IDeclaration} {d : Declaration}
    {s s' : AState},
    FoldOK env (I.view k) s → PinsDenote s.store pins pinsP →
    Frontend.denoteDecl s.store pd = some d →
    recordCheck .verified pins I k pd s = .ok ((), s') →
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ env' F,
        ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env d = .ok env'

/-- con-leche: ConLeche/Verify/Cached/DeclPushes.lean:723 checkDeclStepC_pushes
con-leche: ConLeche/Verify/Cached/PushChain.lean:44 PushChain — **an accepted step pushes what
the record says, at fresh names**, for con-leche's pure `checkDecl`.  `Bridge/Checker/Pushes.lean`
proves it. -/
@[expose] def KernelPushes (pinsP : List NatOpPinSet) : Prop :=
  ∀ {F : Nat} {env env' : Env} {d : Declaration},
    ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env d = .ok env' →
    env' = env.pushDelta (declConstants d) (declTables d) ∧
      ((declConstants d).map (·.name)).Nodup ∧ ∀ c ∈ declConstants d, env.find? c.name = none

/-! ## A worker's state -/

/-- con-leche: ConLeche/Driver/CheckPool.lean:199-227 checkPool — **what a worker's state keeps
between two jobs**: the store invariant, the store a persistent extension of the driver's, the
caches flushed, the driver's pins. -/
structure WorkerOK (s₁ w : AState) : Prop where
  state : StateOK w
  pext : PExt s₁.store w.store
  caches : w.caches = Caches.empty
  pins : w.pins = s₁.pins

/-- con-leche: none — the driver's state's worker (`AState.worker`). -/
theorem WorkerOK.start {s₁ : AState} (hst : StateOK s₁) : WorkerOK s₁ s₁.worker where
  state := ⟨EStore.dropScratch_wf hst.wf⟩
  pext := PExt.dropScratch hst.wf
  caches := rfl
  pins := rfl

/-! ## The fold's prefix -/

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:441 jobs_run — **the prefix of length `k`
accepted**: con-leche's pure fold accepts it at every fuel from some on, with the environment its
records denote. -/
@[expose] def PrefixOK (pinsP : List NatOpPinSet) (dsP : List Declaration) (k : Nat) : Prop :=
  ∃ F, ∀ F', F ≤ F' →
    (dsP.take k).foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F') pinsP)
      Env.empty = .ok (ConLeche.Cached.streamEnv (dsP.take k))

/-- con-leche: ConLeche/Verify/Cached/BridgeCS4.lean:56 FueledM.up — `checkDecl` at a larger
fuel. -/
theorem checkDecl_up {pinsP : List NatOpPinSet} {F F' : Nat} (hle : F ≤ F') {env env' : Env}
    {d : Declaration}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env d = .ok env') :
    ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F') pinsP env d = .ok env' := by
  rw [← ConLeche.checkDecl_datF] at h ⊢
  exact ConLeche.Cached.FueledM.up hle h

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:155 recsConsts_snoc — a prefix one longer. -/
theorem take_succ_eq {α : Type} {l : List α} {k : Nat} (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  rfl

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:441 jobs_run — **the step**: the prefix of
length `k` accepted and the record at `k` accepted at its environment give the prefix of length
`k + 1`, and the names so far stay distinct. -/
theorem PrefixOK.step {pinsP : List NatOpPinSet} {dsP : List Declaration} {k : Nat}
    (hpush : KernelPushes pinsP) (hk : k < dsP.length) (hP : PrefixOK pinsP dsP k)
    {F : Nat} {env' : Env}
    (hd : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP
      (ConLeche.Cached.streamEnv (dsP.take k)) dsP[k] = .ok env')
    (hnd : ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup) :
    PrefixOK pinsP dsP (k + 1) ∧
      ((ConLeche.Cached.recsConsts (dsP.take (k + 1))).map (·.name)).Nodup := by
  obtain ⟨F₀, hF₀⟩ := hP
  obtain ⟨henv', hndD, hfr⟩ := hpush hd
  have hsplit := take_succ_eq hk
  have hstream : ConLeche.Cached.streamEnv (dsP.take (k + 1)) = env' := by
    rw [henv', hsplit]
    show List.foldl _ _ _ = _
    rw [List.foldl_append]
    rfl
  refine ⟨⟨max F₀ F, fun F' hle => ?_⟩, ?_⟩
  · rw [hsplit, List.foldlM_append, hF₀ F' (by omega)]
    simp only [List.foldlM, Bind.bind, Except.bind]
    rw [checkDecl_up (by omega) hd, ← hstream, hsplit]
    rfl
  · rw [hsplit, ConLeche.Cached.recsConsts_snoc, List.map_append, List.nodup_append]
    refine ⟨hnd, hndD, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    have hnone := hfr c hc
    have hcons : (ConLeche.Cached.streamEnv (dsP.take k)).consts =
        (ConLeche.Cached.recsConsts (dsP.take k)).reverse := by
      simpa [Env.empty] using ConLeche.Cached.streamEnv_consts (dsP.take k) Env.empty
    obtain ⟨c', hc', hn⟩ := List.mem_map.mp ha
    unfold Env.find? at hnone
    rw [hcons] at hnone
    have := List.find?_eq_none.mp hnone c' (List.mem_reverse.mpr hc')
    simp [hn] at this

/-! ## One job -/

/-- con-leche: ConLeche/Cached/StreamIndex.lean:74-81 recordJob — **one job, from a worker's
state**: at a position whose prefix the fold has accepted with distinct names, record `k`'s job
accepting leaves a worker's state and con-leche's `checkDecl` accepting the record at the
prefix's environment. -/
theorem job_spec (V : Type w) [ConLeche.SetTheory V]
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {I : IStreamIndex} {s₁ w w' : AState}
    {k : Nat}
    (hrec : RecordSpec pins pinsP) (hpp : PersPinSets pins)
    (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁) (hpins : PinsDenote s₁.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hden : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s₁.store ds[i] = some dsP[i])
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base)
    (hw : WorkerOK s₁ w) (hk : k < ds.size) (hP : PrefixOK pinsP dsP k)
    (hnd : ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup)
    (hjob : recordJob .verified pins I k ds[k] w = .ok ((), w')) :
    WorkerOK s₁ w' ∧ ∃ (hk' : k < dsP.length) (env' : Env) (F : Nat),
      ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP
        (ConLeche.Cached.streamEnv (dsP.take k)) dsP[k] = .ok env' := by
  obtain ⟨hk', hdk⟩ := hden k hk
  -- the bracket
  simp only [recordJob, Bind.bind, StateT.bind, Except.bind] at hjob
  have henter : enterScratch w =
      .ok ((), AState.mk w.store.enableScratch Memos.empty w.caches w.pins) := rfl
  generalize hsj : AState.mk w.store.enableScratch Memos.empty w.caches w.pins = sj at henter
  rw [henter] at hjob
  simp only at hjob
  cases hrc : recordCheck .verified pins I k ds[k] sj with
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
    -- the invariant at the view
    have hxj : PExt s₁.store sj.store := by
      rw [← hsj]; exact hw.pext.trans (PExt.enterScratch hw.state.wf)
    have hstj : StateOK sj := by rw [← hsj]; exact ⟨EStore.enableScratch_wf hw.state.wf⟩
    have hIj := hI.pmono hpI hxj
    have hspec : ConLeche.Cached.IndexSpec (dsP.take k ++ dsP.drop k)
        (ConLeche.Cached.buildIndex dsP.toArray) := by
      rw [List.take_append_drop]
      simpa using ConLeche.Cached.buildIndex_spec dsP.toArray
    have hlen : (dsP.take k).length = k := by simp; omega
    obtain ⟨hienv, hgate⟩ := view_ok hstj hIj hspec hnd
    rw [hlen] at hienv hgate
    obtain ⟨F₀, hF₀⟩ := hP
    obtain ⟨⟨mp, -, -⟩, -, -⟩ := ConLeche.Model.foldPM (V := V) (pins := pinsP) (dsP.take k)
      Env.empty ConLeche.Model.EnvModelOk.empty (hF₀ F₀ (Nat.le_refl _))
    have hpj : sj.pins = s₁.pins := by rw [← hsj]; exact hw.pins
    have hcj : sj.caches = Caches.empty := by rw [← hsj]; exact hw.caches
    have hok : FoldOK (ConLeche.Cached.streamEnv (dsP.take k)) (I.view k) sj :=
      { check := ⟨hstj, CacheOK.of_empty hcj,
          (hpinsOK.pmono hpersPins hxj hpj), hienv⟩
        envWF := mp.toEnvFacts.wf
        tblShape := fun t ht => by simp [IStreamIndex.view] at ht
        persPins := hpersPins.mono hpj
        coh := ⟨fun _ => rfl, fun _ => rfl⟩
        gate := hgate }
    have hpinsj := PinsDenote.pmono hxj pins pinsP hpp hpins
    have hdj := denoteDecl_pext hxj (hpd _ (Array.getElem_mem_toList hk)) hdk
    obtain ⟨hst', hx', hp', env', F, hF⟩ := hrec hok hpinsj hdj (by cases u; exact hrc)
    refine ⟨{ state := ⟨EStore.dropScratch_wf hst'.wf⟩
              pext := (hxj.trans (PExt.of_ext hx')).trans (PExt.dropScratch hst'.wf)
              caches := rfl
              pins := hp'.trans hpj }, hk', env', F, hF⟩

/-! ## A worker's list

The fold over a worker's claims, abstracted: a worker's state `σ` (the arena state, and on an
`--olean` run the value cache beside it), a step `Run k σ σ'` (job `k` accepted from `σ`, ending in
`σ'`), and a list of claims run in order (`JobChain`).  `pooled_fold` holds for any such step whose
accept is the fold's step at its position (`JobSpecAt`); the stream's step is `recordJob`
(`job_spec`), an `--olean` run's is `Arena/OleanJobs.lean`'s `oleanJob`. -/

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:396-419 parWorker — a worker's claims, run in
order from `σ`, every step accepted. -/
inductive JobChain {σ : Type} (Run : Nat → σ → σ → Prop) : σ → List Nat → Prop
  | nil (w : σ) : JobChain Run w []
  | cons {t : Nat} {w w' : σ} {l : List Nat} : Run t w w' → JobChain Run w' l →
      JobChain Run w (t :: l)

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:441 jobs_run — **what a step must give**:
from a worker's state, at a position whose prefix the fold has accepted with distinct names, an
accepted job leaves a worker's state and con-leche's `checkDecl` accepting the record at the
prefix's environment. -/
@[expose] def JobSpecAt {σ : Type} (s₁ : AState) (wst : σ → AState) (Run : Nat → σ → σ → Prop)
    (pinsP : List NatOpPinSet) (dsP : List Declaration) : Prop :=
  ∀ {k : Nat} {w w' : σ} (hk : k < dsP.length), WorkerOK s₁ (wst w) → PrefixOK pinsP dsP k →
    ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup → Run k w w' →
    WorkerOK s₁ (wst w') ∧ ∃ (env' : Env) (F : Nat),
      ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP
        (ConLeche.Cached.streamEnv (dsP.take k)) (dsP[k]'hk) = .ok env'

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:396-419 parWorker — **a worker reaches each of
its jobs from a worker's state**, provided every job it ran before is at a position whose prefix
the fold has accepted with distinct names: the claims increase, so those are the positions below
the job's. -/
theorem worker_reaches {σ : Type} {s₁ : AState} {wst : σ → AState} {Run : Nat → σ → σ → Prop}
    {pinsP : List NatOpPinSet} {dsP : List Declaration}
    (hspec : JobSpecAt s₁ wst Run pinsP dsP) (hrange : ∀ {t w w'}, Run t w w' → t < dsP.length)
    {k : Nat}
    (hbelow : ∀ t < k, PrefixOK pinsP dsP t ∧
      ((ConLeche.Cached.recsConsts (dsP.take t)).map (·.name)).Nodup) :
    ∀ (l : List Nat) (w : σ), WorkerOK s₁ (wst w) → l.Pairwise (· < ·) → k ∈ l →
      JobChain Run w l → ∃ wk wk', WorkerOK s₁ (wst wk) ∧ Run k wk wk' := by
  intro l
  induction l with
  | nil => intro _ _ _ hm; exact absurd hm (by simp)
  | cons t rest ih =>
    intro w hw hpw hm hc
    cases hc with
    | cons hr hrest =>
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact ⟨w, _, hw, hr⟩
      · have hlt : t < k := (List.pairwise_cons.mp hpw).1 k hm'
        obtain ⟨hPt, hndt⟩ := hbelow t hlt
        obtain ⟨hw₁, -⟩ := hspec (hrange hr) hw hPt hndt hr
        exact ih _ hw₁ (List.pairwise_cons.mp hpw).2 hm' hrest

/-! ## The pool -/

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:488 checkDecls_of_jobs — **every job
passing is an accept of con-leche's fold**, at the stream the records denote: job lists covering
the positions, each increasing, each run from a worker's state by a step whose accept is the
fold's step at its position. -/
theorem pooled_fold {σ : Type} {s₁ : AState} {wst : σ → AState} {Run : Nat → σ → σ → Prop}
    {pinsP : List NatOpPinSet} {dsP : List Declaration}
    (hspec : JobSpecAt s₁ wst Run pinsP dsP) (hrange : ∀ {t w w'}, Run t w w' → t < dsP.length)
    (hpush : KernelPushes pinsP) (parts : List (List Nat))
    (hcov : ∀ t < dsP.length, ∃ w ∈ parts, t ∈ w)
    (hinc : ∀ w ∈ parts, w.Pairwise (· < ·))
    (hacc : ∀ w ∈ parts, ∃ w₀, WorkerOK s₁ (wst w₀) ∧ JobChain Run w₀ w) :
    ∃ F, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pinsP dsP
      = .ok (ConLeche.Cached.streamEnv dsP) := by
  have main : ∀ k, k ≤ dsP.length → ∀ t ≤ k, PrefixOK pinsP dsP t ∧
      ((ConLeche.Cached.recsConsts (dsP.take t)).map (·.name)).Nodup := by
    intro k
    induction k with
    | zero =>
      intro _ t ht
      obtain rfl : t = 0 := by omega
      have h0 : (ConLeche.Cached.recsConsts ([] : List Declaration)).length = 0 := by
        have := (ConLeche.Cached.buildIndex_spec (#[] : Array Declaration)).next
        simpa [ConLeche.Cached.buildIndex] using this.symm
      refine ⟨⟨0, fun _ _ => rfl⟩, ?_⟩
      rw [List.take_zero, List.eq_nil_of_length_eq_zero h0]
      exact List.nodup_nil
    | succ k ih =>
      intro hk t ht
      rcases Nat.lt_or_ge t (k + 1) with htk | htk
      · exact ih (by omega) t (by omega)
      obtain rfl : t = k + 1 := by omega
      have hbelow := ih (by omega)
      have hks : k < dsP.length := by omega
      obtain ⟨wl, hwl, hkw⟩ := hcov k hks
      obtain ⟨w₀, hw₀, hch⟩ := hacc wl hwl
      obtain ⟨wk, wk', hwk, hrun⟩ :=
        worker_reaches (Run := Run) (wst := wst) hspec hrange (fun t ht => hbelow t (by omega)) wl w₀ hw₀
          (hinc wl hwl) hkw hch
      obtain ⟨hPk, hndk⟩ := hbelow k (Nat.le_refl _)
      obtain ⟨-, env', F, hF⟩ := hspec hks hwk hPk hndk hrun
      exact PrefixOK.step hpush hks hPk hF hndk
  obtain ⟨⟨F, hF⟩, -⟩ := main dsP.length (Nat.le_refl _) dsP.length (Nat.le_refl _)
  rw [List.take_of_length_le (Nat.le_refl _)] at hF
  exact ⟨F, hF F (Nat.le_refl _)⟩

/-! ## The stream's jobs -/

/-- con-leche: ConLeche/Cached/StreamIndex.lean:74-81 recordJob — the stream's step: record
`k`'s job, at a position of the records. -/
@[expose] def RecordRun (pins : List INatOpPinSet) (I : IStreamIndex) (ds : Array IDeclaration)
    (k : Nat) (w w' : AState) : Prop :=
  ∃ hk : k < ds.size, recordJob .verified pins I k ds[k] w = .ok ((), w')

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:396-419 parWorker — a worker's accepted list is
a chain of record jobs. -/
theorem checkJobList_chain {pins : List INatOpPinSet} {I : IStreamIndex}
    {ds : Array IDeclaration} :
    ∀ (l : List Nat) (w w'' : AState),
      checkJobList .verified pins I ds l w = .ok (.ok (), w'') →
      JobChain (RecordRun pins I ds) w l := by
  intro l
  induction l with
  | nil => intro w _ _; exact .nil w
  | cons t rest ih =>
    intro w w'' hl
    simp only [checkJobList] at hl
    cases hr : runJob .verified pins I ds t w with
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
          cases hj : recordJob .verified pins I t dt w with
          | error e => rw [hj] at hr; simp at hr
          | ok q =>
            obtain ⟨u', w₁'⟩ := q
            rw [hj] at hr
            simp only [Except.ok.injEq, Prod.mk.injEq] at hr
            obtain ⟨-, rfl⟩ := hr
            obtain ⟨ht, rfl⟩ := Array.getElem?_eq_some_iff.mp hdt
            exact .cons ⟨ht, by cases u'; exact hj⟩ (ih _ w'' hl)

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:488 checkDecls_of_jobs — **the stream's
pool**: every record job passing is an accept of con-leche's fold, from an index that denotes
con-leche's index of the denoted stream. -/
theorem pooled_fold_records (V : Type w) [ConLeche.SetTheory V]
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {I : IStreamIndex} {s₁ : AState}
    (hrec : RecordSpec pins pinsP) (hpush : KernelPushes pinsP) (hpp : PersPinSets pins)
    (hst : StateOK s₁) (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁)
    (hpins : PinsDenote s₁.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x) (hlen : dsP.length = ds.size)
    (hden : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s₁.store ds[i] = some dsP[i])
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base) (parts : List (List Nat))
    (hcov : ∀ t < ds.size, ∃ w ∈ parts, t ∈ w)
    (hinc : ∀ w ∈ parts, w.Pairwise (· < ·))
    (hacc : ∀ w ∈ parts, ∃ s'', checkJobList .verified pins I ds w s₁.worker = .ok (.ok (), s'')) :
    ∃ F, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pinsP dsP
      = .ok (ConLeche.Cached.streamEnv dsP) := by
  refine pooled_fold (s₁ := s₁) (wst := id) (Run := RecordRun pins I ds) ?_ ?_ hpush parts
    (fun t ht => hcov t (by omega)) hinc
    (fun w hw => ?_)
  · intro k w w' _ hw hP hnd hrun
    obtain ⟨hk, hj⟩ := hrun
    obtain ⟨hw', hk', env', F, hF⟩ :=
      job_spec V hrec hpp hpinsOK hpersPins hpins hpd hden hI hpI hw hk hP hnd hj
    exact ⟨hw', env', F, hF⟩
  · intro t w w' hr
    obtain ⟨hk, -⟩ := hr
    omega
  · obtain ⟨s'', h⟩ := hacc w hw
    exact ⟨s₁.worker, WorkerOK.start hst, checkJobList_chain w _ _ h⟩

end ConRon.Bridge
