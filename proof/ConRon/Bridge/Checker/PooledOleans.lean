/-
# `ConRon.Bridge.Checker.PooledOleans` — the check phase of an `--olean` run

An `--olean` read leaves a theorem's value in its file: the record holds a reference
(`.thmDecl cv (.bvar code)`), and the theorem's job reads the value into its own scratch tier
(`Arena/OleanJobs.lean`'s `oleanJob`), checks the record with it in place and drops it with the
tier.  `pooled_fold_oleans`: every such job passing is an accept of con-leche's pure fold of the
FILLED stream `dsF`, the records with every reference replaced by the value the job reads.

The index is built from the records with their references (`IndexDenotes … (buildIndex dsP)`);
what a record installs does not read a theorem's value, so that index is the filled stream's
(upstream's `buildIndex_fill`).  A reference's job is `Pooled.lean`'s step with the value read in
between (`readValue_run`, the reader's walk) and the record checked with it (`oleanJob_spec`);
every other record's job is `recordJob` (`job_spec`).
-/
module

public import ConRon.Bridge.Checker.Pooled
public import ConRon.Arena.OleanJobs
public import ConRon.Bridge.Frontend.Olean.Value
public import ConLeche.Verify.Cached.Fill
import ConRon.Bridge.Frontend.Rel
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena
open ConRon.Arena.Frontend.Olean (OleanFs OleanPins ModRef ValueCache readValue)


/-! ## A reference is a `bvar`

`oleanJob` reads a theorem's value as a reference exactly when its handle is a `bvar` (the tag
test, then `viewBVar`); at a denoting handle that is exactly when the value denotes a `bvar`. -/

/-- con-leche: none — a `bvar` view is the `bvar` projection's answer. -/
theorem viewBVar_of_view {st : EStore} {i : EIdx} {k : Nat} (h : st.view i = some (.bvar k)) :
    st.viewBVar i = some k := by
  have htg : i.tag = ETag.bvar := by
    have := EStore.tagOf_of_view h; simpa [ENodeView.tagOf] using this
  rw [EStore.view_eq_tier] at h
  simp only [EStore.viewBVar, EStore.persGetBVar]
  have key : ∀ t : ETables, t.get i = some (.bvar k) → t.getBVar i = some k := by
    intro t ht
    simp only [ETables.get, htg, beq_self_eq_true, ↓reduceIte, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, hk⟩ := ht
    simp only [ENodeView.bvar.injEq] at hk
    simp [ETables.getBVar, hr, hk]
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at h ⊢; exact key _ h
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢
    simp only [Bool.false_eq_true, ite_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at h ⊢; exact key _ h
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

/-- con-leche: none — **the job's reference test is the denotation's `bvar`**. -/
theorem refTest_iff {st : EStore} (hwf : StoreWF st) {v : EIdx} {x : Expr}
    (hv : denoteE st v = some x) (code : Nat) :
    (if v.tag == ETag.bvar then st.viewBVar v else none) = some code ↔ x = .bvar code := by
  constructor
  · intro h
    split at h
    · rename_i htg
      have hview := view_of_viewBVar (by simpa using htg) h
      exact denote_bvar_inv hwf hview hv
    · cases h
  · intro hx
    subst hx
    have htag : v.tag = ETag.bvar := by
      have h := denote_tag hwf v
      rw [hv] at h
      have := h.some
      simp [exprTag] at this
      exact this.symm
    obtain ⟨w, hw⟩ := denoteE_view hv
    have hwt := EStore.tagOf_of_view hw
    rw [htag] at hwt
    cases w with
    | bvar i =>
      obtain ⟨⟩ := denote_bvar_inv hwf hw hv
      simp only [htag, beq_self_eq_true, ↓reduceIte]
      exact viewBVar_of_view hw
    | _ => simp [ENodeView.tagOf, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
        ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj] at hwt

/-! ## The filled stream -/

/-- con-leche: ConLeche/Verify/Cached/Fill.lean:21 fillDecl — a theorem's value at a
reference, replaced by the value at that reference. -/
@[expose] def fillRef (val : Nat → Expr) : Expr → Expr
  | .bvar code => val code
  | e => e

/-- con-leche: ConLeche/Verify/Frontend/Olean/Files.lean:758 ValueAt — **the value at a
reference** in the snapshot, where there is one (`ValueAt.unique`). -/
noncomputable def valueOf (sp : ConLeche.Frontend.Olean.SearchPath) (F : FS) (valuesP : Array ConLeche.Frontend.Olean.ModRef)
    (code : Nat) : Expr :=
  open Classical in
  if h : ∃ x, ConLeche.Frontend.Olean.ValueAt sp F valuesP code x then Classical.choose h
  else .bvar code

theorem valueOf_eq {sp : ConLeche.Frontend.Olean.SearchPath} {F : FS} {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    {code : Nat} {x : Expr} (h : ConLeche.Frontend.Olean.ValueAt sp F valuesP code x) :
    valueOf sp F valuesP code = x := by
  have hex : ∃ x, ConLeche.Frontend.Olean.ValueAt sp F valuesP code x := ⟨x, h⟩
  unfold valueOf
  rw [dite_eq_left hex]
  exact ConLeche.Frontend.Olean.ValueAt.unique (Classical.choose_spec hex) h

/-! ## An `--olean` job, read off -/

/-- con-leche: ConLeche/Driver/CheckMain.lean:120-133 oleanJobRun — **an accepted `--olean` job**
is either a record's plain job, at a record that is not a theorem with a reference, or the
reference read into the job's scratch tier and the theorem checked with the value in place. -/
theorem oleanJob_ok {fs : ConRon.Arena.Frontend.Olean.OleanFs}
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {sp : List System.FilePath}
    {values : Array ConRon.Arena.Frontend.Olean.ModRef} {pins : List INatOpPinSet}
    {I : IStreamIndex} {ds : Array IDeclaration} {c c' : ValueCache} {t : Nat}
    {s s' : AState} (ht : t < ds.size)
    (h : oleanJob fs pk sp values .verified pins I ds c t s = .ok ((c', .ok ()), s')) :
    (c' = c ∧ recordJob .verified pins I t ds[t] s = .ok ((), s') ∧
      ∀ cv v, ds[t] = .thmDecl cv v →
        (if v.tag == ETag.bvar then s.store.viewBVar v else none) = none) ∨
    ∃ cv v code e s₁, ds[t] = .thmDecl cv v ∧
      (if v.tag == ETag.bvar then s.store.viewBVar v else none) = some code ∧
      (do enterScratch; readValue fs pk sp values c code) s = .ok ((c', .ok e), s₁) ∧
      (do recordCheck .verified pins I t (.thmDecl cv e); dropScratch) s₁ = .ok ((), s') := by
  have plain : (match runJob .verified pins I ds t s with
        | .ok (r, s'') => (.ok (c, r, s'') :
            Except Arena.CheckError (ValueCache × Except (Arena.CheckError × Nat) Unit × AState))
        | .error e => .error e) = .ok (c', .ok (), s') →
      c' = c ∧ recordJob .verified pins I t ds[t] s = .ok ((), s') := by
    intro hp
    unfold runJob at hp
    rw [Array.getElem?_eq_getElem ht] at hp
    simp only at hp
    split at hp
    · rename_i hj
      cases hp
      split at hj
      · rename_i u s₀ hr
        cases hj; exact ⟨rfl, hr⟩
      · cases hj
    · cases hp
  unfold oleanJob at h
  rw [Array.getElem?_eq_getElem ht] at h
  simp only at h
  split at h
  · rename_i cv v hd
    split at h
    · rename_i code hcode
      split at h
      · rename_i c₁ e s₁ hread
        split at h
        · rename_i s₂ hcheck
          cases h
          exact Or.inr ⟨cv, v, code, e, s₁, Option.some.inj hd, hcode, hread, hcheck⟩
        · cases h
      · cases h
      · cases h
    · rename_i hnone
      left
      split at h
      · rename_i c₀ r s₀ hx
        cases h
        obtain ⟨rfl, hj⟩ := plain hx
        refine ⟨rfl, hj, fun cv' v' hd' => ?_⟩
        rw [hd'] at hd
        cases hd
        exact hnone
      · cases h
  · rename_i hnot
    left
    split at h
    · rename_i c₀ r s₀ hx
      cases h
      obtain ⟨rfl, hj⟩ := plain hx
      exact ⟨rfl, hj, fun cv v hd => absurd (congrArg some hd) (hnot cv v)⟩
    · cases h

/-! ## The `--olean` jobs, as `Pooled.lean`'s step -/

/-- con-leche: ConLeche/Driver/CheckMain.lean:120-133 oleanJobRun — the `--olean` step: job `k`
from a worker's state and cache, accepted. -/
@[expose] def OleanRun (fs : ConRon.Arena.Frontend.Olean.OleanFs)
    (pk : ConRon.Arena.Frontend.Olean.OleanPins) (sp : List System.FilePath)
    (values : Array ConRon.Arena.Frontend.Olean.ModRef) (pins : List INatOpPinSet)
    (I : IStreamIndex) (ds : Array IDeclaration) (k : Nat) (w w' : AState × ValueCache) : Prop :=
  ∃ _ : k < ds.size, oleanJob fs pk sp values .verified pins I ds w.2 k w.1 = .ok ((w'.2, .ok ()), w'.1)

/-- con-leche: ConLeche/Verify/Cached/Fill.lean:21 fillDecl — the filled stream: every
reference replaced by the snapshot's value there. -/
@[expose] noncomputable def fillStream (sp : ConLeche.Frontend.Olean.SearchPath) (F : FS)
    (valuesP : Array ConLeche.Frontend.Olean.ModRef) (dsP : List Declaration) : List Declaration :=
  dsP.map (ConLeche.Cached.fillDecl (fillRef (valueOf sp F valuesP)))

theorem fillRef_of_not_bvar {val : Nat → Expr} {x : Expr} (h : ∀ n, x ≠ .bvar n) :
    fillRef val x = x := by
  cases x <;> simp_all [fillRef]

/-- con-leche: ConLeche/Driver/CheckMain.lean:120-133 oleanJobRun — **an `--olean` job's accept
is the fold's step at the filled record**. -/
theorem oleanJob_spec
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {F : FS}
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {sp : ConLeche.Frontend.Olean.SearchPath}
    {values : Array ConRon.Arena.Frontend.Olean.ModRef}
    {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    {ds : Array IDeclaration} {dsP : List Declaration} {I : IStreamIndex} {s₀ s₁ : AState}
    (hrec : RecordSpec pins pinsP) (hpp : PersPinSets pins)
    (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁) (hpins : PinsDenote s₁.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hden : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s₁.store ds[i] = some dsP[i])
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base)
    (hwf₀ : StoreWF s₀.store) (hoff₀ : s₀.store.scratchOn = false) (hx₀ : PExt s₀.store s₁.store)
    (hv₀ : Frontend.Olean.ValuesRel sp F s₀.store values valuesP)
    (hnu₀ : Frontend.Olean.NullsRel s₀.store pk) :
    JobSpecAt (fun w => WorkerOK s₁ w.1 ∧ Frontend.Olean.CacheOK sp F valuesP w.2)
      (OleanRun (Frontend.Olean.modelFs F) pk sp values pins I ds) pinsP
      (fillStream sp F valuesP dsP) := by
  intro k w w' hkF hw hP hnd hrun
  obtain ⟨hk, hjob⟩ := hrun
  obtain ⟨hkP, hdk⟩ := hden k hk
  have hI' : IndexDenotes s₁.store I
      (ConLeche.Cached.buildIndex (fillStream sp F valuesP dsP).toArray) := by
    simp only [fillStream, ← List.map_toArray, ConLeche.Cached.buildIndex_fill]; exact hI
  have hFk : (fillStream sp F valuesP dsP)[k]'hkF =
      ConLeche.Cached.fillDecl (fillRef (valueOf sp F valuesP)) (dsP[k]'hkP) := by
    simp [fillStream]
  rcases oleanJob_ok hk hjob with ⟨hc, hj, hnot⟩ | ⟨cv, v, code, e, sr, hd, hcode, hread, hcheck⟩
  · -- the plain job: the record is its own fill
    have hfill : ConLeche.Cached.fillDecl (fillRef (valueOf sp F valuesP)) (dsP[k]'hkP) =
        dsP[k]'hkP := by
      generalize dsP[k]'hkP = d at hdk ⊢
      cases hdk' : ds[k] with
      | thmDecl cv v =>
        have hnone := hnot cv v hdk'
        rw [hdk'] at hdk
        simp only [Frontend.denoteDecl] at hdk
        split at hdk
        · rename_i cv' x hcv hx
          cases hdk
          have hpk : PersDecl (IDeclaration.thmDecl cv v) := by
            have := hpd _ (Array.getElem_mem_toList hk); rw [hdk'] at this; exact this
          have hxw : denoteE w.1.store v = some x := denoteE_pext hw.1.pext hpk.2 hx
          have hnb : ∀ n, x ≠ .bvar n := fun n hxn =>
            by rw [(refTest_iff hw.1.state.wf hxw n).mpr hxn] at hnone; cases hnone
          simp only [ConLeche.Cached.fillDecl, fillRef_of_not_bvar hnb]
        · cases hdk
      | _ =>
        rw [hdk'] at hdk
        simp only [Frontend.denoteDecl] at hdk
        first
        | (obtain ⟨_, -, hh⟩ := Option.map_eq_some_iff.mp hdk; rw [← hh]; rfl)
        | (split at hdk
           · cases hdk; rfl
           · cases hdk)
    obtain ⟨hw', env', Fu, hFu⟩ :=
      job_spec hrec hpp hpinsOK hpersPins hpins hpd hI' hpI hw.1 hk hkF
        (by rw [hFk, hfill]; exact hdk) hP hnd hj
    exact ⟨⟨hw', hc ▸ hw.2⟩, env', Fu, hFu⟩
  · -- the reference read in the job
    have hpk : PersDecl (IDeclaration.thmDecl cv v) := by
      have := hpd _ (Array.getElem_mem_toList hk); rw [hd] at this; exact this
    rw [hd] at hdk
    obtain ⟨cv', x, hcv, hx, hdP⟩ : ∃ cv' x, Frontend.denoteCV s₁.store cv = some cv' ∧
        denoteE s₁.store v = some x ∧ dsP[k]'hkP = .thmDecl cv' x := by
      simp only [Frontend.denoteDecl] at hdk
      cases h1 : Frontend.denoteCV s₁.store cv <;> cases h2 : denoteE s₁.store v <;>
        rw [h1, h2] at hdk <;> simp only [reduceCtorEq, Option.some.injEq] at hdk
      exact ⟨_, _, rfl, rfl, hdk.symm⟩
    have hxb : x = .bvar code :=
      (refTest_iff hw.1.state.wf (denoteE_pext hw.1.pext hpk.2 hx) code).mp hcode
    -- the scratch tier opened, the value read into it
    simp only [Bind.bind, StateT.bind, Except.bind] at hread hcheck
    have henter : enterScratch w.1 =
        .ok ((), AState.mk w.1.store.enableScratch Memos.empty w.1.caches w.1.pins) := rfl
    generalize hsj : AState.mk w.1.store.enableScratch Memos.empty w.1.caches w.1.pins = sj
      at henter
    rw [henter] at hread
    simp only at hread
    have hxj : PExt s₁.store sj.store := by
      rw [← hsj]; exact hw.1.pext.trans (PExt.enterScratch hw.1.state.wf)
    have hstj : StateOK sj := by rw [← hsj]; exact ⟨EStore.enableScratch_wf hw.1.state.wf⟩
    have hpj : sj.pins = s₁.pins := by rw [← hsj]; exact hw.1.pins
    have hcj : sj.caches = Caches.empty := by rw [← hsj]; exact hw.1.caches
    have hx₀j := hx₀.trans hxj
    obtain ⟨hps, hc', x', hx', hva⟩ := Frontend.Olean.readValue_run hstj
      (hnu₀.pmono hwf₀ hoff₀ hx₀j) (hv₀.pmono hwf₀ hoff₀ hx₀j) hw.2 hread
    have hdF : (fillStream sp F valuesP dsP)[k]'hkF = .thmDecl cv' x' := by
      rw [hFk, hdP, hxb]
      simp only [ConLeche.Cached.fillDecl, fillRef, valueOf_eq hva]
    -- the record checked with the value in place
    have hxr : PExt s₁.store sr.store := hxj.trans (PExt.of_ext hps.ext)
    have hok := view_foldOK hpinsOK hpersPins hI' hpI hkF hP hnd hps.ok hxr
      ((CacheOK.of_empty hcj).monoF hps.ext hps.cframe) (hps.pins.trans hpj)
    have hpinsr := PinsDenote.pmono hxr pins pinsP hpp hpins
    have hdr : Frontend.denoteDecl sr.store (.thmDecl cv e) = some (.thmDecl cv' x') := by
      simp only [Frontend.denoteDecl, denoteCV_pext hxr hpk.1 hcv, hx']
    cases hrc : recordCheck .verified pins I k (.thmDecl cv e) sr with
    | error err => rw [hrc] at hcheck; exact nomatch hcheck
    | ok r =>
      obtain ⟨u, s'⟩ := r
      rw [hrc] at hcheck
      simp only at hcheck
      have hdrop : dropScratch s' =
          .ok ((), AState.mk s'.store.dropScratch s'.memos Caches.empty s'.pins) := rfl
      rw [hdrop] at hcheck
      simp only [Except.ok.injEq, Prod.mk.injEq] at hcheck
      obtain ⟨-, hw'⟩ := hcheck
      obtain ⟨hst', hx'', hp', env', Fu, hFu⟩ := hrec hok hpinsr hdr (by cases u; exact hrc)
      rw [← hdF] at hFu
      refine ⟨⟨?_, hc'⟩, env', Fu, hFu⟩
      rw [← hw']
      exact { state := ⟨EStore.dropScratch_wf hst'.wf⟩
              pext := (hxr.trans (PExt.of_ext hx'')).trans (PExt.dropScratch hst'.wf)
              caches := rfl
              pins := (hp'.trans hps.pins).trans hpj }

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:396-419 parWorker — a worker's accepted list on
an `--olean` run is a chain of `--olean` jobs. -/
theorem checkOleanJobList_chain {fs : ConRon.Arena.Frontend.Olean.OleanFs}
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {sp : List System.FilePath}
    {values : Array ConRon.Arena.Frontend.Olean.ModRef} {pins : List INatOpPinSet}
    {I : IStreamIndex} {ds : Array IDeclaration} :
    ∀ (l : List Nat) (c : ValueCache) (w w'' : AState),
      checkOleanJobList fs pk sp values .verified pins I ds l c w = .ok (.ok (), w'') →
      JobChain (OleanRun fs pk sp values pins I ds) (w, c) l := by
  intro l
  induction l with
  | nil => intro c w _ _; exact .nil _
  | cons t rest ih =>
    intro c w w'' hl
    simp only [checkOleanJobList] at hl
    cases hj : oleanJob fs pk sp values .verified pins I ds c t w with
    | error e => rw [hj] at hl; exact nomatch hl
    | ok r =>
      obtain ⟨⟨c', res⟩, w₁⟩ := r
      rw [hj] at hl
      cases res with
      | error e => simp at hl
      | ok u =>
        simp only at hl
        have ht : t < ds.size := by
          unfold oleanJob at hj
          cases hdt : ds[t]? with
          | none => simp [hdt, runJob] at hj
          | some _ => exact (Array.getElem?_eq_some_iff.mp hdt).1
        exact .cons (w' := (w₁, c')) ⟨ht, by cases u; exact hj⟩ (ih c' w₁ w'' hl)

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:488 checkDecls_of_jobs — **the pool of an
`--olean` run**: every `--olean` job passing is an accept of con-leche's fold at the FILLED
stream, from an index that denotes con-leche's index of the records as read. -/
theorem pooled_fold_oleans
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {F : FS}
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {sp : ConLeche.Frontend.Olean.SearchPath}
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
    (hnu₀ : Frontend.Olean.NullsRel s₀.store pk) (parts : List (List Nat))
    (hcov : ∀ t < ds.size, ∃ w ∈ parts, t ∈ w)
    (hinc : ∀ w ∈ parts, w.Pairwise (· < ·))
    (hacc : ∀ w ∈ parts, ∃ s'', checkOleanJobList (Frontend.Olean.modelFs F) pk sp values
      .verified pins I ds w {} s₁.worker = .ok (.ok (), s'')) :
    ∃ Fu, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified Fu) pinsP
      (fillStream sp F valuesP dsP) =
        .ok (ConLeche.Cached.streamEnv (fillStream sp F valuesP dsP)) := by
  have hlenF : (fillStream sp F valuesP dsP).length = ds.size := by simp [fillStream, hlen]
  refine pooled_fold
    (Inv := fun w => WorkerOK s₁ w.1 ∧ Frontend.Olean.CacheOK sp F valuesP w.2)
    (Run := OleanRun (Frontend.Olean.modelFs F) pk sp values pins I ds)
    (oleanJob_spec hrec hpp hpinsOK hpersPins hpins hpd hden hI hpI hwf₀ hoff₀ hx₀ hv₀ hnu₀)
    ?_ hpush parts (fun t ht => hcov t (by omega)) hinc (fun w hw => ?_)
  · intro t w w' hr
    obtain ⟨hk, -⟩ := hr
    omega
  · obtain ⟨s'', h⟩ := hacc w hw
    exact ⟨(s₁.worker, {}), ⟨WorkerOK.start hst, Frontend.Olean.CacheOK.empty sp F valuesP⟩,
      checkOleanJobList_chain w {} _ _ h⟩

end ConRon.Bridge
