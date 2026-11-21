/-
# `ConRon.Bridge.Compare.PooledOleans` — an `--olean` challenge's check phase with a solution

`Bridge/Checker/PooledOleans.lean` at a solution: an `--olean` run's job (`Arena/OleanJobs.lean`'s
`oleanJobJ`) reads a theorem's value into its scratch tier where the record holds a reference,
then checks the record at the solution `J`.  `Arena.pooledOleanAcceptsJ_bridge`: every such job
passing makes the FILLED stream (`fillStream`, every reference replaced by the snapshot's value)
a mixed run against con-leche's solution, as `Compare/Pooled.lean`'s `Arena.pooledAcceptsJ_bridge`
for a lean4export stream.  The proofs are the flat module's, in its run style, with
`Compare/Record.lean`'s `RecordSpecC` in place of `RecordSpec` and `Compare/Pooled.lean`'s
`MixedPrefix` in place of `PrefixOK`.
-/
module

public import ConRon.Bridge.Compare.Pooled
public import ConRon.Bridge.Checker.PooledOleans
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Install
import ConRon.Bridge.Frontend.Rel
import ConLeche.Verify.Cached.Fill
import ConLeche.Semantics.DeclWF

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena
open ConRon.Arena.Frontend.Olean (OleanFs OleanPins ModRef ValueCache readValue)

/-- con-leche: ConLeche/Driver/CheckMain.lean:120-133 oleanJobRun — **an accepted `--olean` job
with a solution**: `oleanJob_ok` at `J`. -/
theorem oleanJobJ_ok {fs : ConRon.Arena.Frontend.Olean.OleanFs}
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {sp : ConLeche.Frontend.Olean.Roots}
    {values : Array ConRon.Arena.Frontend.Olean.ModRef} {pins : List INatOpPinSet}
    {J : Option ISolution}
    {I : IStreamIndex} {ds : Array IDeclaration} {c c' : ValueCache} {t : Nat}
    {s s' : AState} (ht : t < ds.size)
    (h : oleanJobJ fs pk sp values .verified pins J I ds c t s = .ok ((c', .ok ()), s')) :
    (c' = c ∧ recordJob .verified pins J I t ds[t] s = .ok ((), s') ∧
      ∀ cv v, ds[t] = .thmDecl cv v →
        (if v.tag == ETag.bvar then s.store.viewBVar v else none) = none) ∨
    ∃ cv v code e s₁, ds[t] = .thmDecl cv v ∧
      (if v.tag == ETag.bvar then s.store.viewBVar v else none) = some code ∧
      (do enterScratch; readValue fs pk sp values c code) s = .ok ((c', .ok e), s₁) ∧
      (do recordCheck .verified pins J I t (.thmDecl cv e); dropScratch) s₁ = .ok ((), s') := by
  have plain : (match runJob .verified pins J I ds t s with
        | .ok (r, s'') => (.ok (c, r, s'') :
            Except Arena.CheckError (ValueCache × Except (Arena.CheckError × Nat) Unit × AState))
        | .error e => .error e) = .ok (c', .ok (), s') →
      c' = c ∧ recordJob .verified pins J I t ds[t] s = .ok ((), s') := by
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
  unfold oleanJobJ at h
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

/-- con-leche: ConLeche/Driver/CheckMain.lean:120-133 oleanJobRun — the `--olean` step with a
solution: job `k` from a worker's state and cache, accepted. -/
@[expose] def OleanRunJ (fs : ConRon.Arena.Frontend.Olean.OleanFs)
    (pk : ConRon.Arena.Frontend.Olean.OleanPins) (sp : ConLeche.Frontend.Olean.Roots)
    (values : Array ConRon.Arena.Frontend.Olean.ModRef) (pins : List INatOpPinSet)
    (J : Option ISolution)
    (I : IStreamIndex) (ds : Array IDeclaration) (k : Nat) (w w' : AState × ValueCache) : Prop :=
  ∃ _ : k < ds.size,
    oleanJobJ fs pk sp values .verified pins J I ds w.2 k w.1 = .ok ((w'.2, .ok ()), w'.1)

/-- con-leche: ConLeche/Driver/CheckMain.lean:120-133 oleanJobRun — **an `--olean` job's accept
with a solution is a mixed step at the filled record**: `oleanJob_spec` with the solution's view
and mates read at the job's state. -/
theorem oleanJobJ_spec
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {F : FS}
    {J : ISolution} {dsS : List Declaration}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {sp : ConLeche.Frontend.Olean.Roots}
    {values : Array ConRon.Arena.Frontend.Olean.ModRef}
    {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    {ds : Array IDeclaration} {dsP : List Declaration} {I : IStreamIndex} {s₀ s₁ : AState}
    (hrec : RecordSpecC pins pinsP J (ConLeche.streamEnv dsS) matesU) (hpp : PersPinSets pins)
    (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁) (hpins : PinsDenote s₁.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hden : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s₁.store ds[i] = some dsP[i])
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base)
    (hIS : IndexDenotes s₁.store J.idx (ConLeche.Cached.buildIndex dsS.toArray))
    (hpIS : PersIFBase J.idx.base)
    (hndS : ((ConLeche.Cached.recsConsts dsS).map (·.name)).Nodup)
    (hmates : MatesRel s₁.store J.mates matesU)
    (hwf₀ : StoreWF s₀.store) (hoff₀ : s₀.store.scratchOn = false) (hx₀ : PExt s₀.store s₁.store)
    (hv₀ : Frontend.Olean.ValuesRel sp F s₀.store values valuesP)
    (hnu₀ : Frontend.Olean.NullsRel s₀.store pk) (hsp : sp.bare = sp)
    {k : Nat} {w w' : AState × ValueCache} (hkF : k < (fillStream sp F valuesP dsP).length)
    (hw : WorkerOK s₁ w.1 ∧ Frontend.Olean.CacheOK sp F valuesP w.2)
    (hP : MixedPrefix pinsP ⟨mkFEnv (ConLeche.streamEnv dsS), matesU⟩
      (fillStream sp F valuesP dsP) k)
    (hrun : OleanRunJ (Frontend.Olean.modelFs F) pk sp values pins (some J) I ds k w w') :
    (WorkerOK s₁ w'.1 ∧ Frontend.Olean.CacheOK sp F valuesP w'.2) ∧
      ∃ env', Compare.MixedStep pinsP ⟨mkFEnv (ConLeche.streamEnv dsS), matesU⟩
        (ConLeche.streamEnv ((fillStream sp F valuesP dsP).take k))
        ((fillStream sp F valuesP dsP)[k]'hkF) env' := by
  obtain ⟨hk, hjob⟩ := hrun
  obtain ⟨hkP, hdk⟩ := hden k hk
  have hI' : IndexDenotes s₁.store I
      (ConLeche.Cached.buildIndex (fillStream sp F valuesP dsP).toArray) := by
    simp only [fillStream, ← List.map_toArray, ConLeche.Cached.buildIndex_fill]; exact hI
  have hFk : (fillStream sp F valuesP dsP)[k]'hkF =
      ConLeche.Cached.fillDecl (fillRef (valueOf sp F valuesP)) (dsP[k]'hkP) := by
    simp [fillStream]
  rcases oleanJobJ_ok hk hjob with ⟨hc, hj, hnot⟩ | ⟨cv, v, code, e, sr, hd, hcode, hread, hcheck⟩
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
    obtain ⟨hw', env', hstep⟩ :=
      job_specC hrec hpp hpinsOK hpersPins hpins hpd hI' hpI hIS hpIS hndS hmates hw.1 hk hkF
        (by rw [hFk, hfill]; exact hdk) hP hj
    exact ⟨⟨hw', hc ▸ hw.2⟩, env', hstep⟩
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
    obtain ⟨hps, hc', x', hx', hva⟩ := Frontend.Olean.readValue_run hsp hstj
      (hnu₀.pmono hwf₀ hoff₀ hx₀j) (hv₀.pmono hwf₀ hoff₀ hx₀j) hw.2 hread
    have hdF : (fillStream sp F valuesP dsP)[k]'hkF = .thmDecl cv' x' := by
      rw [hFk, hdP, hxb]
      simp only [ConLeche.Cached.fillDecl, fillRef, valueOf_eq hva]
    have hxr : PExt s₁.store sr.store := hxj.trans (PExt.of_ext hps.ext)
    obtain ⟨hrunP, hnd⟩ := hP
    have hok := view_foldOK hpinsOK hpersPins hI' hpI hkF
      (hrunP.envWF ConLeche.Semantics.EnvWF.empty) hnd hps.ok hxr
      ((CacheOK.of_empty hcj).monoF hps.ext hps.cframe) (hps.pins.trans hpj)
    have hpinsr := PinsDenote.pmono hxr pins pinsP hpp hpins
    have hdr : Frontend.denoteDecl sr.store (.thmDecl cv e) = some (.thmDecl cv' x') := by
      simp only [Frontend.denoteDecl, denoteCV_pext hxr hpk.1 hcv, hx']
    have hsolr := solView_ok hIS hpIS hndS hps.ok hxr
    have hmr := (hmates.pmono hxr).toDen hps.ok.wf
    cases hrc : recordCheck .verified pins (some J) I k (.thmDecl cv e) sr with
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
      obtain ⟨hst', hx'', hp', env', hstep⟩ :=
        hrec hok hpinsr hdr hsolr hmr (by cases u; exact hrc)
      rw [← hdF] at hstep
      refine ⟨⟨?_, hc'⟩, env', hstep⟩
      rw [← hw']
      exact { state := ⟨EStore.dropScratch_wf hst'.wf⟩
              pext := (hxr.trans (PExt.of_ext hx'')).trans (PExt.dropScratch hst'.wf)
              caches := rfl
              pins := (hp'.trans hps.pins).trans hpj }

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:461-484 parWorker — a worker's accepted list on
an `--olean` run with a solution is a chain of `--olean` jobs. -/
theorem checkOleanJobListJ_chain {fs : ConRon.Arena.Frontend.Olean.OleanFs}
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {sp : ConLeche.Frontend.Olean.Roots}
    {values : Array ConRon.Arena.Frontend.Olean.ModRef} {pins : List INatOpPinSet}
    {J : Option ISolution} {I : IStreamIndex} {ds : Array IDeclaration} :
    ∀ (l : List Nat) (c : ValueCache) (w w'' : AState),
      checkOleanJobListJ fs pk sp values .verified pins J I ds l c w = .ok (.ok (), w'') →
      JobChain (OleanRunJ fs pk sp values pins J I ds) (w, c) l := by
  intro l
  induction l with
  | nil => intro c w _ _; exact .nil _
  | cons t rest ih =>
    intro c w w'' hl
    simp only [checkOleanJobListJ] at hl
    cases hj : oleanJobJ fs pk sp values .verified pins J I ds c t w with
    | error e => rw [hj] at hl; exact nomatch hl
    | ok r =>
      obtain ⟨⟨c', res⟩, w₁⟩ := r
      rw [hj] at hl
      cases res with
      | error e => simp at hl
      | ok u =>
        simp only at hl
        have ht : t < ds.size := by
          unfold oleanJobJ at hj
          cases hdt : ds[t]? with
          | none => simp [hdt, runJob] at hj
          | some _ => exact (Array.getElem?_eq_some_iff.mp hdt).1
        exact .cons (w' := (w₁, c')) ⟨ht, by cases u; exact hj⟩ (ih c' w₁ w'' hl)

open ConRon.Arena.Frontend.Olean (OleanPins ModRef) in
/-- con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
con-leche: ConLeche/Model/Solution/Fold.lean:98 sideFold — **THEOREM 1 at an `--olean`
challenge's check phase**: from `Arena.PooledOleanAcceptsJ` at the solution `J` on a snapshot
`F`, the FILLED records are a mixed run from the empty environment to the one they denote,
against con-leche's solution (`J`'s index and mates, as `Arena.pooledAcceptsJ_bridge`). -/
theorem Arena.pooledOleanAcceptsJ_bridge
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {s₀ s s' : AState} {I : IStreamIndex}
    {F : FS} {pk : OleanPins} {sp : ConLeche.Frontend.Olean.Roots}
    {values : Array ModRef} {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    {J : ISolution} {dsS : List Declaration}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    (hst : DriverOK s) (hoff : s.store.scratchOn = false)
    (hpersPins : PersPins s) (hpp : PersPinSets pins) (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x) (hden : denoteDecls s.store ds.toList = some dsP)
    (hwf₀ : StoreWF s₀.store) (hoff₀ : s₀.store.scratchOn = false) (hx₀ : PExt s₀.store s.store)
    (hv₀ : Frontend.Olean.ValuesRel sp F s₀.store values valuesP)
    (hnu₀ : Frontend.Olean.NullsRel s₀.store pk) (hsp : sp.bare = sp)
    (hIS : IndexDenotes s.store J.idx (ConLeche.Cached.buildIndex dsS.toArray))
    (hpIS : PersIFBase J.idx.base)
    (hndS : ((ConLeche.Cached.recsConsts dsS).map (·.name)).Nodup)
    (hmates : MatesRel s.store J.mates matesU)
    (hrun : Arena.PooledOleanAcceptsJ (Frontend.Olean.modelFs F) pk sp values .verified pins
      (some J) ds s I s') :
    Compare.MixedRun pinsP ⟨mkFEnv (ConLeche.streamEnv dsS), matesU⟩
      (fillStream sp F valuesP dsP) Env.empty
      (ConLeche.streamEnv (fillStream sp F valuesP dsP)) := by
  obtain ⟨parts, hidx, hcov, -, hinc, hacc⟩ := hrun
  obtain ⟨hst', hx, hp', -, hI, hpI⟩ :=
    buildIndex_run constsSpec tablesSpec hst hpersPins hoff hpd hden hidx
  have hx' := PExt.of_ext hx
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hden
  have hden' : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s'.store ds[i] = some dsP[i] := fun i hi => by
    obtain ⟨hi', h⟩ := hget i (by simpa using hi)
    exact ⟨hi', Frontend.denoteDecl_ext hx (by simpa using h)⟩
  have hlenF : (fillStream sp F valuesP dsP).length = ds.size := by
    simp [fillStream]; simpa using hlen
  have hrec : RecordSpecC pins pinsP J (ConLeche.streamEnv dsS) matesU := recordSpecC hk hind
  have hpinsOK := hst.pins.pmono hpersPins hx' hp'
  have hpersPins' := hpersPins.mono hp'
  have hpins' := PinsDenote.mono hx pins pinsP hpins
  have hIS' := hIS.pmono hpIS hx'
  have hmates' := hmates.mono hx
  have hfin := pooled_foldP
    (Inv := fun w : AState × ValueCache =>
      WorkerOK s' w.1 ∧ Frontend.Olean.CacheOK sp F valuesP w.2)
    (Run := OleanRunJ (Frontend.Olean.modelFs F) pk sp values pins (some J) I ds)
    (N := (fillStream sp F valuesP dsP).length)
    (P := MixedPrefix pinsP ⟨mkFEnv (ConLeche.streamEnv dsS), matesU⟩
      (fillStream sp F valuesP dsP))
    (MixedPrefix.zero _ _ _)
    (fun {k w w'} hkN hw hP hr => by
      obtain ⟨hw', env', hstep⟩ := oleanJobJ_spec hrec hpp hpinsOK hpersPins' hpins' hpd hden'
        hI hpI hIS' hpIS hndS hmates' hwf₀ hoff₀ (hx₀.trans hx') hv₀ hnu₀ hsp hkN hw hP hr
      exact ⟨hw', MixedPrefix.step hkN hP hstep⟩)
    (fun {t w w'} hr => by obtain ⟨hk, -⟩ := hr; omega) parts
    (fun t ht => hcov t (by omega)) hinc
    (fun w hw => by
      obtain ⟨s'', h⟩ := hacc w hw
      exact ⟨(s'.worker, {}), ⟨WorkerOK.start hst'.state, Frontend.Olean.CacheOK.empty sp F valuesP⟩,
        checkOleanJobListJ_chain w {} _ _ h⟩)
  obtain ⟨hrunF, -⟩ := hfin
  rw [List.take_of_length_le (Nat.le_refl _)] at hrunF
  exact hrunF

end ConRon.Bridge
