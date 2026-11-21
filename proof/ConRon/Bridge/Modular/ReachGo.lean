/-
# `ConRon.Bridge.Modular.ReachGo` — the reach's worklist and the reach, Theorem 1 (task #166)

The twin's worklist (`reachGo`: `reachRead` at a name popped, `reachPartners` at an empty stack)
against upstream's `reachGo`, over the log's relation (`ReachLogRel`), and the reach's headline
(`reachRunHyp_holds'`, `ReachRunHyp` of `Accepted.lean`) gluing the clash rule, the worklist, the
read order, the validation and the flags' pending statements.  The record read at a name
(`readRecord`) is taken in the shape `ReadRecordHyp`.  Run style throughout.
-/
module

public import ConRon.Bridge.Modular.ReachRecord
public import ConRon.Bridge.Modular.Accepted

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM)
open ConLeche.Frontend.Olean (Region Roots OLeanLevel ModFiles CEntryF CKindF Copy)

/-- con-leche: ConLeche/Driver/Reach.lean:693-729 readRecord — **the record read at `x`, at the
twin**: its accept is upstream's, the record and its home read back, the caches related after,
the record persistent. -/
@[expose] def ReadRecordHyp : Prop :=
  ∀ {pk : OleanPins} {F : FS} {sp : Roots} {env : ConRon.Arena.Modular.ReachEnv}
    {envC : ConLeche.Driver.ReachEnv ModelIO} {c c' : ConRon.Arena.Modular.ReachCache}
    {cC : ConLeche.Driver.ReachCache} {x : NIdx} {xC : ConLeche.Name} {s s' : AState}
    {d : IDeclaration} {h : NIdx},
    sp.bare = sp → RCtx pk s → EnvRel sp s.store env envC → CacheRel s.store c cC →
    denoteN s.store.ns x = some xC →
    ConRon.Arena.Modular.readRecord (modelFs F) pk sp env c x s = .ok ((c', d, h), s') →
    DStep s s' ∧ PersDecl d ∧ ∃ cC' dC hC,
      ModelIO.Gives (ConLeche.Driver.readRecord envC cC xC) F (cC', .ok (dC, hC)) ∧
      CacheRel s'.store c' cC' ∧ ConRon.Arena.Frontend.denoteDecl s'.store d = some dC ∧
      denoteN s'.store.ns h = some hC

/-! ## The log's pure steps -/

/-- con-leche: ConLeche/Driver/Reach.lean:746-752 pushNames — the names pushed, read back. -/
theorem pushNames_rel {st : EStore} (hw : NStoreWF st.ns) :
    ∀ {ys : List NIdx} {ysC : List ConLeche.Name} {seen : Std.HashSet NIdx}
      {seenC : Std.HashSet ConLeche.Name} {stack : List NIdx} {stackC : List ConLeche.Name},
      ListRel (NR st) ys ysC → SetRel st seen seenC → ListRel (NR st) stack stackC →
      SetRel st (ConRon.Arena.Modular.pushNames seen stack ys).1
          (ConLeche.Driver.pushNames seenC stackC ysC).1 ∧
        ListRel (NR st) (ConRon.Arena.Modular.pushNames seen stack ys).2
          (ConLeche.Driver.pushNames seenC stackC ysC).2
  | [], [], _, _, _, _, .nil, hs, hk => by
    simp only [ConRon.Arena.Modular.pushNames, ConLeche.Driver.pushNames]
    exact ⟨hs, hk⟩
  | y :: ys, yC :: ysC, seen, seenC, stack, stackC, .cons hy hys, hs, hk => by
    simp only [ConRon.Arena.Modular.pushNames, ConLeche.Driver.pushNames]
    rw [hs.contains hw hy]
    split
    · exact pushNames_rel hw hys hs hk
    · exact pushNames_rel hw hys (hs.insert hy) (.cons hy hk)

/-- The names a record stores, into the stored set, read back. -/
theorem storedFold_rel {st : EStore} :
    ∀ {ns : List NIdx} {nsC : List ConLeche.Name} {t : Std.HashSet NIdx}
      {tC : Std.HashSet ConLeche.Name}, ListRel (NR st) ns nsC → SetRel st t tC →
      SetRel st (ns.foldl (fun s n => s.insert n) t) (nsC.foldl (fun s n => s.insert n) tC)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons hn hns, h => by
    simp only [List.foldl_cons]
    exact storedFold_rel hns (h.insert hn)

/-- A name among a list of names, read back. -/
theorem listContains_rel {st : EStore} (hw : NStoreWF st.ns) {x : NIdx} {xC : ConLeche.Name}
    (hx : denoteN st.ns x = some xC) :
    ∀ {ns : List NIdx} {nsC : List ConLeche.Name}, ListRel (NR st) ns nsC →
      ns.contains x = nsC.contains xC
  | [], [], .nil => rfl
  | n :: ns, nC :: nsC, .cons hn hns => by
    have ih := listContains_rel hw hx hns
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_cons, List.mem_cons]
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem] at ih
    constructor
    · rintro (he | he)
      · subst he; exact .inl (Option.some.inj (hx.symm.trans hn))
      · exact .inr (ih.1 he)
    · rintro (he | he)
      · subst he; exact .inl (denoteN_inj hw hx hn)
      · exact .inr (ih.2 he)

/-- Some name of a list stored, read back. -/
theorem anyStored_rel {st : EStore} (hw : NStoreWF st.ns) {t : Std.HashSet NIdx}
    {tC : Std.HashSet ConLeche.Name} (ht : SetRel st t tC) :
    ∀ {ns : List NIdx} {nsC : List ConLeche.Name}, ListRel (NR st) ns nsC →
      ConRon.Arena.Modular.anyStored t ns = nsC.any tC.contains
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hn hns => by
    have ih := anyStored_rel hw ht hns
    simp only [ConRon.Arena.Modular.anyStored, List.any_cons] at ih ⊢
    rw [ht.contains hw hn, ih]

theorem ReachLogRel.ext {st st' : EStore} (hx : Ext st st') {L : ConRon.Arena.Modular.ReachLog}
    {LC : ConLeche.Driver.ReachLog} (h : ReachLogRel st L LC) : ReachLogRel st' L LC :=
  ⟨h.seen.ext hx, h.stored.ext hx, denoteDecls_ext hx _ _ h.ctx,
    ListRel.mono' (fun _ _ h => denoteN_ext h hx) h.homes,
    ListRel.mono' (fun _ _ h => ListRel.mono' (fun _ _ h => denoteN_ext h hx) h) h.reads,
    ListRel.mono' (fun _ _ h => denoteN_ext h hx) h.stack⟩

/-- con-leche: ConLeche/Driver/Reach.lean:760-763 ReachLog.init — the worklist's start, read back. -/
theorem init_rel {st : EStore} (hw : NStoreWF st.ns) {rs : List NIdx} {rsC : List ConLeche.Name}
    (hr : ListRel (NR st) rs rsC) :
    ReachLogRel st (ConRon.Arena.Modular.ReachLog.init rs) (ConLeche.Driver.ReachLog.init rsC) := by
  obtain ⟨h1, h2⟩ := pushNames_rel hw hr (SetRel.empty st) .nil
  exact ⟨h1, SetRel.empty st, rfl, .nil, .nil, h2⟩

theorem denoteDecls_push {st : EStore} {ds : Array IDeclaration} {dsC : Array Declaration}
    {d : IDeclaration} {dC : Declaration} (hds : denoteDecls st ds.toList = some dsC.toList)
    (hd : ConRon.Arena.Frontend.denoteDecl st d = some dC) :
    denoteDecls st (ds.push d).toList = some (dsC.push dC).toList := by
  simp only [Array.toList_push]
  exact denoteDecls_append hds (by simp [denoteDecls, hd])

/-- con-leche: ConLeche/Driver/Reach.lean:754-758 ReachLog.add — a record added, read back. -/
theorem add_rel {st : EStore} (hw : NStoreWF st.ns) {L : ConRon.Arena.Modular.ReachLog}
    {LC : ConLeche.Driver.ReachLog} {restC : List ConLeche.Name}
    (hL : ReachLogRel st L { LC with stack := restC })
    {d : IDeclaration} {dC : Declaration} (hd : ConRon.Arena.Frontend.denoteDecl st d = some dC)
    {h : NIdx} {hC : ConLeche.Name} (hh : denoteN st.ns h = some hC)
    {ns rd : List NIdx} {rdC : List ConLeche.Name}
    (hns : ListRel (NR st) ns (ConLeche.Modular.declNames dC)) (hrd : ListRel (NR st) rd rdC) :
    ReachLogRel st (L.add d h ns rd) (LC.add dC hC rdC restC) := by
  obtain ⟨h1, h2⟩ := pushNames_rel hw hrd hL.seen hL.stack
  unfold ConRon.Arena.Modular.ReachLog.add ConLeche.Driver.ReachLog.add
  exact ⟨h1, storedFold_rel hns hL.stored, denoteDecls_push hL.ctx hd,
    by simpa using listRel_append hL.homes (.cons hh .nil),
    by simpa using listRel_append hL.reads (.cons hrd .nil), h2⟩

/-! ## The worklist's steps -/

/-- An action's failure caught as a value: its accept is the action's. -/
theorem catchE_ok {α : Type} {x : AM α} {a : α} {s s' : AState}
    (h : ConRon.Arena.Modular.catchE x s = .ok (.ok a, s')) : x s = .ok (a, s') := by
  unfold ConRon.Arena.Modular.catchE at h
  split at h
  · rename_i a' s'' hx
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    cases h1
    exact hx
  · simp at h

theorem CacheRel.withPartners {st : EStore} {c : ConRon.Arena.Modular.ReachCache}
    {cC : ConLeche.Driver.ReachCache} (h : CacheRel st c cC) {p : Array (NIdx × NIdx)}
    {pC : Array (ConLeche.Name × ConLeche.Name)} (hp : ListRel (NN st) p.toList pC.toList) :
    CacheRel st { c with partners := p } { cC with partners := pC } :=
  ⟨h.tables, h.looks, h.parts, h.recBlocks, h.views, h.located, h.completed, h.pending, hp,
    h.searches⟩

/-- con-leche: ConLeche/Driver/Reach.lean:801-826 reachGo — **the worklist's step at a name `x`
popped, at the twin** (`reachRead`): upstream's step at `x` answers whatever its run from the
related log and caches after the step answers. -/
theorem reachRead_run (hRR : ReadRecordHyp) {pk : OleanPins} {F : FS} {sp : Roots}
    (hsp : sp.bare = sp) {env : ConRon.Arena.Modular.ReachEnv}
    {envC : ConLeche.Driver.ReachEnv ModelIO} {L L' : ConRon.Arena.Modular.ReachLog}
    {LC : ConLeche.Driver.ReachLog} {c c' : ConRon.Arena.Modular.ReachCache}
    {cC : ConLeche.Driver.ReachCache} {x : NIdx} {xC : ConLeche.Name}
    {restC : List ConLeche.Name} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hL : ReachLogRel s.store L { LC with stack := restC }) (hst : LC.stack = xC :: restC)
    (hx : denoteN s.store.ns x = some xC) (hpL : ∀ d ∈ L.ctx.toList, PersDecl d)
    (h : ConRon.Arena.Modular.reachRead (modelFs F) pk sp env L c x s = .ok ((L', c'), s')) :
    DStep s s' ∧ (∀ d ∈ L'.ctx.toList, PersDecl d) ∧ ∃ LC' cC', ReachLogRel s'.store L' LC' ∧
      CacheRel s'.store c' cC' ∧ ∀ (fuel : Nat) (R : Except ConLeche.CheckError
        (ConLeche.Driver.ReachLog × ConLeche.Driver.ReachCache)),
        ModelIO.Gives (ConLeche.Driver.reachGo envC fuel LC' cC') F R →
        ModelIO.Gives (ConLeche.Driver.reachGo envC (fuel + 1) LC cC) F R := by
  have hw := hctx.wf
  have hstoredC : L.stored.contains x = LC.stored.contains xC := hL.stored.contains hw hx
  unfold ConRon.Arena.Modular.reachRead at h
  by_cases hsx : L.stored.contains x = true
  · rw [ite_eq_left hsx] at h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    cases hv
    refine ⟨DStep.refl hctx.ok hctx.off, hpL, { LC with stack := restC }, cC, hL, hc,
      fun fuel R hR => ?_⟩
    rw [ConLeche.Driver.reachGo]
    simp only [hst]
    rw [hstoredC] at hsx
    simp only [hsx, ↓reduceIte]
    exact hR
  rw [ite_eq_right hsx] at h
  have hsxC : LC.stored.contains xC = false := by rw [← hstoredC]; simpa using hsx
  obtain ⟨u0, s₀, h0, h⟩ := AM.bind_ok h
  obtain ⟨-, hs0⟩ := AM.pure_ok h0
  subst s₀
  -- the record
  obtain ⟨⟨c₁, d, hh⟩, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hst1, hpd, cC₁, dC, hC, hg1, hc1, hd1, hh1⟩ := hRR hsp hctx he hc hx h1
  have hctx1 := hctx.step hst1
  have hw1 := hctx1.wf
  -- its names
  obtain ⟨ns, s₂, h2, h⟩ := AM.bind_ok h
  obtain ⟨hst2, hns⟩ := declNames_run hctx1.ok hctx1.off hpd hd1 h2
  have hctx2 := hctx1.step hst2
  have hw2 := hctx2.wf
  have hnsR := nr_of_denoteNList hns
  have hx2 := denoteN_ext hx (hst1.ext.trans hst2.ext)
  have hcont : ns.contains x = (ConLeche.Modular.declNames dC).contains xC := listContains_rel hw2 hx2 hnsR
  have hL2 := hL.ext (hst1.ext.trans hst2.ext)
  have hany : ConRon.Arena.Modular.anyStored L.stored ns = (ConLeche.Modular.declNames dC).any LC.stored.contains :=
    anyStored_rel hw2 hL2.stored hnsR
  -- the record stores `x`, and no stored name
  dsimp only at h
  split at h
  · rename_i hb
    exfalso
    obtain ⟨_, _, _, ha⟩ := AM.bind_ok h
    obtain ⟨_, _, hb2, _⟩ := AM.bind_ok ha
    exact AM.fail_ok hb2
  rename_i hcx
  obtain ⟨u, s₃, h3, h⟩ := AM.bind_ok h
  obtain ⟨-, hs3⟩ := AM.pure_ok h3
  subst s₃
  split at h
  · rename_i hb
    exfalso
    obtain ⟨_, _, _, ha⟩ := AM.bind_ok h
    obtain ⟨_, _, _, hb2⟩ := AM.bind_ok ha
    obtain ⟨_, _, hc2, _⟩ := AM.bind_ok hb2
    exact AM.fail_ok hc2
  rename_i hna
  obtain ⟨u, s₃, h3, h⟩ := AM.bind_ok h
  obtain ⟨-, hs3⟩ := AM.pure_ok h3
  subst s₃
  -- what it reads
  obtain ⟨rd, s₃, h3, h⟩ := AM.bind_ok h
  obtain ⟨hst3, hrd⟩ := recordReads_exact hctx2.ok hctx2.off hpd
    (denoteDecl_ext hst2.ext hd1) h3
  have hctx3 := hctx2.step hst3
  have hx13 : Ext s₁.store s₃.store := hst2.ext.trans hst3.ext
  have hrdR := nr_of_denoteNList hrd
  -- its reads captured
  obtain ⟨ce, s₄, h4, h⟩ := AM.bind_ok h
  rcases ce with e | c₂
  · exfalso
    obtain ⟨_, _, _, ha⟩ := AM.bind_ok h
    obtain ⟨_, _, hb2, _⟩ := AM.bind_ok ha
    exact AM.fail_ok hb2
  have h4' := catchE_ok h4
  obtain ⟨hst4, cC₂, hg4, hc2⟩ := captureAll_run hsp rd hctx3
    ((he.ext hst1.ext hctx1.wf).ext hx13 hctx3.wf) (hc1.ext hx13)
    (denoteN_ext hh1 hx13) hrdR h4'
  have hctx4 := hctx3.step hst4
  dsimp only at h
  obtain ⟨c₂', s₄', h5a, h⟩ := AM.bind_ok h
  obtain ⟨hv5, hs5⟩ := AM.pure_ok h5a
  subst hv5
  subst s₄'
  -- its names against the importers' copies
  obtain ⟨c₃, s₅, h5, h⟩ := AM.bind_ok h
  have hx14 : Ext s₁.store s₄.store := hx13.trans hst4.ext
  obtain ⟨hst5, cC₃, hg5, hc3⟩ := storedNamesOk_run hsp ns hctx4
    ((he.ext hst1.ext hctx1.wf).ext hx14 hctx4.wf) hc2 (denoteN_ext hh1 hx14)
    (ListRel.mono' (fun _ _ h => denoteN_ext h (hst3.ext.trans hst4.ext)) hnsR) h5
  have hctx5 := hctx4.step hst5
  have hx25 : Ext s₂.store s₅.store := (hst3.ext.trans hst4.ext).trans hst5.ext
  -- the partners
  obtain ⟨ps, s₆, h6, h⟩ := AM.bind_ok h
  obtain ⟨hst6, hps⟩ := clashPartners_run hctx5.ok hctx5.off
    ((he.ext hst1.ext hctx1.wf).ext (hx14.trans hst5.ext) hctx5.wf)
    (ListRel.mono' (fun _ _ h => denoteN_ext h hx25) hnsR) hc3.partners h6
  obtain ⟨hv, rfl⟩ := AM.pure_ok h
  cases hv
  have hx26 : Ext s₂.store s'.store := hx25.trans hst6.ext
  have hw6 := (hctx5.step hst6).wf
  refine ⟨hst1.trans (hst2.trans (hst3.trans (hst4.trans (hst5.trans hst6)))), ?_,
    LC.add dC hC (ConLeche.Cached.recordReads dC).toList restC,
    { cC₃ with partners := cC₃.partners ++ ConLeche.Driver.clashPartners envC (ConLeche.Modular.declNames dC) },
    ?_, (hc3.ext hst6.ext).withPartners (by simpa using hps), fun fuel R hR => ?_⟩
  · intro d' hd'
    simp only [ConRon.Arena.Modular.ReachLog.add, Array.toList_push, List.mem_append,
      List.mem_singleton] at hd'
    rcases hd' with hd' | rfl
    · exact hpL d' hd'
    · exact hpd
  · exact add_rel hw6 (hL2.ext hx26) (denoteDecl_ext (hst2.ext.trans hx26) hd1)
      (denoteN_ext hh1 (hst2.ext.trans hx26)) (ListRel.mono' (fun _ _ h => denoteN_ext h hx26) hnsR)
      (ListRel.mono' (fun _ _ h => denoteN_ext h ((hst4.ext.trans hst5.ext).trans hst6.ext)) hrdR)
  · -- upstream's step
    rw [ConLeche.Driver.reachGo]
    simp only [hst, hsxC, Bool.false_eq_true, ↓reduceIte]
    refine hg1.bind ?_
    simp only
    have hcxC : (ConLeche.Modular.declNames dC).contains xC = true := by rw [← hcont]; simpa using hcx
    have hnaC : (ConLeche.Modular.declNames dC).any LC.stored.contains = false := by
      rw [← hany]; simpa using hna
    simp only [hcxC, hnaC, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine hg4.bind ?_
    simp only
    refine hg5.bind ?_
    simp only
    exact hR

theorem listRel_map_snd {st : EStore} :
    ∀ {ps : List (NIdx × NIdx)} {psC : List (ConLeche.Name × ConLeche.Name)},
      ListRel (NN st) ps psC → ListRel (NR st) (ps.map (·.2)) (psC.map (·.2))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => .cons h.2 (listRel_map_snd t)

theorem listRel_length {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, ListRel R l l' → l.length = l'.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ t => by simp [listRel_length t]

/-- con-leche: ConLeche/Driver/Reach.lean:791-800 reachGo — **the worklist's step at an empty
stack, at the twin** (`reachPartners`): upstream's step answers whatever its run from the related
log and caches after the step answers. -/
theorem reachPartners_run {pk : OleanPins} {F : FS} {sp : Roots}
    (hsp : sp.bare = sp) {env : ConRon.Arena.Modular.ReachEnv}
    {envC : ConLeche.Driver.ReachEnv ModelIO} {L L' : ConRon.Arena.Modular.ReachLog}
    {LC : ConLeche.Driver.ReachLog} {c c' : ConRon.Arena.Modular.ReachCache}
    {cC : ConLeche.Driver.ReachCache} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hL : ReachLogRel s.store L LC) (hst : LC.stack = []) (hne : cC.partners.isEmpty = false)
    (h : ConRon.Arena.Modular.reachPartners (modelFs F) pk sp env L c s = .ok ((L', c'), s')) :
    DStep s s' ∧ L'.ctx = L.ctx ∧ ∃ LC' cC', ReachLogRel s'.store L' LC' ∧
      CacheRel s'.store c' cC' ∧ ∀ (fuel : Nat) (R : Except ConLeche.CheckError
        (ConLeche.Driver.ReachLog × ConLeche.Driver.ReachCache)),
        ModelIO.Gives (ConLeche.Driver.reachGo envC fuel LC' cC') F R →
        ModelIO.Gives (ConLeche.Driver.reachGo envC (fuel + 1) LC cC) F R := by
  unfold ConRon.Arena.Modular.reachPartners at h
  obtain ⟨c₁, s₁, h1, h⟩ := AM.bind_ok h
  have hps : ListRel (NN s.store) c.partners.toList cC.partners.toList := hc.partners
  obtain ⟨hst1, cC₁, hg1, hc1⟩ := capturePairs_run hsp c.partners.toList hctx he
    (hc.withPartners (p := #[]) (pC := #[]) .nil) hps h1
  obtain ⟨hv, rfl⟩ := AM.pure_ok h
  cases hv
  have hw1 := (hctx.step hst1).wf
  obtain ⟨h1', h2'⟩ := pushNames_rel hw1 (listRel_map_snd (ListRel.mono' (fun _ _ h => h.ext hst1.ext) hps))
    (hL.seen.ext hst1.ext) .nil
  refine ⟨hst1, rfl, ConLeche.Driver.ReachLog.mk
      (ConLeche.Driver.pushNames LC.seen [] (cC.partners.toList.map (·.2))).1 LC.stored LC.ctx
      LC.homes LC.reads (ConLeche.Driver.pushNames LC.seen [] (cC.partners.toList.map (·.2))).2, cC₁,
    ⟨h1', hL.stored.ext hst1.ext, denoteDecls_ext hst1.ext _ _ hL.ctx,
      ListRel.mono' (fun _ _ h => denoteN_ext h hst1.ext) hL.homes,
      ListRel.mono' (fun _ _ h => ListRel.mono' (fun _ _ h => denoteN_ext h hst1.ext) h) hL.reads, h2'⟩,
    hc1, fun fuel R hR => ?_⟩
  rw [ConLeche.Driver.reachGo]
  simp only [hst, hne, Bool.false_eq_true, ↓reduceIte]
  refine hg1.bind ?_
  simp only
  exact hR

/-- con-leche: ConLeche/Driver/Reach.lean:788-826 reachGo — **the worklist at the twin is
upstream's**: an accepting twin run at fuel `fuel`, from related logs and caches, gives upstream's
run, at any fuel at least the twin's, accepting with the related log and caches. -/
theorem reachGo_run (hRR : ReadRecordHyp) {pk : OleanPins} {F : FS} {sp : Roots}
    (hsp : sp.bare = sp) {env : ConRon.Arena.Modular.ReachEnv}
    {envC : ConLeche.Driver.ReachEnv ModelIO} :
    ∀ (fuel : Nat) {L L' : ConRon.Arena.Modular.ReachLog} {LC : ConLeche.Driver.ReachLog}
      {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache} {s s' : AState}
      (fuelC : Nat), fuel ≤ fuelC → RCtx pk s → EnvRel sp s.store env envC →
      CacheRel s.store c cC → ReachLogRel s.store L LC → (∀ d ∈ L.ctx.toList, PersDecl d) →
      ConRon.Arena.Modular.reachGo (modelFs F) pk sp env fuel L c s = .ok ((L', c'), s') →
      DStep s s' ∧ (∀ d ∈ L'.ctx.toList, PersDecl d) ∧ ∃ LC' cC',
        ModelIO.Gives (ConLeche.Driver.reachGo envC fuelC LC cC) F (.ok (LC', cC')) ∧
        ReachLogRel s'.store L' LC' ∧ CacheRel s'.store c' cC'
  | fuel, L, L', LC, c, c', cC, s, s', fuelC, hle, hctx, he, hc, hL, hpL, h => by
    have hpe : c.partners.isEmpty = cC.partners.isEmpty := by
      have hsz : c.partners.size = cC.partners.size := by simpa using listRel_length hc.partners
      unfold Array.isEmpty
      rw [hsz]
    have hrs := hL.stack
    rcases hLs : L.stack with _ | ⟨x, rest⟩
    · rw [hLs] at hrs
      generalize hLCs : LC.stack = lsC at hrs
      cases hrs
      rw [ConRon.Arena.Modular.reachGo.eq_def] at h
      simp only [hLs] at h
      by_cases hemp : c.partners.isEmpty = true
      · rw [ite_eq_left hemp] at h
        obtain ⟨hv, rfl⟩ := AM.pure_ok h
        cases hv
        refine ⟨DStep.refl hctx.ok hctx.off, hpL, LC, cC, ?_, hL, hc⟩
        rw [ConLeche.Driver.reachGo.eq_def]
        simp only [hLCs, ← hpe, hemp, ↓reduceIte]
        exact ModelIO.gives_pure _ _
      · rw [ite_eq_right hemp] at h
        cases fuel with
        | zero => exact (AM.fail_ok h).elim
        | succ f =>
          obtain ⟨⟨L₁, c₁⟩, s₁, h1, h⟩ := AM.bind_ok h
          obtain ⟨hst1, hctxL, LC₁, cC₁, hL1, hc1, hstep⟩ :=
            reachPartners_run hsp hctx he hc hL hLCs (by rw [← hpe]; simpa using hemp) h1
          have hctx1 := hctx.step hst1
          obtain ⟨k, rfl⟩ : ∃ k, fuelC = k + 1 := ⟨fuelC - 1, by omega⟩
          obtain ⟨hst2, hp2, LC', cC', hg, hL', hc'⟩ := reachGo_run hRR hsp f k (by omega) hctx1
            (he.ext hst1.ext hctx1.wf) hc1 hL1 (by rw [hctxL]; exact hpL) h
          exact ⟨hst1.trans hst2, hp2, LC', cC', hstep k _ hg, hL', hc'⟩
    · rw [hLs] at hrs
      generalize hq : LC.stack = lsC at hrs
      cases hrs with
      | cons hx hrest =>
        rename_i xC restC
        rw [ConRon.Arena.Modular.reachGo.eq_def] at h
        simp only [hLs] at h
        cases fuel with
        | zero => exact (AM.fail_ok h).elim
        | succ f =>
          obtain ⟨⟨L₁, c₁⟩, s₁, h1, h⟩ := AM.bind_ok h
          have hL0 : ReachLogRel s.store { L with stack := rest } { LC with stack := restC } :=
            ⟨hL.seen, hL.stored, hL.ctx, hL.homes, hL.reads, hrest⟩
          obtain ⟨hst1, hp1, LC₁, cC₁, hL1, hc1, hstep⟩ :=
            reachRead_run hRR hsp hctx he hc hL0 hq hx hpL h1
          have hctx1 := hctx.step hst1
          obtain ⟨k, rfl⟩ : ∃ k, fuelC = k + 1 := ⟨fuelC - 1, by omega⟩
          obtain ⟨hst2, hp2, LC', cC', hg, hL', hc'⟩ := reachGo_run hRR hsp f k (by omega) hctx1
            (he.ext hst1.ext hctx1.wf) hc1 hL1 hp1 h
          exact ⟨hst1.trans hst2, hp2, LC', cC', hstep k _ hg, hL', hc'⟩

end ConRon.Bridge.Modular
