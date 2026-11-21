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
    sp.bare = sp → RCtx pk s → PinsRel s.store pk → EnvRel sp s.store env envC →
    CacheRel s.store c cC → denoteN s.store.ns x = some xC →
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
    (hctx : RCtx pk s) (hpk : PinsRel s.store pk) (he : EnvRel sp s.store env envC)
    (hc : CacheRel s.store c cC)
    (hL : ReachLogRel s.store L { LC with stack := restC }) (hst : LC.stack = xC :: restC)
    (hx : denoteN s.store.ns x = some xC) (hpL : ∀ d ∈ L.ctx.toList, PersDecl d)
    (hsz : L.homes.size = L.ctx.size)
    (h : ConRon.Arena.Modular.reachRead (modelFs F) pk sp env L c x s = .ok ((L', c'), s')) :
    DStep s s' ∧ (∀ d ∈ L'.ctx.toList, PersDecl d) ∧ L'.homes.size = L'.ctx.size ∧
      ∃ LC' cC', ReachLogRel s'.store L' LC' ∧
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
    refine ⟨DStep.refl hctx.ok hctx.off, hpL, hsz, { LC with stack := restC }, cC, hL, hc,
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
  obtain ⟨hst1, hpd, cC₁, dC, hC, hg1, hc1, hd1, hh1⟩ := hRR hsp hctx hpk he hc hx h1
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
    by simp [ConRon.Arena.Modular.ReachLog.add, hsz], LC.add dC hC (ConLeche.Cached.recordReads dC).toList restC,
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
    DStep s s' ∧ L'.ctx = L.ctx ∧ L'.homes = L.homes ∧ ∃ LC' cC', ReachLogRel s'.store L' LC' ∧
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
  refine ⟨hst1, rfl, rfl, ConLeche.Driver.ReachLog.mk
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
      (fuelC : Nat), fuel ≤ fuelC → RCtx pk s → PinsRel s.store pk → EnvRel sp s.store env envC →
      CacheRel s.store c cC → ReachLogRel s.store L LC → (∀ d ∈ L.ctx.toList, PersDecl d) →
      L.homes.size = L.ctx.size →
      ConRon.Arena.Modular.reachGo (modelFs F) pk sp env fuel L c s = .ok ((L', c'), s') →
      DStep s s' ∧ (∀ d ∈ L'.ctx.toList, PersDecl d) ∧ L'.homes.size = L'.ctx.size ∧ ∃ LC' cC',
        ModelIO.Gives (ConLeche.Driver.reachGo envC fuelC LC cC) F (.ok (LC', cC')) ∧
        ReachLogRel s'.store L' LC' ∧ CacheRel s'.store c' cC'
  | fuel, L, L', LC, c, c', cC, s, s', fuelC, hle, hctx, hpk, he, hc, hL, hpL, hsz, h => by
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
        refine ⟨DStep.refl hctx.ok hctx.off, hpL, hsz, LC, cC, ?_, hL, hc⟩
        rw [ConLeche.Driver.reachGo.eq_def]
        simp only [hLCs, ← hpe, hemp, ↓reduceIte]
        exact ModelIO.gives_pure _ _
      · rw [ite_eq_right hemp] at h
        cases fuel with
        | zero => exact (AM.fail_ok h).elim
        | succ f =>
          obtain ⟨⟨L₁, c₁⟩, s₁, h1, h⟩ := AM.bind_ok h
          obtain ⟨hst1, hctxL, hhomL, LC₁, cC₁, hL1, hc1, hstep⟩ :=
            reachPartners_run hsp hctx he hc hL hLCs (by rw [← hpe]; simpa using hemp) h1
          have hctx1 := hctx.step hst1
          obtain ⟨k, rfl⟩ : ∃ k, fuelC = k + 1 := ⟨fuelC - 1, by omega⟩
          obtain ⟨hst2, hp2, hsz2, LC', cC', hg, hL', hc'⟩ := reachGo_run hRR hsp f k (by omega) hctx1
            (hpk.ext hst1.ext) (he.ext hst1.ext hctx1.wf) hc1 hL1 (by rw [hctxL]; exact hpL) (by rw [hctxL, hhomL]; exact hsz) h
          exact ⟨hst1.trans hst2, hp2, hsz2, LC', cC', hstep k _ hg, hL', hc'⟩
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
          obtain ⟨hst1, hp1, hsz1, LC₁, cC₁, hL1, hc1, hstep⟩ :=
            reachRead_run hRR hsp hctx hpk he hc hL0 hq hx hpL hsz h1
          have hctx1 := hctx.step hst1
          obtain ⟨k, rfl⟩ : ∃ k, fuelC = k + 1 := ⟨fuelC - 1, by omega⟩
          obtain ⟨hst2, hp2, hsz2, LC', cC', hg, hL', hc'⟩ := reachGo_run hRR hsp f k (by omega) hctx1
            (hpk.ext hst1.ext) (he.ext hst1.ext hctx1.wf) hc1 hL1 hp1 hsz1 h
          exact ⟨hst1.trans hst2, hp2, hsz2, LC', cC', hstep k _ hg, hL', hc'⟩

/-! ## The reach's fuel -/

/-- An injective map from a list without repeats into another list: the first no longer. -/
theorem length_le_of_inj {α β : Type} [BEq β] [LawfulBEq β] (f : α → Option β) :
    ∀ {l : List α} {l₂ : List β}, l.Nodup →
      (∀ a ∈ l, ∃ b ∈ l₂, f a = some b) →
      (∀ a ∈ l, ∀ a' ∈ l, ∀ b, f a = some b → f a' = some b → a = a') →
      l.length ≤ l₂.length
  | [], _, _, _, _ => Nat.zero_le _
  | a :: l, l₂, hnd, hm, hinj => by
    obtain ⟨b, hb, hfb⟩ := hm a (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.1 hnd
    have ih : l.length ≤ (l₂.erase b).length := by
      refine length_le_of_inj f hnd'.2 (fun a' ha' => ?_) (fun x hx y hy => hinj x
        (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      obtain ⟨b', hb', hfb'⟩ := hm a' (List.mem_cons_of_mem _ ha')
      refine ⟨b', (List.mem_erase_of_ne (fun he => ?_)).2 hb', hfb'⟩
      subst he
      have := hinj a (List.mem_cons_self ..) a' (List.mem_cons_of_mem _ ha') b' hfb hfb'
      subst this
      exact hnd'.1 ha'
    rw [List.length_erase_of_mem hb] at ih
    have : 0 < l₂.length := List.length_pos_of_mem hb
    simp only [List.length_cons]
    omega

/-- **A map over handles has no more entries than the map over names it denotes.** -/
theorem HMRel.size_le {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap NIdx α} {MC : Std.HashMap ConLeche.Name β} (h : HMRel R st M MC) :
    M.size ≤ MC.size := by
  rw [← Std.HashMap.length_keys, ← Std.HashMap.length_keys]
  refine length_le_of_inj (denoteN st.ns) Std.HashMap.nodup_keys (fun a ha => ?_)
    (fun a _ a' _ b h1 h2 => denoteN_inj hw h1 h2)
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_isSome_getElem?] at ha
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ha
  obtain ⟨n, b, hn, hb, -⟩ := h.fwd a v hv
  refine ⟨n, ?_, hn⟩
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_isSome_getElem?, hb]
  rfl

/-! ## The reach -/

/-- The records the read order picks are records of the log. -/
theorem inReadOrder_mem {L : ConRon.Arena.Modular.ReachLog} {o : Array Nat} :
    ∀ d ∈ (ConRon.Arena.Modular.inReadOrder L o).1.toList, d ∈ L.ctx.toList := by
  unfold ConRon.Arena.Modular.inReadOrder
  rw [← Array.foldl_toList]
  suffices ∀ (os : List Nat) (acc : Array IDeclaration × Array NIdx),
      (∀ d ∈ acc.1.toList, d ∈ L.ctx.toList) →
      ∀ d ∈ (os.foldl (fun (acc : Array IDeclaration × Array NIdx) j =>
        match L.ctx[j]?, L.homes[j]? with
        | some d, some h => (acc.1.push d, acc.2.push h)
        | _, _ => acc) acc).1.toList, d ∈ L.ctx.toList from this _ _ (by simp)
  intro os
  induction os with
  | nil => intro acc h; exact h
  | cons j os ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    split
    · rename_i d h hd _
      intro d' hd'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd'
      rcases hd' with hd' | rfl
      · exact hacc d' hd'
      · exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hd)
    · exact hacc

/-- con-leche: ConLeche/Driver/Reach.lean:937-968 reachWith — **Theorem 1 of the reach, given
the record read** (`ReadRecordHyp`): the twin's accept gives upstream's context, homes,
completions and counts, its pending statements read back, and upstream's reach answering it under
every flag inference accepting those statements. -/
theorem reachRunHyp_holds' (hRR : ReadRecordHyp) : ReachRunHyp := by
  intro pk F sp s s' m mC wr wrC own ownC roots rootsC r hsp hok hoff hpk hm hwr hkeys hown hroots h
  have hctx : RCtx pk s := ⟨hok, hoff, hpk.nulls⟩
  have hw := hctx.wf
  unfold ConRon.Arena.Modular.reach at h
  let envC : ConLeche.Driver.ReachEnv ModelIO :=
    { rd := .ofPath sp, mod := mC, wr := wrC, own := ownC,
      copies := ConLeche.Driver.clashCopiesOf wrC }
  have he : EnvRel sp s.store { mod := m, wr, own, copies := ConRon.Arena.Modular.clashCopiesOf pk wr }
      envC := ⟨rfl, hm, hwr, hkeys, hown, clashCopiesOf_rel hw hpk.nulls hwr⟩
  -- the clash rule
  obtain ⟨⟨c₁, extra⟩, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hst1, cC₁, accC, hg1, hc1, hacc⟩ :=
    clashAgree_run hsp hctx he (CacheRel.empty _) (by simpa using hwr.clashes) .nil h1
  have hctx1 := hctx.step hst1
  have hw1 := hctx1.wf
  have he1 := he.ext hst1.ext hw1
  -- the roots
  have hrs : ListRel (NR s₁.store) (ConRon.Arena.Modular.reachRoots own roots extra)
      ((rootsC ++ accC).toList.filter (!ownC.contains ·)) := by
    unfold ConRon.Arena.Modular.reachRoots
    refine listRel_filter (fun a b hab => by rw [(hown.ext hst1.ext).contains hw1 hab]) ?_
    simp only [Array.toList_append]
    exact listRel_append (ListRel.mono' (fun _ _ h => denoteN_ext h hst1.ext) hroots) hacc
  cases hfind : (ConRon.Arena.Modular.reachRoots own roots extra).find? (!wr.index.first.contains ·) with
  | some x =>
    exfalso
    simp only [hfind] at h
    obtain ⟨_, _, _, ha⟩ := AM.bind_ok h
    exact AM.fail_ok ha
  | none =>
  simp only [hfind] at h
  have hfindC : ((rootsC ++ accC).toList.filter (!ownC.contains ·)).find?
      (!wrC.index.first.contains ·) = none :=
    find?_none_rel (fun a b hab => by
      rw [HMRel.contains hw1 (hwr.index.first.ext' hst1.ext) hab]) hrs hfind
  -- the worklist
  obtain ⟨⟨L, c₂⟩, s₂, h2, h⟩ := AM.bind_ok h
  have hfuel : wr.index.first.size + wr.index.more.size + (1 <<< 24) ≤
      wrC.index.first.size + wrC.index.more.size + (1 <<< 24) := by
    have h1' := HMRel.size_le hw1 (hwr.index.first.ext' hst1.ext)
    have h2' : wr.index.more.size = wrC.index.more.size := by
      simpa using listRel_length hwr.index.more
    omega
  obtain ⟨hst2, hpL, hszL, LC, cC₂, hg2, hL, hc2⟩ := reachGo_run hRR hsp _ _ hfuel hctx1 (hpk.ext hst1.ext) he1 hc1
    (init_rel hw1 hrs) (by simp [ConRon.Arena.Modular.ReachLog.init]) (by simp [ConRon.Arena.Modular.ReachLog.init]) h2
  have hctx2 := hctx1.step hst2
  -- the read order
  obtain ⟨o, s₃, h3, h⟩ := AM.bind_ok h
  obtain ⟨hst3, ho⟩ := readOrder_run hctx2.ok hL.ctx hL.reads h3
  have hlt := readOrder_lt ho
  have hlenC : L.ctx.size = LC.ctx.size := by
    simpa using denoteDecls_length hL.ctx
  have hj : ∀ j ∈ o.toList, j < L.ctx.size ∧ j < L.homes.size := fun j hj => by
    have := hlt j hj; omega
  obtain ⟨hdc, hdh⟩ := inReadOrder_rel (hL.ext hst3.ext).ctx (hL.ext hst3.ext).homes hj
  -- the validation
  obtain ⟨u, s₄, h4, h⟩ := AM.bind_ok h
  have hoff3 : s₃.store.scratchOn = false := by rw [hst3.scr]; exact hctx2.off
  have hpctx : ∀ d ∈ (ConRon.Arena.Modular.inReadOrder L o).1.toList, PersDecl d :=
    fun d hd => hpL d (inReadOrder_mem d hd)
  obtain ⟨hst4, hoff4, hall⟩ := validateCtx_run hst3.ok hoff3 hpctx hdc h4
  obtain ⟨hv, rfl⟩ := AM.pure_ok h
  cases hv
  have hx34 : Ext s₃.store s'.store := hst4.ext
  have hx24 : Ext s₂.store s'.store := hst3.ext.trans hst4.ext
  refine ⟨⟨hst4.ok, (hst1.ext.trans hst2.ext).trans hx24,
      by rw [hst4.pins, hst3.pins, hst2.pins, hst1.pins], hoff4⟩, hpctx,
    ⟨o.map (LC.ctx.getD · default), o.map (LC.homes.getD · default), cC₂.completed,
      cC₂.searches, cC₂.pending.size⟩, cC₂.pending.toList, ?_, ?_, fun fl hfl => ?_⟩
  · refine ⟨?_, ?_, ListRel.mono' (fun _ _ h => ⟨denoteN_ext h.1 hx24, denoteN_ext h.2 hx24⟩)
      hc2.completed, hc2.searches, ?_⟩
    · simpa [Array.getD_eq_getD_getElem?] using denoteDecls_ext hx34 _ _ hdc
    · simpa [Array.getD_eq_getD_getElem?] using ListRel.mono' (fun _ _ h => denoteN_ext h hx34) hdh
    · simpa using listRel_length hc2.pending
  · exact ListRel.mono' (fun _ _ h => h.ext hx24) hc2.pending
  · -- upstream's reach
    refine ModelIO.Gives.canGive ?_
    unfold ConLeche.Driver.reachWith
    refine hg1.bind ?_
    simp only
    rw [hfindC]
    simp only
    refine hg2.bind ?_
    simp only [ho]
    have hallC : (o.map (LC.ctx.getD · default)).all ConLeche.Driver.recordOk = true := by
      rw [← Array.all_toList]
      simpa [Array.getD_eq_getD_getElem?] using hall
    simp only [ConLeche.Driver.validateCtx, hallC, ↓reduceIte]
    rw [show fl (o.map (LC.ctx.getD · default)).toList cC₂.pending.toList = .ok () from hfl]
    exact ModelIO.gives_pure _ _


/-- con-leche: ConLeche/Driver/Reach.lean:693-729 readRecord — **the record read at `x`**
(`readRecord_run`). -/
theorem readRecordHyp_holds : ReadRecordHyp :=
  fun hsp hctx hpk he hc hx h => readRecord_run hsp hctx hpk he hc hx h

/-- con-leche: ConLeche/Driver/Reach.lean:937-968 reachWith — **Theorem 1 of the reach**: the twin's
reach is upstream's under every flag inference accepting its pending statements. -/
theorem reachRunHyp_holds : ReachRunHyp := reachRunHyp_holds' readRecordHyp_holds

end ConRon.Bridge.Modular
