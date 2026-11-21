/-
# `ConRon.Bridge.Modular.Worker` — the worker's own records, Theorem 1 (task #166)

**What the twin's worker computes besides the reads, the reach and the copies, upstream's
computes on the denotations.**  The own records (`ownRecords_run`): the load's unskipped
constants merged (`mergedOfList_rel`), their blocks checked, emitted and parsed, as on `--olean`
(`Bridge/Frontend/Olean/Records.lean`'s lemmas, over any merge).

Run style (`readOleans_run`'s), not `sym … vcgen … finish`: the steps are the flat reader's
lemmas, glued.
-/
module

public import ConRon.Bridge.Modular.Rel
public import ConRon.Bridge.Frontend.Olean.Records
public import ConRon.Bridge.Checker.Install
import Std.Data.HashMap.Lemmas

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins Merged CEntry Loaded)
open ConLeche.Frontend.Olean (CEntryF CKindF Copy bind_some_left)

/-! ## A merge of a list -/

/-- A merge's lookups and keys decide its relation: two merges that answer alike are related
alike. -/
theorem MergedRel.congr {st : EStore} {mg mg' : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    (h : MergedRel st mg mgC) (hget : ∀ n, mg'.get n = mg.get n) (hmap : mg'.map = mg.map)
    (hord : mg'.order = mg.order) : MergedRel st mg' mgC :=
  ⟨fun hdn hx => h.got hdn (by rw [← hget]; exact hx),
   fun hdn hx => h.absent hdn (by rw [← hget]; exact hx),
   fun hdn => by rw [hmap]; exact h.contains hdn,
   by rw [hord]; exact h.order,
   fun hp => h.keys (by rw [← hmap]; exact hp),
   fun hz => by rw [hmap]; exact h.keysC hz⟩

/-- The twin's merge of a list, its parts. -/
@[expose] def mOf (pk : OleanPins) (x : Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array CEntry) :
    Merged :=
  { ls := #[{ name := pk.anon, constants := x.2.2, frontier := {} }], map := x.1, order := x.2.1 }

/-- con-leche: none — the fold's invariant: every key at a kept constant of its name, the merge
related, upstream's keys their constants' names. -/
structure MInv (st : EStore) (pk : OleanPins)
    (x : Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array CEntry)
    (mgC : ConLeche.Frontend.Olean.Merged) : Prop where
  keys : ∀ (n : NIdx) (p : Nat × Nat), x.1[n]? = some p → p.1 = 0 ∧
    ∃ c : CEntry, x.2.2[p.2]? = some c ∧ c.c.name = n
  rel : MergedRel st (mOf pk x) mgC
  names : ∀ (n : ConLeche.Name) (c : ConLeche.Frontend.Olean.CEntry), mgC.map[n]? = some c → c.name = n

theorem MInv.empty (st : EStore) (pk : OleanPins) : MInv st pk ({}, #[], #[]) {} where
  keys := fun _ _ h => by simp at h
  rel := ⟨fun _ hx => by simp [mOf, Merged.get] at hx, fun _ _ => by simp,
    fun _ => by simp [mOf], .nil, fun hp => by simp [mOf] at hp,
    fun hz => by simp at hz⟩
  names := fun _ _ h => by simp at h

theorem mergedOfList_step {st : EStore} (hw : NStoreWF st.ns) {pk : OleanPins}
    {x : Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array CEntry}
    {mgC : ConLeche.Frontend.Olean.Merged} (hi : MInv st pk x mgC) {c : CEntry}
    {cC : ConLeche.Frontend.Olean.CEntry} (hd : denoteCEntry st c = some cC) :
    MInv st pk
      (if x.1.contains c.c.name then x
       else (x.1.insert c.c.name (0, x.2.2.size), x.2.1.push c.c.name, x.2.2.push c))
      (if mgC.map.contains cC.name then mgC
       else { map := mgC.map.insert cC.name cC, order := mgC.order.push cC.name }) := by
  obtain ⟨hn, -, -, -⟩ := denoteCEntry_parts hd
  have hc := hi.rel.contains hn
  simp only [mOf] at hc
  by_cases hk : x.1.contains c.c.name = true
  · rw [ite_eq_left hk, ite_eq_left (hc ▸ hk)]
    exact hi
  · rw [ite_eq_right hk, ite_eq_right (by rw [← hc]; exact hk)]
    obtain ⟨map, order, kept⟩ := x
    simp only at hk ⊢
    -- the kept list grown: the old lookups unchanged
    have hget : ∀ n, (mOf pk (map, order, kept.push c)).get n = (mOf pk (map, order, kept)).get n := by
      intro n
      simp only [mOf, Merged.get]
      cases hm : map[n]? with
      | none => rfl
      | some p =>
        obtain ⟨-, c', hc', -⟩ := hi.keys n p hm
        have hlt : p.2 < kept.size := by
          rcases Array.getElem?_eq_some_iff.mp hc' with ⟨h, -⟩
          exact h
        cases p with
        | mk m i =>
          have hlt' : i < kept.size := hlt
          simp only [Array.getElem?_singleton]
          split
          · simp [Array.getElem?_push, Nat.ne_of_lt hlt']
          · rfl
    have hrel1 : MergedRel st (mOf pk (map, order, kept.push c)) mgC :=
      MergedRel.congr hi.rel hget rfl rfl
    have hself : ((mOf pk (map, order, kept.push c)).ls[0]?).bind (·.constants[kept.size]?) = some c := by
      simp [mOf]
    have hord : ListRel (NR st) (order.push c.c.name).toList (mgC.order.push cC.name).toList :=
      array_rel_push hi.rel.order hn
    have hrel2 := MergedRel.insert hw hrel1 hself hd (order.push c.c.name) (mgC.order.push cC.name) hord
    refine ⟨fun n p hp => ?_, ?_, fun n z hz => ?_⟩
    · rw [Std.HashMap.getElem?_insert] at hp
      by_cases e : c.c.name = n
      · rw [ite_eq_left (by simpa using e)] at hp
        cases hp
        exact ⟨rfl, c, by simp, e⟩
      · rw [ite_eq_right (by simpa using e)] at hp
        obtain ⟨h1, c', hc', hn'⟩ := hi.keys n p hp
        refine ⟨h1, c', ?_, hn'⟩
        have hlt : p.2 < kept.size := (Array.getElem?_eq_some_iff.mp hc').1
        simpa [Array.getElem?_push, Nat.ne_of_lt hlt] using hc'
    · exact hrel2
    · rw [Std.HashMap.getElem?_insert] at hz
      by_cases e : cC.name = n
      · rw [ite_eq_left (by simpa using e)] at hz
        cases hz
        exact e
      · rw [ite_eq_right (by simpa using e)] at hz
        exact hi.names n z hz

/-- The twin's fold step of `mergedOfList`. -/
@[expose] def mStep (acc : Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array CEntry) (c : CEntry) :
    Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array CEntry :=
  if acc.1.contains c.c.name then acc
  else (acc.1.insert c.c.name (0, acc.2.2.size), acc.2.1.push c.c.name, acc.2.2.push c)

/-- Upstream's fold step of `mergedOfList`. -/
@[expose] def mStepC (mg : ConLeche.Frontend.Olean.Merged) (c : ConLeche.Frontend.Olean.CEntry) :
    ConLeche.Frontend.Olean.Merged :=
  if mg.map.contains c.name then mg
  else { map := mg.map.insert c.name c, order := mg.order.push c.name }

theorem mergedOfList_fold {st : EStore} (hw : NStoreWF st.ns) {pk : OleanPins} :
    ∀ {cs : List CEntry} {csC : List ConLeche.Frontend.Olean.CEntry},
      ListRel (fun c cC => denoteCEntry st c = some cC) cs csC →
      ∀ {x mgC}, MInv st pk x mgC → MInv st pk (cs.foldl mStep x) (csC.foldl mStepC mgC)
  | _, _, .nil, _, _, hi => hi
  | _, _, .cons hd hr, _, _, hi => by
    simp only [List.foldl_cons]
    exact mergedOfList_fold hw hr (mergedOfList_step hw hi hd)

theorem mergedOfList_eq (pk : OleanPins) (cs : Array CEntry) :
    ConRon.Arena.Frontend.Olean.mergedOfList pk cs = mOf pk (cs.toList.foldl mStep ({}, #[], #[])) := by
  unfold ConRon.Arena.Frontend.Olean.mergedOfList
  rw [← Array.foldl_toList]
  have : (fun (acc : Std.HashMap NIdx (Nat × Nat) × Array NIdx × Array CEntry) (c : CEntry) =>
      let (map, order, kept) := acc
      if map.contains c.c.name then acc
      else (map.insert c.c.name (0, kept.size), order.push c.c.name, kept.push c)) = mStep := by
    funext acc c
    obtain ⟨a, b, d⟩ := acc
    rfl
  rw [this]
  generalize cs.toList.foldl mStep ({}, #[], #[]) = r
  obtain ⟨a, b, d⟩ := r
  rfl

theorem mergedOfListC_eq (cs : List ConLeche.Frontend.Olean.CEntry) :
    ConLeche.Frontend.Olean.mergedOfList cs = cs.foldl mStepC {} := rfl

/-- con-leche: ConLeche/Frontend/Olean/Group.lean:31-35 mergedOfList — **the twin's merge of a
list denotes upstream's**, the emitter's context. -/
theorem mergedOfList_rel {st : EStore} (hw : NStoreWF st.ns) (pk : OleanPins) {cs : Array CEntry}
    {csC : List ConLeche.Frontend.Olean.CEntry}
    (h : ListRel (fun c cC => denoteCEntry st c = some cC) cs.toList csC) :
    WalkCtx st (ConRon.Arena.Frontend.Olean.mergedOfList pk cs)
      (ConLeche.Frontend.Olean.mergedOfList csC) := by
  have hi := mergedOfList_fold hw h (MInv.empty st pk)
  rw [mergedOfList_eq, mergedOfListC_eq]
  exact ⟨hi.rel, hw, hi.names⟩

/-! ## The own records -/

theorem listRel_filter {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {l : List α} {ys : List β}, ListRel R l ys → ListRel R (l.filter p) (ys.filter q)
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons hab hr => by
    simp only [List.filter_cons, hpq a b hab]
    split
    · exact .cons hab (listRel_filter hpq hr)
    · exact listRel_filter hpq hr

/-- A constant's filter, read back. -/
theorem denoteCEntry_skipped {st : EStore} {c : CEntry} {cC : ConLeche.Frontend.Olean.CEntry}
    (h : denoteCEntry st c = some cC) : c.skipped = cC.skipped := by
  obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts h
  exact (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).2

/-- con-leche: ConLeche/Driver/Worker.lean:44-51 ownRecords — **the own records, upstream's**:
where the twin's emission of a module's unskipped constants answers, upstream's does, and its
records denote upstream's. -/
theorem ownRecords_run {pk : OleanPins} {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) (hp : PinsRel s.store pk)
    {l : Loaded} {lC : ConLeche.Frontend.Olean.Loaded} (hl : LoadedRel s.store l lC)
    {ds : Array IDeclaration}
    (h : ConRon.Arena.Modular.ownRecords pk l s = .ok (.ok ds, s')) :
    ParseStep s s' ∧ PersDecls ds ∧ ∃ dsC, ConLeche.Driver.ownRecords lC = .ok dsC ∧
      denoteDeclArray s'.store ds = some dsC := by
  have hw := nsWF_of_StateOK hok
  have hcs : ListRel (fun c cC => denoteCEntry s.store c = some cC)
      (ConRon.Arena.Modular.unskipped l.constants).toList
      (lC.constants.toList.filter (!·.skipped)) := by
    simp only [ConRon.Arena.Modular.unskipped, Array.toList_filter]
    exact listRel_filter (fun a b hab => by rw [denoteCEntry_skipped hab])
      (listRel_of_mapM hl.constants)
  have hwc := mergedOfList_rel hw pk hcs
  unfold ConRon.Arena.Modular.ownRecords at h
  obtain ⟨u, s₁, h1, k1⟩ := AM.bind_ok h
  clear h
  obtain ⟨hs1, hb⟩ := blocksOk_run hwc hp h1
  subst hs1
  obtain ⟨em, s₂, h2, k2⟩ := AM.bind_ok k1
  obtain ⟨hs2, hem⟩ := emitAll_run hwc hp hwc.rel.order h2
  subst hs2
  obtain ⟨x, s₃, h3, k3⟩ := AM.bind_ok k2
  cases x with
  | error e => cases (AM.pure_ok k3).1
  | ok p =>
  obtain ⟨hv, hs⟩ := AM.pure_ok k3
  cases hv
  subst hs
  obtain ⟨hst, hpers, dsC, hds, hden⟩ := declsOf_run hok hoff hpins hem h3
  refine ⟨hst, hpers, dsC, ?_, hden⟩
  unfold ConLeche.Driver.ownRecords
  simp only [hb, hds]

/-! ## A record's names -/

/-- con-leche: none — **a step of the driver's state**: the core invariant at the empty
environment kept (`DriverOK`), the store extended, the pins and the closed scratch tier kept;
what the installs' readers (`constsSpec`) keep. -/
structure DStep (s s' : AState) : Prop where
  ok : DriverOK s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins
  scratch : s'.store.scratchOn = false

theorem DStep.refl {s : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false) : DStep s s :=
  ⟨hok, Ext.refl _, rfl, hoff⟩

theorem DStep.trans {a b c : AState} (h₁ : DStep a b) (h₂ : DStep b c) : DStep a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, h₂.pins.trans h₁.pins, h₂.scratch⟩

/-- A parse step from a driver's state is a step of it. -/
theorem DStep.of_parse {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    (h : ParseStep s s') : DStep s s' :=
  ⟨DriverOK.of_pstep hok ⟨h.ok, h.ext, h.cframe, h.pins⟩, h.ext, h.pins, by rw [h.scratch]; exact hoff⟩

/-- con-leche: ConLeche/Modular.lean:98-99 declNames — **a record's names, upstream's**. -/
theorem declNames_run {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    {d : IDeclaration} {dC : Declaration} (hp : PersDecl d)
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dC) {ns : List NIdx}
    (h : ConRon.Arena.Modular.declNames d s = .ok (ns, s')) :
    DStep s s' ∧ ConRon.Arena.Frontend.denoteNList s'.store.ns ns = some (ConLeche.Modular.declNames dC) := by
  unfold ConRon.Arena.Modular.declNames at h
  obtain ⟨L, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hv, rfl⟩ := AM.pure_ok h
  subst hv
  obtain ⟨hok1, hx, hpins, hoff1, hL, -⟩ := constsSpec hok hoff hp hd h1
  exact ⟨⟨hok1, hx, hpins, hoff1⟩, ciNames_denote hL⟩

/-! ## The context's names distinct -/

theorem namesNodupGo_spec' :
    ∀ (ns : List NIdx) (t t' : Std.HashSet NIdx),
      ConRon.Arena.Modular.namesNodupGo t ns = (true, t') →
      ns.Nodup ∧ (∀ x ∈ ns, t.contains x = false) ∧
        ∀ x, t'.contains x = true ↔ (t.contains x = true ∨ x ∈ ns)
  | [], t, t', h => by
    simp only [ConRon.Arena.Modular.namesNodupGo, Prod.mk.injEq, true_and] at h
    subst h
    simp
  | n :: ns, t, t', h => by
    simp only [ConRon.Arena.Modular.namesNodupGo] at h
    split at h
    · cases h
    · rename_i hn
      obtain ⟨h1, h2, h3⟩ := namesNodupGo_spec' ns _ _ h
      refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, h1⟩, fun x hx => ?_, fun x => ?_⟩
      · have := h2 n hm
        simp at this
      · rcases List.mem_cons.1 hx with rfl | hx
        · simpa using hn
        · have := h2 x hx
          simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at this
          exact this.2
      · rw [h3 x]
        simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inr (Or.inl h.symm)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h.symm)
          · exact Or.inr h

theorem ctxNamesNodupGo_run :
    ∀ (ds : List IDeclaration) {dsC : List Declaration} (t : Std.HashSet NIdx) {s s' : AState},
      DriverOK s → s.store.scratchOn = false → (∀ d ∈ ds, PersDecl d) →
      denoteDecls s.store ds = some dsC →
      ConRon.Arena.Modular.ctxNamesNodupGo t ds s = .ok (true, s') →
      DStep s s' ∧ ∃ hs, ConRon.Arena.Frontend.denoteNList s'.store.ns hs =
          some (dsC.flatMap ConLeche.Modular.declNames) ∧ hs.Nodup ∧ ∀ x ∈ hs, t.contains x = false
  | [], dsC, t, s, s', hok, hoff, _, hd, h => by
    simp only [denoteDecls, Option.some.injEq] at hd
    subst hd
    simp only [ConRon.Arena.Modular.ctxNamesNodupGo] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨DStep.refl hok hoff, [], rfl, List.nodup_nil, fun _ h => nomatch h⟩
  | d :: ds, dsC, t, s, s', hok, hoff, hp, hd, h => by
    simp only [denoteDecls] at hd
    split at hd
    · rename_i dC dsC' hd1 hds
      cases hd
      simp only [ConRon.Arena.Modular.ctxNamesNodupGo] at h
      obtain ⟨ns, s₁, h1, h⟩ := AM.bind_ok h
      obtain ⟨hst1, hns⟩ := declNames_run hok hoff (hp d (List.mem_cons_self ..)) hd1 h1
      cases hg : ConRon.Arena.Modular.namesNodupGo t ns with
      | mk ok t' =>
      rw [hg] at h
      cases ok with
      | false => cases (AM.pure_ok h).1
      | true =>
      simp only [↓reduceIte] at h
      obtain ⟨g1, g2, g3⟩ := namesNodupGo_spec' ns t t' hg
      obtain ⟨hst2, hs, hhs, hnd, hdis⟩ := ctxNamesNodupGo_run ds t' hst1.ok hst1.scratch
        (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (denoteDecls_ext hst1.ext _ _ hds) h
      refine ⟨hst1.trans hst2, ns ++ hs, ?_, ?_, fun x hx => ?_⟩
      · simp only [List.flatMap_cons]
        exact denoteNList_append' (denoteNList_ext hst2.ext.lss.ls.ns _ _ hns) hhs
      · refine List.nodup_append.2 ⟨g1, hnd, fun a ha b hb hab => ?_⟩
        subst hab
        have := hdis a hb
        rw [(g3 a).2 (Or.inr ha)] at this
        cases this
      · rcases List.mem_append.1 hx with hx | hx
        · exact g2 x hx
        · have := hdis x hx
          cases e : t.contains x
          · rfl
          · rw [(g3 x).2 (Or.inl e)] at this; cases this
    · cases hd

theorem denoteNList_mem {st : NStore} :
    ∀ {hs : List NIdx} {xs : List ConLeche.Name}, ConRon.Arena.Frontend.denoteNList st hs = some xs →
      ∀ y ∈ xs, ∃ h ∈ hs, denoteN st h = some y
  | [], xs, h, y, hy => by
    simp only [ConRon.Arena.Frontend.denoteNList, Option.some.injEq] at h
    subst h; cases hy
  | a :: hs, xs, h, y, hy => by
    simp only [ConRon.Arena.Frontend.denoteNList] at h
    split at h
    · rename_i x xs' hx hxs
      cases h
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨a, List.mem_cons_self .., hx⟩
      · obtain ⟨h', hm, hd⟩ := denoteNList_mem hxs y hy
        exact ⟨h', List.mem_cons_of_mem _ hm, hd⟩
    · cases h

theorem denoteNList_nodup {st : NStore} (hw : NStoreWF st) :
    ∀ {hs : List NIdx} {xs : List ConLeche.Name}, ConRon.Arena.Frontend.denoteNList st hs = some xs →
      hs.Nodup → xs.Nodup
  | [], xs, h, _ => by
    simp only [ConRon.Arena.Frontend.denoteNList, Option.some.injEq] at h
    subst h; exact List.nodup_nil
  | a :: hs, xs, h, hnd => by
    simp only [ConRon.Arena.Frontend.denoteNList] at h
    split at h
    · rename_i x xs' hx hxs
      cases h
      obtain ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
      refine List.nodup_cons.2 ⟨fun hm => ?_, denoteNList_nodup hw hxs hnd'⟩
      obtain ⟨h', hm', hd'⟩ := denoteNList_mem hxs x hm
      exact hna (denoteN_inj hw hd' hx ▸ hm')
    · cases h

/-- con-leche: ConLeche/Driver/Worker.lean:322-323 workerRead — **the context's names
distinct**, upstream's `nodup` field: the twin's check over handles, read back through the
store's one-to-one names. -/
theorem ctxNamesNodup_run {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    {ctx : Array IDeclaration} {ctxC : List Declaration} (hp : ∀ d ∈ ctx.toList, PersDecl d)
    (hd : denoteDecls s.store ctx.toList = some ctxC)
    (h : ConRon.Arena.Modular.ctxNamesNodup ctx s = .ok (true, s')) :
    DStep s s' ∧ (ctxC.flatMap ConLeche.Modular.declNames).Nodup := by
  obtain ⟨hst, hs, hhs, hnd, -⟩ := ctxNamesNodupGo_run ctx.toList {} hok hoff hp hd h
  refine ⟨hst, ?_⟩
  exact denoteNList_nodup (nsWF_of_StateOK hst.ok.state) hhs hnd

/-! ## The own names -/

/-- A map over handles against one over names: `contains` answers alike. -/
theorem HMRel.contains {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap NIdx α} {MC : Std.HashMap ConLeche.Name β} (h : HMRel R st M MC) {x : NIdx}
    {n : ConLeche.Name} (hd : denoteN st.ns x = some n) : M.contains x = MC.contains n := by
  rcases optRel_cases (h.get hw hd) with ⟨h1, h2⟩ | ⟨a, b, h1, h2, -⟩
  · simp [Std.HashMap.contains_eq_isSome_getElem?, h1, h2]
  · simp [Std.HashMap.contains_eq_isSome_getElem?, h1, h2]

/-- Added imports read back: empty alike. -/
theorem ImpsD.isEmpty {st : EStore} {x : Array (ConLeche.Frontend.Olean.ImportF NIdx)}
    {xC : Array ConLeche.Frontend.Olean.ImportRec} (h : ImpsD st x xC) : x.isEmpty = xC.isEmpty := by
  have hl := (listRel_of_mapM h).length_eq
  have hs : x.size = xC.size := by simpa using hl
  simp [Array.isEmpty, hs]

theorem ownNamesFold_rel {st : EStore} {P : CEntry → Bool} {PC : ConLeche.Frontend.Olean.CEntry → Bool}
    (hP : ∀ c cC, denoteCEntry st c = some cC → P c = PC cC) :
    ∀ {cs : List CEntry} {csC : List ConLeche.Frontend.Olean.CEntry},
      ListRel (fun c cC => denoteCEntry st c = some cC) cs csC →
      ∀ {t tC}, SetRel st t tC →
      SetRel st (cs.foldl (fun s c => if P c then s else s.insert c.c.name) t)
        (csC.foldl (fun s c => if PC c then s else s.insert c.name) tC)
  | _, _, .nil, _, _, h => h
  | c :: _, cC :: _, .cons hc hr, _, _, h => by
    simp only [List.foldl_cons]
    refine ownNamesFold_rel hP hr ?_
    rw [hP c cC hc]
    split
    · exact h
    · exact h.insert (denoteCEntry_parts hc).1

/-- con-leche: ConLeche/Driver/Worker.lean:137-141 ownNamesOf — **the reach's own names,
upstream's**. -/
theorem ownNamesOf_rel {st : EStore} (hw : NStoreWF st.ns)
    {x : Array (ConLeche.Frontend.Olean.ImportF NIdx)} {xC : Array ConLeche.Frontend.Olean.ImportRec}
    (hx : ImpsD st x xC) {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (hix : IndexRel st ix ixC)
    {l : Loaded} {lC : ConLeche.Frontend.Olean.Loaded} (hl : LoadedRel st l lC) :
    SetRel st (ConRon.Arena.Modular.ownNamesOf x ix l.constants)
      (ConLeche.Driver.ownNamesOf xC ixC lC) := by
  have hcs := listRel_of_mapM hl.constants
  unfold ConRon.Arena.Modular.ownNamesOf ConLeche.Driver.ownNamesOf
  rw [(ImpsD.isEmpty hx)]
  split
  · unfold ConRon.Arena.Modular.ownNames ConLeche.Driver.ownNames
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    have := ownNamesFold_rel (P := fun _ => false) (PC := fun _ => false) (fun _ _ _ => rfl) hcs
      (SetRel.empty st)
    simpa using this
  · rw [← Array.foldl_toList, ← Array.foldl_toList]
    exact ownNamesFold_rel (P := fun c => ix.first.contains c.c.name)
      (PC := fun c => ixC.first.contains c.name)
      (fun c cC hc => HMRel.contains hw hix.first (denoteCEntry_parts hc).1) hcs (SetRel.empty st)

/-! ## What an own theorem's record mentions -/

theorem ownUsesAt_fold (n : NIdx) :
    ∀ (l : List CEntry) (m : Std.HashMap NIdx Nat) (k : Nat),
      (l.foldl (fun (acc : Std.HashMap NIdx Nat × Nat) c =>
        (if acc.1.contains c.c.name then acc.1 else acc.1.insert c.c.name acc.2, acc.2 + 1))
        (m, k)).1[n]? =
      match m[n]? with
      | some i => some i
      | none => (l.findIdx? (·.c.name == n)).map (· + k)
  | [], m, k => by
    simp only [List.foldl_nil, List.findIdx?_nil, Option.map_none]
    cases m[n]? <;> rfl
  | c :: l, m, k => by
    simp only [List.foldl_cons]
    rw [ownUsesAt_fold n l]
    by_cases hc : m.contains c.c.name = true
    · simp only [hc, ↓reduceIte]
      cases hm : m[n]? with
      | some i => rfl
      | none =>
        have hne : (c.c.name == n) = false := by
          rw [beq_eq_false_iff_ne]
          rintro rfl
          rw [Std.HashMap.contains_eq_isSome_getElem?, hm] at hc
          cases hc
        simp only [List.findIdx?_cons, hne, Bool.false_eq_true, ↓reduceIte, Option.map_map]
        congr 1
        funext i
        simp only [Function.comp]
        omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, Std.HashMap.getElem?_insert]
      by_cases e : c.c.name = n
      · subst e
        have hm : m[c.c.name]? = none := by
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
          cases h : m[c.c.name]? with
          | none => rfl
          | some _ => rw [h] at hc; exact absurd rfl hc
        simp [hm, List.findIdx?_cons]
      · have hb : (c.c.name == n) = false := beq_eq_false_iff_ne.mpr e
        simp only [hb, Bool.false_eq_true, ↓reduceIte, List.findIdx?_cons, Option.map_map]
        cases m[n]? with
        | some i => rfl
        | none =>
          simp only
          congr 1
          funext i
          simp only [Function.comp]
          omega

theorem findIdx?_bind {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.findIdx? p).bind (l[·]?) = l.find? p
  | [] => rfl
  | c :: l => by
    simp only [List.findIdx?_cons, List.find?_cons]
    cases hp : p c
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_map]
      rw [← findIdx?_bind p l]
      rfl
    · rfl

/-- The twin's index of a load by name finds a name's first constant. -/
theorem ownUsesThm_eq (cs : Array CEntry) (n : NIdx) :
    ConRon.Arena.Modular.ownUsesThm cs (ConRon.Arena.Modular.ownUsesAt cs) n =
      (cs.toList.find? (·.c.name == n)).map (·.uses) := by
  unfold ConRon.Arena.Modular.ownUsesThm ConRon.Arena.Modular.ownUsesAt
  rw [← Array.foldl_toList, ownUsesAt_fold n cs.toList {} 0]
  simp only [Std.HashMap.getElem?_empty]
  rw [← findIdx?_bind _ cs.toList]
  cases cs.toList.findIdx? (·.c.name == n) with
  | none => rfl
  | some i => simp [Array.getElem?_toList]

theorem find?_rel {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) {l : List α} {ys : List β} (h : ListRel R l ys) :
    Option.Rel R (l.find? p) (ys.find? q) := by
  induction h with
  | nil => exact .none
  | @cons a b _ _ hab _ ih =>
    rw [List.find?_cons, List.find?_cons, hpq a b hab]
    cases q b
    · exact ih
    · exact .some hab

/-- con-leche: ConLeche/Driver/Worker.lean:87-94 ownUses — **what an own record mentions,
upstream's**: at a theorem, what the load read off the file, found by name in the load (the
twin's index of it, upstream's `find?`); else the record's own constants. -/
theorem ownUsesOf_other (cs : Array CEntry) (at_ : Std.HashMap NIdx Nat) (d : IDeclaration)
    (h : ∀ cv v, d ≠ .thmDecl cv v) :
    ConRon.Arena.Modular.ownUsesOf cs at_ d = ConRon.Arena.Frontend.IDeclaration.usedConsts d := by
  cases d with
  | thmDecl cv v => exact absurd rfl (h cv v)
  | _ => rfl

theorem ownUses_other (lC : ConLeche.Frontend.Olean.Loaded) (d : Declaration)
    (h : ∀ cv v, d ≠ .thmDecl cv v) : ConLeche.Driver.ownUses lC d = d.usedConsts := by
  cases d with
  | thmDecl cv v => exact absurd rfl (h cv v)
  | _ => rfl

theorem denoteDecl_thm_iff {st : EStore} {d : IDeclaration} {dP : Declaration}
    (hd : ConRon.Arena.Frontend.denoteDecl st d = some dP) {cvP : ConstantVal} {vP : Expr}
    (he : dP = .thmDecl cvP vP) : ∃ cv v, d = .thmDecl cv v := by
  subst he
  cases d with
  | thmDecl cv v => exact ⟨cv, v, rfl⟩
  | _ =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    first
    | (simp only [Option.map_eq_some_iff] at hd; obtain ⟨_, -, h⟩ := hd; cases h)
    | (split at hd <;> simp at hd)

theorem ownUses_thm_run {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false)
    {cs : Array CEntry} {lC : ConLeche.Frontend.Olean.Loaded}
    (hcs : ListRel (fun c cC => denoteCEntry s.store c = some cC) cs.toList lC.constants.toList)
    {cv : IConstantVal} {v : EIdx} {dP : Declaration}
    (hd : ConRon.Arena.Frontend.denoteDecl s.store (.thmDecl cv v) = some dP) {ns : Array NIdx}
    (hrun : ((cs.toList.find? (·.c.name == cv.name)).map (·.uses)).elim
        (ConRon.Arena.Frontend.IDeclaration.usedConsts (.thmDecl cv v)) pure s = .ok (ns, s')) :
    ParseStep s s' ∧ denoteNList s'.store.ns ns.toList = some (ConLeche.Driver.ownUses lC dP).toList := by
  have hw := nsWF_of_StateOK hok
  simp only [ConRon.Arena.Frontend.denoteDecl] at hd
  cases hcv : ConRon.Arena.Frontend.denoteCV s.store cv with
  | none => simp [hcv] at hd
  | some cvP =>
  cases he : denoteE s.store v with
  | none => simp [hcv, he] at hd
  | some vP =>
  simp only [hcv, he, Option.some.injEq] at hd
  subst hd
  have hname := denoteCV_name hcv
  have hrel := find?_rel (p := (·.c.name == cv.name)) (q := (·.name == cvP.name))
    (fun a b hab => by
      have ha := (denoteCEntry_parts hab).1
      cases h1 : (a.c.name == cv.name) <;> cases h2 : (b.name == cvP.name) <;> try rfl
      · simp only [beq_iff_eq, beq_eq_false_iff_ne] at h1 h2
        exact absurd (h2 ▸ ha) (fun h => h1 (denoteN_inj hw h hname))
      · simp only [beq_iff_eq, beq_eq_false_iff_ne] at h1 h2
        rw [h1] at ha
        exact absurd (Option.some.inj (ha.symm.trans hname)) h2) hcs
  simp only [ConLeche.Driver.ownUses, ← Array.find?_toList]
  rcases optRel_cases hrel with ⟨h1, h2⟩ | ⟨a, b, h1, h2, hab⟩
  · rw [h1] at hrun
    rw [h2]
    simp only [Option.map_none, Option.elim] at hrun
    exact usedConsts_run hok hoff (by simp [ConRon.Arena.Frontend.denoteDecl, hcv, he]) hrun
  · rw [h1] at hrun
    rw [h2]
    simp only [Option.map_some, Option.elim] at hrun
    obtain ⟨hv, rfl⟩ := AM.pure_ok hrun
    subst hv
    refine ⟨ParseStep.refl hok, ?_⟩
    unfold denoteCEntry at hab
    obtain ⟨e, -, hab⟩ := ConLeche.Frontend.Olean.bind_some_left hab
    obtain ⟨u, hu, hab⟩ := ConLeche.Frontend.Olean.bind_some_left hab
    simp only [pure, Option.some.injEq] at hab
    subst hab
    simp only [toArray_toSubarray_toList]
    rw [denoteNList_eq_mapM]
    exact hu

/-- con-leche: ConLeche/Driver/Worker.lean:87-94 ownUses — **what an own record mentions,
upstream's**: at a theorem, what the load read off the file, found by name in the load (the
twin's index of it, upstream's `find?`); else the record's own constants. -/
theorem usedRel_ownUses {st0 : EStore} {l : Loaded} {lC : ConLeche.Frontend.Olean.Loaded}
    (hl : LoadedRel st0 l lC) :
    UsedRel st0 (ConRon.Arena.Modular.ownUsesOf l.constants (ConRon.Arena.Modular.ownUsesAt l.constants))
      (ConLeche.Driver.ownUses lC) := by
  intro s s' d dP ns hx hok hoff hd hrun
  have hcs : ListRel (fun c cC => denoteCEntry s.store c = some cC) l.constants.toList
      lC.constants.toList :=
    ListRel.mono' (fun a b h => denoteCEntry_ext hx h) (listRel_of_mapM hl.constants)
  by_cases hk : ∃ cv v, d = .thmDecl cv v
  · obtain ⟨cv, v, rfl⟩ := hk
    have e : ConRon.Arena.Modular.ownUsesOf l.constants (ConRon.Arena.Modular.ownUsesAt l.constants)
        (.thmDecl cv v) = ((l.constants.toList.find? (·.c.name == cv.name)).map (·.uses)).elim
        (ConRon.Arena.Frontend.IDeclaration.usedConsts (.thmDecl cv v)) pure := by
      simp only [ConRon.Arena.Modular.ownUsesOf, ownUsesThm_eq]
      cases (l.constants.toList.find? (·.c.name == cv.name)).map (·.uses) <;> rfl
    rw [e] at hrun
    exact ownUses_thm_run hok hoff hcs hd hrun
  · have hk' : ∀ cv v, d ≠ .thmDecl cv v := fun cv v h => hk ⟨cv, v, h⟩
    rw [ownUsesOf_other _ _ _ hk'] at hrun
    have hkP : ∀ cvP vP, dP ≠ .thmDecl cvP vP := fun cvP vP h => hk (denoteDecl_thm_iff hd h)
    rw [ownUses_other _ _ hkP]
    exact usedConsts_run hok hoff hd hrun

/-! ## The own records of a compared challenge, and the hoist -/

theorem denoteDecls_append {st : EStore} :
    ∀ {a b : List IDeclaration} {aC bC : List Declaration}, denoteDecls st a = some aC →
      denoteDecls st b = some bC → denoteDecls st (a ++ b) = some (aC ++ bC)
  | [], b, aC, bC, ha, hb => by
    simp only [denoteDecls, Option.some.injEq] at ha
    subst ha; simpa using hb
  | d :: a, b, aC, bC, ha, hb => by
    simp only [denoteDecls] at ha
    split at ha
    · rename_i x xs hx hxs
      cases ha
      simp only [List.cons_append, denoteDecls, hx, denoteDecls_append hxs hb]
    · cases ha

theorem anyLoaded_rel {st : EStore} (hw : NStoreWF st.ns) {first : Std.HashMap NIdx Copy}
    {firstC : Std.HashMap ConLeche.Name Copy} (hf : HMRel (· = ·) st first firstC) :
    ∀ {ns : List NIdx} {zs : List ConLeche.Name}, ConRon.Arena.Frontend.denoteNList st.ns ns = some zs →
      ns.any first.contains = zs.any firstC.contains
  | [], zs, hns => by
    simp only [ConRon.Arena.Frontend.denoteNList, Option.some.injEq] at hns
    subst hns; rfl
  | a :: l, zs, hns => by
    simp only [ConRon.Arena.Frontend.denoteNList] at hns
    split at hns
    · rename_i y ys hy hys
      cases hns
      simp only [List.any_cons, anyLoaded_rel hw hf hys, HMRel.contains hw hf hy]
    · cases hns

/-- con-leche: ConLeche/Driver/Worker.lean:124-125 loadedRec — **a record some name of which a
loaded module stores, upstream's**. -/
theorem loadedRec_run {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    {first : Std.HashMap NIdx Copy} {firstC : Std.HashMap ConLeche.Name Copy}
    (hf : HMRel (· = ·) s.store first firstC) {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (hix1 : ix.first = first) (hix2 : ixC.first = firstC)
    {d : IDeclaration} {dC : Declaration} (hp : PersDecl d)
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dC) {b : Bool}
    (h : ConRon.Arena.Modular.loadedRec ix d s = .ok (b, s')) :
    DStep s s' ∧ b = ConLeche.Driver.loadedRec ixC dC := by
  unfold ConRon.Arena.Modular.loadedRec at h
  obtain ⟨ns, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hv, rfl⟩ := AM.pure_ok h
  subst hv
  obtain ⟨hst, hns⟩ := declNames_run hok hoff hp hd h1
  refine ⟨hst, ?_⟩
  have hw := nsWF_of_StateOK hst.ok.state
  have hf' := hf.ext hst.ext (fun _ _ h => h)
  unfold ConRon.Arena.Modular.anyLoaded ConLeche.Driver.loadedRec
  rw [hix1, hix2]
  exact anyLoaded_rel hw hf' hns

theorem recsLoaded_go {want : Bool} {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} :
    ∀ (l : List IDeclaration) {lC : List Declaration} (out : Array IDeclaration)
      {outC : List Declaration} {s s' : AState} {r : Array IDeclaration},
      DriverOK s → s.store.scratchOn = false → HMRel (· = ·) s.store ix.first ixC.first →
      (∀ d ∈ l, PersDecl d) → PersDecls out →
      denoteDecls s.store l = some lC → denoteDecls s.store out.toList = some outC →
      l.foldlM (m := AM) (fun out d => do
        if (← ConRon.Arena.Modular.loadedRec ix d) == want then pure (out.push d) else pure out)
        out s = .ok (r, s') →
      DStep s s' ∧ PersDecls r ∧
        denoteDecls s'.store r.toList =
          some (outC ++ lC.filter (fun d => ConLeche.Driver.loadedRec ixC d == want))
  | [], lC, out, outC, s, s', r, hok, hoff, _, _, hpo, hl, ho, h => by
    simp only [denoteDecls, Option.some.injEq] at hl
    subst hl
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨DStep.refl hok hoff, hpo, by simpa using ho⟩
  | d :: l, lC, out, outC, s, s', r, hok, hoff, hf, hp, hpo, hl, ho, h => by
    simp only [denoteDecls] at hl
    split at hl
    · rename_i dC lC' hd hls
      cases hl
      simp only [List.foldlM_cons] at h
      obtain ⟨out₁, s₁, h1, h⟩ := AM.bind_ok h
      obtain ⟨b, s₀, h0, h1⟩ := AM.bind_ok h1
      obtain ⟨hst0, hb⟩ := loadedRec_run hok hoff hf rfl rfl (hp d (List.mem_cons_self ..)) hd h0
      subst hb
      have hs10 : s₁ = s₀ := by split at h1 <;> exact (AM.pure_ok h1).2
      subst hs10
      have hpo1 : PersDecls out₁ ∧ denoteDecls s₁.store out₁.toList =
          some (outC ++ ([dC].filter (fun d => ConLeche.Driver.loadedRec ixC d == want))) := by
        split at h1
        · rename_i hw
          obtain ⟨rfl, -⟩ := AM.pure_ok h1
          refine ⟨fun x hx => ?_, ?_⟩
          · rcases Array.mem_push.1 hx with hx | rfl
            · exact hpo x hx
            · exact hp _ (List.mem_cons_self ..)
          · simp only [List.filter_cons, hw, ↓reduceIte, List.filter_nil, Array.toList_push]
            exact denoteDecls_append (denoteDecls_ext hst0.ext _ _ ho)
              (by simp [denoteDecls, denoteDecl_ext hst0.ext hd])
        · rename_i hw
          obtain ⟨rfl, -⟩ := AM.pure_ok h1
          refine ⟨hpo, ?_⟩
          simp only [List.filter_cons, hw, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
            List.append_nil]
          exact denoteDecls_ext hst0.ext _ _ ho
      obtain ⟨hst, hpr, hr⟩ := recsLoaded_go l out₁ hst0.ok hst0.scratch
        (hf.ext hst0.ext (fun _ _ h => h)) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
        hpo1.1 (denoteDecls_ext hst0.ext _ _ hls) hpo1.2 h
      refine ⟨hst0.trans hst, hpr, ?_⟩
      rw [hr, List.filter_cons]
      simp only [List.append_assoc, List.filter_cons, List.filter_nil]
      split <;> simp
    · cases hl

/-- con-leche: ConLeche/Driver/Worker.lean:127-135 ownRecs — **the own records of a worker that
adds the imports `x`, upstream's**. -/
theorem ownRecs_run {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    {x : Array (ConLeche.Frontend.Olean.ImportF NIdx)} {xC : Array ConLeche.Frontend.Olean.ImportRec}
    (hx : ImpsD s.store x xC) {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (hix : HMRel (· = ·) s.store ix.first ixC.first)
    {ds : Array IDeclaration} {dsC : Array Declaration} (hp : PersDecls ds)
    (hd : denoteDeclArray s.store ds = some dsC) {r : Array IDeclaration}
    (h : ConRon.Arena.Modular.ownRecs x ix ds s = .ok (r, s')) :
    DStep s s' ∧ PersDecls r ∧ denoteDeclArray s'.store r = some (ConLeche.Driver.ownRecs xC ixC dsC) := by
  unfold ConRon.Arena.Modular.ownRecs at h
  unfold ConLeche.Driver.ownRecs
  rw [← (ImpsD.isEmpty hx)]
  by_cases he : x.isEmpty = true
  · rw [ite_eq_left he] at h ⊢
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨DStep.refl hok hoff, hp, hd⟩
  · rw [ite_eq_right he] at h ⊢
    unfold ConRon.Arena.Modular.recsLoaded at h
    rw [← Array.foldlM_toList] at h
    obtain ⟨hst, hpr, hr⟩ := recsLoaded_go (want := false) ds.toList #[] hok hoff hix
      (fun d hd => hp d (by simpa using hd)) (fun _ h => by simp at h) (denoteDeclArray_iff.mp hd) rfl h
    refine ⟨hst, hpr, denoteDeclArray_iff.mpr ?_⟩
    rw [hr, Array.toList_filter]
    simp only [List.nil_append]
    congr 1
    try (apply List.filter_congr; intro d _; cases ConLeche.Driver.loadedRec ixC d <;> rfl)

/-- con-leche: ConLeche/Driver/Worker.lean:300-343 workerRead — **the records checked, upstream's
`recsOf`**: the own records hoisted (`hoistNatOpGround` at `ownUses`). -/
theorem recsOf_run {s s₁ s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    {x : Array (ConLeche.Frontend.Olean.ImportF NIdx)} {xC : Array ConLeche.Frontend.Olean.ImportRec}
    (hx : ImpsD s.store x xC) {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (hix : HMRel (· = ·) s.store ix.first ixC.first)
    {l : Loaded} {lC : ConLeche.Frontend.Olean.Loaded} (hl : LoadedRel s.store l lC)
    {ds : Array IDeclaration} {dsC : Array Declaration} (hp : PersDecls ds)
    (hd : denoteDeclArray s.store ds = some dsC) {recs : Array IDeclaration}
    (h1 : ConRon.Arena.Modular.ownRecs x ix ds s = .ok (recs, s₁))
    {own : Array IDeclaration} {moved : Array NIdx}
    (h2 : ConRon.Arena.Frontend.hoistNatOpGround
      (ConRon.Arena.Modular.ownUsesOf l.constants (ConRon.Arena.Modular.ownUsesAt l.constants))
      recs s₁ = .ok ((own, moved), s')) :
    DStep s s' ∧ PersDecls own ∧ denoteDeclArray s'.store own =
      some (ConLeche.Frontend.hoistNatOpGround (ConLeche.Driver.ownUses lC)
        (ConLeche.Driver.ownRecs xC ixC dsC)).1 := by
  obtain ⟨hst1, hp1, hr1⟩ := ownRecs_run hok hoff hx hix hp hd h1
  obtain ⟨hst2, hp2, ho, -⟩ := hoistNatOpGround_run hst1.ok.state hst1.scratch hst1.ok.pins
    hst1.ok.state.wf hr1 hp1 (UsedRel.mono hst1.ext (usedRel_ownUses hl)) h2
  exact ⟨hst1.trans (DStep.of_parse hst1.ok hst1.scratch hst2), hp2, ho⟩
