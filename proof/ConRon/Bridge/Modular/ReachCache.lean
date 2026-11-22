/-
# `ConRon.Bridge.Modular.ReachCache` — the reach's caches, Theorem 1 (task #166)

The reach's caches over handles against upstream's over names: a map keyed by parts
(`MRel` at `PKRel`), by names (`HMRel`), each value read back.  The twin's caches are a mirror
of upstream's, key for key: every lookup of the twin hits where upstream's does, so the caches
are related entry by entry (`CacheRel`) and every read of a part answers as upstream's.  The
regions' memos are related through the snapshot's values only: the twin's memo good
(`SparseGood`), upstream's good (`SM.Good`), at the same region.

A simulation in the run style (`Bridge/Frontend/Olean/Closure.lean`'s), not a `vcgen` walk.
-/
module

public import ConRon.Bridge.Modular.Rel
public import ConRon.Bridge.Modular.Reads
public import ConRon.Bridge.Modular.Graph
public import ConRon.Bridge.Modular.ReadsParts
public import ConRon.Bridge.Modular.Worker
public import ConRon.Bridge.Frontend.Olean.Sparse
public import ConRon.Bridge.Frontend.Olean.Files
public import ConLeche.Verify.Driver.ReachFrom
public import ConLeche.Verify.Driver.Loads
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM)
open ConRon.Arena.Frontend.Olean (LvState levelsGo)
open ConLeche.Frontend.Olean (Region Roots OLeanLevel ModFiles ImportF ImportRec bind_some_left CKindF Copy)

theorem arenaPartKey_beq_iff (a b : ConRon.Arena.Modular.PartKey) : (a == b) = true ↔ a = b := by
  cases a; cases b
  show (_ && _) = true ↔ _
  simp

instance : LawfulBEq ConRon.Arena.Modular.PartKey where
  eq_of_beq h := (arenaPartKey_beq_iff _ _).1 h
  rfl := (arenaPartKey_beq_iff _ _).2 rfl

/-! ## Keys and spots -/

/-- con-leche: ConLeche/Driver/Reach.lean:163-167 PartKey — a part key read back. -/
@[expose] def PKRel (st : EStore) (k : ConRon.Arena.Modular.PartKey)
    (kC : ConLeche.Driver.PartKey) : Prop :=
  denoteN st.ns k.mod = some kC.mod ∧ k.level = kC.level

theorem PKRel.ext {st st' : EStore} (hx : Ext st st') {k : ConRon.Arena.Modular.PartKey}
    {kC : ConLeche.Driver.PartKey} (h : PKRel st k kC) : PKRel st' k kC :=
  ⟨denoteN_ext h.1 hx, h.2⟩

theorem PKRel.inj {st : EStore} (hw : NStoreWF st.ns) {k k' : ConRon.Arena.Modular.PartKey}
    {kC : ConLeche.Driver.PartKey} (h : PKRel st k kC) (h' : PKRel st k' kC) : k = k' := by
  obtain ⟨m, l⟩ := k
  obtain ⟨m', l'⟩ := k'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  simp only at h1 h2 h1' h2'
  rw [denoteN_inj hw h1 h1', h2, h2']

theorem PKRel.func {st : EStore} {k : ConRon.Arena.Modular.PartKey}
    {kC kC' : ConLeche.Driver.PartKey} (h : PKRel st k kC) (h' : PKRel st k kC') : kC = kC' := by
  obtain ⟨m, l⟩ := kC
  obtain ⟨m', l'⟩ := kC'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  simp only at h1 h2 h1' h2'
  rw [Option.some.inj (h1.symm.trans h1'), ← h2, ← h2']

/-- con-leche: ConLeche/Driver/Reach.lean:169-172 Spot — a copy's spot read back. -/
@[expose] def SpotRel (st : EStore) (s : ConRon.Arena.Modular.Spot) (sC : ConLeche.Driver.Spot) :
    Prop :=
  PKRel st s.part sC.part ∧ NPRel st s.pos sC.pos

theorem SpotRel.ext {st st' : EStore} (hx : Ext st st') {s : ConRon.Arena.Modular.Spot}
    {sC : ConLeche.Driver.Spot} (h : SpotRel st s sC) : SpotRel st' s sC :=
  ⟨h.1.ext hx, h.2.ext hx⟩

/-! ## Maps keyed by parts -/

/-- con-leche: none — **a map over part keys against one over upstream's**: each entry's key
read back as one of the other's, the values related. -/
structure MRel {α β : Type} (R : α → β → Prop) (st : EStore)
    (M : Std.HashMap ConRon.Arena.Modular.PartKey α) (MC : Std.HashMap ConLeche.Driver.PartKey β) :
    Prop where
  fwd : ∀ k a, M[k]? = some a → ∃ kC b, PKRel st k kC ∧ MC[kC]? = some b ∧ R a b
  bwd : ∀ kC b, MC[kC]? = some b → ∃ k a, PKRel st k kC ∧ M[k]? = some a ∧ R a b

theorem MRel.empty {α β : Type} (R : α → β → Prop) (st : EStore) : MRel R st {} {} :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

theorem MRel.ext {α β : Type} {R R' : α → β → Prop} {st st' : EStore}
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) (hx : Ext st st') (hr : ∀ a b, R a b → R' a b) : MRel R' st' M MC :=
  ⟨fun k a hk => let ⟨kC, b, h1, h2, h3⟩ := h.fwd k a hk; ⟨kC, b, h1.ext hx, h2, hr _ _ h3⟩,
   fun kC b hk => let ⟨k, a, h1, h2, h3⟩ := h.bwd kC b hk; ⟨k, a, h1.ext hx, h2, hr _ _ h3⟩⟩

/-- A lookup answers alike. -/
theorem MRel.get {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey}
    (hk : PKRel st k kC) : Option.Rel R M[k]? MC[kC]? := by
  generalize hm : M[k]? = o
  cases o with
  | some a =>
    obtain ⟨kC', b, h1, h2, h3⟩ := h.fwd k a hm
    obtain rfl := hk.func h1
    rw [h2]
    exact .some h3
  | none =>
    cases hc : MC[kC]? with
    | none => exact .none
    | some b =>
      obtain ⟨k', a, h1, h2, _⟩ := h.bwd kC b hc
      obtain rfl := h1.inj hw hk
      rw [hm] at h2
      cases h2

theorem MRel.contains {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey}
    (hk : PKRel st k kC) : M.contains k = MC.contains kC := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?]
  rcases optRel_cases (h.get hw hk) with ⟨h1, h2⟩ | ⟨a, b, h1, h2, -⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2]; rfl

theorem MRel.insert {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey}
    (hk : PKRel st k kC) {a : α} {b : β} (hr : R a b) :
    MRel R st (M.insert k a) (MC.insert kC b) := by
  constructor
  · intro x a' hx
    rw [Std.HashMap.getElem?_insert] at hx
    by_cases he : k = x
    · subst he
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      exact ⟨kC, b, hk, by simp, hr⟩
    · simp only [beq_iff_eq, he, ↓reduceIte] at hx
      obtain ⟨xC, b', h1, h2, h3⟩ := h.fwd x a' hx
      have hn : ¬ kC = xC := fun hn => he (hk.inj hw (hn ▸ h1))
      exact ⟨xC, b', h1, by simp [Std.HashMap.getElem?_insert, hn, h2], h3⟩
  · intro xC b' hn
    rw [Std.HashMap.getElem?_insert] at hn
    by_cases he : kC = xC
    · subst he
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      exact ⟨k, a, hk, by simp, hr⟩
    · simp only [beq_iff_eq, he, ↓reduceIte] at hn
      obtain ⟨x, a', h1, h2, h3⟩ := h.bwd xC b' hn
      have hx : ¬ k = x := fun hx => he (hk.func (hx ▸ h1))
      exact ⟨x, a', h1, by simp [Std.HashMap.getElem?_insert, hx, h2], h3⟩

theorem MRel.erase {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey}
    (hk : PKRel st k kC) : MRel R st (M.erase k) (MC.erase kC) := by
  constructor
  · intro x a' hx
    rw [Std.HashMap.getElem?_erase] at hx
    by_cases he : k = x
    · subst he; simp at hx
    · simp only [beq_iff_eq, he, ↓reduceIte] at hx
      obtain ⟨xC, b', h1, h2, h3⟩ := h.fwd x a' hx
      have hn : ¬ kC = xC := fun hn => he (hk.inj hw (hn ▸ h1))
      exact ⟨xC, b', h1, by simp [Std.HashMap.getElem?_erase, hn, h2], h3⟩
  · intro xC b' hn
    rw [Std.HashMap.getElem?_erase] at hn
    by_cases he : kC = xC
    · subst he; simp at hn
    · simp only [beq_iff_eq, he, ↓reduceIte] at hn
      obtain ⟨x, a', h1, h2, h3⟩ := h.bwd xC b' hn
      have hx : ¬ k = x := fun hx => he (hk.func (hx ▸ h1))
      exact ⟨x, a', h1, by simp [Std.HashMap.getElem?_erase, hx, h2], h3⟩

/-! ## The reach's environment and caches -/

/-- con-leche: ConLeche/Driver/Reach.lean:174-185 ReachEnv — a clashing name's copies read back. -/
@[expose] def CopiesRel (st : EStore) (a : Array (NIdx × ConRon.Arena.Frontend.Olean.StmtRec))
    (b : Array (ConLeche.Name × ConstantVal)) : Prop :=
  ListRel (fun x y => denoteN st.ns x.1 = some y.1 ∧ denoteStmt st x.2 = some y.2) a.toList b.toList

/-- con-leche: none — a pair of names read back. -/
@[expose] def NN (st : EStore) (a : NIdx × NIdx) (b : ConLeche.Name × ConLeche.Name) : Prop :=
  denoteN st.ns a.1 = some b.1 ∧ denoteN st.ns a.2 = some b.2

/-- con-leche: ConLeche/Driver/Reach.lean:174-185 ReachEnv — **the reach's environment read
back**: upstream's reads are the search path's, the module, the reads, the own names and the
clashes' copies denoted. -/
structure EnvRel (sp : Roots) (st : EStore) (env : ConRon.Arena.Modular.ReachEnv)
    (envC : ConLeche.Driver.ReachEnv ModelIO) : Prop where
  rd : envC.rd = .ofPath sp
  mod : denoteN st.ns env.mod = some envC.mod
  wr : WorkerReadsRel st env.wr envC.wr
  keys : LoadsKeys env.wr.loads envC.wr.loads
  own : SetRel st env.own envC.own
  copies : HMRel (CopiesRel st) st env.copies envC.copies

/-- con-leche: ConLeche/Driver/Reach.lean:187-211 ReachCache — **the reach's caches read back**,
entry for entry: tables, lookups, the regions (each memo good at its region on both sides),
recursor maps, views, located copies; the completions, pending statements and partners in
order; the count of searches. -/
structure CacheRel (st : EStore) (c : ConRon.Arena.Modular.ReachCache)
    (cC : ConLeche.Driver.ReachCache) : Prop where
  tables : MRel (NPsRel st) st c.tables cC.tables
  looks : MRel (HMRel (NPRel st) st) st c.looks cC.looks
  parts : MRel (fun (p : Region × SM) (q : Region × ConLeche.Frontend.Olean.SM) =>
    p.1 = q.1 ∧ SparseGood st p.1 p.2 ∧ q.2.Good q.1) st c.parts cC.parts
  recBlocks : MRel (HMRel (· = ·) st) st c.recBlocks cC.recBlocks
  views : HMRel (HMRel (SpotRel st) st) st c.views cC.views
  located : HMRel (SpotRel st) st c.located cC.located
  completed : ListRel (NN st) c.completed.toList cC.completed.toList
  pending : ListRel (PendRel st) c.pending.toList cC.pending.toList
  partners : ListRel (NN st) c.partners.toList cC.partners.toList
  searches : c.searches = cC.searches

theorem CacheRel.empty (st : EStore) : CacheRel st {} {} :=
  ⟨MRel.empty _ _, MRel.empty _ _, MRel.empty _ _, MRel.empty _ _, HMRel.empty _ _,
    HMRel.empty _ _, .nil, .nil, .nil, rfl⟩

theorem NN.ext {st st' : EStore} (hx : Ext st st') {a : NIdx × NIdx}
    {b : ConLeche.Name × ConLeche.Name} (h : NN st a b) : NN st' a b :=
  ⟨denoteN_ext h.1 hx, denoteN_ext h.2 hx⟩

theorem PendRel.ext {st st' : EStore} (hx : Ext st st')
    {a : String × NIdx × ConRon.Arena.Frontend.Olean.StmtRec} {b : String × ConLeche.Name × ConstantVal}
    (h : PendRel st a b) : PendRel st' a b :=
  ⟨denoteN_ext h.1 hx, denoteStmt_ext hx h.2⟩

theorem CacheRel.ext {st st' : EStore} (hx : Ext st st') {c : ConRon.Arena.Modular.ReachCache}
    {cC : ConLeche.Driver.ReachCache} (h : CacheRel st c cC) : CacheRel st' c cC :=
  ⟨h.tables.ext hx (fun _ _ h => h.ext hx), h.looks.ext hx (fun _ _ h => h.ext hx (fun _ _ h => h.ext hx)),
    h.parts.ext hx (fun _ _ h => ⟨h.1, h.2.1.ext hx, h.2.2⟩),
    h.recBlocks.ext hx (fun _ _ h => h.ext hx (fun _ _ h => h)),
    h.views.ext hx (fun _ _ h => h.ext hx (fun _ _ h => h.ext hx)),
    h.located.ext hx (fun _ _ h => h.ext hx),
    ListRel.mono' (fun _ _ h => h.ext hx) h.completed, ListRel.mono' (fun _ _ h => h.ext hx) h.pending,
    ListRel.mono' (fun _ _ h => h.ext hx) h.partners, h.searches⟩

/-! ## The reads' relations at a larger store -/

theorem WorkerReadsRel.extR {st st' : EStore} (hx : Ext st st') (hw' : NStoreWF st'.ns)
    {wr : ConRon.Arena.Frontend.Olean.WorkerReads} {wrC : ConLeche.Frontend.Olean.WorkerReads}
    (h : WorkerReadsRel st wr wrC) (hk : LoadsKeys wr.loads wrC.loads) : WorkerReadsRel st' wr wrC :=
  ⟨h.own.ext hx, ConRon.Bridge.Frontend.Olean.LoadsRel.ext' hx hw' h.loads hk, h.pub, h.index.ext' hx,
    listRel_ext (fun _ _ hc => hc.ext hx) h.clashes⟩

theorem EnvRel.ext {sp : Roots} {st st' : EStore} (hx : Ext st st') (hw' : NStoreWF st'.ns)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    (h : EnvRel sp st env envC) : EnvRel sp st' env envC :=
  ⟨h.rd, denoteN_ext h.mod hx, h.wr.extR hx hw' h.keys, h.keys, h.own.ext hx,
    h.copies.ext hx (fun _ _ h => ListRel.mono' (fun _ _ h => ⟨denoteN_ext h.1 hx,
      denoteStmt_ext hx h.2⟩) h)⟩

/-! ## A part's name table -/

/-- con-leche: ConLeche/Driver/Reach.lean:229-247 tableOf — upstream's index branch of
`tableOf`: the table of the part where its module is loaded at that level. -/
@[expose] def indexTableC (wr : ConLeche.Frontend.Olean.WorkerReads) (k : ConLeche.Driver.PartKey) :
    Option ConLeche.Frontend.Olean.NamePositions :=
  match wr.loads.index[k.mod]? with
  | some i => if ((wr.loads.flags[i]?).getD default).level == k.level then wr.index.parts[i]? else none
  | none => none

theorem indexTable_rel {st : EStore} {wr : ConRon.Arena.Frontend.Olean.WorkerReads}
    {wrC : ConLeche.Frontend.Olean.WorkerReads} (h : WorkerReadsRel st wr wrC)
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} (hk : PKRel st k kC) :
    Option.Rel (NPsRel st) (ConRon.Arena.Modular.indexTable wr k) (indexTableC wrC kC) := by
  unfold ConRon.Arena.Modular.indexTable indexTableC
  rw [h.loads.index k.mod kC.mod hk.1]
  cases wrC.loads.index[kC.mod]? with
  | none => exact .none
  | some i =>
    simp only [ConRon.Arena.Frontend.Olean.HeaderLoads.levelAt, h.loads.flags, hk.2]
    split
    · have := listRel_getElem? h.index.parts i
      simpa [Array.getElem?_toList] using this
    · exact .none

/-- con-leche: ConLeche/Driver/Reach.lean:229-247 tableOf — upstream's `tableOf`, the cache
missed. -/
theorem tableOfC_miss {envC : ConLeche.Driver.ReachEnv ModelIO} {cC : ConLeche.Driver.ReachCache}
    {kC : ConLeche.Driver.PartKey} (hm : cC.tables[kC]? = none) :
    ConLeche.Driver.tableOf envC cC kC = (match indexTableC envC.wr kC with
      | some t => pure (cC, .ok t)
      | none => do
        match ← envC.rd.names (kC.mod, kC.level) with
        | .error e => pure (cC, .error e)
        | .ok t => pure ({ cC with tables := cC.tables.insert kC t }, .ok t)) := by
  unfold ConLeche.Driver.tableOf indexTableC
  simp only [hm]
  rcases hi : envC.wr.loads.index[kC.mod]? with _ | i
  · rfl
  · by_cases hl : (((envC.wr.loads.flags[i]?).getD default).level == kC.level) = true
    · simp only [hl, ↓reduceIte]
      rcases hp : envC.wr.index.parts[i]? with _ | t <;> rfl
    · simp only [hl, Bool.false_eq_true, ↓reduceIte]
      rfl

/-- con-leche: none — **the reach's reading context**: the driver's invariant, no scratch tier
open, the reader's pins denoted. -/
structure RCtx (pk : OleanPins) (s : AState) : Prop where
  ok : DriverOK s
  off : s.store.scratchOn = false
  nulls : NullsRel s.store pk

theorem RCtx.ctx {pk : OleanPins} {s : AState} (h : RCtx pk s) : Ctx pk s :=
  ⟨h.ok.state, h.off, h.nulls⟩

theorem RCtx.step {pk : OleanPins} {s s' : AState} (h : RCtx pk s) (hst : DStep s s') : RCtx pk s' :=
  ⟨hst.ok, hst.scratch, h.nulls.ext hst.ext⟩

theorem RCtx.wf {pk : OleanPins} {s : AState} (h : RCtx pk s) : NStoreWF s.store.ns :=
  nsWF_of_StateOK h.ok.state

/-- con-leche: ConLeche/Driver/Reach.lean:229-247 tableOf — **a part's name table**: the twin's
answer (`tableGet` after `tableOf`) is upstream's, the caches related after. -/
theorem tableOf_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hk : PKRel s.store k kC)
    (h : ConRon.Arena.Modular.tableOf (modelFs F) pk sp env c k s = .ok (c', s')) :
    DStep s s' ∧ ∃ cC' tC t, ModelIO.Gives (ConLeche.Driver.tableOf envC cC kC) F (cC', .ok tC) ∧
      CacheRel s'.store c' cC' ∧ ConRon.Arena.Modular.tableGet env.wr c' k = some t ∧
      NPsRel s'.store t tC := by
  have hw := hctx.wf
  unfold ConRon.Arena.Modular.tableOf at h
  have htab := hc.tables.get hw hk
  by_cases h1 : c.tables.contains k = true
  · simp only [h1, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    rw [Std.HashMap.contains_eq_isSome_getElem?] at h1
    rcases optRel_cases htab with ⟨g1, -⟩ | ⟨t, tC, g1, g2, g3⟩
    · rw [g1] at h1; cases h1
    refine ⟨DStep.refl hctx.ok hctx.off, cC, tC, t, ?_, hc, ?_, g3⟩
    · unfold ConLeche.Driver.tableOf
      simp only [g2]
      exact ModelIO.gives_pure _ _
    · simp [ConRon.Arena.Modular.tableGet, g1]
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
  have hmiss : c.tables[k]? = none := by
    rw [Std.HashMap.contains_eq_isSome_getElem?] at h1
    cases hh : c.tables[k]? with
    | none => rfl
    | some _ => rw [hh] at h1; exact absurd rfl h1
  have hmissC : cC.tables[kC]? = none := by
    rw [hmiss] at htab
    rcases optRel_cases htab with ⟨-, g⟩ | ⟨a, b, g, -, -⟩
    · exact g
    · cases g
  have hix := indexTable_rel he.wr hk
  rw [tableOfC_miss hmissC]
  by_cases h2 : (ConRon.Arena.Modular.indexTable env.wr k).isSome = true
  · simp only [h2, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    rcases optRel_cases hix with ⟨g1, -⟩ | ⟨t, tC, g1, g2, g3⟩
    · rw [g1] at h2; cases h2
    refine ⟨DStep.refl hctx.ok hctx.off, cC, tC, t, ?_, hc, ?_, g3⟩
    · simp only [g2]; exact ModelIO.gives_pure _ _
    · simp [ConRon.Arena.Modular.tableGet, hmiss, g1]
  simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
  have hnone : ConRon.Arena.Modular.indexTable env.wr k = none := by
    cases hh : ConRon.Arena.Modular.indexTable env.wr k with
    | none => rfl
    | some _ => rw [hh] at h2; exact absurd rfl h2
  have hnoneC : indexTableC envC.wr kC = none := by
    rw [hnone] at hix
    rcases optRel_cases hix with ⟨-, g⟩ | ⟨a, b, g, -, -⟩
    · exact g
    · cases g
  simp only [pure_bind] at h
  obtain ⟨t, s₁, h3, h4⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
  obtain ⟨hst, tC, hg, hrel⟩ := readPartNames_run (roots_ok_of_bare hsp) rfl hctx.ctx hk.1 h3
  have hds := DStep.of_parse hctx.ok hctx.off hst
  refine ⟨hds, { cC with tables := cC.tables.insert kC tC }, tC, t, ?_, ?_, ?_, hrel⟩
  · simp only [hnoneC, he.rd]
    rw [← hk.2]
    exact hg.bind (ModelIO.gives_pure _ _)
  · have hc' := hc.ext hst.ext
    exact { hc' with tables := hc'.tables.insert (nsWF_of_StateOK hst.ok) (hk.ext hst.ext) hrel }
  · simp [ConRon.Arena.Modular.tableGet]

/-! ## A part's name lookup -/

theorem lookFold_rel {st : EStore} (hw : NStoreWF st.ns) :
    ∀ {qs : List ConRon.Arena.Frontend.Olean.NamePosition}
      {qsC : List ConLeche.Frontend.Olean.NamePosition}
      {l : Std.HashMap NIdx ConRon.Arena.Frontend.Olean.NamePosition}
      {lC : Std.HashMap ConLeche.Name ConLeche.Frontend.Olean.NamePosition},
      ListRel (NPRel st) qs qsC → HMRel (NPRel st) st l lC →
      HMRel (NPRel st) st (qs.foldl (fun l q => l.insert q.name q) l)
        (qsC.foldl (fun l q => l.insert q.name q) lC)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons hq hqs, h => by
    simp only [List.foldl_cons]
    exact lookFold_rel hw hqs (h.insert hw hq.name hq)

/-- con-leche: ConLeche/Driver/Reach.lean:249-260 lookOf — a table's lookup, upstream's. -/
theorem lookBuild_rel {st : EStore} (hw : NStoreWF st.ns)
    {t : ConRon.Arena.Frontend.Olean.NamePositions} {tC : ConLeche.Frontend.Olean.NamePositions}
    (h : NPsRel st t tC) :
    HMRel (NPRel st) st (ConRon.Arena.Modular.lookBuild t)
      (tC.consts.foldl (fun (l : Std.HashMap ConLeche.Name ConLeche.Frontend.Olean.NamePosition) q =>
        l.insert q.name q) (Std.HashMap.emptyWithCapacity tC.consts.size)) := by
  unfold ConRon.Arena.Modular.lookBuild
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  refine lookFold_rel hw h.consts ⟨fun _ _ h => by simp at h, fun _ _ h => ?_⟩
  simp at h

/-- con-leche: ConLeche/Driver/Reach.lean:249-260 lookOf — **a part's name lookup**: the twin's
cached lookup after `lookOf` is upstream's answer. -/
theorem lookOf_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hk : PKRel s.store k kC)
    (h : ConRon.Arena.Modular.lookOf (modelFs F) pk sp env c k s = .ok (c', s')) :
    DStep s s' ∧ ∃ cC' lC l, ModelIO.Gives (ConLeche.Driver.lookOf envC cC kC) F (cC', .ok lC) ∧
      CacheRel s'.store c' cC' ∧ c'.looks[k]? = some l ∧ HMRel (NPRel s'.store) s'.store l lC := by
  have hw := hctx.wf
  unfold ConRon.Arena.Modular.lookOf at h
  have hlk := hc.looks.get hw hk
  by_cases h1 : c.looks.contains k = true
  · simp only [h1, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    rw [Std.HashMap.contains_eq_isSome_getElem?] at h1
    rcases optRel_cases hlk with ⟨g1, -⟩ | ⟨l, lC, g1, g2, g3⟩
    · rw [g1] at h1; cases h1
    refine ⟨DStep.refl hctx.ok hctx.off, cC, lC, l, ?_, hc, g1, g3⟩
    unfold ConLeche.Driver.lookOf
    simp only [g2]
    exact ModelIO.gives_pure _ _
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
  have hmissC : cC.looks[kC]? = none := by
    have hm : c.looks[k]? = none := by
      rw [Std.HashMap.contains_eq_isSome_getElem?] at h1
      cases hh : c.looks[k]? with
      | none => rfl
      | some _ => rw [hh] at h1; exact absurd rfl h1
    rw [hm] at hlk
    rcases optRel_cases hlk with ⟨-, g⟩ | ⟨a, b, g, -, -⟩
    · exact g
    · cases g
  simp only [pure_bind] at h
  obtain ⟨c₁, s₁, h2, h3⟩ := AM.bind_ok h
  obtain ⟨hst1, cC₁, tC, t, hg, hc1, ht, htr⟩ := tableOf_run hsp hctx he hc hk h2
  rw [ht] at h3
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
  have hw1 := nsWF_of_StateOK hst1.ok.state
  refine ⟨hst1, { cC₁ with looks := cC₁.looks.insert kC _ }, _, ConRon.Arena.Modular.lookBuild t,
    ?_, { hc1 with looks := hc1.looks.insert hw1 (hk.ext hst1.ext) (lookBuild_rel hw1 htr) }, by simp,
    lookBuild_rel hw1 htr⟩
  unfold ConLeche.Driver.lookOf
  simp only [hmissC]
  exact hg.bind (ModelIO.gives_pure _ _)

/-- con-leche: ConLeche/Driver/Reach.lean:249-260 lookOf — a name in a related lookup. -/
theorem lookAt_eq {c : ConRon.Arena.Modular.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {l : Std.HashMap NIdx ConRon.Arena.Frontend.Olean.NamePosition}
    (hl : c.looks[k]? = some l) (n : NIdx) {s : AState} :
    ConRon.Arena.Modular.lookAt c k n s = .ok (l[n]?, s) := by
  simp [ConRon.Arena.Modular.lookAt, hl]; rfl

end ConRon.Bridge.Modular
