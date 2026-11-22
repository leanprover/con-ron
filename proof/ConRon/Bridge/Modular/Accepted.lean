/-
# `ConRon.Bridge.Modular.Accepted` — an accepted worker at the twin is upstream's (task #166)

The composition of the worker's Theorem 1: the twin's `workerRead` accepting, then its check
phase from `start` accepting and its inferred flags accepting, give upstream's `WorkerAccepted`
(`ConLeche/Verify/Driver/Worker.lean`): the facts of what the worker read and checked
(`WorkerFacts`), and the pure run of the own records, their theorems' values in place, from the
context's environment.

* `workerRead_run` — the twin's phases 1–4 against upstream's, piece by piece: the home
  (`HomeHyp`), the reads (`workerReads_run`), the own records (`ownRecords_run`), the holes, the
  roots (`rootsAt_exact`), the reach (`ReachRunHyp`), the context's names (`ctxNamesNodup_run`),
  the copies (`copiesOk_run`), the own records in the hoist's order (`recsOf_run`).
-/
module

public import ConRon.Bridge.Modular.Reads
public import ConRon.Bridge.Modular.Worker
public import ConRon.Bridge.Modular.Roots
public import ConRon.Bridge.Modular.Copies
public import ConRon.Bridge.Modular.Flags
public import ConRon.Bridge.Modular.ReachTail
public import ConRon.Bridge.Checker.PoolFrom
public import ConLeche.Verify.Driver.Worker
public import ConRon.Bridge.Stages
public import ConRon.Bridge.Checker.Pins
import ConLeche.Verify.Driver.Reach
import ConRon.Bridge.Specs
import ConLeche.Verify.Driver.PropPart
import all ConLeche.Verify.Cached.StreamIndex

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins Loaded)
open ConLeche.Frontend.Olean (Roots ImportF ImportRec Expo)

/-- con-leche: none — `DriverOK` across a read of the files. -/
theorem DriverOK.of_parse {s s' : AState} (h : DriverOK s) (hp : ParseStep s s') : DriverOK s' :=
  DriverOK.of_check ⟨hp.ok, h.caches.monoF hp.ext hp.cframe, h.pins.mono hp.ext hp.pins,
    h.ienv.mono hp.ext⟩ hp.pins

/-- con-leche: ConLeche/Verify/Driver/Worker.lean WorkerFacts.home — **the home at the twin**:
the private files read and the private view loaded and checked give upstream's load of them
(`LoadOf`) and its views' check, the load read back, its frontier good on the files' region. -/
@[expose] def HomeHyp : Prop :=
  ∀ {pk : OleanPins} {F : FS} {sp : Roots} {s s₁ s' : AState} {m : NIdx} {mC : ConLeche.Name}
    {f : ConLeche.Frontend.Olean.ModFiles} {l : Loaded} {expo : Array Expo},
    sp.bare = sp → Ctx pk s → PinsRel s.store pk → denoteN s.store.ns m = some mC →
    ConRon.Arena.Frontend.Olean.liftE
      (ConRon.Arena.Frontend.Olean.readFiles (modelFs F) sp mC .private) s = .ok (f, s₁) →
    ConRon.Arena.Modular.homeOf pk m f s₁ = .ok ((l, expo), s') →
    ParseStep s s' ∧ ∃ lC expoC,
      ModelIO.Gives (ConLeche.Frontend.Olean.readFiles sp mC .private : ModelIO _) F (.ok f) ∧
      ConLeche.Driver.LoadOf 0 mC f lC ∧
      ConLeche.Frontend.Olean.checkViews mC f lC = .ok expoC ∧
      LoadedRel s'.store l lC ∧ FrontGoodAt s'.store f l.frontier

/-- con-leche: ConLeche/Verify/Driver/Worker.lean WorkerFacts.reach — **the reach at the twin**:
its accept gives upstream's context and pending statements, read back, and upstream's reach
answering it under every flag inference that accepts them. -/
@[expose] def ReachRunHyp : Prop :=
  ∀ {pk : OleanPins} {F : FS} {sp : Roots} {s s' : AState} {m : NIdx} {mC : ConLeche.Name}
    {wr : ConRon.Arena.Frontend.Olean.WorkerReads} {wrC : ConLeche.Frontend.Olean.WorkerReads}
    {own : Std.HashSet NIdx} {ownC : Std.HashSet ConLeche.Name}
    {roots : Array NIdx} {rootsC : Array ConLeche.Name} {r : ConRon.Arena.Modular.Reach},
    sp.bare = sp → DriverOK s → s.store.scratchOn = false → PinsRel s.store pk →
    denoteN s.store.ns m = some mC → WorkerReadsRel s.store wr wrC → LoadsKeys wr.loads wrC.loads →
    SetRel s.store own ownC → ListRel (NR s.store) roots.toList rootsC.toList →
    ConRon.Arena.Modular.reach (modelFs F) pk sp m wr own roots s = .ok (r, s') →
    DStep s s' ∧ (∀ d ∈ r.ctx.toList, PersDecl d) ∧ ∃ rC pendC, ReachRel s'.store r rC ∧
      ListRel (PendRel s'.store) r.pending.toList pendC ∧
      ∀ fl : ConLeche.Driver.FlagInfer, fl rC.ctx.toList pendC = .ok () →
        ModelIO.CanGive (ConLeche.Driver.reachWith fl (.ofPath sp) mC wrC ownC rootsC) F
          (.ok rC)

/-- con-leche: ConLeche/Verify/Driver/Worker.lean WorkerFacts — **what the twin's `workerRead`
gives of upstream's worker read `wC`**: every field of `WorkerFacts` but the reach's, which is
stated under any flag inference accepting the pending statements `pendC`; and the twin's values
read back at `st`: the reach, its pending statements, the own records, the values' module, the
reader's pins. -/
structure WorkerReadOK (pins : List NatOpPinSet) (sp : Roots) (F : FS) (mC : ConLeche.Name)
    (xC : Array ImportRec) (st : EStore) (w : ConRon.Arena.Modular.WorkerRead)
    (wC : ConLeche.Driver.WorkerRead) (pendC : List (String × ConLeche.Name × ConstantVal)) :
    Prop where
  home : ∃ f, ModelIO.Gives (ConLeche.Frontend.Olean.readFiles sp mC .private : ModelIO _) F (.ok f) ∧
    ConLeche.Driver.LoadOf 0 mC f wC.home ∧ ConLeche.Frontend.Olean.checkViews mC f wC.home = .ok wC.expo ∧
    ValuesRel sp F st w.values #[⟨mC, wC.home.frontier⟩]
  reads : ModelIO.CanGive (ConLeche.Frontend.Olean.workerReads (.ofPath sp) mC 1 xC) F (.ok wC.reads)
  emitted : ConLeche.Driver.ownRecords wC.home = .ok wC.emitted
  reach : ∀ fl : ConLeche.Driver.FlagInfer, fl wC.reach.ctx.toList pendC = .ok () →
    ModelIO.CanGive (ConLeche.Driver.reachWith fl (.ofPath sp) mC wC.reads (ConLeche.Driver.ownOf xC wC)
      (ConLeche.Driver.rootsOf pins xC wC)) F (.ok wC.reach)
  nodup : (wC.reach.ctx.toList.flatMap ConLeche.Modular.declNames).Nodup
  own : wC.own = ConLeche.Driver.recsOf xC wC
  values : wC.values = {}
  copies : ConLeche.Driver.copiesOk mC xC wC.reads wC.reach wC.emitted = .ok ()
  reachRel : ReachRel st w.reach wC.reach
  pend : ListRel (PendRel st) w.reach.pending.toList pendC
  ownRel : denoteDeclArray st w.own = some wC.own
  persCtx : ∀ d ∈ w.reach.ctx.toList, PersDecl d
  persOwn : PersDecls w.own
  nulls : NullsRel st w.pins
  start : w.start = wC.reach.ctx.size

/-- The roots, as a list of handles denoting upstream's. -/
theorem nr_of_denoteNList {st : NStore} {l : List NIdx} {ys : List ConLeche.Name}
    (h : denoteNList st l = some ys) : ListRel (fun a b => denoteN st a = some b) l ys :=
  listRel_of_mapM (by rw [← denoteNList_eq_mapM]; exact h)

/-- The reads at a larger store. -/
theorem WorkerReadsRel.ext' {st st' : EStore} (hx : Ext st st') (hw' : NStoreWF st'.ns)
    {wr : ConRon.Arena.Frontend.Olean.WorkerReads} {wrC : ConLeche.Frontend.Olean.WorkerReads}
    (h : WorkerReadsRel st wr wrC) (hk : LoadsKeys wr.loads wrC.loads) : WorkerReadsRel st' wr wrC :=
  ⟨h.own.ext hx, h.loads.ext' hx hw' hk, h.pub, h.index.ext' hx,
    listRel_ext (fun _ _ hq => hq.ext hx) h.clashes⟩

/-- con-leche: ConLeche/Verify/Driver/Worker.lean:122-176 workerRead_ok — **the twin's phases 1–4
of the worker are upstream's**: an accepting `workerRead`, from a driver state with the pins
denoted (`intern_all_pins` runs first), gives an upstream worker read `wC` with `WorkerFacts`'
content (`WorkerReadOK`), the reach's under every flag inference accepting its pending
statements. -/
theorem workerRead_run (hH : HomeHyp) (hR : ReachRunHyp) {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {pins : List INatOpPinSet} {pinsC : List NatOpPinSet} {m : NIdx} {mC : ConLeche.Name}
    {x : Array (ImportF NIdx)} {xC : Array ImportRec} {w : ConRon.Arena.Modular.WorkerRead}
    {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    (hpins : PinsDenote s.store pins pinsC) (hm : denoteN s.store.ns m = some mC)
    (hx : ImpsD s.store x xC)
    (h : ConRon.Arena.Modular.workerRead (modelFs F) sp pins m x s = .ok (.ok w, s')) :
    DStep s s' ∧ ∃ wC pendC, WorkerReadOK pinsC sp F mC xC s'.store w wC pendC := by
  unfold ConRon.Arena.Modular.workerRead at h
  -- the reader's pins
  obtain ⟨pk, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hst1, hpk⟩ := oleanPins_run hok.state hoff h1
  have hok1 := DriverOK.of_parse hok hst1
  have hoff1 : s₁.store.scratchOn = false := by rw [hst1.scratch]; exact hoff
  have hm1 := denoteN_ext hm hst1.ext
  -- the private files
  obtain ⟨mn, s₂, h2, h⟩ := AM.bind_ok h
  obtain ⟨hs2, hmn⟩ := readName_run h2
  subst s₂
  rw [hm1] at hmn
  cases hmn
  obtain ⟨f, s₃, h3, h⟩ := AM.bind_ok h
  -- the home
  obtain ⟨le, s₄, h4, h⟩ := AM.bind_ok h
  obtain ⟨l, expo⟩ := le
  have hctx1 : Ctx pk s₁ := ⟨hok1.state, hoff1, hpk.nulls⟩
  obtain ⟨hst4, lC, expoC, hgf, hload, hviews, hl, hfront⟩ := hH hsp hctx1 hpk hm1 h3 h4
  have hok4 := DriverOK.of_parse hok1 hst4
  have hoff4 : s₄.store.scratchOn = false := by rw [hst4.scratch]; exact hoff1
  have hpk4 := hpk.ext hst4.ext
  -- the reads
  obtain ⟨wr, s₅, h5, h⟩ := AM.bind_ok h
  obtain ⟨hst5, wrC, hgr, hwr, hkeys⟩ :=
    workerReads_run hsp ⟨hok4.state, hoff4, hpk4.nulls⟩ (denoteN_ext hm1 hst4.ext)
      (hx.ext (hst1.ext.trans hst4.ext)) h5
  have hok5 := DriverOK.of_parse hok4 hst5
  have hoff5 : s₅.store.scratchOn = false := by rw [hst5.scratch]; exact hoff4
  -- the solution's closure does not hold the challenge
  dsimp only at h
  split at h
  · exfalso
    obtain ⟨_, _, _, h'⟩ := AM.bind_ok h
    obtain ⟨_, _, h'', _⟩ := AM.bind_ok h'
    exact ConRon.Bridge.Modular.fail_not_ok h''
  rename_i hnx
  obtain ⟨u0, s₆, h6, h⟩ := AM.bind_ok h
  obtain ⟨-, hs6⟩ := AM.pure_ok h6
  subst s₆
  -- the own records
  obtain ⟨ro, s₇, h7, h⟩ := AM.bind_ok h
  rcases ro with e | ds
  · obtain ⟨hv, -⟩ := AM.pure_ok h
    cases hv
  dsimp only at h
  have hl5 := hl.ext hst5.ext
  obtain ⟨hst7, hpds, dsC, hrecC, hds⟩ :=
    ownRecords_run hok5.state hoff5 hok5.pins (hpk4.ext hst5.ext) hl5 h7
  have hok7 := DriverOK.of_parse hok5 hst7
  have hoff7 : s₇.store.scratchOn = false := by rw [hst7.scratch]; exact hoff5
  have hw7 := nsWF_of_StateOK hok7.state
  have hx7 : ImpsD s₇.store x xC := hx.ext (((hst1.ext.trans hst4.ext).trans hst5.ext).trans hst7.ext)
  have hwr7 := hwr.ext' hst7.ext hw7 hkeys
  have hl7 := hl5.ext hst7.ext
  have hpins7 : PinsDenote s₇.store pins pinsC :=
    hpins.mono (((hst1.ext.trans hst4.ext).trans hst5.ext).trans hst7.ext)
  have hpk7 := (hpk4.ext hst5.ext).ext hst7.ext
  have hm7 := denoteN_ext hm (((hst1.ext.trans hst4.ext).trans hst5.ext).trans hst7.ext)
  -- the reach and the hoist
  obtain ⟨rr, s₈, h8, h⟩ := AM.bind_ok h
  obtain ⟨r, own, hoisted⟩ := rr
  obtain ⟨hv, hs⟩ := AM.pure_ok h
  cases hv
  subst hs
  unfold ConRon.Arena.Modular.workerReach at h8
  -- the holes
  obtain ⟨u, s₉, h9, h⟩ := AM.bind_ok h8
  obtain ⟨hst9, -⟩ := ownHolesOk_run (mC := mC) hok7 hoff7 (usedRel_ownUses hl7) hx7
    hwr7.index.first hpds hds h9
  have hx9 := hx7.ext hst9.ext
  have hw9 := nsWF_of_StateOK hst9.ok.state
  have hwr9 := hwr7.ext' hst9.ext hw9 hkeys
  have hl9 := hl7.ext hst9.ext
  have hds9 := denoteDeclArray_ext hst9.ext hds
  -- the roots
  obtain ⟨roots, s₁₀, h10, h⟩ := AM.bind_ok h
  obtain ⟨hst10, hroots⟩ := rootsAt_exact hst9.ok hst9.scratch (hpins7.mono hst9.ext) hx9
    hwr9.index.first hl9 hpds hds9 h10
  have hw10 := nsWF_of_StateOK hst10.ok.state
  have hwr10 := hwr9.ext' hst10.ext hw10 hkeys
  -- the reach
  obtain ⟨r', s₁₁, h11, h⟩ := AM.bind_ok h
  obtain ⟨hst11, hpctx, rC, pendC, hrr, hpend, hcan⟩ :=
    hR hsp hst10.ok hst10.scratch (hpk7.ext (hst9.ext.trans hst10.ext))
      (denoteN_ext hm7 (hst9.ext.trans hst10.ext)) hwr10 hkeys
      ((ownNamesOf_rel hw10 (hx9.ext hst10.ext) hwr10.index (hl9.ext hst10.ext)))
      (nr_of_denoteNList hroots) h11
  have hw11 := nsWF_of_StateOK hst11.ok.state
  -- the context's names distinct
  obtain ⟨b, s₁₂, h12, h⟩ := AM.bind_ok h
  cases b with
  | false =>
    exfalso
    simp only [Bool.not_false, ite_true] at h
    obtain ⟨_, _, h', _⟩ := AM.bind_ok h
    exact ConRon.Bridge.Modular.fail_not_ok h'
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
  obtain ⟨hst12, hnd⟩ := ctxNamesNodup_run hst11.ok hst11.scratch hpctx hrr.ctx h12
  obtain ⟨u1, s₁₂', h12', h⟩ := AM.bind_ok h
  obtain ⟨-, hs12⟩ := AM.pure_ok h12'
  subst s₁₂'
  have hx12 := (hx9.ext (hst10.ext.trans hst11.ext)).ext hst12.ext
  have hwr12 := (hwr10.ext' hst11.ext hw11 hkeys).ext' hst12.ext (nsWF_of_StateOK hst12.ok.state) hkeys
  have hext9_12 := (hst10.ext.trans hst11.ext).trans hst12.ext
  -- the copies
  obtain ⟨u2, s₁₃, h13, h⟩ := AM.bind_ok h
  obtain ⟨hst13, hcop⟩ := copiesOk_run (mC := mC) hst12.ok
    ((hpk7.ext hst9.ext).ext hext9_12).nulls hx12 hwr12
    (hrr.ext hst12.ext) (denoteDeclArray_ext hext9_12 hds9) hnd h13
  have hoff13 : s₁₃.store.scratchOn = false := by rw [hst13.scr]; exact hst12.scratch
  have hext9_13 := hext9_12.trans hst13.ext
  -- the own records, hoisted
  obtain ⟨recs, s₁₄, h14, h⟩ := AM.bind_ok h
  obtain ⟨oh, s₁₅, h15, h⟩ := AM.bind_ok h
  obtain ⟨own', moved⟩ := oh
  obtain ⟨hv, hs⟩ := AM.pure_ok h
  cases hv
  subst hs
  obtain ⟨hst15, hpown, hown⟩ := recsOf_run hst13.ok hoff13 (hx12.ext hst13.ext)
    (hwr12.index.first.ext' hst13.ext) (hl9.ext hext9_13) hpds (denoteDeclArray_ext hext9_13 hds9)
    h14 h15
  -- the steps, composed
  have hd7 : DStep s s₇ := ⟨hok7, ((hst1.ext.trans hst4.ext).trans hst5.ext).trans hst7.ext,
    by rw [hst7.pins, hst5.pins, hst4.pins, hst1.pins], hoff7⟩
  have hst : DStep s s' :=
    hd7.trans (hst9.trans (hst10.trans (hst11.trans (hst12.trans
      ((⟨hst13.ok, hst13.ext, hst13.pins, hoff13⟩ : DStep s₁₂ s₁₃).trans hst15)))))
  have hx11_15 : Ext s₁₁.store s'.store := (hst12.ext.trans hst13.ext).trans hst15.ext
  have hx4_15 : Ext s₄.store s'.store :=
    ((hst5.ext.trans hst7.ext).trans hst9.ext).trans ((hst10.ext.trans hst11.ext).trans hx11_15)
  refine ⟨hst, ⟨lC, expoC, wrC, dsC,
    (ConLeche.Frontend.hoistNatOpGround (ConLeche.Driver.ownUses lC)
      (ConLeche.Driver.ownRecs xC wrC.index dsC)).1, rC,
    (ConLeche.Frontend.hoistNatOpGround (ConLeche.Driver.ownUses lC)
      (ConLeche.Driver.ownRecs xC wrC.index dsC)).2, {}⟩, pendC, ?_⟩
  refine ⟨⟨f, hgf, hload, hviews, .cons ⟨denoteN_ext hm hst.ext, f, hgf, hfront.ext hx4_15⟩ .nil⟩,
    hgr.canGive, hrecC, fun fl hfl => hcan fl hfl, hnd, rfl, rfl, hcop, hrr.ext hx11_15,
    listRel_ext (fun _ _ hq => ⟨denoteN_ext hq.1 hx11_15, denoteStmt_ext hx11_15 hq.2⟩) hpend,
    hown, hpctx, hpown, (hpk.ext (hst4.ext.trans hx4_15)).nulls, ?_⟩
  · have := denoteDecls_length hrr.ctx
    simpa using this

/-- The names of a list of records, as the consts of their records. -/
theorem recsConsts_names (ds : List Declaration) :
    (ConLeche.Cached.recsConsts ds).map (·.name) = ds.flatMap ConLeche.Modular.declNames := by
  simp only [ConLeche.Cached.recsConsts, List.map_flatMap]
  rfl

/-- con-leche: ConLeche/Verify/Driver/Worker.lean:238-249 WorkerAccepted — **an accepted worker
at the twin is upstream's accepted worker**: phases 1–4 (`workerRead_run`), the check phase of the
own records from `start` (`Arena.pooledOleanAcceptsFrom_bridge`, the pure run from the context's
environment), the inferred flags on a fresh worker at the frozen index (`inferFlags_run`, whose
accept is `soundFlags`', a sound inference). -/
theorem workerAccepted_run (hk : CoreSpec Arena.checkFuel) (hind : IndSpec) (hH : HomeHyp)
    (hR : ReachRunHyp) {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {pins : List INatOpPinSet} {pinsC : List NatOpPinSet} {m : NIdx} {mC : ConLeche.Name}
    {x : Array (ImportF NIdx)} {xC : Array ImportRec} {w : ConRon.Arena.Modular.WorkerRead}
    {s s' sE w₁ : AState} {I : IStreamIndex} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    (hpp : PersPins s) (hpps : PersPinSets pins) (hpins : PinsDenote s.store pins pinsC)
    (hm : denoteN s.store.ns m = some mC) (hx : ImpsD s.store x xC)
    (h : ConRon.Arena.Modular.workerRead (modelFs F) sp pins m x s = .ok (.ok w, s'))
    (hP : Arena.PooledOleanAcceptsFromJ (modelFs F) w.pins sp w.values .verified pins none w.start
      (ConRon.Arena.Modular.workerDecls w) s' I sE)
    (hI : ConRon.Arena.Modular.inferFlags I w.reach.ctx w.reach.pending sE.worker = .ok ((), w₁)) :
    ConLeche.Driver.WorkerAccepted pinsC sp F mC 1 xC := by
  obtain ⟨hst, wC, pendC, hw⟩ := workerRead_run hH hR hsp hok hoff hpins hm hx h
  have hpp' : PersPins s' := hpp.mono hst.pins
  have hpins' : PinsDenote s'.store pins pinsC := hpins.mono hst.ext
  have hctx : denoteDecls s'.store w.reach.ctx.toList = some wC.reach.ctx.toList := hw.reachRel.ctx
  have hown : denoteDecls s'.store w.own.toList = some wC.own.toList := denoteDeclArray_iff.mp hw.ownRel
  have hden : denoteDecls s'.store (ConRon.Arena.Modular.workerDecls w).toList =
      some (wC.reach.ctx.toList ++ wC.own.toList) := by
    simp only [ConRon.Arena.Modular.workerDecls, Array.toList_append]
    exact denoteDecls_append hctx hown
  have hpd : ∀ d ∈ (ConRon.Arena.Modular.workerDecls w).toList, PersDecl d := by
    intro d hd
    simp only [ConRon.Arena.Modular.workerDecls, Array.toList_append, List.mem_append] at hd
    rcases hd with hd | hd
    · exact hw.persCtx d hd
    · exact hw.persOwn d (Array.mem_toList_iff.mp hd)
  -- the context, from the reach under any inference (the trivial one)
  obtain ⟨_, _, hr0⟩ := hw.reach (fun _ _ => .ok ()) rfl
  obtain ⟨hord, -, -, hwfC, -⟩ := ConLeche.Driver.reach_ok hr0
  have hndC : ((ConLeche.Cached.recsConsts wC.reach.ctx.toList).map (·.name)).Nodup := by
    rw [recsConsts_names]; exact hw.nodup
  -- the inferred flags, at the frozen index
  have hP' := hP
  obtain ⟨parts, hbuild, -⟩ := hP
  obtain ⟨hokE, hxE, hpinsE, hoffE, hIE, hpIE⟩ :=
    buildIndex_run constsSpec tablesSpec hst.ok hpp' hst.scratch hpd hden hbuild
  have hpre : ∀ k ≤ wC.reach.ctx.toList.length,
      ConLeche.EnvWF (ConLeche.streamEnv (wC.reach.ctx.toList.take k)) ∧
        ((ConLeche.Cached.recsConsts (wC.reach.ctx.toList.take k)).map (·.name)).Nodup := by
    intro k _
    refine ⟨ConLeche.Driver.envWF_prefix hord hwfC, ?_⟩
    rw [recsConsts_names]
    have hn := hw.nodup
    rw [← List.take_append_drop k wC.reach.ctx.toList, List.flatMap_append] at hn
    exact (List.nodup_append.mp hn).1
  obtain ⟨-, hfl⟩ := inferFlags_run hk hokE.pins (hpp'.mono hpinsE) hokE.state.wf hoffE hIE hpIE hpre
    hw.persCtx (denoteDecls_ext hxE _ _ hctx)
    (listRel_ext (fun _ _ hq => ⟨denoteN_ext hq.1 hxE, denoteStmt_ext hxE hq.2⟩) hw.pend)
    (WorkerOK.start hokE.state) hI
  -- the own records, from the context's environment
  obtain ⟨f, hgf, hload, hviews, hvals⟩ := hw.home
  have hstart : w.start = wC.reach.ctx.toList.length := by rw [hw.start]; simp
  rw [hstart] at hP'
  have hpure := Arena.pooledOleanAcceptsFrom_bridge (ctxC := wC.reach.ctx.toList)
    (ownC := wC.own.toList) (s₀ := s') hk hind hst.ok hst.scratch hpp' hpps hpins' hpd hden
    hst.ok.state.wf hst.scratch (PExt.of_ext (Ext.refl _)) hvals hw.nulls hsp hwfC hndC hP'
  exact ⟨wC, ⟨⟨f, hgf.canGive, hload, hviews⟩, hw.reads, hw.emitted,
    ⟨soundFlags, soundFlags_ok, hw.reach _ hfl⟩, hw.nodup, hw.own,
    by rw [hw.values]; exact ConLeche.Driver.cacheOK_empty, hw.copies⟩, hpure⟩

/-- con-leche: ConLeche/Verify/Driver/Worker.lean:238-249 WorkerAccepted — **a worker run at the
twin, from its start state, is upstream's accepted worker**: the reserved pins, the module's name
(and under `--compare` the solution's) interned, the pins interned (before the worker, which reads
them for the roots' pin ground), phases 1–4, the check phase from `start` and the inferred flags.
`hx`: the imports the run adds, read back from the interned names. -/
theorem workerStage_run (hk : CoreSpec Arena.checkFuel) (hind : IndSpec) (hH : HomeHyp)
    (hR : ReachRunHyp) {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {names : List ConLeche.Name} {hs : List NIdx} {m : NIdx} {mC : ConLeche.Name}
    {pinsC : List NatOpPinSet} {maxNatSize : Nat} {pins : List INatOpPinSet}
    {x : Array (ImportF NIdx)} {xC : Array ImportRec} {w : ConRon.Arena.Modular.WorkerRead}
    {sA sB sC sD sE w₁ : AState} {I : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hN : (mC :: names).mapM ConRon.Arena.internName sA = .ok (m :: hs, sB))
    (hx : ListRel (NR sB.store) (m :: hs) (mC :: names) → ImpsD sB.store x xC)
    (hE : internAllPins pinsC maxNatSize sB = .ok (pins, sC))
    (hW : ConRon.Arena.Modular.workerRead (modelFs F) sp pins m x sC = .ok (.ok w, sD))
    (hP : Arena.PooledOleanAcceptsFromJ (modelFs F) w.pins sp w.values .verified pins none w.start
      (ConRon.Arena.Modular.workerDecls w) sD I sE)
    (hI : ConRon.Arena.Modular.inferFlags I w.reach.ctx w.reach.pending sE.worker = .ok ((), w₁)) :
    ConLeche.Driver.WorkerAccepted pinsC sp F mC 1 xC := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ := internReservedPins_run hok0 rfl hA
  obtain ⟨hstB, hnr⟩ := internNames_run hokA hoffA (mC :: names) hN
  have hoffB : sB.store.scratchOn = false := by rw [hstB.scratch]; exact hoffA
  obtain ⟨hokC, hxC, hpinsC, hppC, hipins, hpps, hoffC, hcachesC, -⟩ :=
    internAllPins_run hstB.ok (hpinsA.mono hstB.ext hstB.pins) (hppA.mono hstB.pins) hoffB hE
  have hdC : DriverOK sC := DriverOK.start hokC hpinsC
    (((CacheOK.of_empty (s := sA) (by rw [hcachesA]; exact hc0)).monoF hstB.ext hstB.cframe).mono
      hxC hcachesC)
  have hm : denoteN sC.store.ns m = some mC := by
    cases hnr with
    | cons h1 _ => exact denoteN_ext h1 hxC
  exact workerAccepted_run hk hind hH hR hsp hdC hoffC hppC hpps hipins hm ((hx hnr).ext hxC) hW hP hI

end ConRon.Bridge.Modular
