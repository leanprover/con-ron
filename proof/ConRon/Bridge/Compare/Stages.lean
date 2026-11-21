/-
# `ConRon.Bridge.Compare.Stages` — THEOREM 1 at the compared run's pipeline

The binary's `--compare -- C S` runs, on one state from the driver's start,

    internReservedPins → builtinPreludeE → parseChunks C → parseChunks S → preparePrelude S
      → internAllPins → the solution's check phase (`Arena.PooledAccepts`, no solution)
      → preparePrelude C → sideRecordsGo → the challenge's check phase at `solutionOf`

(`crates/con-ron/src/compare.rs`, the twin's `Arena/Main.lean` `compareJsonTail`).
`stagesC_model`: the challenge's checked records (`sideRecord` of each prepared record) have an
environment with a model; `stagesC_no_False`: a challenge file declaring a theorem of type
`False` is not accepted.  Nothing about the solution is concluded.

The solution's check phase is `Bridge/Checker/Pool.lean`'s `Arena.pooledAccepts_bridge` (the
pure fold accepting the solution stream), the challenge's `Compare/Pooled.lean`'s
`Arena.pooledAcceptsJ_bridge` (a mixed run against that solution), and con-leche's comparison
soundness restated over them, `Compare/Model.lean`'s `mixed_model`.
-/
module

public import ConRon.Bridge.Compare.Pooled
public import ConRon.Bridge.Compare.Side
public import ConRon.Bridge.Stages
import ConRon.Bridge.Specs
import ConLeche.Verify.Cached.PureRun
import ConLeche.Verify.CheckerF
import ConRon.Bridge.Checker.Install
import ConLeche.Verify.Frontend.FileFalse
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Driver.Reach

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge.Frontend

universe w

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:290 streamEnv_consts — **an accepted pure
fold's stream has distinct names**: its push chain from the empty environment. -/
theorem pure_nodup {pinsP : List NatOpPinSet} {F : Nat} {ds : List Declaration}
    (h : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pinsP ds =
      .ok (ConLeche.streamEnv ds)) :
    ((ConLeche.Cached.recsConsts ds).map (·.name)).Nodup := by
  have h' : ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP)
      Env.empty = .ok (ConLeche.streamEnv ds) := h
  have hch := (ConLeche.PureRun.of_foldlM (pins := pinsP) ds h').chain (ConLeche.Cached.PushChain.refl Env.empty)
  have hnd : ConLeche.NodupNames (ConLeche.streamEnv ds) := by
    have := hch.2.2.1 List.nodup_nil
    rwa [mkFEnv_env] at this
  unfold ConLeche.NodupNames at hnd
  rw [ConLeche.Cached.streamEnv_consts] at hnd
  have he : (Env.empty).consts = [] := rfl
  rw [he, List.append_nil, List.map_reverse] at hnd
  exact (List.pairwise_reverse.mp hnd).imp fun h e => h e.symm

/-- con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG — **the compared run's frame,
up to the solution's check phase**: after the pins, the prelude, both parses, the solution's
preparation and the pin variants from the driver's start state, the scratch tier is closed, the
check phase's start invariant holds, the pins and the solution's prepared stream denote, and the
challenge's parsed records and the prelude still denote. -/
theorem stagesC_frame {chunksC chunksS : List ByteArray} {pins : List NatOpPinSet}
    {maxNatSize : Nat} {sA sB sC sC' sD sE : AState} {pre : PreludeIx} {rC rS : ParseResultD}
    {dsS : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunksC sB = .ok (.ok rC, sC))
    (hCS : parseChunks chunksS sC = .ok (.ok rS, sC'))
    (hDS : preparePrelude pre rS.decls sC' = .ok (dsS, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE)) :
    sE.store.scratchOn = false ∧ DriverOK sE ∧ PersPins sE ∧
      PinsDenote sE.store ipins pins ∧ PersPinSets ipins ∧
      (∀ x ∈ dsS.toList, PersDecl x) ∧ PersPreludeIx pre ∧ PersDecls rC.decls ∧
      ∃ rcC rcS preC, ConLeche.Frontend.parseChunks chunksC = .ok rcC ∧
        ConLeche.Frontend.parseChunks chunksS = .ok rcS ∧
        PreludeIxRel sE.store pre preC ∧
        denoteDeclArray sE.store rC.decls = some rcC.decls ∧
        denoteDecls sE.store dsS.toList =
          some (ConLeche.Frontend.preparePrelude preC rcS.decls).toList := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ :=
    builtinPreludeE_run hokA hoffA hpinsA hB
  obtain ⟨hstep2, hpersRC, rcC, hclC, hrelC⟩ :=
    parseChunks_run hstep1.ok
      (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins) hC
  obtain ⟨hstep2', hpersRS, rcS, hclS, hrelS⟩ :=
    parseChunks_run hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins) hCS
  have h12 := (hstep1.trans hstep2).trans hstep2'
  obtain ⟨hstep3, hpersDs, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2'.ok
      (by rw [h12.scratch, hoffA])
      (hpinsA.mono h12.ext h12.pins)
      (denoteDeclArray_ext (hstep2.ext.trans hstep2'.ext) hrelPre) hpersPre
      hrelS.decls hpersRS hDS
  have h13 := h12.trans hstep3
  have hoff3 : sD.store.scratchOn = false := by rw [h13.scratch]; exact hoffA
  obtain ⟨hokP, hxP, hpinsP, hppP, hipins, hpps, hoffP, hcachesP, -⟩ :=
    internAllPins_run hstep3.ok
      (hpinsA.mono h13.ext h13.pins)
      (hppA.mono h13.pins) hoff3 hE
  have hx2E : Ext sC.store sE.store := (hstep2'.ext.trans hstep3.ext).trans hxP
  refine ⟨hoffP, DriverOK.start hokP hpinsP
      (((CacheOK.of_empty (s := sA) (by rw [hcachesA]; exact hc0)).monoF
            h13.ext h13.cframe).mono hxP hcachesP),
    hppP, hipins, hpps, fun x hx => hpersDs x (by simpa using hx), hpersPre,
    hpersRC, rcC, rcS, preC, hclC, hclS,
    denoteDeclArray_ext ((hstep2.ext.trans hstep2'.ext).trans (hstep3.ext.trans hxP)) hrelPre,
    denoteDeclArray_ext hx2E hrelC.decls,
    denoteDeclArray_iff.mp (denoteDeclArray_ext hxP hclPrep)⟩

/-- con-leche: ConLeche/MainTheorem.lean:63 main_compare_json_model
con-leche: ConLeche/Model/PureChecker.lean:43 solution_model_exists — **the compared run's
challenge has a model, at the pipeline**: the challenge's checked records (each prepared record
through `sideRecord`) are what the twin's records denote at its end state, and their
environment has a model.  The solution's check phase is a premise like any other stage; nothing
is concluded about the solution. -/
theorem stagesC_model (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {chunksC chunksS : List ByteArray} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {sA sB sC sC' sD sE sF sG sH sI : AState} {pre : PreludeIx} {rC rS : ParseResultD}
    {dsS dsC : Array IDeclaration} {recsC : List IDeclaration} {ipins : List INatOpPinSet}
    {IS IC : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunksC sB = .ok (.ok rC, sC))
    (hCS : parseChunks chunksS sC = .ok (.ok rS, sC'))
    (hDS : preparePrelude pre rS.decls sC' = .ok (dsS, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE))
    (hFS : Arena.PooledAccepts .verified ipins dsS sE IS sF)
    (hDC : preparePrelude pre rC.decls sF = .ok (dsC, sG))
    (hside : sideRecordsGo [] dsC.toList sG = .ok (recsC, sH))
    (hFC : ∃ (parts : List (List Nat)),
      buildIndex recsC.toArray sH = .ok (.ok IC, sI) ∧
      (∀ t < recsC.toArray.size, ∃ w ∈ parts, t ∈ w) ∧
      (∀ w ∈ parts, ∀ t ∈ w, t < recsC.toArray.size) ∧
      (∀ w ∈ parts, w.Pairwise (· < ·)) ∧
      (∀ w ∈ parts, ∃ s'', checkJobList .verified ipins (some (solutionOf IS recsC)) IC
        recsC.toArray w sI.worker = .ok (.ok (), s''))) :
    StoreWF sH.store ∧ ∃ rcC preC dsP, ConLeche.Frontend.parseChunks chunksC = .ok rcC ∧
      dsP = (ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map
        ConLeche.Cached.sideRecord ∧
      denoteDecls sH.store recsC = some dsP ∧
      Nonempty (ConLeche.Model.EnvModelM V (ConLeche.streamEnv dsP)) := by
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, hpersPre, hpersRC, rcC, rcS, preC, hclC, -,
    hrelPre, hrelC, hdenS⟩ := stagesC_frame hA hB hC hCS hDS hE
  -- the solution: the pure fold accepts it
  obtain ⟨F, hpure⟩ :=
    Arena.pooledAccepts_bridge hk hind hst hoff hpp hpps hipins hpd hdenS hFS
  obtain ⟨partsS, hidxS, -⟩ := hFS
  obtain ⟨hstF, hxF, hpF, hoffF, hIS, hpIS⟩ :=
    buildIndex_run constsSpec tablesSpec hst hpp hoff hpd hdenS hidxS
  -- the challenge's preparation and its records
  obtain ⟨hstepG, hpersC, hclPrepC⟩ :=
    preparePrelude_run (preC := preC) hstF.state hoffF (hstF.pins)
      (denoteDeclArray_ext hxF hrelPre) hpersPre (denoteDeclArray_ext hxF hrelC) hpersRC hDC
  have hdenC : denoteDecls sG.store dsC.toList =
      some (ConLeche.Frontend.preparePrelude preC rcC.decls).toList :=
    denoteDeclArray_iff.mp hclPrepC
  obtain ⟨rfl, hdenR, hpersR⟩ := sideRecordsGo_run hstepG.ok (hstF.pins.mono hstepG.ext hstepG.pins)
    dsC.toList [] recsC _ [] rfl hdenC hside
  simp only [List.nil_append] at hdenR
  have hpR : ∀ x ∈ recsC, PersDecl x :=
    hpersR (fun _ h => nomatch h) (fun x hx => hpersC x (by simpa using hx))
  -- the challenge's check phase
  have hstG : DriverOK sG := DriverOK.of_check
    (hstF.monoF hstepG.ok hstepG.ext hstepG.cframe hstepG.pins) hstepG.pins
  have hxEG : Ext sE.store sG.store := hxF.trans hstepG.ext
  have hrun := Arena.pooledAcceptsJ_bridge (pinsP := pins) (dsS :=
      (ConLeche.Frontend.preparePrelude preC rcS.decls).toList)
    (matesU := ConLeche.Cached.recordMates
      ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map
        ConLeche.Cached.sideRecord).toArray)
    hk hind hstG (by rw [hstepG.scratch]; exact hoffF)
    (hpp.mono (by rw [hstepG.pins, hpF])) hpps (PinsDenote.mono hxEG ipins pins hipins)
    (by simpa using hpR) (by simpa using hdenR)
    (hIS.pmono hpIS (PExt.of_ext hstepG.ext)) hpIS (pure_nodup hpure)
    (solutionOf_mates hstepG.ok.wf hdenR hpR) hFC
  exact ⟨hstepG.ok.wf, rcC, preC, _, hclC, rfl, hdenR,
    Compare.mixed_model (pinsP := pins) V hpure hrun⟩

/-- con-leche: ConLeche/MainTheorem.lean:63 main_compare_json_model — **a compared run accepting
a challenge file that declares a theorem of type `False` is impossible**: the theorem is in the
challenge's prepared records (`parseChunks_jsonWithTheoremFalse`, `mem_preparePrelude`), its
checked record (`sideRecord`: itself, or the axiom of its statement) installs a constant of type
`False`, and the challenge's environment has a model. -/
theorem stagesC_no_False (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {chunksC chunksS : List ByteArray} {pins : List NatOpPinSet} {maxNatSize : Nat}
    (hfalse : ConLeche.jsonWithTheoremFalse chunksC)
    {sA sB sC sC' sD sE sF sG sH sI : AState} {pre : PreludeIx} {rC rS : ParseResultD}
    {dsS dsC : Array IDeclaration} {recsC : List IDeclaration} {ipins : List INatOpPinSet}
    {IS IC : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunksC sB = .ok (.ok rC, sC))
    (hCS : parseChunks chunksS sC = .ok (.ok rS, sC'))
    (hDS : preparePrelude pre rS.decls sC' = .ok (dsS, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE))
    (hFS : Arena.PooledAccepts .verified ipins dsS sE IS sF)
    (hDC : preparePrelude pre rC.decls sF = .ok (dsC, sG))
    (hside : sideRecordsGo [] dsC.toList sG = .ok (recsC, sH))
    (hFC : ∃ (parts : List (List Nat)),
      buildIndex recsC.toArray sH = .ok (.ok IC, sI) ∧
      (∀ t < recsC.toArray.size, ∃ w ∈ parts, t ∈ w) ∧
      (∀ w ∈ parts, ∀ t ∈ w, t < recsC.toArray.size) ∧
      (∀ w ∈ parts, w.Pairwise (· < ·)) ∧
      (∀ w ∈ parts, ∃ s'', checkJobList .verified ipins (some (solutionOf IS recsC)) IC
        recsC.toArray w sI.worker = .ok (.ok (), s''))) :
    False := by
  obtain ⟨-, rcC, preC, dsP, hclC, rfl, -, ⟨mp⟩⟩ :=
    stagesC_model V hk hind hA hB hC hCS hDS hE hFS hDC hside hFC
  obtain ⟨cv, vl, hty, hmem⟩ := ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hclC
  have hmem' : Declaration.thmDecl cv vl ∈
      (ConLeche.Frontend.preparePrelude preC rcC.decls).toList := by
    simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem
  -- the checked record installs a constant of the theorem's type
  have hc : ∃ c ∈ ConLeche.declConstants (ConLeche.Cached.sideRecord (.thmDecl cv vl)),
      c.toConstantVal.type = .const falseName [] := by
    simp only [ConLeche.Cached.sideRecord]
    split
    · next hb =>
      have hbi : ConLeche.Cached.builtinAxiomName cv.name = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb; exact hb.1
      have hq : cv.name ≠ quotSoundName := fun h => by
        simp [ConLeche.Cached.builtinAxiomName, h] at hbi
      have hs : cv.name ≠ sorryAxName := fun h => by
        simp [ConLeche.Cached.builtinAxiomName, h] at hbi
      exact ⟨.axiomInfo cv, by simp [ConLeche.declConstants, hq, hs], hty⟩
    · exact ⟨.thmInfo cv, by simp [ConLeche.declConstants], hty⟩
  obtain ⟨c, hcd, hcty⟩ := hc
  have hcs : c ∈ (ConLeche.streamEnv ((ConLeche.Frontend.preparePrelude preC
      rcC.decls).toList.map ConLeche.Cached.sideRecord)).consts :=
    (ConLeche.Driver.mem_streamEnv_consts _ _).2
      (.inl ⟨_, List.mem_map_of_mem hmem', hcd⟩)
  exact ConLeche.Model.no_constant_of_False mp c hcs hcty

end ConRon.Bridge
