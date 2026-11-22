import ConRon.Bridge.Stages
import ConRon.Bridge.Compare.Stages
import ConRon.Bridge.Compare.StagesOleans
import ConLeche.Model.IsModelJson
import ConLeche.Model.IsModelBridge
import ConLeche.Verify.IsModelRecords
import ConLeche.Verify.IsModelSide
import ConLeche.Verify.OleanInput
import ConLeche.Verify.CompareInput
import ConLeche.Verify.Cached.PureRun
import ConLeche.Verify.Frontend.FileFalse
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Driver.Copies
import ConLeche.Verify.Inductives.IotaRead
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.BridgeDecl
import ConLeche.Model.Fold
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Install

/-!
# `ConRon.MainTheorem.PureStored` — what the PURE accept stores, and the stages in con-leche's words

con-leche's main theorems reach `IsModel` (`ConLeche/IsModel.lean`) from the CACHED checker's
accept: the fold's model (`Cached.checkDecls_sound`) and that the fold stores every record it
read (`Cached.checkDecls_recordsStored`, `Olean.checkDecls_inputStored`), joined by
`isModel_of_envModelM`.  Theorem 1 ends instead at the PURE fold (`checkDeclsPure`, the pure run
`PureRun`) and, for a comparison's challenge, at the mixed run (`Compare.MixedRun`).  This file
states the storing half for those two runs, and the stages' conclusions in con-leche's words:

| here | con-leche, at the cached accept |
|---|---|
| `pureRun_recordsStored` | `Cached.declsRun_recordsStored` |
| `mixedRun_recordsStored` | `Cached.declsRun_recordsStored` at a solution |
| `inputStored_of_covered` | `Olean.inputStored_of`, the reader's cover a premise |
| `stages_isModel` | `json_isModel` |
| `stagesC_isModel` | `compare_json_isModel` |
| `stagesO_isModel` | `oleans_isModel` |
| `stagesOC_isModel` | `compare_isModel` |

Each is upstream's proof with the pure run's facts (`PureRun.env`, `.chain`, `.blockRead`,
`.reads`, `.basisNamesOk`) in place of the cached run's.
-/

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConLeche.Cached ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge.Frontend

universe w

/-! ## The pure run stores its records -/

/-- con-leche: ConLeche/Verify/IsModelRecords.lean:582 declsRun_recordsStored — **a pure run
from the empty environment stores its records** (`RecordsStored`). -/
theorem pureRun_recordsStored {pins : List NatOpPinSet} {ds : List Declaration} {E' : Env}
    (h : PureRun pins ds Env.empty E') : RecordsStored (· ∈ constantsOf ds) E' := by
  have henv : E' = streamEnv ds := h.env
  have hnd : NodupNames E' := by
    have := (h.chain (PushChain.refl Env.empty)).2.2.1 List.nodup_nil
    rwa [mkFEnv_env] at this
  have hb := h.blockRead
  have hr := h.reads
  intro c hc
  obtain ⟨d, hd, hc⟩ := mem_constantsOf.1 hc
  obtain ⟨ci, hci, hst⟩ := records_stored (hb d hd) c hc
  have hmem : ci ∈ E'.consts := by
    rw [henv]
    exact (Driver.mem_streamEnv_consts ds _).2 (.inl ⟨d, hd, hci⟩)
  have hn : c.name = ci.name := by
    show c.toConstantVal.name = ci.toConstantVal.name
    rw [hst.1]
  exact ⟨ci, hn ▸ Driver.find?_of_nodup hnd hmem, hst, fun _ _ _ _ _ _ => hr d hd ci hci⟩

/-- con-leche: ConLeche/Verify/Cached/PureRun.lean:579 PureRun.basisNamesOk — **every record of a
mixed run passed the reserved names' check**: the pure arm by `checkDecl_inv`, the justified arm
by its own premise. -/
theorem mixedRun_basisNamesOk {pinsP : List NatOpPinSet} {JS : Solution} {ds : List Declaration}
    {E E' : Env} (h : Compare.MixedRun pinsP JS ds E E') : ∀ d ∈ ds, basisNamesOk d = true := by
  induction h with
  | nil => exact fun _ h => nomatch h
  | cons hs _ ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · rcases hs with ⟨-, F, hF⟩ | ⟨cv, -, -, -, hb, -⟩
      · exact (ConLeche.checkDecl_inv hF).2
      · exact hb
    · exact ih d hd

/-- con-leche: ConLeche/Verify/Cached/PureRun.lean:491 PureRun.blockRead
con-leche: ConLeche/Verify/Cached/PureRun.lean:591 PureRun.reads — **a mixed run's records read
their blocks, and its recursors read at its end**: the pure arm a one-step pure run, the
justified arm one axiom (`justifiable_constants`). -/
theorem mixedRun_facts {pinsP : List NatOpPinSet} {JS : Solution} {ds : List Declaration}
    {E E' : Env} (h : Compare.MixedRun pinsP JS ds E E') :
    ∀ d ∈ ds, (∀ block nP, d = .indDecl block nP → BlockRead nP block) ∧
      ∀ ci ∈ declConstants d, RecReads E'.find? ci ∨ ∃ k cv, ci = ConLeche.quotAt k cv := by
  induction h with
  | nil => exact fun _ h => nomatch h
  | @cons pd ds E E₁ E' hs rest ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · have hq : PushChain E₁ (mkFEnv E') := rest.chain (PushChain.refl E₁)
      rcases hs with ⟨-, F, hF⟩ | ⟨cv, hj, rfl, -, -, -⟩
      · have hp1 : PureRun pinsP [d] E E₁ := .cons ⟨F, hF⟩ (.nil _)
        refine ⟨hp1.blockRead d List.mem_cons_self, fun ci hci => ?_⟩
        rcases hp1.reads d List.mem_cons_self ci hci with hR | hR
        · exact .inl (RecReads.mono (fun n c h => ConLeche.PushChain.find?_some hq h) hR)
        · exact .inr hR
      · refine ⟨fun block nP he => ?_, fun ci hci => ?_⟩
        · subst he; simp [Cached.justifiable] at hj
        · rw [(justifiable_constants hj).1, List.mem_singleton] at hci
          subst hci
          exact .inl fun _ _ _ _ _ hcr => nomatch hcr
    · exact ih d hd

/-- con-leche: ConLeche/Verify/IsModelRecords.lean:582 declsRun_recordsStored — **a mixed run
from the empty environment to its stream's environment stores its records**. -/
theorem mixedRun_recordsStored {pinsP : List NatOpPinSet} {JS : Solution} {ds : List Declaration}
    {E' : Env} (h : Compare.MixedRun pinsP JS ds Env.empty E') (henv : E' = streamEnv ds) :
    RecordsStored (· ∈ constantsOf ds) E' := by
  have hnd : NodupNames E' := by
    have := (h.chain (PushChain.refl Env.empty)).2.2.1 List.nodup_nil
    rwa [mkFEnv_env] at this
  have hf := mixedRun_facts h
  intro c hc
  obtain ⟨d, hd, hc⟩ := mem_constantsOf.1 hc
  obtain ⟨ci, hci, hst⟩ := records_stored (hf d hd).1 c hc
  have hmem : ci ∈ E'.consts := by
    rw [henv]
    exact (Driver.mem_streamEnv_consts ds _).2 (.inl ⟨d, hd, hci⟩)
  have hn : c.name = ci.name := by
    show c.toConstantVal.name = ci.toConstantVal.name
    rw [hst.1]
  exact ⟨ci, hn ▸ Driver.find?_of_nodup hnd hmem, hst, fun _ _ _ _ _ _ => (hf d hd).2 ci hci⟩

/-! ## The `.olean` input, stored -/

/-- con-leche: ConLeche/Verify/OleanInput.lean:615 inputStored_of — **a read's closure is stored
where records standing for the read's records are stored**, the read's cover of the closure
(`readOleans_run`'s, `Olean/Covers.lean`) a premise in place of upstream's `ModelIO` run. -/
theorem inputStored_of_covered {sp : ConLeche.Frontend.Olean.Roots} {fs : FS}
    {roots : Array ConLeche.Name} {rdecls : Array Declaration}
    (hcov : ∀ r, ConLeche.Frontend.Olean.closureConstants sp fs roots r →
      ConLeche.Frontend.Olean.CoveredBy rdecls r)
    {pre : ConLeche.Frontend.PreludeIx} {used : Declaration → Array ConLeche.Name}
    {g : Declaration → Declaration}
    {D : List Declaration} {env : Env} (hst : RecordsStored (· ∈ constantsOf D) env)
    (hmem : ∀ d ∈ (ConLeche.Frontend.prepareD pre rdecls used).decls, g d ∈ D)
    (hb : ∀ d ∈ D, basisNamesOk d = true) (hg : ∀ d, basisNamesOk (g d) = basisNamesOk d)
    (hcov' : ∀ d, ∀ c ∈ d.constants, ∃ c' ∈ (g d).constants, StoredAs c' c) :
    RecordsStored (ConLeche.Frontend.Olean.closureConstants sp fs roots) env := by
  refine hst.mono fun r hr => ?_
  obtain ⟨d, hd, hcv⟩ := hcov r hr
  have hd' := hmem _ (ConLeche.Frontend.mem_prepareD (used := used) (pre := pre) hd)
  obtain ⟨c', hc', hs⟩ := hcv (hg d ▸ hb _ hd')
  obtain ⟨c'', hc'', hs''⟩ := hcov' d c' hc'
  exact ⟨c'', mem_constantsOf.2 ⟨_, hd', hc''⟩, hs''.trans hs⟩

theorem fillDecl_constants (f : Expr → Expr) (d : Declaration) :
    (fillDecl f d).constants = d.constants := by
  cases d <;> rfl

theorem fillDecl_basisNamesOk (f : Expr → Expr) (d : Declaration) :
    basisNamesOk (fillDecl f d) = basisNamesOk d := by
  cases d <;> rfl

/-! ## The stages, in con-leche's words -/

/-- con-leche: ConLeche/Model/IsModelJson.lean:46 json_isModel — **the stream's records have a
model, at (B)**: the check phase accepting, the chunks parse (`parseChunks`) to records that
have a model in every set theory.  `stages_frame`, `Arena.pooledAccepts_bridge`, then
`model_exists`'s proof at the pure accept (`pureRun_recordsStored`). -/
theorem stages_isModel (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {chunks : List ByteArray} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {I : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE))
    (hF : Arena.PooledAccepts .verified ipins ds sE I sF) :
    ∃ rc, ConLeche.Frontend.parseChunks chunks = .ok rc ∧
      ∃ model, IsModel V model (· ∈ constantsOf rc.decls.toList) := by
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, rc, preC, hclR, hden⟩ :=
    stages_frame hA hB hC hD hE
  obtain ⟨F', hpure⟩ :=
    Arena.pooledAccepts_bridge hk hind hst hoff hpp hpps hipins hpd hden hF
  have hrun := PureRun.of_foldlM (pins := pins) _ hpure
  obtain ⟨m⟩ := ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) hpure
  exact ⟨rc, hclR, _, (isModel_of_envModelM m (pureRun_recordsStored hrun)).anti
    fun _ => constantsOf_preparePrelude⟩

/-- con-leche: ConLeche/Model/IsModelJson.lean:64 compare_json_isModel — **a compared run's
challenge has a model, at (B)**: the challenge's chunks parse to records that have a model in
every set theory.  `stagesC_model`'s proof, with the challenge's mixed run storing its records
(`mixedRun_recordsStored`) and `isModel_sideRecords` reading the side records as the
challenge's own. -/
theorem stagesC_isModel (V : Type w) [ConLeche.SetTheory V]
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
    ∃ rcC, ConLeche.Frontend.parseChunks chunksC = .ok rcC ∧
      ∃ model, IsModel V model (· ∈ constantsOf rcC.decls.toList) := by
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
  obtain ⟨m⟩ := Compare.mixed_model (pinsP := pins) V hpure hrun
  obtain ⟨model, hI⟩ : ∃ model, IsModel V model (· ∈ constantsOf
      ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord)) :=
    ⟨_, isModel_of_envModelM m (mixedRun_recordsStored hrun rfl)⟩
  have he : (ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map
      ConLeche.Cached.sideRecord =
      (sideRecords (some Env.empty) (ConLeche.Frontend.preparePrelude preC rcC.decls)).toList := by
    simp [sideRecords]
  rw [he] at hI
  exact ⟨rcC, hclC, model, ((isModel_sideRecords _ _ _).mp hI).anti
    fun _ => constantsOf_preparePrelude⟩

/-- con-leche: ConLeche/Model/IsModelOlean.lean:31 oleans_isModel — **the closure's constants
have a model, at (B), on `--olean`**: the check phase accepting, every constant of every module of
the closure of the roots, read by the specification (`closureConstants`), is in a model.
`stagesO_frame` (the reader's cover of the closure), `Arena.pooledOleanAccepts_bridge`, then
`oleans_isModel`'s proof at the pure accept (`inputStored_of_covered`). -/
theorem stagesO_isModel (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {F : FS} {sp : ConLeche.Frontend.Olean.SearchPath} {names : List ConLeche.Name}
    {pins : List NatOpPinSet} {maxNatSize : Nat} {roots : List NIdx}
    {sA sB sB' sC sD sE sF : AState} {pre : PreludeIx}
    {rd : ConRon.Arena.Frontend.Olean.OleanRead} {prep : Prepared} {ipins : List INatOpPinSet}
    {I : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hR : names.mapM ConRon.Arena.internName sB = .ok (roots, sB'))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) sp roots.toArray none false false sB' =
      .ok (.ok rd, sC))
    (hD : prepareD pre rd.decls rd.usedOf sC = .ok (prep, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE))
    (hF : Arena.PooledOleanAccepts (Olean.modelFs F) rd.pins sp rd.values .verified ipins
      prep.decls sE I sF) :
    ∃ model, IsModel V model (ConLeche.Frontend.Olean.closureConstants sp F names.toArray) := by
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, hwfC, hoffC, hxC, hnu, valuesP, dsR, preC, usedC,
    hvals, hden, -, hcov⟩ := stagesO_frame hA hB hR hC hD hE
  obtain ⟨Fu, hpure⟩ := Arena.pooledOleanAccepts_bridge hk hind hst hoff hpp hpps hipins hpd
    hden hwfC hoffC hxC hvals hnu rfl hF
  have hrun := PureRun.of_foldlM (pins := pins) _ hpure
  obtain ⟨m⟩ := ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) hpure
  exact ⟨_, isModel_of_envModelM m (inputStored_of_covered hcov (pre := preC) (used := usedC)
    (g := fillDecl (fillRef (valueOf sp F valuesP))) (pureRun_recordsStored hrun)
    (fun d hd => List.mem_map_of_mem (Array.mem_toList_iff.mpr hd)) hrun.basisNamesOk
    (fillDecl_basisNamesOk _) (fun d c hc => ⟨c, (fillDecl_constants _ d).symm ▸ hc,
      StoredAs.refl c⟩))⟩

/-- con-leche: ConLeche/Model/IsModelCompare.lean:31 compare_isModel — **a compared `--olean`
run's challenge closure has a model, at (B), on every snapshot that agrees with the run's under
the challenge's lookup**: `stagesOC_core`'s proof, with the challenge's cover of its closure
(`stagesOC_frame`), its mixed run storing its records, and `chalChecked_inputStored`'s
reading of a hole and a side record by its statement; then `closureConstants_local`. -/
theorem stagesOC_isModel (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {F : FS} {crp : ConLeche.Frontend.Olean.SearchPath} {sr : ConLeche.Frontend.Olean.Roots}
    (hsr : sr.bare = sr)
    {c s : ConLeche.Name} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {sA sB sB₁ sB₂ sC sD sD' sC₂ sD₂ sE sF sH sI : AState} {pre : PreludeIx} {ch sh : NIdx}
    {rdC rdS : ConRon.Arena.Frontend.Olean.OleanRead} {prepC prepS : Prepared}
    {holed recsC : List IDeclaration} {ipins : List INatOpPinSet} {IS IC : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hRC : ConRon.Arena.internName c sB = .ok (ch, sB₁))
    (hRS : ConRon.Arena.internName s sB₁ = .ok (sh, sB₂))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) crp #[ch] none true true sB₂ =
      .ok (.ok rdC, sC))
    (hD : prepareD pre rdC.decls rdC.usedOf sC = .ok (prepC, sD))
    (hhole : holeRecordsGo rdC.usedOf [] prepC.decls.toList sD = .ok (holed, sD'))
    (hCS : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) sr #[sh] none true false sD' =
      .ok (.ok rdS, sC₂))
    (hDS : prepareD pre rdS.decls rdS.usedOf sC₂ = .ok (prepS, sD₂))
    (hE : internAllPins pins maxNatSize sD₂ = .ok (ipins, sE))
    (hFS : Arena.PooledOleanAccepts (Olean.modelFs F) rdS.pins sr rdS.values .verified ipins
      prepS.decls sE IS sF)
    (hside : sideRecordsGo [] holed sF = .ok (recsC, sH))
    (hFC : Arena.PooledOleanAcceptsJ (Olean.modelFs F) rdC.pins crp rdC.values .verified ipins
      (some (solutionOf IS recsC)) recsC.toArray sH IC sI) :
    ∀ fs', FS.AgreeUnder crp F fs' →
      ∃ model, IsModel V model (ConLeche.Frontend.Olean.closureConstants crp fs' #[c]) := by
  have hcr : (crp : ConLeche.Frontend.Olean.Roots).bare = crp := rfl
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpdS, hpdH, hwfC, hoffC, hxC, hnu, hwfC₂, hoffC₂, hxC₂,
    hnuS, valuesC, valuesS, dsR, dsRS, preC, usedC, usedS, hvals, hvalsS, hdenH, hdenS, -,
    hcov⟩ := stagesOC_frame hcr hsr hA hB hRC hRS hC hD hhole hCS hDS hE
  -- the solution: the pure fold accepts its filled stream
  obtain ⟨Fu, hpure⟩ := Arena.pooledOleanAccepts_bridge hk hind hst hoff hpp hpps hipins hpdS
    hdenS hwfC₂ hoffC₂ hxC₂ hvalsS hnuS hsr hFS
  obtain ⟨partsS, hidxS, -⟩ := hFS
  obtain ⟨hstF, hxF, hpF, hoffF, hIS, hpIS⟩ :=
    buildIndex_run constsSpec tablesSpec hst hpp hoff hpdS hdenS hidxS
  -- the challenge's side records
  obtain ⟨rfl, hdenR, hpersR⟩ := sideRecordsGo_run hstF.state hstF.pins holed [] recsC _ [] rfl
    (denoteDecls_ext hxF _ _ hdenH) hside
  simp only [List.nil_append] at hdenR
  have hpR : ∀ x ∈ recsC, PersDecl x := hpersR (fun _ h => nomatch h) hpdH
  -- the challenge's check phase
  let dsP := (((ConLeche.Frontend.prepareD preC dsR usedC).decls.toList.map
    (ConLeche.Driver.holeRecord usedC)).map ConLeche.Cached.sideRecord)
  let fS := fillStream sr F valuesS (ConLeche.Frontend.prepareD preC dsRS usedS).decls.toList
  have hIS' : IndexDenotes sF.store IS (ConLeche.Cached.buildIndex fS.toArray) := by
    simp only [fS, fillStream, ← List.map_toArray, ConLeche.Cached.buildIndex_fill]; exact hIS
  have hmates : MatesRel sF.store (solutionOf IS recsC).mates
      (ConLeche.Cached.recordMates (fillStream crp F valuesC dsP).toArray) := by
    rw [fillStream, recordMates_fillDecl]
    exact solutionOf_mates hstF.state.wf hdenR hpR
  have hrun := Arena.pooledOleanAcceptsJ_bridge (pinsP := pins) (dsS := fS) (dsP := dsP)
    hk hind hstF hoffF (hpp.mono hpF) hpps (PinsDenote.mono hxF ipins pins hipins)
    (by simpa using hpR) (by simp only; exact hdenR) hwfC hoffC
    (hxC.trans (PExt.of_ext hxF)) hvals
    hnu hcr hIS' hpIS (pure_nodup hpure) hmates hFC
  obtain ⟨m⟩ := Compare.mixed_model (pinsP := pins) V hpure hrun
  have hstored : RecordsStored (ConLeche.Frontend.Olean.closureConstants crp F #[c])
      (ConLeche.streamEnv (fillStream crp F valuesC dsP)) :=
    inputStored_of_covered hcov (pre := preC) (used := usedC)
      (g := fun d => fillDecl (fillRef (valueOf crp F valuesC))
        (sideRecord (ConLeche.Driver.holeRecord usedC d)))
      (mixedRun_recordsStored hrun rfl)
      (fun d hd => List.mem_map_of_mem (List.mem_map_of_mem (List.mem_map_of_mem
        (Array.mem_toList_iff.mpr hd))))
      (mixedRun_basisNamesOk hrun)
      (fun d => by
        rw [fillDecl_basisNamesOk, basisNamesOk_sideRecord, basisNamesOk_holeRecord])
      (fun d => StoredAs.covers_trans (covers_stmt (holeRecord_constants usedC d))
        (by rw [fillDecl_constants]; exact covers_stmt (constants_sideRecord _)))
  intro fs' hag
  rw [← closureConstants_local hag]
  exact ⟨_, isModel_of_envModelM m hstored⟩

end ConRon.Bridge
