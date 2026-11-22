/-
# `ConRon.Bridge.Compare.StagesOleans` — THEOREM 1 at the compared `--olean` run's pipeline

The binary's `--olean --compare -- C S` (`crates/con-ron/src/compare.rs` `compare_oleans`, the
twin's `Arena/Main.lean` `compareOleanPipeline`), without `--constant`, runs on one state

    internReservedPins → builtinPreludeE → internName C → internName S
      → readOleans at the challenge's lookup `cr` (lenient, homes) → prepareD → holeRecordsGo
      → readOleans at the solution's lookup `sr` (lenient) → prepareD → internAllPins
      → the solution's `--olean` check phase (no solution) → sideRecordsGo
      → the challenge's `--olean` check phase at `solutionOf`

`stagesOC_model`: the challenge's checked records, each reference filled with the snapshot's
value, have an environment with a model; `stagesOC_no_False`: no theorem of the challenge's
closure (read through `cr`, by the specification `InClosure`/`ViewOf`) has type `False`.
Nothing is concluded about the solution.  `Bridge/Stages.lean`'s `stagesO_frame` with the second
read, the holes (`Compare/Holes.lean`) and the two check phases
(`Arena.pooledOleanAccepts_bridge`, `Compare/PooledOleans.lean`'s
`Arena.pooledOleanAcceptsJ_bridge`), and `Compare/Model.lean`'s `mixed_model`.
-/
module

public import ConRon.Bridge.Compare.PooledOleans
public import ConRon.Bridge.Compare.Holes
public import ConRon.Bridge.Compare.Stages
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Install
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Cached.Fill
import ConLeche.Verify.Cached.IndWalksC

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge.Frontend

universe w

/-- con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates — filling theorem values changes
no record mate (`fillDecl` keeps every inductive block). -/
theorem recordMates_fillDecl (f : Expr → Expr) (ds : List Declaration) :
    ConLeche.Cached.recordMates (ds.map (ConLeche.Cached.fillDecl f)).toArray =
      ConLeche.Cached.recordMates ds.toArray := by
  simp only [ConLeche.Cached.recordMates, List.foldl_toArray', List.foldl_map]
  congr 1
  funext m d
  cases d <;> rfl

/-- con-leche: ConLeche/Driver/Compare.lean:132-138 chalRecords — **a theorem of type `False`
stays one through the challenge's records**: its hole (the axiom of its statement, or itself),
its side record (a reference uses no `sorryAx`) and its fill all install a constant of its
statement's type. -/
theorem false_const_of_thm (usedC : Declaration → Array ConLeche.Name) (f : Expr → Expr)
    {cv : ConstantVal} (code : Nat) (hty : cv.type = .const falseName []) :
    ∃ c ∈ ConLeche.declConstants (ConLeche.Cached.fillDecl f (ConLeche.Cached.sideRecord
      (ConLeche.Driver.holeRecord usedC (.thmDecl cv (.bvar code))))),
      c.toConstantVal.type = .const falseName [] := by
  simp only [ConLeche.Driver.holeRecord]
  split
  · next hb =>
    have hbi : ConLeche.Cached.builtinAxiomName cv.name = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb; exact hb.1
    have hq : cv.name ≠ quotSoundName := fun h => by
      simp [ConLeche.Cached.builtinAxiomName, h] at hbi
    have hs : cv.name ≠ sorryAxName := fun h => by
      simp [ConLeche.Cached.builtinAxiomName, h] at hbi
    exact ⟨.axiomInfo cv, by
      simp [ConLeche.Cached.sideRecord, ConLeche.Cached.fillDecl, ConLeche.declConstants, hq, hs],
      hty⟩
  · have hm : ConLeche.Expr.mentionsAnyConstC [ConLeche.sorryAxName] (.bvar code) = false := by
      rw [ConLeche.Expr.mentionsAnyConstC_spec]; rfl
    exact ⟨.thmInfo cv, by
      simp [ConLeche.Cached.sideRecord, hm, ConLeche.Cached.fillDecl, ConLeche.declConstants],
      hty⟩

/-- con-leche: ConLeche/Driver/Compare.lean:141-208 compareG — **the compared `--olean` run,
read**: everything up to the two check phases, at the twin, with what they need. -/
theorem stagesOC_frame {F : FS} {cr sr : ConLeche.Frontend.Olean.Roots}
    (hcr : cr.bare = cr) (hsr : sr.bare = sr)
    {c s : ConLeche.Name} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {sA sB sB₁ sB₂ sC sD sD' sC₂ sD₂ sE : AState} {pre : PreludeIx} {ch sh : NIdx}
    {rdC rdS : ConRon.Arena.Frontend.Olean.OleanRead} {prepC prepS : Prepared}
    {holed : List IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hRC : ConRon.Arena.internName c sB = .ok (ch, sB₁))
    (hRS : ConRon.Arena.internName s sB₁ = .ok (sh, sB₂))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) cr #[ch] none true true sB₂ =
      .ok (.ok rdC, sC))
    (hD : prepareD pre rdC.decls rdC.usedOf sC = .ok (prepC, sD))
    (hhole : holeRecordsGo rdC.usedOf [] prepC.decls.toList sD = .ok (holed, sD'))
    (hCS : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) sr #[sh] none true false sD' =
      .ok (.ok rdS, sC₂))
    (hDS : prepareD pre rdS.decls rdS.usedOf sC₂ = .ok (prepS, sD₂))
    (hE : internAllPins pins maxNatSize sD₂ = .ok (ipins, sE)) :
    sE.store.scratchOn = false ∧ DriverOK sE ∧ PersPins sE ∧
      PinsDenote sE.store ipins pins ∧ PersPinSets ipins ∧
      (∀ x ∈ prepS.decls.toList, PersDecl x) ∧ (∀ x ∈ holed, PersDecl x) ∧
      StoreWF sC.store ∧ sC.store.scratchOn = false ∧ PExt sC.store sE.store ∧
      Olean.NullsRel sC.store rdC.pins ∧
      StoreWF sC₂.store ∧ sC₂.store.scratchOn = false ∧ PExt sC₂.store sE.store ∧
      Olean.NullsRel sC₂.store rdS.pins ∧
      ∃ valuesC valuesS dsR dsRS preC usedC usedS,
        Olean.ValuesRel cr F sC.store rdC.values valuesC ∧
        Olean.ValuesRel sr F sC₂.store rdS.values valuesS ∧
        denoteDecls sE.store holed = some
          ((ConLeche.Frontend.prepareD preC dsR usedC).decls.toList.map
            (ConLeche.Driver.holeRecord usedC)) ∧
        denoteDecls sE.store prepS.decls.toList =
          some (ConLeche.Frontend.prepareD preC dsRS usedS).decls.toList ∧
        (∀ {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
          {cc : ConLeche.Frontend.Olean.CEntryF ConLeche.Name Expr} {v : Expr}
          {all : List ConLeche.Name}, ConLeche.Frontend.Olean.InClosure cr F #[c] m →
          ConLeche.Frontend.Olean.ViewOf cr F m d → cc ∈ d.constants → cc.kind = .thm v all →
          ∃ code, Declaration.thmDecl ⟨cc.name, cc.levelParams, cc.type⟩ (.bvar code) ∈ dsR) ∧
        (∀ r, ConLeche.Frontend.Olean.closureConstants cr F #[c] r →
          ConLeche.Frontend.Olean.CoveredBy dsR r) := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ := internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ := builtinPreludeE_run hokA hoffA hpinsA hB
  have hoffB : sB.store.scratchOn = false := by rw [hstep1.scratch]; exact hoffA
  -- the two names
  obtain ⟨hn1, hdc⟩ := internName_sstep hstep1.ok hRC
  have hn1' := (hn1.toIStep hoffB).toParse hoffB
  have hoffB₁ : sB₁.store.scratchOn = false := by rw [hn1'.scratch]; exact hoffB
  obtain ⟨hn2, hds⟩ := internName_sstep hn1'.ok hRS
  have hn2' := (hn2.toIStep hoffB₁).toParse hoffB₁
  have hoffB₂ : sB₂.store.scratchOn = false := by rw [hn2'.scratch]; exact hoffB₁
  have hdc₂ := denoteN_ext hdc hn2'.ext
  have h12 := (hstep1.trans hn1').trans hn2'
  -- the challenge's read, preparation and holes
  obtain ⟨hstC, hpersR, hpk, ⟨usedC, hU⟩, valuesC, dsR, hvals, hdenR, hthm, hcovR, -⟩ :=
    Olean.readOleans_run (roots := #[ch]) (rootsC := #[c]) hcr hn2'.ok hoffB₂
      (hpinsA.mono h12.ext h12.pins) (by simpa using (show ListRel (Olean.NR sB₂.store) [ch] [c] from .cons hdc₂ .nil)) hC
  have h13 := h12.trans hstC
  have hoffC : sC.store.scratchOn = false := by rw [h13.scratch]; exact hoffA
  obtain ⟨hstD, hpersDC, hclPrepC⟩ :=
    prepareD_run (preC := preC) hstC.ok hoffC (hpinsA.mono h13.ext h13.pins)
      (denoteDeclArray_ext (hn1'.ext.trans (hn2'.ext.trans hstC.ext)) hrelPre) hpersPre
      hdenR hpersR hU hD
  have h14 := h13.trans hstD
  have hoffD : sD.store.scratchOn = false := by rw [h14.scratch]; exact hoffA
  obtain ⟨hstH, hdenH, hpersH⟩ := holeRecordsGo_run hU prepC.decls.toList [] holed _ []
    hstD.ext hstD.ok hoffD (hpinsA.mono h14.ext h14.pins) rfl
    (denoteDeclArray_iff.mp hclPrepC) hhole
  have h15 := h14.trans hstH
  have hoffD' : sD'.store.scratchOn = false := by rw [h15.scratch]; exact hoffA
  -- the solution's read and preparation
  obtain ⟨hstC₂, hpersRS, hpkS, ⟨usedS, hUS⟩, valuesS, dsRS, hvalsS, hdenRS, -, -⟩ :=
    Olean.readOleans_run (roots := #[sh]) (rootsC := #[s]) hsr hstH.ok hoffD'
      (hpinsA.mono h15.ext h15.pins)
      (by simpa using (show ListRel (Olean.NR sD'.store) [sh] [s] from
        .cons (denoteN_ext hds (hstC.ext.trans (hstD.ext.trans hstH.ext))) .nil)) hCS
  have h16 := h15.trans hstC₂
  have hoffC₂ : sC₂.store.scratchOn = false := by rw [h16.scratch]; exact hoffA
  obtain ⟨hstD₂, hpersDS, hclPrepS⟩ :=
    prepareD_run (preC := preC) hstC₂.ok hoffC₂ (hpinsA.mono h16.ext h16.pins)
      (denoteDeclArray_ext
        ((hn1'.ext.trans hn2'.ext).trans ((hstC.ext.trans hstD.ext).trans
          (hstH.ext.trans hstC₂.ext))) hrelPre) hpersPre hdenRS hpersRS hUS hDS
  have h17 := h16.trans hstD₂
  have hoffD₂ : sD₂.store.scratchOn = false := by rw [h17.scratch]; exact hoffA
  -- the pins
  obtain ⟨hokP, hxP, hpinsP, hppP, hipins, hpps, hoffP, hcachesP, -⟩ :=
    internAllPins_run hstD₂.ok (hpinsA.mono h17.ext h17.pins) (hppA.mono h17.pins) hoffD₂ hE
  have hxCE : Ext sC.store sE.store :=
    ((hstD.ext.trans hstH.ext).trans (hstC₂.ext.trans hstD₂.ext)).trans hxP
  have hxC₂E : Ext sC₂.store sE.store := hstD₂.ext.trans hxP
  refine ⟨hoffP, DriverOK.start hokP hpinsP
      (((CacheOK.of_empty (s := sA) (by rw [hcachesA]; exact hc0)).monoF
            h17.ext h17.cframe).mono hxP hcachesP),
    hppP, hipins, hpps, fun x hx => hpersDS x (by simpa using hx),
    hpersH (fun _ h => nomatch h) (fun x hx => hpersDC x (by simpa using hx)),
    hstC.ok.wf, hoffC, PExt.of_ext hxCE, hpk.nulls,
    hstC₂.ok.wf, hoffC₂, PExt.of_ext hxC₂E, hpkS.nulls,
    valuesC, valuesS, dsR, dsRS, preC, usedC, usedS, hvals, hvalsS,
    denoteDecls_ext ((hstC₂.ext.trans hstD₂.ext).trans hxP) _ _ (by simpa using hdenH),
    denoteDeclArray_iff.mp (denoteDeclArray_ext hxP hclPrepS), hthm, hcovR⟩

/-- con-leche: ConLeche/MainTheorem.lean:88 main_compare_model — **the compared `--olean` run's
challenge, at the pipeline**: what the reader puts in its records, and: the challenge's checked records, each reference
filled with a value, denote a stream whose environment has a model.  The solution's check
phase is a premise; nothing is concluded about the solution. -/
theorem stagesOC_core (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {F : FS} {cr sr : ConLeche.Frontend.Olean.Roots}
    (hcr : cr.bare = cr) (hsr : sr.bare = sr)
    {c s : ConLeche.Name} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {sA sB sB₁ sB₂ sC sD sD' sC₂ sD₂ sE sF sH sI : AState} {pre : PreludeIx} {ch sh : NIdx}
    {rdC rdS : ConRon.Arena.Frontend.Olean.OleanRead} {prepC prepS : Prepared}
    {holed recsC : List IDeclaration} {ipins : List INatOpPinSet} {IS IC : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hRC : ConRon.Arena.internName c sB = .ok (ch, sB₁))
    (hRS : ConRon.Arena.internName s sB₁ = .ok (sh, sB₂))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) cr #[ch] none true true sB₂ =
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
    (hFC : Arena.PooledOleanAcceptsJ (Olean.modelFs F) rdC.pins cr rdC.values .verified ipins
      (some (solutionOf IS recsC)) recsC.toArray sH IC sI) :
    StoreWF sH.store ∧ ∃ (preC : ConLeche.Frontend.PreludeIx) (dsR : Array Declaration)
      (usedC : Declaration → Array ConLeche.Name) (val : Nat → Expr),
      (∀ {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
        {cc : ConLeche.Frontend.Olean.CEntryF ConLeche.Name Expr} {v : Expr}
        {all : List ConLeche.Name}, ConLeche.Frontend.Olean.InClosure cr F #[c] m →
        ConLeche.Frontend.Olean.ViewOf cr F m d → cc ∈ d.constants → cc.kind = .thm v all →
        ∃ code, Declaration.thmDecl ⟨cc.name, cc.levelParams, cc.type⟩ (.bvar code) ∈ dsR) ∧
      denoteDecls sH.store recsC = some (((ConLeche.Frontend.prepareD preC dsR usedC).decls.toList.map
        (ConLeche.Driver.holeRecord usedC)).map ConLeche.Cached.sideRecord) ∧
      Nonempty (ConLeche.Model.EnvModelM V
        (ConLeche.streamEnv ((((ConLeche.Frontend.prepareD preC dsR usedC).decls.toList.map
          (ConLeche.Driver.holeRecord usedC)).map ConLeche.Cached.sideRecord).map
          (ConLeche.Cached.fillDecl (fillRef val))))) := by
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpdS, hpdH, hwfC, hoffC, hxC, hnu, hwfC₂, hoffC₂, hxC₂,
    hnuS, valuesC, valuesS, dsR, dsRS, preC, usedC, usedS, hvals, hvalsS, hdenH, hdenS, hthm, -⟩ :=
    stagesOC_frame hcr hsr hA hB hRC hRS hC hD hhole hCS hDS hE
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
      (ConLeche.Cached.recordMates (fillStream cr F valuesC dsP).toArray) := by
    rw [fillStream, recordMates_fillDecl]
    exact solutionOf_mates hstF.state.wf hdenR hpR
  have hrun := Arena.pooledOleanAcceptsJ_bridge (pinsP := pins) (dsS := fS) (dsP := dsP)
    hk hind hstF hoffF (hpp.mono hpF) hpps (PinsDenote.mono hxF ipins pins hipins)
    (by simpa using hpR) (by simp only; exact hdenR) hwfC hoffC
    (hxC.trans (PExt.of_ext hxF)) hvals
    hnu hcr hIS' hpIS (pure_nodup hpure) hmates hFC
  exact ⟨hstF.state.wf, preC, dsR, usedC, valueOf cr F valuesC, hthm, hdenR,
    Compare.mixed_model (pinsP := pins) V hpure hrun⟩

/-- con-leche: ConLeche/MainTheorem.lean:88 main_compare_model — **the compared `--olean` run's
challenge has a model, at the pipeline**: the challenge's checked records, each reference
filled with a value, denote a stream whose environment has a model.  The solution's check
phase is a premise; nothing is concluded about the solution. -/
theorem stagesOC_model (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {F : FS} {cr sr : ConLeche.Frontend.Olean.Roots}
    (hcr : cr.bare = cr) (hsr : sr.bare = sr)
    {c s : ConLeche.Name} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {sA sB sB₁ sB₂ sC sD sD' sC₂ sD₂ sE sF sH sI : AState} {pre : PreludeIx} {ch sh : NIdx}
    {rdC rdS : ConRon.Arena.Frontend.Olean.OleanRead} {prepC prepS : Prepared}
    {holed recsC : List IDeclaration} {ipins : List INatOpPinSet} {IS IC : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hRC : ConRon.Arena.internName c sB = .ok (ch, sB₁))
    (hRS : ConRon.Arena.internName s sB₁ = .ok (sh, sB₂))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) cr #[ch] none true true sB₂ =
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
    (hFC : Arena.PooledOleanAcceptsJ (Olean.modelFs F) rdC.pins cr rdC.values .verified ipins
      (some (solutionOf IS recsC)) recsC.toArray sH IC sI) :
    StoreWF sH.store ∧ ∃ (dsP : List Declaration) (val : Nat → Expr),
      denoteDecls sH.store recsC = some dsP ∧
      Nonempty (ConLeche.Model.EnvModelM V
        (ConLeche.streamEnv (dsP.map (ConLeche.Cached.fillDecl (fillRef val))))) := by
  obtain ⟨hwf, preC, dsR, usedC, val, -, hden, hmod⟩ :=
    stagesOC_core V hk hind hcr hsr hA hB hRC hRS hC hD hhole hCS hDS hE hFS hside hFC
  exact ⟨hwf, _, val, hden, hmod⟩

/-- con-leche: ConLeche/MainTheorem.lean:88 main_compare_model — **a compared `--olean` run
accepting a challenge whose closure holds a theorem of type `False` is impossible**: the reader
puts the theorem in the challenge's records with a reference (`readOleans_run`), its hole, side
record and fill install a constant of its type (`false_const_of_thm`), and the challenge's
environment has a model. -/
theorem stagesOC_no_False (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {F : FS} {cr sr : ConLeche.Frontend.Olean.Roots}
    (hcr : cr.bare = cr) (hsr : sr.bare = sr)
    {c s : ConLeche.Name}
    {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
    {cc : ConLeche.Frontend.Olean.CEntryF ConLeche.Name Expr} {v : Expr}
    {all : List ConLeche.Name}
    (hcl : ConLeche.Frontend.Olean.InClosure cr F #[c] m)
    (hv : ConLeche.Frontend.Olean.ViewOf cr F m d) (hmem : cc ∈ d.constants)
    (hkind : cc.kind = .thm v all) (hty : cc.type = .const ConLeche.falseName [])
    {pins : List NatOpPinSet} {maxNatSize : Nat}
    {sA sB sB₁ sB₂ sC sD sD' sC₂ sD₂ sE sF sH sI : AState} {pre : PreludeIx} {ch sh : NIdx}
    {rdC rdS : ConRon.Arena.Frontend.Olean.OleanRead} {prepC prepS : Prepared}
    {holed recsC : List IDeclaration} {ipins : List INatOpPinSet} {IS IC : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hRC : ConRon.Arena.internName c sB = .ok (ch, sB₁))
    (hRS : ConRon.Arena.internName s sB₁ = .ok (sh, sB₂))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) cr #[ch] none true true sB₂ =
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
    (hFC : Arena.PooledOleanAcceptsJ (Olean.modelFs F) rdC.pins cr rdC.values .verified ipins
      (some (solutionOf IS recsC)) recsC.toArray sH IC sI) :
    False := by
  obtain ⟨-, preC, dsR, usedC, val, hthm, -, ⟨mp⟩⟩ :=
    stagesOC_core V hk hind hcr hsr hA hB hRC hRS hC hD hhole hCS hDS hE hFS hside hFC
  obtain ⟨code, hd⟩ := hthm hcl hv hmem hkind
  have hmem' : Declaration.thmDecl ⟨cc.name, cc.levelParams, cc.type⟩ (.bvar code) ∈
      (ConLeche.Frontend.prepareD preC dsR usedC).decls.toList :=
    Array.mem_toList_iff.mpr (ConLeche.Frontend.mem_prepareD (pre := preC) (used := usedC) hd)
  obtain ⟨k, hk', hkty⟩ := false_const_of_thm usedC (fillRef val) (cv := ⟨cc.name, cc.levelParams,
    cc.type⟩) code hty
  have hcs : k ∈ (ConLeche.streamEnv (((((ConLeche.Frontend.prepareD preC dsR usedC).decls.toList.map
      (ConLeche.Driver.holeRecord usedC)).map ConLeche.Cached.sideRecord)).map
        (ConLeche.Cached.fillDecl (fillRef val)))).consts :=
    (ConLeche.Driver.mem_streamEnv_consts _ _).2
      (.inl ⟨_, List.mem_map_of_mem (List.mem_map_of_mem (List.mem_map_of_mem hmem')), hk'⟩)
  exact ConLeche.Model.no_constant_of_False mp k hcs hkty

end ConRon.Bridge
