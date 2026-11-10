/-
# `ConRon.Bridge.Stages` — THEOREM 1 at the twin's pipeline, stage by stage

The binary runs, on one state from the driver's start, the stages

    internReservedPins → builtinPreludeE → parseChunks → preparePrelude → internAllPins
      → the check phase (`Arena.PooledAccepts`: the index, then the pool's jobs)

and on `--olean` the parse replaced by the roots' names interned and `readOleans`, the
preparation by `prepareD` at the reader's `usedOf`, the check phase by
`Arena.PooledOleanAccepts`.  `ConRon/Capstone.lean` walks the Rust runs into these twin runs
(Theorem 2) and takes the conclusions below for the headlines:

| theorem | conclusion |
|---|---|
| `stages_frame` | the check phase's start: `DriverOK`, the pins and the stream denoting |
| `stages_model` | the stream's environment has a model, and the end state's store is well formed |
| `stages_no_False` | a file declaring a `False` theorem is not accepted |
| `stagesO_model`, `stagesO_no_False` | the same on `--olean`, at the filled stream |

Each is the stage lemmas (`Bridge/Checker/Pins.lean`, `Bridge/Frontend/**`) composed with
`Bridge/Checker/Pool.lean`'s `Arena.pooledAccepts_bridge` / `Arena.pooledOleanAccepts_bridge`
and con-leche's `checkDeclsPure_sound_of` or `no_proof_of_False_pure`.
-/
module

public import ConRon.Bridge.Checker.Pool
public import ConRon.Bridge.Checker.Pins
public import ConRon.Bridge.Frontend.Prepare
public import ConRon.Bridge.Frontend.Chunks
public import ConRon.Bridge.Frontend.Capstone
public import ConRon.Bridge.Frontend.Olean.Records
public import ConLeche.Verify.Frontend.FileFalse
public import ConLeche.Model.Fold
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Install
public import ConLeche.Verify.Frontend.Prepare

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge.Frontend

universe w

/-- con-leche: none — **the check phase's start invariant** at a state with nothing installed:
the empty environment, and the empty index over it, answer nothing. -/
theorem DriverOK.start {s : AState} (hok : StateOK s) (hpins : PinsOK s)
    (hc : CacheOK false Env.empty s) : DriverOK s :=
  { state := hok
    caches := hc
    pins := hpins
    ienv :=
      { hit := fun n ci h => by
          simp [mkIFEnv, IEnv.empty, IFEnv.find?, IFEnv.lookup, mkIFEnvGo, IFBase.find?] at h
        cover := fun nm c h => by simp [Env.empty, Env.find?] at h
        tblHit := fun n t h => by
          simp [mkIFEnv, IEnv.empty, IFEnv.findTable?, IFEnv.find?, IFEnv.lookup, mkIFEnvGo,
            IFBase.find?] at h
        tblCover := fun nm pt h => by simp [Env.empty, Env.findTable?, Env.find?] at h } }

/-! ## The stream -/

/-- con-leche: ConLeche/Driver/CheckPool.lean:236-269 checkPool — **the stages' frame, up to the
check phase**: after the first five stages from the driver's start state, the scratch tier is
closed, the check phase's start invariant holds, and the pins and the prepared stream denote. -/
theorem stages_frame {chunks : List ByteArray} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {sA sB sC sD sE : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE)) :
    sE.store.scratchOn = false ∧ DriverOK sE ∧ PersPins sE ∧
      PinsDenote sE.store ipins pins ∧ PersPinSets ipins ∧
      (∀ x ∈ ds.toList, PersDecl x) ∧
      ∃ rc preC, ConLeche.Frontend.parseChunks chunks = .ok rc ∧
        denoteDecls sE.store ds.toList =
          some (ConLeche.Frontend.preparePrelude preC rc.decls).toList := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ :=
    builtinPreludeE_run hokA hoffA hpinsA hB
  obtain ⟨hstep2, hpersR, rc, hclR, hrelR⟩ :=
    parseChunks_run hstep1.ok
      (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins) hC
  obtain ⟨hstep3, hpersDs, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      hrelR.decls hpersR hD
  have hoff3 : sD.store.scratchOn = false := by
    rw [hstep3.scratch, hstep2.scratch, hstep1.scratch]; exact hoffA
  obtain ⟨hokP, hxP, hpinsP, hppP, hipins, hpps, hoffP, hcachesP, -⟩ :=
    internAllPins_run hstep3.ok
      (hpinsA.mono ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
        (by rw [hstep3.pins, hstep2.pins, hstep1.pins]))
      (hppA.mono (by rw [hstep3.pins, hstep2.pins, hstep1.pins])) hoff3 hE
  refine ⟨hoffP, DriverOK.start hokP hpinsP
      (((CacheOK.of_empty (s := sA) (by rw [hcachesA]; exact hc0)).monoF
            ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
            ((hstep1.cframe.trans hstep2.cframe).trans hstep3.cframe)).mono
        hxP hcachesP),
    hppP, hipins, hpps, fun x hx => hpersDs x (by simpa using hx), rc, preC, hclR,
    denoteDeclArray_iff.mp (denoteDeclArray_ext hxP hclPrep)⟩

/-- con-leche: ConLeche/Model/Fold.lean:306 checkDeclsPure_sound_of — **the model at (B), at the
pipeline**: the check phase accepting, the records denote at its end state, whose store is well
formed, and the environment the stream denotes (`streamEnv`) has a model.
`stages_frame`, then `Arena.pooledAccepts_bridge`, then con-leche. -/
theorem stages_model (V : Type w) [ConLeche.SetTheory V]
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
    StoreWF sF.store ∧ ∃ dsP, denoteDecls sF.store ds.toList = some dsP ∧
      Nonempty (ConLeche.Model.EnvModelM V (ConLeche.Cached.streamEnv dsP)) := by
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, rc, preC, hclR, hden⟩ :=
    stages_frame hA hB hC hD hE
  obtain ⟨F', hpure⟩ :=
    Arena.pooledAccepts_bridge V hk hind hst hoff hpp hpps hipins hpd hden hF
  obtain ⟨parts, hidx, -⟩ := hF
  obtain ⟨hst', hx, -⟩ := buildIndex_run constsSpec tablesSpec hst hoff hpd hden hidx
  exact ⟨hst'.state.wf, _, denoteDecls_ext hx _ _ hden,
    ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) hpure⟩

/-- con-leche: ConLeche/MainTheorem.lean:112 no_False_declaration — **a check phase accepting a
file that declares a `False` theorem is impossible, at (B)**: the parse puts the theorem in the
stream (`parseChunks_jsonWithTheoremFalse`, `mem_preparePrelude`), `Arena.pooledAccepts_bridge`
makes the stream an accept of the pure fold, and `no_False_theorem_accepted_pure` refutes it. -/
theorem stages_no_False (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {chunks : List ByteArray} {pins : List NatOpPinSet} {maxNatSize : Nat}
    (hfalse : ConLeche.jsonWithTheoremFalse chunks)
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {I : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE))
    (hF : Arena.PooledAccepts .verified ipins ds sE I sF) :
    False := by
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, rc, preC, hclR, hden⟩ :=
    stages_frame hA hB hC hD hE
  obtain ⟨F', hpure⟩ :=
    Arena.pooledAccepts_bridge V hk hind hst hoff hpp hpps hipins hpd hden hF
  obtain ⟨cv, vl, hty, hmem⟩ := ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hclR
  exact no_False_theorem_accepted_pure V
    (by simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem) hty hpure

/-! ## `--olean` -/

/-- con-leche: none — the driver's names interned: the handles denote them. -/
theorem internNames_run {s : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false) :
    ∀ (names : List ConLeche.Name) {hs : List NIdx} {s' : AState},
      names.mapM ConRon.Arena.internName s = .ok (hs, s') →
      ParseStep s s' ∧ ListRel (Olean.NR s'.store) hs names
  | [], hs, s', h => by
    simp only [List.mapM_nil] at h
    obtain ⟨hv, hsx⟩ := AM.pure_ok h
    cases hv
    subst hsx
    exact ⟨ParseStep.refl hok, .nil⟩
  | n :: ns, hs, s', h => by
    simp only [List.mapM_cons] at h
    obtain ⟨x, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hst1, hd⟩ := internName_sstep hok h1
    have hst1' := (hst1.toIStep hoff).toParse hoff
    obtain ⟨xs, s₂, h2, h⟩ := AM.bind_ok h
    obtain ⟨hv, hsx⟩ := AM.pure_ok h
    cases hv
    subst hsx
    obtain ⟨hst2, hr⟩ := internNames_run hst1'.ok (by rw [hst1'.scratch]; exact hoff) ns h2
    exact ⟨hst1'.trans hst2, .cons (denoteN_ext hd hst2.ext) hr⟩

/-- con-leche: ConLeche/Driver/CheckMain.lean:152-170 checkOleansG — **the stages' frame on
`--olean`, up to the check phase**: `stages_frame` with the parse replaced by the roots and the
reader (`readOleans_run`), and the preparation at the reader's `usedOf`.  Beside it, what the
check phase's jobs read a value with: the reader's module references and pins, related at the
read's end state, which the check phase's start persistently extends; and the closure's
theorems, each a record holding a reference. -/
theorem stagesO_frame {F : FS} {sp : ConLeche.Frontend.Olean.SearchPath}
    {names : List ConLeche.Name} {pins : List NatOpPinSet} {maxNatSize : Nat} {roots : List NIdx}
    {sA sB sB' sC sD sE : AState} {pre : PreludeIx}
    {rd : ConRon.Arena.Frontend.Olean.OleanRead} {prep : Prepared} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hR : names.mapM ConRon.Arena.internName sB = .ok (roots, sB'))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) sp roots.toArray none sB' =
      .ok (.ok rd, sC))
    (hD : prepareD pre rd.decls rd.usedOf sC = .ok (prep, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE)) :
    sE.store.scratchOn = false ∧ DriverOK sE ∧ PersPins sE ∧
      PinsDenote sE.store ipins pins ∧ PersPinSets ipins ∧
      (∀ x ∈ prep.decls.toList, PersDecl x) ∧
      StoreWF sC.store ∧ sC.store.scratchOn = false ∧ PExt sC.store sE.store ∧
      Olean.NullsRel sC.store rd.pins ∧
      ∃ valuesP dsR preC usedC, Olean.ValuesRel sp F sC.store rd.values valuesP ∧
        denoteDecls sE.store prep.decls.toList =
          some (ConLeche.Frontend.prepareD preC dsR usedC).decls.toList ∧
        (∀ {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
          {c : ConLeche.Frontend.Olean.CEntryF ConLeche.Name Expr} {v : Expr}
          {all : List ConLeche.Name}, ConLeche.Frontend.Olean.InClosure sp F names.toArray m →
          ConLeche.Frontend.Olean.ViewOf sp F m d → c ∈ d.constants → c.kind = .thm v all →
          ∃ code, Declaration.thmDecl ⟨c.name, c.levelParams, c.type⟩ (.bvar code) ∈ dsR) := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ := internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ := builtinPreludeE_run hokA hoffA hpinsA hB
  have hoffB : sB.store.scratchOn = false := by rw [hstep1.scratch]; exact hoffA
  obtain ⟨hstR, hnr⟩ := internNames_run hstep1.ok hoffB names hR
  have hoffB' : sB'.store.scratchOn = false := by rw [hstR.scratch]; exact hoffB
  obtain ⟨hstC, hpersR, hpk, ⟨usedC, hU⟩, valuesP, dsR, hvals, hdenR, hthm, -⟩ :=
    Olean.readOleans_run (roots := roots.toArray) (rootsC := names.toArray) hstR.ok hoffB'
      (hpinsA.mono (hstep1.trans hstR).ext (hstep1.trans hstR).pins) (by simpa using hnr) hC
  have hstep2 := hstR.trans hstC
  have hoffC : sC.store.scratchOn = false := by rw [hstC.scratch]; exact hoffB'
  obtain ⟨hstep3, hpersDs, hclPrep⟩ :=
    prepareD_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre hdenR hpersR hU hD
  have hoff3 : sD.store.scratchOn = false := by
    rw [hstep3.scratch, hstep2.scratch, hstep1.scratch]; exact hoffA
  obtain ⟨hokP, hxP, hpinsP, hppP, hipins, hpps, hoffP, hcachesP, -⟩ :=
    internAllPins_run hstep3.ok
      (hpinsA.mono ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
        (by rw [hstep3.pins, hstep2.pins, hstep1.pins]))
      (hppA.mono (by rw [hstep3.pins, hstep2.pins, hstep1.pins])) hoff3 hE
  refine ⟨hoffP, DriverOK.start hokP hpinsP
      (((CacheOK.of_empty (s := sA) (by rw [hcachesA]; exact hc0)).monoF
            ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
            ((hstep1.cframe.trans hstep2.cframe).trans hstep3.cframe)).mono
        hxP hcachesP),
    hppP, hipins, hpps, fun x hx => hpersDs x (by simpa using hx), hstC.ok.wf, hoffC,
    PExt.of_ext (hstep3.ext.trans hxP), hpk.nulls, valuesP, dsR, preC, usedC, hvals,
    denoteDeclArray_iff.mp (denoteDeclArray_ext hxP hclPrep), hthm⟩

/-- con-leche: ConLeche/MainTheorem.lean:161 main_oleans_no_False — **a check phase accepting a
closure that holds a `False` theorem is impossible, at (B)**: the reader puts the theorem in the
stream with a reference for its value (`readOleans_run`), the check phase's accept is the pure
fold of the FILLED stream (`Arena.pooledOleanAccepts_bridge`), which still holds the theorem
with its statement, and con-leche refutes it — upstream's proof, at the twin. -/
theorem stagesO_no_False (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {F : FS} {sp : ConLeche.Frontend.Olean.SearchPath} {names : List ConLeche.Name}
    {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
    {c : ConLeche.Frontend.Olean.CEntryF ConLeche.Name Expr} {v : Expr} {all : List ConLeche.Name}
    (hcl : ConLeche.Frontend.Olean.InClosure sp F names.toArray m)
    (hv : ConLeche.Frontend.Olean.ViewOf sp F m d) (hmem : c ∈ d.constants)
    (hkind : c.kind = .thm v all) (hty : c.type = .const ConLeche.falseName [])
    {pins : List NatOpPinSet} {maxNatSize : Nat} {roots : List NIdx}
    {sA sB sB' sC sD sE sF : AState} {pre : PreludeIx}
    {rd : ConRon.Arena.Frontend.Olean.OleanRead} {prep : Prepared} {ipins : List INatOpPinSet}
    {I : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hR : names.mapM ConRon.Arena.internName sB = .ok (roots, sB'))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) sp roots.toArray none sB' =
      .ok (.ok rd, sC))
    (hD : prepareD pre rd.decls rd.usedOf sC = .ok (prep, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE))
    (hF : Arena.PooledOleanAccepts (Olean.modelFs F) rd.pins sp rd.values .verified ipins
      prep.decls sE I sF) :
    False := by
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, hwfC, hoffC, hxC, hnu, valuesP, dsR, preC, usedC,
    hvals, hden, hthm⟩ := stagesO_frame hA hB hR hC hD hE
  obtain ⟨Fu, hpure⟩ := Arena.pooledOleanAccepts_bridge V hk hind hst hoff hpp hpps hipins hpd
    hden hwfC hoffC hxC hvals hnu hF
  obtain ⟨code, hd⟩ := hthm hcl hv hmem hkind
  have hm := List.mem_map_of_mem (f := ConLeche.Cached.fillDecl (fillRef (valueOf sp F valuesP)))
    (Array.mem_toList_iff.mpr (ConLeche.Frontend.mem_prepareD (pre := preC) (used := usedC) hd))
  exact no_False_theorem_accepted_pure V (cv := ⟨c.name, c.levelParams, c.type⟩) hm hty hpure

/-- con-leche: ConLeche/Model/Fold.lean:306 checkDeclsPure_sound_of — **the model at (B), on
`--olean`**: the check phase accepting, the records denote at its end state, whose store is well
formed, and the environment of the stream with each theorem's reference replaced by a value has
a model.  The values are the snapshot's (`fillStream`, at `valueOf`); upstream states no model
theorem for `--olean`, only `main_oleans_no_False`. -/
theorem stagesO_model (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {F : FS} {sp : ConLeche.Frontend.Olean.SearchPath} {names : List ConLeche.Name}
    {pins : List NatOpPinSet} {maxNatSize : Nat} {roots : List NIdx}
    {sA sB sB' sC sD sE sF : AState} {pre : PreludeIx}
    {rd : ConRon.Arena.Frontend.Olean.OleanRead} {prep : Prepared} {ipins : List INatOpPinSet}
    {I : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hR : names.mapM ConRon.Arena.internName sB = .ok (roots, sB'))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (Olean.modelFs F) sp roots.toArray none sB' =
      .ok (.ok rd, sC))
    (hD : prepareD pre rd.decls rd.usedOf sC = .ok (prep, sD))
    (hE : internAllPins pins maxNatSize sD = .ok (ipins, sE))
    (hF : Arena.PooledOleanAccepts (Olean.modelFs F) rd.pins sp rd.values .verified ipins
      prep.decls sE I sF) :
    StoreWF sF.store ∧ ∃ (dsP : List Declaration) (val : Nat → Expr), denoteDecls sF.store prep.decls.toList = some dsP ∧
      Nonempty (ConLeche.Model.EnvModelM V
        (ConLeche.Cached.streamEnv (dsP.map (ConLeche.Cached.fillDecl (fillRef val))))) := by
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, hwfC, hoffC, hxC, hnu, valuesP, dsR, preC, usedC,
    hvals, hden, -⟩ := stagesO_frame hA hB hR hC hD hE
  obtain ⟨Fu, hpure⟩ := Arena.pooledOleanAccepts_bridge V hk hind hst hoff hpp hpps hipins hpd
    hden hwfC hoffC hxC hvals hnu hF
  obtain ⟨parts, hidx, -⟩ := hF
  obtain ⟨hst', hx, -⟩ := buildIndex_run constsSpec tablesSpec hst hoff hpd hden hidx
  exact ⟨hst'.state.wf, _, valueOf sp F valuesP, denoteDecls_ext hx _ _ hden,
    ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) hpure⟩

end ConRon.Bridge
