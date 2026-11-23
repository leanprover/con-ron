import ConRon.MainTheorem.CmpArgs
import ConRon.MainTheorem.CompareJson

/-!
# `ConRon.MainTheorem.CompareOleans` — the walk of `--olean --compare -- C S`

**Task #171, slice 3b** (DESIGN.md §3.9).  An exit 0 of `driver::compare::compare_oleans` is the
compared staged lemma's step premises (`CmpOleanStages`), at the driver's calls: each read's
records moved out before its preparation, and the reads, the solution's pool and the
challenge's pool each at a state of the instance of its own
(`rust_stages_oleans_compare_dec`, `compare_model_of_stages_dec`: lane C's
`compare_model_of_stages` at those calls).  `run_args_cmp` walks the argument list to it, the
challenge's directories `trustedOr (searchPathOf T) (searchPathOf D)` (`chal_roots_val`):
`compare_of_canGive`, con-leche's `main_compare_model`'s proof.

| lemma | what it walks |
|---|---|
| `chal_roots_val`, `sol_roots_abs` | `cli::chal_roots`, `cli::sol_roots`: con-leche's `trustedOr`, `CmpReq.solRoots` |
| `step_failed_ne`, `one_root_val`, `compare_oleans_zero` | `compare::step_failed`, `one_root`, `compare_oleans` |
| `two_roots`, `olean_args_cmp`, `run_args_cmp` | `cli::olean_args` → `compare_olean_args`, `cli::run_args` |
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.MainTheorem.Stages
open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean
open ConLeche (IsModel FS)
open ConLeche.Frontend.Olean (closureConstants)

namespace ConRon.MainTheorem

set_option autoImplicit false

universe w

/-! ## The staged lemma at the driver's calls -/

/-- `Stages.rust_stages_oleans_compare` at the driver's calls: each read's records moved out
before its preparation (`{ rd with decls := v }`, what a record mentions is read off the merged
constants alone, `olean_read_used_rel_dec`), and the reads, the solution's pool and the
challenge's pool each at a snapshot of its own (the instance's state moves between them, at the
`--pins` escape and at the worker map). -/
theorem rust_stages_oleans_compare_dec (hT2 : ReadOleansRefines)
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {pers : arena.store.PersTier} {est : arena.store.EStore}
    (hfz : pers.frozen = false)
    {st0 st1 st2 st4 st4h st5 st6 st7 st10 st11 : arena.monad.AState}
    {pre : frontend.prepare.PreludeIx} {F : ConLeche.FS}
    (hest : arena.store.EStore.empty = ok est)
    (hst0 : arena.monad.AState.init est = ok st0)
    (h1 : arena.pins.intern_reserved_pins pers st0 = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e pers st1 = ok (.Ok pre, st2))
    {c s : kernel.name.Name} {ch sh : arena.handle.NIdx} {stR1 stR : arena.monad.AState}
    (hwfC : ConRon.Refine.NameWF c) (hwfS : ConRon.Refine.NameWF s)
    (hnC : arena.monad.intern_name pers st2 c = ok (.Ok ch, stR1))
    (hnS : arena.monad.intern_name pers stR1 s = ok (.Ok sh, stR))
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {Fs' : Type} {finst' : frontend.checker_io.CheckerFs Fs'} {fsv' : Fs'}
    (hsnap' : SnapshotOf finst' fsv' F)
    {Fs'' : Type} {finst'' : frontend.checker_io.CheckerFs Fs''} {fsv'' : Fs''}
    (hsnap'' : SnapshotOf finst'' fsv'' F)
    {cr sr : frontend.olean.files.Roots} {rootsC rootsS : alloc.vec.Vec arena.handle.NIdx}
    (hrC : rootsC.val = [ch]) (hrS : rootsS.val = [sh])
    {rdC rdS : frontend.olean.records.OleanRead} {store3 store5 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv pers stR.store cr rootsC none true true
      = ok (.Ok rdC, store3))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepC : frontend.prepare.Prepared} {vC vS : alloc.vec.Vec arena.env.IDeclaration}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts pers { stR with store := store3 } preC rdC.decls { rdC with decls := vC }
      = ok (.Ok prepC, st4))
    {holed : alloc.vec.Vec arena.env.IDeclaration}
    (hhole : frontend.compare.hole_records frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts { rdC with decls := vC } pers st4 prepC.decls 0#usize (alloc.vec.Vec.new _)
      = ok (.Ok holed, st4h))
    (h3S : frontend.olean.records.read_oleans finst fsv pers st4h.store sr rootsS none true false
      = ok (.Ok rdS, store5))
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts pers { st4h with store := store5 } pre rdS.decls { rdS with decls := vS }
      = ok (.Ok prepS, st5))
    {maxNatSize : ron.nat.Nat} {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins pers st5 pins maxNatSize = ok (.Ok ipins, st6))
    {ixS ixC : arena.stream_index.IStreamIndex}
    (h6S : OleanPoolAccepts finst' fsv' pers st6 .Verified ipins prepS.decls rdS.pins rdS.values sr
      ixS st7)
    {recsC : alloc.vec.Vec arena.env.IDeclaration}
    (hside : arena.justify.side_records pers st7 holed 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    {sol : arena.justify.Solution}
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    (h6 : OleanPoolAcceptsSol finst'' fsv'' pers st10 .Verified ipins recsC rdC.pins rdC.values cr
      (some sol) ixC st11) :
    ∃ (sA sB sB₁ sB₂ sC sD sD' sC₂ sD₂ sE sF sH sI : ConRon.Arena.AState)
      (rdC' rdS' : ConRon.Arena.Frontend.Olean.OleanRead) (IS IC : ConRon.Arena.IStreamIndex),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE sA = .ok (.ok (absPreludeIx pre), sB) ∧
      ConRon.Arena.internName (ConRon.Refine.absName c) sB = .ok (absNIdx ch, sB₁) ∧
      ConRon.Arena.internName (ConRon.Refine.absName s) sB₁ = .ok (absNIdx sh, sB₂) ∧
      ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F)
          (absRoots cr) #[absNIdx ch] none true true sB₂ = .ok (.ok rdC', sC) ∧
      ConRon.Arena.Frontend.prepareD (absPreludeIx pre) rdC'.decls rdC'.usedOf sC
          = .ok (absPrepared prepC, sD) ∧
      ConRon.Arena.Frontend.holeRecordsGo rdC'.usedOf [] (absPrepared prepC).decls.toList sD
          = .ok (absIDeclL holed, sD') ∧
      ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F)
          (absRoots sr) #[absNIdx sh] none true false sD' = .ok (.ok rdS', sC₂) ∧
      ConRon.Arena.Frontend.prepareD (absPreludeIx pre) rdS'.decls rdS'.usedOf sC₂
          = .ok (absPrepared prepS, sD₂) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins)
          (ConRon.Refine.Nat.toNat maxNatSize) sD₂
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.PooledOleanAccepts (ConRon.Bridge.Frontend.Olean.modelFs F) rdS'.pins
          (absRoots sr) rdS'.values .verified (absINatOpPinSetL ipins)
          (absPrepared prepS).decls sE IS sF ∧
      ConRon.Arena.sideRecordsGo [] (absIDeclL holed) sF = .ok (absIDeclL recsC, sH) ∧
      ConRon.Arena.PooledOleanAcceptsJ (ConRon.Bridge.Frontend.Olean.modelFs F) rdC'.pins
          (absRoots cr) rdC'.values .verified (absINatOpPinSetL ipins)
          (some (ConRon.Arena.solutionOf IS (absIDeclL recsC))) (absIDeclL recsC).toArray
          sH IC sI ∧
      AStateRel₀ pers st10 sH := by
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := pers) hfz hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ :=
    (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨preL, sB, hB, hpreL, hrelB, hinvB⟩ :=
    builtin_prelude_e_refines scanSpec hrelA hinvA h2
  subst hpreL
  obtain ⟨sB₁, hRC, hrelB₁, hinvB₁⟩ := (intern_name_run'₀ c hwfC hrelB hinvB hnC).1.apply
  obtain ⟨sB₂, hRS, hrelB₂, hinvB₂⟩ := (intern_name_run'₀ s hwfS hrelB₁ hinvB₁ hnS).1.apply
  have hfs := fsRel_of_snapshot hsnap
  have hrootsC : absNIdxArr rootsC = #[absNIdx ch] := by simp [absNIdxArr, hrC]
  have hrootsS : absNIdxArr rootsS = #[absNIdx sh] := by simp [absNIdxArr, hrS]
  obtain ⟨rdC', sC, hC, hrdC, hrelC, hinvC⟩ := hT2 hfs hrelB₂ hinvB₂ h3
  rw [hrootsC] at hC
  obtain ⟨sD, hD, hrelD, hinvD⟩ :=
    (prepare_d_refines (olean_read_used_rel_dec hrdC vC) hrelC hinvC h4).apply
  have hdeclsC : absIDeclArr rdC.decls = rdC'.decls := by simp [absIDeclArr, hrdC.decls]
  rw [hdeclsC, prelude_ix_dup_abs hdup] at hD
  obtain ⟨holedL, sD', hH, hholed, hrelD', hinvD'⟩ :=
    hole_records_ls (olean_read_used_rel_dec hrdC vC) prepC.decls 0#usize st4 sD
      (alloc.vec.Vec.new _) hrelD hinvD _ _ hhole
  have hholed' : holedL = absIDeclL holed := hholed
  subst hholed'
  obtain ⟨rdS', sC₂, hCS, hrdS, hrelC₂, hinvC₂⟩ := hT2 hfs hrelD' hinvD' h3S
  rw [hrootsS] at hCS
  obtain ⟨sD₂, hDS, hrelD₂, hinvD₂⟩ :=
    (prepare_d_refines (olean_read_used_rel_dec hrdS vS) hrelC₂ hinvC₂ h4S).apply
  have hdeclsS : absIDeclArr rdS.decls = rdS'.decls := by simp [absIDeclArr, hrdS.decls]
  rw [hdeclsS] at hDS
  obtain ⟨sE, hE, hrelE, hinvE⟩ :=
    (intern_all_pins_refines hrelD₂ hinvD₂
      (ConRon.Refine.PinsWF.decode_wf_refine2 hdec) h5).dest
  obtain ⟨IS, sF, hF, hrelF, hIS⟩ :=
    olean_pool_accepts_refines (values' := rdS'.values) (fsRel_of_snapshot hsnap') hrdS.values
      hrelE hinvE hfz h6S
  rw [hrdS.pins] at hF
  have hinvF : AStateInv pers st7 := by
    obtain ⟨_, _, hB', -⟩ := h6S
    exact (build_index_empty_refines hrelE hinvE hB').choose_spec.choose_spec.2.2.1
  obtain ⟨recsL, sH, hSd, hrecs, hrelH, hinvH⟩ :=
    side_records_ls holed 0#usize st7 sF (alloc.vec.Vec.new _) hrelF hinvF _ _ hside
  have hrecs' : recsL = absIDeclL recsC := hrecs
  subst hrecs'
  have hJ : OptSolRel (some sol) (some (ConRon.Arena.solutionOf IS (absIDeclL recsC))) :=
    solution_of_rel hIS hsol
  obtain ⟨IC, sI, hI, -, -, -⟩ :=
    olean_pool_accepts_sol_refines (values' := rdC'.values) hJ (fsRel_of_snapshot hsnap'')
      hrdC.values hrelH hinvH hfz h6
  rw [hrdC.pins] at hI
  exact ⟨sA, sB, sB₁, sB₂, sC, sD, sD', sC₂, sD₂, sE, sF, sH, sI, rdC', rdS', IS, IC, hA, hB,
    hRC, hRS, hC, hD, hH, hCS, hDS, hE, hF, hSd, hI, hrelH⟩

/-- `compare_model_of_stages` (lane C) at the driver's calls (`rust_stages_oleans_compare_dec`):
the reads' records moved out before their preparations, the reads and the two pools each at a
snapshot of `F` of its own. -/
theorem compare_model_of_stages_dec (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {st1 st2 st4 st4h st5 st6 st7 st10 st11 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {c s : kernel.name.Name} {ch sh : arena.handle.NIdx} {stR1 stR : arena.monad.AState}
    (hwfC : ConRon.Refine.NameWF c) (hwfS : ConRon.Refine.NameWF s)
    (hnC : arena.monad.intern_name emptyTier st2 c = ok (.Ok ch, stR1))
    (hnS : arena.monad.intern_name emptyTier stR1 s = ok (.Ok sh, stR))
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {Fs' : Type} {finst' : frontend.checker_io.CheckerFs Fs'} {fsv' : Fs'}
    (hsnap' : SnapshotOf finst' fsv' F)
    {Fs'' : Type} {finst'' : frontend.checker_io.CheckerFs Fs''} {fsv'' : Fs''}
    (hsnap'' : SnapshotOf finst'' fsv'' F)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {sr : frontend.olean.files.Roots}
    {rootsC rootsS : alloc.vec.Vec arena.handle.NIdx}
    (hrC : rootsC.val = [ch]) (hrS : rootsS.val = [sh])
    {rdC rdS : frontend.olean.records.OleanRead} {store3 store5 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store ⟨dirs, alloc.vec.Vec.new _⟩ rootsC none true true
      = ok (.Ok rdC, store3))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepC : frontend.prepare.Prepared} {vC vS : alloc.vec.Vec arena.env.IDeclaration}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } preC rdC.decls { rdC with decls := vC }
      = ok (.Ok prepC, st4))
    {holed : alloc.vec.Vec arena.env.IDeclaration}
    (hhole : frontend.compare.hole_records frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts { rdC with decls := vC } emptyTier st4 prepC.decls 0#usize (alloc.vec.Vec.new _)
      = ok (.Ok holed, st4h))
    (h3S : frontend.olean.records.read_oleans finst fsv emptyTier st4h.store sr rootsS none true false
      = ok (.Ok rdS, store5))
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { st4h with store := store5 } pre rdS.decls { rdS with decls := vS }
      = ok (.Ok prepS, st5))
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st5 pins maxNatSize = ok (.Ok ipins, st6))
    {ixS : arena.stream_index.IStreamIndex}
    (h6S : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st6 e prepS.decls 0#usize) = ok (.Ok ixS, st7))
    {tierS : arena.store.PersTier} {frozenS : arena.store.EStore}
    (h7S : arena.checker.freeze_tier st7.store ixS = ok (tierS, frozenS))
    (h8S : ParallelAll prepS.decls.length (oleanWorkerInit st7.pins)
      (oleanJobStep finst' fsv' tierS .Verified ipins prepS.decls rdS.pins rdS.values sr))
    {recsC : alloc.vec.Vec arena.env.IDeclaration}
    (hside : arena.justify.side_records emptyTier st7 holed 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    {sol : arena.justify.Solution}
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    {ixC : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st10 e recsC 0#usize) = ok (.Ok ixC, st11))
    {tierC : arena.store.PersTier} {frozenC : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st11.store ixC = ok (tierC, frozenC))
    (h8 : ParallelAll recsC.length (oleanWorkerInit st11.pins)
      (oleanJobStepSol finst'' fsv'' tierC .Verified ipins recsC rdC.pins rdC.values ⟨dirs, alloc.vec.Vec.new _⟩
        (some sol))) :
    ∀ fs', FS.AgreeUnder (absSearchPath dirs) F fs' →
      ∃ model, IsModel V model
        (closureConstants (absSearchPath dirs) fs' #[ConRon.Refine.absName c]) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  obtain ⟨sA, sB, sB₁, sB₂, sC, sD, sD', sC₂, sD₂, sE, sF, sH, sI, rdC', rdS', IS, IC, hA, hB,
      hRC, hRS, hC, hD, hH, hCS, hDS, hE, hF, hSd, hI, -⟩ :=
    rust_stages_oleans_compare_dec read_oleans_refines hdec rfl hest hst0 h1 h2 hwfC hwfS hnC hnS
      hsnap hsnap' hsnap'' hrC hrS h3 hdup h4 hhole h3S h4S h5
      (oleanPoolAccepts_intro h6S h7S h8S) hside hsol (oleanPoolAcceptsSol_intro h6 h7 h8)
  exact ConRon.Bridge.stagesOC_isModel V hk hind (crp := absSearchPath dirs) rfl
    (pins := ConRon.Refine.absPins pins) hA hB hRC hRS hC hD hH hCS hDS hE hF hSd hI

/-! ## The walk of `compare::compare_oleans` -/

/-- **What an exit 0 of `--olean --compare -- C S` ran**: the premises of
`compare_model_of_stages_dec`, at the binary's start values, `--verified` and the embedded pins,
the challenge read through the directories `dirs` alone. -/
inductive CmpOleanStages (fs : ConLeche.FS) (cName sName : kernel.name.Name)
    (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)) : Prop where
  | intro {st1 st2 st4 st4h st5 st6 st7 st10 st11 stR1 stR : arena.monad.AState}
      {pre : frontend.prepare.PreludeIx} {ch sh : arena.handle.NIdx}
      {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
      {Fs' : Type} {finst' : frontend.checker_io.CheckerFs Fs'} {fsv' : Fs'}
      {Fs'' : Type} {finst'' : frontend.checker_io.CheckerFs Fs''} {fsv'' : Fs''}
      {sr : frontend.olean.files.Roots} {rootsC rootsS : alloc.vec.Vec arena.handle.NIdx}
      {rdC rdS : frontend.olean.records.OleanRead} {store3 store5 : arena.store.EStore}
      {preC : frontend.prepare.PreludeIx} {prepC : frontend.prepare.Prepared}
      {vC vS : alloc.vec.Vec arena.env.IDeclaration} {holed : alloc.vec.Vec arena.env.IDeclaration}
      {prepS : frontend.prepare.Prepared} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
      {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {maxNatSize : ron.nat.Nat}
      {ixS : arena.stream_index.IStreamIndex} {tierS : arena.store.PersTier}
      {frozenS : arena.store.EStore} {recsC : alloc.vec.Vec arena.env.IDeclaration}
      {sol : arena.justify.Solution} {ixC : arena.stream_index.IStreamIndex}
      {tierC : arena.store.PersTier} {frozenC : arena.store.EStore}
      (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
      (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
      (hwfC : ConRon.Refine.NameWF cName) (hwfS : ConRon.Refine.NameWF sName)
      (hnC : arena.monad.intern_name emptyTier st2 cName = ok (.Ok ch, stR1))
      (hnS : arena.monad.intern_name emptyTier stR1 sName = ok (.Ok sh, stR))
      (hsnap : SnapshotOf finst fsv fs) (hsnap' : SnapshotOf finst' fsv' fs)
      (hsnap'' : SnapshotOf finst'' fsv'' fs)
      (hrC : rootsC.val = [ch]) (hrS : rootsS.val = [sh])
      (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store ⟨dirs, alloc.vec.Vec.new _⟩ rootsC none true true
        = ok (.Ok rdC, store3))
      (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
      (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } preC rdC.decls { rdC with decls := vC }
        = ok (.Ok prepC, st4))
      (hhole : frontend.compare.hole_records frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts { rdC with decls := vC } emptyTier st4 prepC.decls 0#usize (alloc.vec.Vec.new _)
        = ok (.Ok holed, st4h))
      (h3S : frontend.olean.records.read_oleans finst fsv emptyTier st4h.store sr rootsS none true false
        = ok (.Ok rdS, store5))
      (h4S : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { st4h with store := store5 } pre rdS.decls { rdS with decls := vS }
        = ok (.Ok prepS, st5))
      (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
      (h5 : arena.checker.intern_all_pins emptyTier st5 pins maxNatSize = ok (.Ok ipins, st6))
      (h6S : (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st6 e prepS.decls 0#usize) = ok (.Ok ixS, st7))
      (h7S : arena.checker.freeze_tier st7.store ixS = ok (tierS, frozenS))
      (h8S : ParallelAll prepS.decls.length (oleanWorkerInit st7.pins)
        (oleanJobStep finst' fsv' tierS .Verified ipins prepS.decls rdS.pins rdS.values sr))
      (hside : arena.justify.side_records emptyTier st7 holed 0#usize (alloc.vec.Vec.new _) =
        ok (.Ok recsC, st10))
      (hsol : arena.justify.solution_of ixS recsC = ok sol)
      (h6 : (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st10 e recsC 0#usize) = ok (.Ok ixC, st11))
      (h7 : arena.checker.freeze_tier st11.store ixC = ok (tierC, frozenC))
      (h8 : ParallelAll recsC.length (oleanWorkerInit st11.pins)
        (oleanJobStepSol finst'' fsv'' tierC .Verified ipins recsC rdC.pins rdC.values
          ⟨dirs, alloc.vec.Vec.new _⟩ (some sol))) :
      CmpOleanStages fs cName sName dirs

/-- A compared run's stages have the challenge's model (`compare_model_of_stages_dec`). -/
theorem CmpOleanStages.model (V : Type w) [ConLeche.SetTheory V] {fs : ConLeche.FS}
    {cName sName : kernel.name.Name} {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    (h : CmpOleanStages fs cName sName dirs) :
    ∀ fs', FS.AgreeUnder (absSearchPath dirs) fs fs' →
      ∃ model, IsModel V model
        (closureConstants (absSearchPath dirs) fs' #[ConRon.Refine.absName cName]) := by
  cases h with
  | intro h1 h2 hwfC hwfS hnC hnS hsnap hsnap' hsnap'' hrC hrS h3 hdup h4 hhole h3S h4S hpins h5
      h6S h7S h8S hside hsol h6 h7 h8 =>
    exact compare_model_of_stages_dec V h1 h2 hwfC hwfS hnC hnS hsnap hsnap' hsnap'' hrC hrS h3
      hdup h4 hhole h3S h4S hpins h5 h6S h7S h8S hside hsol h6 h7 h8

section Walk

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- `compare::one_root`: the one handle. -/
theorem one_root_val {h : arena.handle.NIdx} {v : alloc.vec.Vec arena.handle.NIdx}
    (hv : driver.compare.one_root h = ok v) : v.val = [h] := by
  rw [driver.compare.one_root] at hv
  simp only [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2, bind_ok] at hv
  rw [ConRon.Refine.vec_push_val hv]; rfl

/-- A compared run's failed step is never exit 0. -/
theorem step_failed_ne {s s' : S} {e v} {c : Std.U8}
    (h : driver.compare.step_failed io s e v = ok (c, s')) : c.val ≠ 0 := by
  rw [driver.compare.step_failed] at h
  obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have := Result.ok_injective h
  simp only [Prod.mk.injEq] at this
  rw [← this.1]
  exact exit_code_ne hc0

/-- An empty vector's length is 0. -/
theorem len_zero_of_nil {α : Type} {v : alloc.vec.Vec α} (h : v.val = []) :
    alloc.vec.Vec.len v = 0#usize := by
  have := alloc.vec.Vec.len_val v
  simp [alloc.vec.Vec.length, h] at this; scalar_tac

/-- A nonempty vector's length is not 0. -/
theorem len_ne_zero_of_ne {α : Type} {v : alloc.vec.Vec α} (h : v.val ≠ []) :
    ¬ alloc.vec.Vec.len v = 0#usize := by
  intro hl
  apply h
  have := alloc.vec.Vec.len_val v
  rw [hl] at this
  simp only [alloc.vec.Vec.length] at this
  exact List.eq_nil_of_length_eq_zero (by simpa using this.symm)

/-- No directories, as paths: none. -/
theorem absSearchPath_isEmpty {d : alloc.vec.Vec (alloc.vec.Vec Std.U32)} :
    (absSearchPath d).isEmpty = decide (d.val = []) := by
  cases h : d.val <;> simp [absSearchPath, h]

/-- **The challenge's lookup** (`cli::chal_roots`): a search path with no fallback, its
directories con-leche's `trustedOr` of the trusted path and the search path. -/
theorem chal_roots_val {a : driver.cli.Args} {cr : frontend.olean.files.Roots}
    (h : driver.cli.chal_roots a = ok cr) :
    ∃ dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32), cr = ⟨dirs, alloc.vec.Vec.new _⟩ ∧
      absSearchPath dirs = ConLeche.Driver.trustedOr (absSearchPath a.trusted_path)
        (absSearchPath a.search_path) := by
  rw [driver.cli.chal_roots] at h
  by_cases h0 : a.trusted_path.val = []
  · rw [ite_eq_left (len_zero_of_nil h0)] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [frontend.olean.files.roots_of_path] at h
    cases Result.ok_injective h
    refine ⟨v, rfl, ?_⟩
    have := push_files_loop_val a.search_path _ _ 0#usize rfl hv
    rw [absSearchPath_of_vals (by simpa using this)]
    simp [ConLeche.Driver.trustedOr, absSearchPath_isEmpty, h0]
  · rw [ite_eq_right (len_ne_zero_of_ne h0)] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [frontend.olean.files.roots_of_path] at h
    cases Result.ok_injective h
    refine ⟨v, rfl, ?_⟩
    have := push_files_loop_val a.trusted_path _ _ 0#usize rfl hv
    rw [absSearchPath_of_vals (by simpa using this)]
    simp [ConLeche.Driver.trustedOr, absSearchPath_isEmpty, h0]

/-- **The solution's lookup** (`cli::sol_roots`): con-leche's `CmpReq.solRoots` at the
command line's trusted path and search path. -/
theorem sol_roots_abs {a : driver.cli.Args} {sp : frontend.olean.files.Roots}
    (h : driver.cli.sol_roots a = ok sp) (X Y : ConLeche.Name) :
    absRoots sp = (⟨X, Y, absSearchPath a.trusted_path, absSearchPath a.search_path, none⟩ :
      ConLeche.Driver.CmpReq).solRoots := by
  rw [driver.cli.sol_roots] at h
  by_cases h0 : a.trusted_path.val = []
  · rw [ite_eq_left (len_zero_of_nil h0)] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [frontend.olean.files.roots_of_path] at h
    cases Result.ok_injective h
    have := push_files_loop_val a.search_path _ _ 0#usize rfl hv
    simp only [absRoots, ConLeche.Driver.CmpReq.solRoots, absSearchPath_isEmpty, h0,
      decide_true, ite_true]
    rw [absSearchPath_of_vals (by simpa using this)]
    rfl
  · rw [ite_eq_right (len_ne_zero_of_ne h0)] at h
    obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v2, hv2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have e1 := push_files_loop_val a.trusted_path _ _ 0#usize rfl hv1
    have e2 := push_files_loop_val a.search_path _ _ 0#usize rfl hv2
    simp only [absRoots, ConLeche.Driver.CmpReq.solRoots, absSearchPath_isEmpty, h0,
      decide_false, Bool.false_eq_true, ite_false]
    rw [absSearchPath_of_vals (d := v1) (d' := a.trusted_path) (by simpa using e1),
      absSearchPath_of_vals (d := v2) (d' := a.search_path) (by simpa using e2)]

/-- **The compared run, 0** (`compare::compare_oleans` at `--verified`, the embedded pins, no
`--constant`): its calls are `compare_model_of_stages_dec`'s premises, the challenge's
directories `trustedOr` of the command line's. -/
theorem compare_oleans_zero (hfs : AnswersAs io fs) (hpool : PoolSound io) {s s' : S}
    {a : driver.cli.Args} (hver : a.verified = true)
    {cn sn : kernel.name.Name} (hwfC : ConRon.Refine.NameWF cn)
    (hwfS : ConRon.Refine.NameWF sn) {cs : alloc.vec.Vec kernel.name.Name} (hcs : cs.val = [])
    {c : Std.U8} (h : driver.compare.compare_oleans io s a cn sn cs = ok (c, s'))
    (hc : c.val = 0) :
    ∃ dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32),
      absSearchPath dirs = ConLeche.Driver.trustedOr (absSearchPath a.trusted_path)
        (absSearchPath a.search_path) ∧ CmpOleanStages fs cn sn dirs := by
  rw [driver.compare.compare_oleans] at h
  simp only [hver, ite_true, bind_ok] at h
  rw [startState_eq, bind_ok, emptyTier_eq, bind_ok] at h
  obtain ⟨⟨r0, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r0 with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok u =>
  obtain ⟨⟨r1, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err p =>
    obtain ⟨e, line⟩ := p
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok pre =>
  obtain ⟨⟨r2, stR1⟩, hnC, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e => exact (step_failed_ne h hc).elim
  | Ok ch =>
  obtain ⟨⟨r3, stR⟩, hnS, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r3 with
  | Err e => exact (step_failed_ne h hc).elim
  | Ok sh =>
  simp only [intern_consts_nil hcs, bind_ok] at h
  obtain ⟨cr, hcr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨dirs, rfl, hdirs⟩ := chal_roots_val hcr
  obtain ⟨sr, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rootsC, hrC, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨readC, store3⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases readC with
  | Err p =>
    obtain ⟨e, line⟩ := p
    obtain ⟨⟨o, _⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases o with
    | none => exact (oleans_failed_ne h hc).elim
    | some why =>
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact (code_ne h (by decide) hc).elim
  | Ok rdC =>
  obtain ⟨o, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | some why =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | none =>
  simp only [core.mem.replace] at h
  obtain ⟨preC, hdup, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r5, st4⟩, h4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r5 with
  | Err e => exact (step_failed_ne h hc).elim
  | Ok prepC =>
  obtain ⟨⟨r6, st4h⟩, hhole, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r6 with
  | Err e => exact (step_failed_ne h hc).elim
  | Ok holed =>
  simp only [bind_ok] at h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rootsS, hrS, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨readS, store5⟩, h3S, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases readS with
  | Err p =>
    obtain ⟨e, line⟩ := p
    exact (oleans_failed_ne h hc).elim
  | Ok rdS =>
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases b with
  | true =>
    simp only [ite_true] at h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | false =>
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨⟨r7, st5⟩, h4S, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r7 with
  | Err e => exact (step_failed_ne h hc).elim
  | Ok prepS =>
  have h := hoisted_bind h
  obtain ⟨o, hpr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | none => exact (code_ne h (by decide) hc).elim
  | some ps =>
  have hpins := embedded_pins_ok hpr
  obtain ⟨⟨r8, st6⟩, h5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r8 with
  | Err e => exact (step_failed_ne h hc).elim
  | Ok ipins =>
  obtain ⟨⟨jobs, io2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r9, io3, st11⟩, hph, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r9 with
  | Err p =>
    obtain ⟨e, i⟩ := p
    exact (solution_failed_ne h hc).elim
  | Ok ixS =>
  obtain ⟨st7, tierS, frozenS, h6S, h7S, h8S, rfl⟩ := check_phase_olean_ok hpool hph
  have h := hoisted_bind h
  obtain ⟨⟨r10, st10⟩, hside, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r10 with
  | Err e => exact (step_failed_ne h hc).elim
  | Ok recsC =>
  obtain ⟨sol, hsol, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨verdict, io4, st14⟩, hph2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ixC, rfl⟩ := compare_verdict_zero h hc
  obtain ⟨st11', tierC, frozenC, h6, h7, h8, -⟩ := check_phase_olean_ok hpool hph2
  exact ⟨dirs, hdirs, CmpOleanStages.intro h1 h2 hwfC hwfS hnC hnS (hfs s) (hfs io2) (hfs io3)
    (one_root_val hrC) (one_root_val hrS) h3 hdup h4 hhole h3S h4S hpins h5 h6S h7S h8S hside hsol
    h6 h7 h8⟩

/-- Two roots of a parse. -/
theorem two_roots {a : driver.cli.Args} {f0 f1 : alloc.vec.Vec Std.U32}
    (hfiles : a.files.val = [f0, f1]) {rs : alloc.vec.Vec kernel.name.Name}
    (hr : driver.cli.parse_mod_names a.files = ok (.Ok rs)) :
    ∃ n0 n1, rs.val = [n0, n1] ∧ frontend.olean.files.parse_mod_name f0 = ok (some n0) ∧
      frontend.olean.files.parse_mod_name f1 = ok (some n1) := by
  obtain ⟨ns, hrs, hfa⟩ := parse_mod_names_loop_val a.files _ _ 0#usize rfl (by simp) hr
  rw [hfiles] at hfa
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hfa
  rcases hfa with _ | ⟨hx, hrest⟩
  rcases hrest with _ | ⟨hy, hrest'⟩
  cases hrest'
  exact ⟨_, _, by rw [hrs]; rfl, hx, hy⟩

/-- **`--olean --compare` at two roots, at exit 0** (`cli::olean_args`, `compare_olean_args`, no
`--module`, `--modular` or `--constant`): the compared run of the two. -/
theorem olean_args_cmp {s s' : S} {a : driver.cli.Args} (hcmp : a.compare = true)
    (hsch : a.scheduled = false) (hmod : a.modular = false) (hmo : a.module = false) (hcon : a.constants.val = [])
    {f0 f1 : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f0, f1]) {c : Std.U8}
    (h : driver.cli.olean_args io s a = ok (c, s')) (hc : c.val = 0) :
    ∃ (n0 n1 : kernel.name.Name) (cs : alloc.vec.Vec kernel.name.Name),
      frontend.olean.files.parse_mod_name f0 = ok (some n0) ∧
      frontend.olean.files.parse_mod_name f1 = ok (some n1) ∧ cs.val = [] ∧
      driver.compare.compare_oleans io s a n0 n1 cs = ok (c, s') := by
  rw [driver.cli.olean_args] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases b with
  | true => exact (usage_ne h hc).elim
  | false =>
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e => exact (usage_ne h hc).elim
  | Ok rs =>
  obtain ⟨n0, n1, hrs, h0, h1⟩ := two_roots hfiles hr
  obtain ⟨cs, hcs, hcsv⟩ := parse_const_names_nil hcon
  simp only [hcs, Aeneas.Std.bind_ok, hcmp, ite_true] at h
  rw [driver.cli.compare_olean_args] at h
  have hl : ¬ (alloc.vec.Vec.len rs != 2#usize) = true := by
    have := alloc.vec.Vec.len_val rs
    simp [alloc.vec.Vec.length, hrs] at this
    simp; scalar_tac
  rw [ite_eq_right hl, ConRon.Args.vec_index_ok' (by simp [hrs]), bind_ok,
    ConRon.Args.vec_index_ok' (by simp [hrs]), bind_ok] at h
  obtain ⟨bb, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases bb with
  | true =>
    simp only [ite_true] at h
    exact (usage_ne h hc).elim
  | false =>
  simp only [Bool.false_eq_true, ite_false, driver.cli.cmp_mode, hmo, hmod, hsch, bind_ok] at h
  simp only [hrs] at h
  exact ⟨n0, n1, cs, h0, h1, hcsv, h⟩

end Walk

/-! ## The run of `["--olean", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]` -/

section Run

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **An exit 0 of `--olean --compare --trusted-search-path=T --search-path=D -- c s`**
(`cli::run_args`): the two roots module names the Rust parsed, the challenge's directories
`trustedOr (searchPathOf T) (searchPathOf D)`, the run's calls `CmpOleanStages`. -/
theorem run_args_cmp (hfs : AnswersAs io fs) (hpool : PoolSound io)
    {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D c s : String}
    (hargv : ArgvOf argv ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) {x x' : S}
    {code : Std.U8} (h : driver.cli.run_args io x argv = ok (code, x')) (hc : code.val = 0) :
    ∃ (cn sn : kernel.name.Name) (dv : alloc.vec.Vec (alloc.vec.Vec Std.U32)),
      ConLeche.Frontend.Olean.parseModName c = some (ConRon.Refine.absName cn) ∧
      ConLeche.Frontend.Olean.parseModName s = some (ConRon.Refine.absName sn) ∧
      absSearchPath dv = ConLeche.Driver.trustedOr (ConLeche.Driver.searchPathOf T)
        (ConLeche.Driver.searchPathOf D) ∧ CmpOleanStages fs cn sn dv := by
  obtain ⟨w0, w1, wT, wD, wE, f0, f1, hv, h0, h1, hT, hD, hE, hf0, hf1⟩ := argv_cmp hargv
  obtain ⟨TT, hTT⟩ := trusted_word hT
  obtain ⟨DD, hDD⟩ := search_word hD
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wE := by simp [hv]
  have hhelp : driver.cli.help_wanted argv = ok false := by
    rw [driver.cli.help_wanted,
      ConRon.Args.help_word g0 (by rw [h0]; simp) (by rw [h0]; simp) (usize_add_lit (b := 1#usize) rfl),
      ConRon.Args.help_word g1 (by rw [h1]; simp) (by rw [h1]; simp) (usize_add_lit (b := 2#usize) rfl),
      ConRon.Args.help_word g2 (by rw [hTT]; simp) (by rw [hTT]; simp) (usize_add_lit (b := 3#usize) rfl),
      ConRon.Args.help_word g3 (by rw [hDD]; simp) (by rw [hDD]; simp) (usize_add_lit (b := 4#usize) rfl),
      ConRon.Args.help_end g4 hE]
  rw [driver.cli.run_args, hhelp, bind_ok] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsch, hmod, hmo, hver, hcon, htp, hsp, hfl⟩ :=
    parse_args_cmp hv h0 h1 hTT hDD hE ha
  simp only [hbad, hcg, hol, hsch, hmod, Bool.false_eq_true, ite_false, ite_true] at h
  obtain ⟨f0', f1', hf', hf0', hf1'⟩ : ∃ f0' f1', a.files.val = [f0', f1'] ∧
      f0'.val = f0.val ∧ f1'.val = f1.val := by
    rcases hfv : a.files.val with _ | ⟨f0', _ | ⟨f1', _ | ⟨g, l⟩⟩⟩ <;> rw [hfv] at hfl <;>
      simp at hfl
    exact ⟨f0', f1', rfl, hfl.1, hfl.2⟩
  obtain ⟨n0, n1, cs, hn0, hn1, hcs, hck⟩ := olean_args_cmp hcmp hsch hmod hmo hcon hf' h hc
  have hc0 : f0'.val.map UScalar.val = c.toList.map Char.toNat := by rw [hf0']; exact hf0
  have hc1 : f1'.val.map UScalar.val = s.toList.map Char.toNat := by rw [hf1']; exact hf1
  obtain ⟨hwf0, hpm0⟩ := ConRon.Args.parse_mod_name_some hc0 hn0
  obtain ⟨hwf1, hpm1⟩ := ConRon.Args.parse_mod_name_some hc1 hn1
  obtain ⟨dv, hdv, hst⟩ := compare_oleans_zero hfs hpool hver hwf0 hwf1 hcs hck hc
  refine ⟨n0, n1, dv, hpm0, hpm1, ?_, hst⟩
  rw [hdv, show absSearchPath a.trusted_path = _ from ConRon.Args.push_dirs_trusted hT htp,
    show absSearchPath a.search_path = _ from ConRon.Args.push_dirs_search hD hsp]

end Run

/-- **`main_compare_model`'s conclusion from an exit 0**. -/
theorem compare_of_canGive (V : Type w) [ConLeche.SetTheory V] {T D c s : String}
    {C S : ConLeche.Name} {fs : ConLeche.FS}
    (hc : ConLeche.Frontend.Olean.parseModName c = some C)
    (_hs : ConLeche.Frontend.Olean.parseModName s = some S)
    (h : CanGiveConforming ["--olean", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D,
      "--", c, s] fs 0) :
    ∀ fs', FS.AgreeUnder (ConLeche.Driver.trustedOr (ConLeche.Driver.searchPathOf T)
        (ConLeche.Driver.searchPathOf D)) fs fs' →
      ∃ model, IsModel V model (closureConstants
        (ConLeche.Driver.trustedOr (ConLeche.Driver.searchPathOf T)
          (ConLeche.Driver.searchPathOf D)) fs' #[C]) := by
  obtain ⟨Sio, io, x, x', argv, code, hfs, hpool, -, hargv, hrun, hcode⟩ := h
  obtain ⟨cn, sn, dv, hpc, -, hdv, hst⟩ := run_args_cmp hfs hpool hargv hrun (by simpa using hcode)
  have hcn : ConRon.Refine.absName cn = C := Option.some.inj (hpc.symm.trans hc)
  have := hst.model V
  rw [hdv, hcn] at this
  exact this

end ConRon.MainTheorem
