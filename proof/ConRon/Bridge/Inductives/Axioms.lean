/-
# `ConRon.Bridge.Inductives.Axioms` — the trust census of the inductive tier

Two groups, as `Bridge/Checker/Axioms.lean` has them.

**Group 1 — the CLOSED results.**  Every one prints
`[propext, Classical.choice, Quot.sound]` and nothing else: no `sorryAx`, and
— the point of task #97a's arithmetic packing — no `bv_decide` axiom.  These
are the tier's plumbing: the two frames and their algebra, the six record and
list transports, the bind inversion, and the five pure identifications
(`structProjPs_eq`, `recIdxOf_spec`, `nativeIsRec_spec`, `rulePrefix_spec`,
`majorIdx_spec` — plus `complete_spec`, `withKinds_spec`,
`denoteCtors_length` and the pure step lemma `checkDecl_ind_route`).

**Round 2 added four blocks to group 1** (task #97-P3-Ind round 2): the
primitives in RUN form (`internE_run` and its faces, the three nested
interners, `mkAppN_run`, `view_run`, `pureOk`, `failOk`), the projection-table
obligation (`ProjOut`'s four lemmas and `mkIFEnvGo_counter_lt`), the whole of
`SumParts.lean` and the whole of `Decl.lean` bar the two headline theorems —
twenty-one statements that were `sorry` at the end of round 1, including
`structPsAt_spec`, which is why `structProjPs_spec` now closes with it.

(`structProjPs_spec` was NOT in round 1's group 1: it is `structPsAt_spec`
through `structProjPs_eq`, and `structPsAt_spec` was open, so it inherited
`sorryAx` while the arithmetic identification beside it did not.  Both are
closed now.)

**Group 2 — the two headline theorems.**  `checkIndDecl_bridge` is the arm
(DESIGN §8.2's Theorem 1 at the inductive route) and `indSpec_of_bridge` is
`Bridge/Checker/Hyp.lean`'s `IndSpec`.  Both print `sorryAx`: the first
because its four sub-statements are open, the second because of that AND of
the one clause `Bridge/Inductives/Decl.lean`'s module note shows is false.
Neither prints `CoreSpec` — it is a hypothesis of the statement, as it is
everywhere else in this library.
-/
import ConRon.Bridge.Inductives.Decl

namespace ConRon.Bridge.Inductives

/-! ## Group 1 — closed -/

-- the two frames and the bridge between them
#print axioms PStep.refl
#print axioms PStep.trans
#print axioms PStep.of_caches
#print axioms PStep.toCore
#print axioms PSpec.toCSpec

-- the `AM` bind's inversion
#print axioms bindOk

-- the record and list transports
#print axioms denoteBinders_ext
#print axioms denoteCtors_ext
#print axioms denoteCIList_ext
#print axioms denoteFEnv_ext
#print axioms ShapeRel.ext
#print axioms PartsRel.ext
#print axioms RenameRel.ext
#print axioms InstRel.trans

-- the pure identifications
#print axioms structProjPs_eq
#print axioms recIdxOf_spec
#print axioms nativeIsRec_spec
#print axioms complete_spec
#print axioms withKinds_spec
#print axioms denoteCtors_length
#print axioms rulePrefix_spec
#print axioms majorIdx_spec

-- the pure side's own step lemma (task #97-P3-Core §5's rule 8)
#print axioms checkDecl_ind_route

/-! ### Round 2's additions -/

-- the `AM` `pure` and `fail` inversions, and `view` as a run
#print axioms pureOk
#print axioms failOk
#print axioms view_run

-- the primitives in RUN form
#print axioms internE_run
#print axioms internBVarE_run
#print axioms internSortE_run
#print axioms internConstE_run
#print axioms internProjE_run
#print axioms internForallEE_run
#print axioms internLamE_run
#print axioms internLNode_run
#print axioms internZeroL_run
#print axioms internParamL_run
#print axioms internLsNode_run
#print axioms internNNode_run
#print axioms mkAppN_run

-- the projection table's obligation (the `guards` clause's home)
#print axioms ProjOut.refl
#print axioms ProjOut.mono
#print axioms ProjOut.trans
#print axioms ProjOut.absolute
#print axioms ProjOut.push
#print axioms mkIFEnvGo_counter_lt
#print axioms structProjGuards_length
#print axioms denoteLList_length

-- the list and record readers
#print axioms denoteEList_append
#print axioms denoteBinders_length
#print axioms denoteCV_name
#print axioms denoteCV_type

-- `SumParts.lean`, whole
#print axioms sumSplit_spec
#print axioms withSort_spec

-- the generators (`StructParts.lean` group 1) and the Π→Π/Π→λ rewrites
#print axioms paramLevels_spec
#print axioms structPsAt_spec
#print axioms bvarsDesc_spec
#print axioms structFam_spec
#print axioms structCtorSpine_spec
#print axioms structRuleBody_spec
#print axioms structElimLevel_spec
#print axioms structCtorSpineAt_spec
#print axioms structFamI_spec
#print axioms structProjPs_spec
#print axioms structProjArgP_spec
#print axioms replacePisPw_spec
#print axioms pisToLamsPw_spec
#print axioms structMotiveTyI_spec

-- the telescope readers and the recursor generators' leaves
#print axioms piSortTeleLen?_spec
#print axioms piBinders_spec
#print axioms structRecPrefixAt_spec
#print axioms structTeleVars_spec
#print axioms mkPisOf_spec
#print axioms mkLamsOf_spec
#print axioms nativeCtors4_spec

-- the arm's own gate (`Decl.lean`, whole bar the headline theorems)
#print axioms indParamsOk_tail
#print axioms indParamsOk_spec

-- round 6 (task #97-P3-Ind round 6): the recognisers, groups 3 and 4, the
-- positivity classification, and the pieces of the installs they unblocked
#print axioms reservedBasisNames_pstep
#print axioms stripLams_pstep
#print axioms lvlEq?_pstep
#print axioms mapM_pstep
#print axioms allM_pstep
#print axioms allM_E_pstep
#print axioms anyM_B_pstep
#print axioms mapM_E_pstep
#print axioms resetPair_pstep
#print axioms fvarBSpec
#print axioms structPartsCore?_run
#print axioms structPartsCore?_spec
#print axioms structPartsCore?_isSome
#print axioms nativeShape?_run
#print axioms nativeShape?_spec
#print axioms nativeParts?_run
#print axioms nativeParts?_spec
#print axioms nativeParts?_isSome
#print axioms instPisAtLift_pstep
#print axioms structProjResidP_spec
#print axioms structProjBodiesGo_spec
#print axioms structProjBodies_spec
#print axioms structTeleAt_spec
#print axioms structIhApp_spec
#print axioms structRuleBodyR_spec
#print axioms structIhPis_spec
#print axioms structMinorTyR_spec
#print axioms structMinorsPisR_spec
#print axioms structMinorsLamsR_spec
#print axioms structRecTyR_spec
#print axioms structRecRhsR_spec
#print axioms recFamOk_spec
#print axioms recPositivity_spec
#print axioms recFieldKind_spec
#print axioms recCtorKinds_spec
#print axioms nativeRulePrefixOk_spec
#print axioms nativeRulesOk_spec
#print axioms checkStructDomsAt_spec
#print axioms closeTelescope_spec
#print axioms consSumCtors_spec
#print axioms recRuleKOf_run
#print axioms recRuleEtaOf_run
#print axioms recRuleBits_run
#print axioms sumRules_spec
#print axioms nativeRawRec_spec
#print axioms mentionsFvarGo_spec
#print axioms mentionsFvar_spec
#print axioms recCtorKindsAll_spec
#print axioms classifyFixKinds_spec
#print axioms renameConstsFast_ns
#print axioms domsMatchRenamed_spec

-- round 7: the EnvWF/WScoped repairs, the opener, the capability theorems,
-- and (after task #97-P3-Checker round 9's layout move) the scoping guards
#print axioms whnfTelescope_mono
#print axioms whnfTelescope_spec
#print axioms checkStructFieldSortsI_mono
#print axioms checkStructFieldSortsI_spec
#print axioms denoteLList_append'
#print axioms denoteEList_contains
#print axioms normPosDom_mono
#print axioms normPosDom_run
#print axioms normPosDom_spec
#print axioms normFieldDoms_mono
#print axioms normFieldDoms_spec
#print axioms denoteOpen_ext
#print axioms openPisAtFvars_run
#print axioms InstLVec_push
#print axioms openPisAtFvarsFGo_run
#print axioms openPisAtFvarsF_run
#print axioms allM_E_ck
#print axioms anyM_E_pstep
#print axioms constsResolveFFast_pstep
#print axioms allM_ck
#print axioms famTail_run
#print axioms nativeOpenedOk_spec
#print axioms nativeFieldsOk_spec
#print axioms CoreStep.of_readonly
#print axioms checkNativeRules_spec
#print axioms denoteCV_inj'
#print axioms denoteCI_inj_ind'
#print axioms eqBasisStored_spec
#print axioms eqApp3?_none
#print axioms checkIotaSidesTy_spec
#print axioms denoteCI_kind
#print axioms domsMatchAux_eq
#print axioms IFEnvOK.find_thm
#print axioms IFEnvOK.find_defn
#print axioms checkProjLookups_spec
#print axioms allM_cstep
#print axioms etaProjOk_run
#print axioms checkEtaThm_spec
#print axioms checkUnitThm_spec
#print axioms piResultIsProp_run
#print axioms piResultZ_run
#print axioms indBlockCaps_spec
#print axioms projBackGo_runW
#print axioms projFwdGo_runW
#print axioms projBack_specW
#print axioms projFwd_specW
#print axioms checkProjTy_spec

/-! ## Group 2 — the two headline theorems -/

#print axioms checkIndDecl_bridge
#print axioms indSpec_of_bridge

end ConRon.Bridge.Inductives
