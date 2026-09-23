/-
# `ConRon.Bridge.Checker.Axioms` — the trust census of the checker tier

`Bridge/Axioms.lean` is the spec layer's census; this is the checker and
promotion tiers'.  Two groups, and the distinction is the point of the file.

**Group 1 — the CLOSED results.**  Every one prints
`[propext, Classical.choice, Quot.sound]` and nothing else: no `sorryAx`, and
— the point of task #97a's arithmetic packing — no `bv_decide` axiom.  The
three standard axioms come in through `Std.HashMap`, `Classical` in `Option`'s
lemmas and `Quot` in `String`, which is the same three every tier of this
repository already carries.

**Group 2 — the three headline theorems.**  `Arena.checkDecl_bridge`,
`Arena.checkDeclsPure_bridge` and `Arena.model_exists` are the deliverable's
(3), and each prints `sorryAx` beside the three: the tier's open items
(DESIGN, task #97-P3-Checker's sorry list as task #97-P3-Checker-2 leaves it)
are reached from them.  What they do NOT print is `CoreSpec` or `IndSpec` —
those are HYPOTHESES of the statements, not axioms of the environment, which
is exactly the discipline `proof/ConRon/RefineOld/Main.lean`'s
`conron.model_exists` kept with `hk` and `hind`, and it is what makes "two
named hypotheses" a checkable claim rather than a prose one.

**All seven arms are in group 1 in every sense but one**: they are proved, and
what they still reach is the leaves below them.  The census prints them in
group 2 for that reason.
-/
import ConRon.Bridge.Checker.Capstone
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Checker.Split
import ConRon.Bridge.Checker.DeclVal
import ConRon.Bridge.Checker.Arms

namespace ConRon.Bridge

/-! ## Group 1 — closed -/

-- the persistent extension and the bracket
#print axioms PExt.refl
#print axioms PExt.trans
#print axioms PExt.of_ext
#print axioms PExt.dropScratch

-- the promotion memo and the frame
#print axioms PMemoOK.empty
#print axioms PMemoOK.mono
#print axioms PFrame.refl
#print axioms PFrame.trans
#print axioms Pushed.refl
#print axioms Pushed.trans
#print axioms Pushed.push
#print axioms StoreWFP.of_wf

-- the declaration layer across a drop
#print axioms denoteN_pext
#print axioms denoteL_pext
#print axioms denoteLs_pext
#print axioms denoteE_pext
#print axioms denoteNList_pext
#print axioms denoteLList_pext
#print axioms denoteEList_pext
#print axioms denoteEArray_pext
#print axioms denoteCV_pext
#print axioms denoteFire_pext
#print axioms denoteRule_pext
#print axioms denoteRules_pext
#print axioms denoteCaps_pext
#print axioms denoteProjTable_pext
#print axioms denoteCI_pext
#print axioms denoteCIList_pext
#print axioms denoteFEnv_pext
#print axioms denoteDecl_pext
#print axioms denoteDecls_pext

-- the pin table across a drop
#print axioms denoteNL_pext
#print axioms PinsOK.pmono
#print axioms PersPins.mono
#print axioms PinsDenote.mono
#print axioms PinsDenote.pmono

-- the core step's composition
#print axioms CoreStep.refl
#print axioms CoreStep.trans

-- **one fuel for the whole fold** — con-leche's `FueledM` monotonicity,
-- reached through `checkDecl_datF`
#print axioms checkDecl_mono

-- the `AM` do-block, and the bracket's three equations
#print axioms AM.bind_apply
#print axioms AM.bind_ok
#print axioms flushCaches_run
#print axioms enterScratch_run
#print axioms dropScratch_run

-- the variant fallback
#print axioms orElseAttempt_run
#print axioms orElseStepOf_ok_iff

/-! ### Task #97-P3-Checker-2's own additions -/

-- the bracket's OPENING step (item 21), and the eight congruences under it
#print axioms EStore.view_bracket
#print axioms EStore.viewBM_bracket
#print axioms denoteN_bracket
#print axioms denoteL_bracket
#print axioms denoteLs_bracket
#print axioms denoteE_bracket
#print axioms PExt.enterScratch

-- the `AM` reading layer: a do-block guard, read backwards
#print axioms fail_apply
#print axioms AM.Never.fail
#print axioms AM.Never.bind
#print axioms AM.Never.of_bind_left
#print axioms AM.Never.fail_any
#print axioms AM.readFail_ne
#print axioms AM.ite_ok
#print axioms AM.pure_ok
#print axioms AM.dguard_ok
#print axioms AM.dunless_ok
#print axioms AM.pure_bind_ok

-- the two `IFEnv.push` lemmas (task #97-P3-Ind §8), and what a push denotes
#print axioms IFEnvCoh.push
#print axioms denoteFEnv_push

-- the index spec across a drop, which takes `IFEnvOK_of_denote` off the
-- critical path
#print axioms PersIFEnv.find
#print axioms IFEnvOK.pmono
#print axioms denoteCIList_mono
#print axioms denoteFEnv_mono

-- `StepOK` (task #97-P3-Checker-3): the invariant at an index a step has just
-- extended, and the three ways it moves.  `FoldOK` is `StepOK` plus the two
-- persistence clauses, and the rule is that only a fold-step BOUNDARY may
-- conclude the latter.
#print axioms StepOK.mono
#print axioms StepOK.pmono
#print axioms FoldOK.toStepOK

-- the name-shape guards (item 10) and the handle/name comparison they cash
#print axioms denoteNList_contains
#print axioms beq_handle_iff
#print axioms nameNodup_spec
#print axioms viewN_run
#print axioms isProjFnShape_run

-- the pin readers and the nineteen reserved names (part of item 13)
#print axioms pinAt_run
#print axioms internName_run
#print axioms denoteNL_snoc
#print axioms reservedBasisNames_run

-- the sibling pin-table walks (task #97-P3-Checker-3), in
-- `reservedBasisNames_run`'s no-accumulator shape
#print axioms natOpNames_run
#print axioms natDivModNames_run
#print axioms natOpDeps_run

-- the pinned-block comparison's two closed entry points (task
-- #97-P3-Checker-3)
#print axioms internNNode_run
#print axioms canonNamesGo_run
#print axioms canonNames_run
#print axioms denoteCIList_cons
#print axioms reservedBasisNameValues_eq
#print axioms reduceOpNames_run

-- the level tier's readers and inversions, and the whole lockstep `canon`
-- comparison (task #97-P3-Checker round 4)
#print axioms viewE_run
#print axioms viewL_run
#print axioms viewLs_run
#print axioms denoteL_view_eq
#print axioms denoteL_zero_inv
#print axioms denoteL_succ_inv
#print axioms denoteL_max_inv
#print axioms denoteL_imax_inv
#print axioms denoteL_param_inv
#print axioms denoteNList_length
#print axioms denoteNList_get
#print axioms canonFindIdx_denote
#print axioms canonNameMap_denote
#print axioms CanonMapD.mono
#print axioms canonLevelEq_run
#print axioms denoteLList_cons
#print axioms canonLevelListEq_run
#print axioms denoteLs_view_inv
#print axioms canonLevelsEq_run
#print axioms canonExprEq_run
#print axioms denoteEList_inj
#print axioms denoteFire_inj
#print axioms denoteRule_inv
#print axioms denoteRules_cons
#print axioms canonRuleHead_eq
#print axioms canonRulesEq_run
#print axioms IConstantVal.canonEq_run
#print axioms denoteCI_axiom_inv
#print axioms denoteCI_ctor_inv
#print axioms denoteCI_proj_inv
#print axioms denoteCI_defn_inv
#print axioms denoteCI_thm_inv
#print axioms denoteCI_ind_inv
#print axioms denoteCI_rec_inv

-- the two memoised DAG walks of the front door (task #97-P3-Checker round 4),
-- which is what takes `Bridge/Checker/Base.lean` to zero
#print axioms readNames_run
#print axioms readLevel_run
#print axioms readLevels_run
#print axioms LPDMemoOK.empty
#print axioms LPDMemoOK.insert
#print axioms allLevelParamsDefinedGo_run
#print axioms allLevelParamsDefined_run
#print axioms IFEnvOK.find_isSome
#print axioms constsResolve_run
#print axioms CRMemoOK.empty
#print axioms CRMemoOK.insert
#print axioms constsResolveFGo_run
#print axioms constsResolveFFast_run

-- the install half of the front door, and the pinned-constant install
#print axioms installConstantVal_pure
#print axioms installConstantVal_bridge
#print axioms installValue_pure
#print axioms installValue_bridge
#print axioms installBasisDecl_bridge

-- the readback facts that moved down out of `Base.lean` (round 4)
#print axioms beq_handle_iff

-- **THE DECLARATION FRONT DOOR** (item 11) and the three list checks (item 12)
#print axioms denoteCV_inv
#print axioms denoteCIList_get
#print axioms denoteEList_cons
#print axioms checkConstantVal_pure
#print axioms checkTypedList_mono
#print axioms checkAnnotList_mono
#print axioms checkDefEqList_mono
#print axioms checkConstantVal_mono
#print axioms checkTypedList_cons_pure
#print axioms checkAnnotList_cons_pure
#print axioms checkDefEqList_cons_pure

-- one fuel per arm
#print axioms checkDefnVal_mono
#print axioms checkThmVal_mono
#print axioms checkOpaqueVal_mono
#print axioms certifyNatEqs_mono
#print axioms checkDivModPin_mono
#print axioms checkReducePin_mono

-- the arms' own plumbing, and con-leche's clauses as step lemmas
#print axioms FoldOK.step
#print axioms FoldOK.ofCore
#print axioms checkDecl_thm_pure
#print axioms checkDecl_basis_pure
#print axioms checkDecl_quot_type_pure
#print axioms checkDecl_quot_other_pure
#print axioms checkDecl_ind_basis_pure
#print axioms checkDecl_opaque_pure
#print axioms checkDecl_opaque_pin_pure
#print axioms checkDecl_axiom_quotSound_pure
#print axioms checkDecl_axiom_std_pure
#print axioms checkDecl_axiom_trust_pure
#print axioms checkDecl_axiom_ofReduce_pure
#print axioms checkDecl_axiom_sorryAx_pure

-- **ROUND 5.**  The index retired (`IFEnvOK_of_denote`, `IFEnvOK_restrictTo`),
-- the whole `canon` comparison, and the recurrence certifier.

-- the index IS the list: con-leche's `mkFEnv_find?` at the arena's hash map
#print axioms mkIFEnvGo_fst
#print axioms mkIFEnvGo_snd
#print axioms mkIFEnvGo_lt
#print axioms mkIFEnvGo_mem
#print axioms mkIFEnv_find?
#print axioms IFEnvCoh.find?
#print axioms IFEnv.find?_mem
#print axioms denoteCIList_find?
#print axioms IFEnvOK_of_denote

-- the bounded view, and `Env.prefixTo`: con-leche's `idxBelow_eq`
#print axioms IFEnv.restrictTo_find?_le
#print axioms mkIFEnvGo_below
#print axioms mkIFEnvGo_below_of
#print axioms denoteCIList_mem
#print axioms denoteCIList_drop
#print axioms denoteCIList_length
#print axioms denoteCIList_nodup
#print axioms IFEnvOK_restrictTo

-- the `.projInfo` comparison, and the two injectivity facts it needed
#print axioms denoteNList_inj
#print axioms denoteEArray_inj
#print axioms denoteProjTable_inj
#print axioms IConstantInfo.canonEq_run
#print axioms canonEqList_run

-- the recurrence certifier
#print axioms EqPairsDenote.mono
#print axioms certifyNatEqs_cons_pure
#print axioms certifyNatEqs_bridge_aux
#print axioms certifyNatEqs_bridge

-- **ROUND 6.**  `EnvWF` at a push — the one theorem round 5 scheduled — and
-- the three value checks that stand on it.

-- the `IFEnv.push` family: the index, and the whole step invariant
#print axioms IFEnvOK.push
#print axioms StepOK.push

-- `ConstWF` at an install: the type half (a hypothesis, read off the front
-- door's own pure run), the value half (con-leche's `installValue_inv` plus
-- `annotateCore`'s two preservation lemmas), and the three introductions
#print axioms CVTypeWF.cons
#print axioms checkConstantVal_typeWF
#print axioms installValue_valueWF
#print axioms constWF_defnInfo
#print axioms constWF_thmInfo
#print axioms constWF_axiomInfo

-- the three value checks
#print axioms checkDefnVal_bridge
#print axioms checkThmVal_bridge
#print axioms checkOpaqueVal_bridge

-- the check half of the install/check seam, on the same machinery
#print axioms checkValueGroup_bridge

-- **ROUND 7.**  `Bridge/Checker/Basis.lean`, behind the frontend round's
-- scratch-agnostic intern family: the two interned blocks, the two
-- recognisers and the block install.

-- `Arena/Intern.lean`'s fresh-memo wrappers, and `toConstantVal` without a
-- scratch flag (the tier's fifth `.projInfo` site)
#print axioms internCI_fresh
#print axioms internCV_fresh
#print axioms toConstantVal_sstep

-- the pinned blocks, interned
#print axioms BasisKind.decls_run
#print axioms BasisKind.declsA_run
#print axioms BasisKind.decls_proj

-- no pinned block declares a projection table, so the tier's standing
-- `.projInfo` hypothesis is DISCHARGED at the basis route rather than carried
#print axioms basis_declsA_no_proj
#print axioms basis_decls_no_proj
#print axioms basis_decls_name_not_num
#print axioms canon_isTowerEntry
#print axioms ci_ne_proj_of_denote
#print axioms noTable_of_names
#print axioms noTable_of_canon

-- the two recognisers and the block install
#print axioms denoteCIList_names
#print axioms basisPinHitGo_run
#print axioms basisPinHit_run
#print axioms quotPinHit_run
#print axioms installBasisDecls_bridge
#print axioms checkBasisDecl_bridge

-- task #97-P3-Checker round 8
#print axioms erasePwEq_run
#print axioms matchesPin_run
#print axioms denoteCV_inj
#print axioms denoteCI_inj_ind
#print axioms IFEnvOK.find_beq_ind
#print axioms reduceElemOk_run
#print axioms reduceStoredOk_run
#print axioms stdAxiomOk_run
#print axioms trustCompilerOk_run
#print axioms ofReduceAxOk_run
#print axioms natLitSupported_run
#print axioms natOpDepsStored_run
#print axioms natOpGuard_run
#print axioms natOpStoredOkAll_run
#print axioms natOpEqs_wscoped
#print axioms reduceDeclPin_run
#print axioms reduceCertVar_run
#print axioms reducePinGuard_run
#print axioms checkReducePin_bridge
#print axioms reservedBasisNames_sstep

/-! ## Group 2 — the three headline theorems

Each carries `sorryAx` from the tier's open items; neither carries `CoreSpec`
nor `IndSpec`, which are hypotheses of the statement. -/

-- the Core tier's half of `CoreSpec`, discharged by
-- `Bridge/Core/Induction.lean`'s `knot_spec_checkFuel` (which carries
-- `sorryAx` through its six `…Body_spec` walks)
#print axioms CoreSpec.of_knot

#print axioms checkDecl_defn_pure_nn
#print axioms checkDecl_defn_pure_nd
#print axioms checkDecl_defn_pure_yn
#print axioms checkDecl_defn_pure_yy

#print axioms checkDecl_bridge_defn
#print axioms checkDecl_bridge_thm
#print axioms checkDecl_bridge_opaque
#print axioms checkDecl_bridge_axiom
#print axioms checkDecl_bridge_basis
#print axioms checkDecl_bridge_ind
#print axioms checkDecl_bridge_quot
#print axioms Arena.checkDecl_bridge
#print axioms Arena.checkDeclsPure_bridge
#print axioms Arena.model_exists
#print axioms Arena.no_proof_of_False
#print axioms Arena.installThenCheck_bridge

end ConRon.Bridge
