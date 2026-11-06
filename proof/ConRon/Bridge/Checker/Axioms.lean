/-
# `ConRon.Bridge.Checker.Axioms` — the trust census of the checker tier

`Bridge/Axioms.lean` is the spec layer's census; this is the checker and
promotion tiers'.  Two groups, and the distinction is the point of the file.

**Group 1 — the CLOSED results.**  Every one prints
`[propext, Classical.choice, Quot.sound]` and nothing else: no `sorryAx`, and
— the point of the arena's arithmetic packing (DESIGN `### Task #97a`) — no
`bv_decide` axiom.  The
three standard axioms come in through `Std.HashMap`, `Classical` in `Option`'s
lemmas and `Quot` in `String`, which is the same three every tier of this
repository already carries.

**Group 2 — the headline theorems.**  `Arena.checkDecl_bridge`,
`Arena.pooledAccepts_bridge` / `Arena.pooledOleanAccepts_bridge` and their uses at the twin's
pipeline (`Bridge/Stages.lean`).  They print the three standard axioms only,
like group 1 (the capstone's closure, which contains them, is
`sorry`-free).  What they do NOT print is `CoreSpec` or `IndSpec` —
those are HYPOTHESES of the statements, not axioms of the environment, which
is exactly the discipline `proof/ConRon/RefineOld/Main.lean`'s
`conron.model_exists` kept with `hk` and `hind`, and it is what makes "two
named hypotheses" a checkable claim rather than a prose one.

**The seven arms are printed in group 2**, beside the theorem they make up.
-/
module -- shake: keep-all (`#print axioms` stores no constant shake can see)

public import ConRon.Bridge.Checker.Fold
public import ConRon.Bridge.Checker.Base
public import ConRon.Bridge.Checker.Basis
public import ConRon.Bridge.Checker.Pins
public import ConRon.Bridge.Checker.DivMod
public import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Stages
import ConRon.Bridge.Checker.Mono
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.TypePins
import ConRon.Bridge.Checker.Pushes

public section

namespace ConRon.Bridge

/-! ## Group 1 — closed -/

-- the persistent extension and the bracket
#print axioms PExt.refl
#print axioms PExt.trans
#print axioms PExt.of_ext
#print axioms PExt.dropScratch

-- the promotion memo and the frame
#print axioms Pushed.refl
#print axioms Pushed.trans
#print axioms Pushed.push

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

/-! ### The bracket, the `AM` reading layer, the index and the pin tables -/

-- the bracket's OPENING step, and the eight congruences under it
#print axioms EStore.view_bracket
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
#print axioms AM.ite_ok
#print axioms AM.pure_ok
#print axioms AM.dguard_ok
#print axioms AM.dunless_ok
#print axioms AM.pure_bind_ok

-- the two `IFEnv.push` lemmas, and what a push denotes
#print axioms IFEnvCoh.push
#print axioms denoteFEnv_push

-- the index spec across a drop, which takes `IFEnvOK_of_denote` off the
-- critical path
#print axioms PersIFEnv.find
#print axioms IFEnvOK.pmono
#print axioms denoteCIList_mono
#print axioms denoteFEnv_mono

-- `StepOK`: the invariant at an index a step has just
-- extended, and the three ways it moves.  `FoldOK` is `StepOK` plus the two
-- persistence clauses, and the rule is that only a fold-step BOUNDARY may
-- conclude the latter.
#print axioms StepOK.mono
#print axioms FoldOK.toStepOK

-- the name-shape guards and the handle/name comparison they cash
#print axioms denoteNList_contains
#print axioms beq_handle_iff
#print axioms nameNodup_spec

-- the pin readers and the nineteen reserved names
#print axioms pinAt_run
#print axioms reservedBasisNames_run

-- the sibling pin-table walks, in
-- `reservedBasisNames_run`'s no-accumulator shape

-- the pinned-block comparison's two entry points
#print axioms internNNode_run
#print axioms canonNamesGo_run
#print axioms canonNames_run
#print axioms denoteCIList_cons
#print axioms reservedBasisNameValues_eq
#print axioms reduceOpNames_run

-- the level tier's readers and inversions, and the whole lockstep `canon`
-- comparison
#print axioms view_run
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
#print axioms denoteCI_defn_inv
#print axioms denoteCI_thm_inv
#print axioms denoteCI_ind_inv
#print axioms denoteCI_rec_inv

-- the two memoised DAG walks of the front door
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
#print axioms valueGuards_bridge

-- the readback facts `Base.lean` reads
#print axioms beq_handle_iff

-- **THE DECLARATION FRONT DOOR**
#print axioms denoteCV_inv
#print axioms denoteCIList_get
#print axioms denoteEList_cons
#print axioms natOpName_run
#print axioms natIndOk_optRun
#print axioms natZeroOk_optRun
#print axioms natSuccOk_optRun
#print axioms litShapeOk_run
#print axioms checkConstantVal_pure
#print axioms checkConstantVal_bridge
#print axioms checkConstantVal_bridge_of_fold
#print axioms checkConstantVal_mono

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
#print axioms checkDecl_opaque_pure
#print axioms checkDecl_opaque_pin_pure
#print axioms checkDecl_axiom_quotSound_pure
#print axioms checkDecl_axiom_std_pure
#print axioms checkDecl_axiom_trust_pure
#print axioms checkDecl_axiom_ofReduce_pure
#print axioms checkDecl_axiom_sorryAx_pure

-- The index's spec (`IFEnvOK_of_denote`, `IFEnvOK_restrictTo`), the whole
-- `canon` comparison, and the recurrence certifier.

-- the index IS the list: con-leche's `mkFEnv_find?` at the arena's hash map

-- the bounded view, and `Env.prefixTo`: con-leche's `idxBelow_eq`
#print axioms denoteCIList_mem
#print axioms denoteCIList_length

-- the canonical-form comparison
#print axioms denoteNList_inj
#print axioms IConstantInfo.canonEq_run
#print axioms canonEqList_run

-- the recurrence certifier
#print axioms EqPairsDenote.mono
#print axioms certifyNatEqs_cons_pure
#print axioms certifyNatEqs_bridge_aux
#print axioms certifyNatEqs_bridge

-- `EnvWF` at a push, and the three value checks that stand on it.

-- the `IFEnv.push` family: the index, and the whole step invariant
#print axioms IFEnvOK.push
#print axioms IFEnvOK.pushTable
#print axioms IFEnvOK.congr_lookup
#print axioms IFEnvOK.findTable_isSome
#print axioms IFEnvOK.pushStored
#print axioms TablesStored.of_envWF
#print axioms TablesStored.cons
#print axioms StepOK.push

-- `ConstWF` at an install: the type half (a hypothesis, read off the front
-- door's own pure run), the value half (`valueGuards_bridge`),
-- and the three introductions
#print axioms CVTypeWF.cons
#print axioms checkConstantVal_typeWF
#print axioms constWF_defnInfo
#print axioms constWF_thmInfo
#print axioms constWF_axiomInfo

-- the three value checks
#print axioms checkDefnVal_pure
#print axioms checkThmVal_pure
#print axioms checkOpaqueVal_pure
#print axioms checkDefnVal_bridge
#print axioms checkThmVal_bridge
#print axioms checkOpaqueVal_bridge

-- the gates' push-and-pop
#print axioms IFEnv.sameView_popTemp
#print axioms checkStructuralNatPinAtFe2_bridge
#print axioms checkStructuralNatPin_bridge

-- the check half of the install/check seam, on the same machinery

-- `Bridge/Checker/Basis.lean`, behind the frontend's scratch-agnostic
-- intern family: the interned blocks, the name test, the renaming, the
-- block's and the quotient record's comparison with the pin, and the checks.

-- `Arena/Intern.lean`'s fresh-memo wrappers
#print axioms internCI_fresh
#print axioms internCV_fresh

-- the pinned blocks, interned, and the name test
#print axioms BasisKind.decls_run
#print axioms denoteCIList_names
#print axioms basisNameHitGo_run
#print axioms basisNameHit_run

-- injectivity: a handle equality is a value equality
#print axioms ConstantVal.beqP_eq
#print axioms ConstantInfo.beqP_eq
#print axioms denoteCV_inj
#print axioms denoteCaps_inj
#print axioms denoteRule_inj
#print axioms denoteRules_inj
#print axioms denoteCI_inj

-- the renaming
#print axioms readNamesM_run
#print axioms readLevelM_run
#print axioms instLPFast_run
#print axioms paramLevels_run
#print axioms substLevelsAt_run
#print axioms IConstantVal.atLps_run
#print axioms IRecRuleFire.atLps_run
#print axioms rulesAtLps_run
#print axioms IConstantInfo.atLps_run

-- the comparison with the pin
#print axioms pinAgrees_eq
#print axioms pinCopyOk_run
#print axioms pinLinkOk_run
#print axioms constNamed_rel
#print axioms rulesLinkOk_run
#print axioms blockLinkOkAt_run
#print axioms blockLinksOk_run
#print axioms pinCopiesOk_run
#print axioms pinListOk_run

-- what a pinned block and a quotient record store, and the checks
#print axioms BasisKind.atBlock_run
#print axioms quotPin_run
#print axioms quotAt_run
#print axioms quotPinHit_run
#print axioms quotPredsOk_run
#print axioms installBasisDecls_bridge
#print axioms checkBasisBlock_bridge
#print axioms checkQuotRecord_bridge
#print axioms checkDecl_bridge_quot

-- the pin checks, the reduce-pin gate and the install/check seam's pieces
#print axioms matchesPin_run
#print axioms IFEnvOK.find_beq_ind
#print axioms eqStored_run
#print axioms reduceElemOk_run
#print axioms reduceStoredOk_run
#print axioms stdAxiomOk_run
#print axioms trustCompilerOk_run
#print axioms ofReduceAxOk_run
#print axioms andPinOk_run
#print axioms natLitSupported_run
#print axioms natOpDepsStored_run
#print axioms natOpGuard_run
#print axioms natOpStoredOkAll_run
#print axioms natOpEqs_wscoped
#print axioms reduceDeclPin_run
#print axioms reduceCertVar_run
#print axioms reducePinGuard_run
#print axioms checkReducePinPre_bridge
#print axioms checkReducePin_bridge
#print axioms reservedBasisNames_sstep
#print axioms natOpEquations_run
#print axioms substConst0Pairs_run

/-! ## Group 2 — the three headline theorems

None carries `sorryAx`; none carries `CoreSpec` nor `IndSpec`, which are
hypotheses of the statement. -/

-- the Core tier's half of `CoreSpec`, discharged by
-- `Bridge/Core/Induction.lean`'s `knot_spec_checkFuel`
#print axioms CoreSpec.of_knot


#print axioms checkDecl_bridge_defn
#print axioms checkDecl_bridge_thm
#print axioms checkDecl_bridge_opaque
#print axioms checkDecl_bridge_axiom
#print axioms checkDecl_bridge_ind
#print axioms checkDecl_bridge_quot
#print axioms Arena.checkDecl_bridge

-- the fold's skeleton and the startup walk
#print axioms internReservedPins_run
#print axioms internAllPins_run

-- the fold's children (each prints the three standard axioms)
#print axioms checkShapeless_ne_ok
#print axioms checkDecl_pushes
#print axioms checkDecl_fresh
#print axioms denoteN_default_of_pinNames
#print axioms internPinSets_run
-- `installStep_split`'s bracket; it reaches `Arena.checkDecl_wfProj` through
-- `Arena.installStepGo_full`
-- `checkDivModPin_bridge` and its loop
#print axioms checkDivModPinLoop_bridge
#print axioms checkDivModPinAtFe2_bridge
#print axioms checkDivModPin_bridge

-- `DeclOut`'s two clauses (each prints the three standard axioms)
#print axioms divModEnvGuard_run
#print axioms divModPinGuard_run
#print axioms substConstAll_run
-- `Arena.checkDecl_wfProj` reaches `IndSpec.wf` (the Inductives tier's
-- hypothesis) and the arms' own leaves
-- the divMod gate's last two pieces; `checkDivModPin_bridge` reaches only the
-- Core tier's leaves
#print axioms divModCertStmts_run
#print axioms divModCertsGuard_run
#print axioms checkDivModCerts_bridge_aux
#print axioms checkDivModPinAt_bridge
-- the type pins (`Bridge/Checker/TypePins.lean`)
#print axioms typePinStored_spec
#print axioms typePinsGuard_spec
#print axioms checkTypePins_spec

-- the check phase (`Bridge/Checker/Pooled.lean`, `PooledOleans.lean`, `Pool.lean`)
#print axioms pooled_fold
#print axioms pooled_fold_records
#print axioms pooled_fold_oleans
#print axioms Arena.pooledAccepts_bridge
#print axioms Arena.pooledOleanAccepts_bridge
-- the twin's pipeline (`Bridge/Stages.lean`)
#print axioms stages_model
#print axioms stages_no_False
#print axioms stagesO_model
#print axioms stagesO_no_False

end ConRon.Bridge
