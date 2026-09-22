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

**Six of the seven arms are in group 1 in every sense but one**: they are
proved, and what they still reach is the leaves below them.  The census prints
them in group 2 for that reason.
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
#print axioms reservedBasisNameValues_eq
#print axioms reduceOpNames_run

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

/-! ## Group 2 — the three headline theorems

Each carries `sorryAx` from the tier's open items; neither carries `CoreSpec`
nor `IndSpec`, which are hypotheses of the statement. -/

-- the Core tier's half of `CoreSpec`, discharged by
-- `Bridge/Core/Induction.lean`'s `knot_spec_checkFuel` (which carries
-- `sorryAx` through its six `…Body_spec` walks)
#print axioms CoreSpec.of_knot

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
