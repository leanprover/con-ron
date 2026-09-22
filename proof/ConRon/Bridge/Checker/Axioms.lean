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
(3), and each prints `sorryAx` beside the three: the tier's twenty open items
(DESIGN, task #97-P3-Checker's sorry list) are reached from them.  What they
do NOT print is `CoreSpec` or `IndSpec` — those are HYPOTHESES of the
statements, not axioms of the environment, which is exactly the discipline
`proof/ConRon/RefineOld/Main.lean`'s `conron.model_exists` kept with `hk` and
`hind`, and it is what makes "two named hypotheses" a checkable claim rather
than a prose one.
-/
import ConRon.Bridge.Checker.Capstone
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Checker.Split
import ConRon.Bridge.Checker.DeclVal

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

/-! ## Group 2 — the three headline theorems

Each carries `sorryAx` from the tier's open items; neither carries `CoreSpec`
nor `IndSpec`, which are hypotheses of the statement. -/

-- the Core tier's half of `CoreSpec`, discharged by
-- `Bridge/Core/Induction.lean`'s `knot_spec_checkFuel` (which carries
-- `sorryAx` through its six `…Body_spec` walks)
#print axioms CoreSpec.of_knot

#print axioms Arena.checkDecl_bridge
#print axioms Arena.checkDeclsPure_bridge
#print axioms Arena.model_exists
#print axioms Arena.no_proof_of_False
#print axioms Arena.installThenCheck_bridge

end ConRon.Bridge
