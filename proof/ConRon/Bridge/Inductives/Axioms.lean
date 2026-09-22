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

(`structProjPs_spec` is NOT in group 1: it is `structPsAt_spec` through
`structProjPs_eq`, and `structPsAt_spec` is open, so it inherits `sorryAx`
while the arithmetic identification beside it does not.)

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

/-! ## Group 2 — the two headline theorems -/

#print axioms checkIndDecl_bridge
#print axioms indSpec_of_bridge

end ConRon.Bridge.Inductives
