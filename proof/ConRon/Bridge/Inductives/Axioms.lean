/-
# `ConRon.Bridge.Inductives.Axioms` — the trust census of the inductive tier

The headline theorem of every module of the uniform route (task #105), each of
which must print `[propext, Classical.choice, Quot.sound]` and nothing else:
no `sorryAx`.  `CoreSpec` never prints — it is a hypothesis of the statements,
as everywhere else in this library.
-/
import ConRon.Bridge.Inductives.Decl

namespace ConRon.Bridge.Inductives

-- the pure-grade leaves
#print axioms nestOcc_spec
#print axioms replaceFVars_spec
#print axioms replaceApps_spec
#print axioms piBinders_spec
#print axioms closeTelescope_spec
-- the recogniser and the pre-pass
#print axioms blockParts?_spec
#print axioms classRead_spec
-- the positivity walk
#print axioms nestPos_spec
#print axioms nestRoot_spec
#print axioms nestSeeds_spec
-- the install's stages
#print axioms checkBlockInds_spec
#print axioms checkBlockCtors_specF
#print axioms checkBlockPositivity_spec
#print axioms consBlockCtors_spec
#print axioms checkSumCtors_specF
#print axioms checkStructProjTable_runF
-- the recursor stage
#print axioms targetMajorOf_spec
#print axioms consBlockRecsTF_spec
#print axioms checkBlockClasses_spec
#print axioms genRecCheck_spec
-- the route, and the tier's theorem
#print axioms checkBlock_envWF
#print axioms checkBlock_bridge
#print axioms checkIndRoute_bridge
#print axioms indSpec_of_bridge

end ConRon.Bridge.Inductives
