import ConRon.Bridge.Grouping.Core1

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

@[spec] theorem iotaCertsAux_keeps (k : EStore) (p : Pins) {r : CoreFnsA} {fe depth lic h acc args i}
    (hr : FnsKeep r) :
    ⦃fun s => ⌜Inv k p s⌝⦄ iotaCertsAux r fe depth lic h acc args i ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  fun_induction iotaCertsAux r fe depth lic h acc args i
  all_goals keeps_step

#keeps iotaCerts
#keeps_ind piResidual 1
@[spec] theorem defEqList_keeps (k : EStore) (p : Pins) {r : CoreFnsA} {fe depth}
    (as bs : List EIdx) (hr : FnsKeep r) :
    ⦃fun s => ⌜Inv k p s⌝⦄ defEqList r fe depth as bs ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction as generalizing bs <;> cases bs <;> keeps_step defEqList
#keeps iotaIndexOk proofIrrel propIrrel
#keeps_ind structEtaProjCerts 8
#keeps_ind towerSlotsAllGo 2
#keeps towerSlotsAll
#keeps_ind recSlotsAllGo 2
#keeps recSlotsAll
#keeps_ind projNodesGo 2
#keeps_ind projAppsGo 4
#keeps etaProjs reservedBasisNames
set_option maxHeartbeats 2000000 in
#keeps structEtaCertWith
#keeps etaCtorShape structEtaCert structUnitCert
  etaCert stuckIrrel etaFabArgs etaFabArgsE IProjEntry.fireOk
#keeps_ind andRescueSlotsGo 5
#keeps andRescueSlots fabScopeOk

@[spec] theorem majorToCtor_keeps (k : EStore) (p : Pins) {mode r fe depth rn major}
    (rules : List IRecRule) (hr : FnsKeep r) :
    ⦃fun s => ⌜Inv k p s⌝⦄ majorToCtor mode r fe depth rn rules major ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  rcases rules with _ | ⟨rl, _ | ⟨rl2, rest⟩⟩ <;> keeps_step majorToCtor

#keeps litMajorToCtor projLitToCtor recRuleKOf
  recRuleEtaOf recRuleBits projFnRule prepareMajor
#keeps_ind substLevelsAt 2
#keeps_ind substParamLevels 2
#keeps_ind instSpinePins 4
#keeps recFireComparands iotaRecAt iotaRec internAppRebuilt
#keeps_ind getAppSpineGo 0
#keeps getAppSpine headAndArgs whnfCoreStuckApp

end ConRon.Bridge.Grouping
