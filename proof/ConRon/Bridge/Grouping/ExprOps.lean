import ConRon.Bridge.Grouping.Monad

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

#erase_foreign_specs

#keeps internRebuilt internRebuiltBVar internRebuiltFVar internRebuiltSort internRebuiltConst
  internRebuiltApp internRebuiltLam internRebuiltForallE internRebuiltLetE internRebuiltLit
  internRebuiltProj internRebuiltBind internRebuiltBindI instListCutoff instantiate1ArmBVar

#keeps_fuel instantiate1Go [instantiate1ArmApp, instantiate1ArmBind, instantiate1ArmLet,
  instantiate1ArmProj]
#keeps instantiate1ArmApp instantiate1ArmBind instantiate1ArmLet instantiate1ArmProj
  instantiate1Fast

#keeps_fuel instantiateList [instListArmApp, instListArmBind, instListArmLet, instListArmProj,
  instListArmBVar]
#keeps instListArmApp instListArmBind instListArmLet instListArmProj instListArmBVar
#keeps_fuel instantiateListGo [instListGoArmApp, instListGoArmBind, instListGoArmLet,
  instListGoArmProj]
#keeps instListGoArmApp instListGoArmBind instListGoArmLet instListGoArmProj instantiateListFast

#keeps_fuel liftLooseBVarsGo [liftArmApp, liftArmLam, liftArmForallE, liftArmLet, liftArmProj]
#keeps liftArmApp liftArmLam liftArmForallE liftArmLet liftArmProj liftLooseBVarsFast

#keeps_fuel resetMetaGo [resetArmFVar, resetArmApp, resetArmLam, resetArmForallE, resetArmLet,
  resetArmProj]
#keeps resetArmFVar resetArmApp resetArmLam resetArmForallE resetArmLet resetArmProj resetMetaFast

#keeps_fuel sizeB [sizeBArmApp, sizeBArmBind, sizeBArmLet, sizeBArmProj]
#keeps sizeBArmApp sizeBArmBind sizeBArmLet sizeBArmProj

#keeps_fuel abstractRange [absRangeArmApp, absRangeArmLam, absRangeArmForallE, absRangeArmLet,
  absRangeArmProj]
#keeps absRangeArmApp absRangeArmLam absRangeArmForallE absRangeArmLet absRangeArmProj

#keeps_fuel sizeF [sizeFArmFVar, sizeFArmApp, sizeFArmBind, sizeFArmLet, sizeFArmProj]
#keeps sizeFArmFVar sizeFArmApp sizeFArmBind sizeFArmLet sizeFArmProj

#keeps_fuel fvarLeaves [fvarLeavesArmFVar, fvarLeavesArmApp, fvarLeavesArmBind, fvarLeavesArmLet]
#keeps fvarLeavesArmFVar fvarLeavesArmApp fvarLeavesArmBind fvarLeavesArmLet

#keeps_fuel wscopedB [wscopedBArmApp, wscopedBArmBind, wscopedBArmLet]
#keeps wscopedBArmApp wscopedBArmBind wscopedBArmLet

#keeps_fuel wscopedBGo [wscopedBGoArmApp, wscopedBGoArmBind, wscopedBGoArmLet]
#keeps wscopedBGoArmApp wscopedBGoArmBind wscopedBGoArmLet wscopedBFast

#keeps_fuel fvarLeavesGo [fvarLeavesGoArmApp, fvarLeavesGoArmBind, fvarLeavesGoArmLet]
#keeps fvarLeavesGoArmApp fvarLeavesGoArmBind fvarLeavesGoArmLet fvarLeavesFast

#keeps_fuel leavesSubGo [leavesSubArmApp, leavesSubArmBind, leavesSubArmLet]
#keeps leavesSubArmApp leavesSubArmBind leavesSubArmLet leafGuard

#keeps_fuel looseBVarsBounded [looseBArmApp, looseBArmBind, looseBArmLet]
#keeps looseBArmApp looseBArmBind looseBArmLet isLam lamPw forallPw

#keeps_fuel hasFvar [hasFvarArmApp, hasFvarArmBind, hasFvarArmLet]
#keeps hasFvarArmApp hasFvarArmBind hasFvarArmLet

#keeps_ind getAppFn
#keeps_ind getAppArgs
#keeps_ind mkAppN 1

@[scoped spec] theorem mkAppNFrom_keeps (k : EStore) (p : Pins) (f : EIdx) (args : Array EIdx) (i : Nat) :
    ⦃fun s => ⌜Inv k p s⌝⦄ mkAppNFrom f args i ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  fun_induction mkAppNFrom f args i
  all_goals keeps_step mkAppNFrom

#keeps_fuel renameConstsGo [renameArmFVar, renameArmApp, renameArmLam, renameArmForallE,
  renameArmLet, renameArmProj]
#keeps renameArmFVar renameArmApp renameArmLam renameArmForallE renameArmLet renameArmProj
  renameConstsFast

#keeps_ind stripLams
#keeps_ind stripPis
#keeps_ind piResult
#keeps_ind instPis 2
#keeps_ind instPisAt 1
#keeps_ind instLamsAt 1
#keeps_ind instPisAtFGo 2
#keeps instPisAtF
#keeps_ind instLamsAtFGo 2
#keeps instLamsAtF fvarTypeD
#keeps_ind instSpine 1
#keeps_ind bvarRange 1
#keeps recRulePlain
#keeps_ind pisToLams
#keeps_ind replacePiBody
#keeps_ind piArity
#keeps_ind resultSort

#keeps_fuel bvarBoundGo [bvarBoundArmApp, bvarBoundArmBind, bvarBoundArmLet]
#keeps bvarBoundArmApp bvarBoundArmBind bvarBoundArmLet bvarBoundMemo

#keeps_fuel fvarRangeGo [fvarRangeArmApp, fvarRangeArmBind, fvarRangeArmLet]
#keeps fvarRangeArmApp fvarRangeArmBind fvarRangeArmLet fvarRangeMemo bvarB fvarB hasFvarFast
  looseBVarsBoundedFast abstract1ArmFVar

#keeps_fuel abstract1Go [abstract1ArmApp, abstract1ArmBind, abstract1ArmLet, abstract1ArmProj]
#keeps abstract1ArmApp abstract1ArmBind abstract1ArmLet abstract1ArmProj abstract1Fast
  absRangeArmFVar

#keeps_fuel abstractRangeGo [absRangeGoArmApp, absRangeGoArmBind, absRangeGoArmLet,
  absRangeGoArmProj]
#keeps absRangeGoArmApp absRangeGoArmBind absRangeGoArmLet absRangeGoArmProj abstractRangeFast

#keeps_fuel lowerBVarsGo [lowerArmApp, lowerArmLam, lowerArmForallE, lowerArmLet, lowerArmProj]
#keeps lowerArmApp lowerArmLam lowerArmForallE lowerArmLet lowerArmProj lowerBVarsFast

#keeps_fuel instantiate1LiftGo [inst1LiftArmApp, inst1LiftArmLam, inst1LiftArmForallE,
  inst1LiftArmLet, inst1LiftArmProj]
#keeps inst1LiftArmApp inst1LiftArmLam inst1LiftArmForallE inst1LiftArmLet inst1LiftArmProj
  instantiate1LiftFast
#keeps_ind instPisAtLift 1
#keeps LIdx.hasParam EIdx.hasLevelParam substLMemoAt substLsMemoAt

#keeps_fuel instLPGo [instLPArmFVar, instLPArmApp, instLPArmLam, instLPArmForallE, instLPArmLet,
  instLPArmProj]
#keeps instLPArmFVar instLPArmApp instLPArmLam instLPArmForallE instLPArmLet instLPArmProj
  instLPFast

end ConRon.Bridge.Grouping
