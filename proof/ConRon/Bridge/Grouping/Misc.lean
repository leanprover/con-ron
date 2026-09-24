import ConRon.Bridge.Grouping.ExprOps

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

#erase_foreign_specs

#keeps pinAt
#keeps pinReserved pinEmptyLevels pinZeroLevel pinSortOne pinEq pinPUnit pinPUnitRec pinNat pinNatZero pinNatSucc pinQuotSound pinString pinStringOfList pinList pinListNil pinListCons pinChar pinAnd pinCharOfNat pinSorryAx pinNatPred pinNatAdd pinNatSub pinNatMul pinNatPow pinNatBeq pinNatBle pinNatDiv pinNatMod pinNatGcd pinNatLand pinNatLor pinNatXor pinNatShiftLeft pinNatShiftRight pinBool pinBoolTrue pinBoolFalse pinPropext pinChoice pinIff pinIffIntro pinIffRec pinNonempty pinNonemptyIntro pinNonemptyRec pinTrue pinTrueIntro pinTrustCompiler pinReduceNat pinReduceBool pinOfReduceNat pinOfReduceBool 

#keeps projFnName projTableName IConstantInfo.toConstantVal IConstantInfo.type
  IEnv.findProj? IFEnv.findProj?
#keeps_ind piSortTeleLen?

#keeps_ind peelNeverPis
#keeps_ind numArgs
#keeps residualPW
#keeps_ind headTypePW 2
#keeps typeSortPW
#keeps_ind headProofPW 2
#keeps proofPW notProofFast isProofFast

#keeps_ind mentionsConstGo 2
#keeps mentionsConst

end ConRon.Bridge.Grouping
