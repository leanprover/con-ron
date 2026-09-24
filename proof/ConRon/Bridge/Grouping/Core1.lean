import ConRon.Bridge.Grouping.Misc

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

#erase_foreign_specs

@[scoped spec] theorem liftFueled_keeps (k : EStore) (p : Pins) {α : Type} (w : String) (o : Option α) :
    ⦃fun s => ⌜Inv k p s⌝⦄ liftFueled w o ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  keeps_step liftFueled

#keeps emptyLevels zeroLevel sortOne constE lvlEq? lvlsEq? constTyAt constValAt ruleRhsAt
  unknownConstError projModelName isCtorApp piResultIsProp piResultZ piResultNeverZero
  capsNeverZero isUnitLikeTy unfoldDefinition unfoldableHead headHint sameConstHeads
  natLitToConstructor natIndOk natZeroOk natSuccOk natLitSupported
#keeps_ind constsResolve 1
#keeps litToCtorIfNat rawNatLit?
#keeps_ind strLitConsSpine 3
#keeps strLitToConstructor stringTyOk charTyOk listTyOk listNilTyOk listConsTyOk charOfNatTyOk
  stringOfListTyOk strLitSupported natPredName natAddName natSubName natMulName natPowName
  natBeqName natBleName natDivName natModName natGcdName natLandName natLorName natXorName
  natShiftLeftName natShiftRightName boolName boolTrueName boolFalseName isBoolTrue natOpNames
  natDivModNames natOpDeps natAp1 natAp2 natOpEquations natOpResult
#keeps_ind natOpDepsStored 1
#keeps natOpGuard natOpWfNames
#keeps_ind substConst0 2
#keeps_ind substConstAll 2
#keeps natOpCod natOpTyPinned natOpStoredOk natOpStored natBinOpName reduceNat

end ConRon.Bridge.Grouping
