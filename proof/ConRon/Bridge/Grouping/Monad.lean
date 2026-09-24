import ConRon.Bridge.Grouping.Gen

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

@[spec] theorem fail_keeps (k : EStore) (p : Pins) {α : Type} (e : CheckError) :
    ⦃fun s => ⌜Inv k p s⌝⦄ (fail e : AM α) ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  intro _ _; trivial

@[spec] theorem failDanglingE_keeps (k : EStore) (p : Pins) {α : Type} :
    ⦃fun s => ⌜Inv k p s⌝⦄ (failDanglingE : AM α) ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  intro _ _; trivial

@[spec] theorem failDanglingLs_keeps (k : EStore) (p : Pins) {α : Type} :
    ⦃fun s => ⌜Inv k p s⌝⦄ (failDanglingLs : AM α) ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  intro _ _; trivial

#keeps view derivedE internBME internLamIE internForallEIE internNodeE
#keeps internE viewApp viewBVar viewSort viewConst
  viewConstName viewFVarIdx viewFVarTy viewLit viewBind viewBindI viewBM viewLet viewProj
#keeps internBVarE internFVarE internSortE internConstE internAppE internLamE
  internForallEE internLetEE internLitE internProjE internBindIE
#keeps viewN internNNode readName viewL derivedL internLNode readLevel viewLs
  internLsNode readLevels viewLsLen readLevelM readNameM readLevelsM
#keeps inst1Get inst1Set inst1Clear instLGet instLSet instLClear liftGet liftSet
  liftClear resetGet resetSet resetClear renameGet renameSet renameClear abs1Get
  abs1Set abs1Clear lowerGet lowerSet lowerClear inst1LGet inst1LSet inst1LClear
  instLPGet instLPSet instLPClear instLPLGet instLPLSet instLPLsGet instLPLsSet
  bvarBGet bvarBSet bvarBClear fvarBGet fvarBSet fvarBClear

@[spec] theorem readNames_keeps (k : EStore) (p : Pins) (hs : List NIdx) :
    ⦃fun s => ⌜Inv k p s⌝⦄ readNames hs ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction hs with
  | nil => mvcgen [readNames]
  | cons h hs ih => mvcgen [readNames, ih]

@[spec] theorem readNamesM_keeps (k : EStore) (p : Pins) (hs : List NIdx) :
    ⦃fun s => ⌜Inv k p s⌝⦄ readNamesM hs ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction hs with
  | nil => mvcgen [readNamesM]
  | cons h hs ih => mvcgen [readNamesM, ih]

@[spec] theorem internName_keeps (k : EStore) (p : Pins) (n : ConLeche.Name) :
    ⦃fun s => ⌜Inv k p s⌝⦄ internName n ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction n with
  | anonymous => mvcgen [internName]
  | str n x ih => mvcgen [internName, ih]
  | num n x ih => mvcgen [internName, ih]

@[spec] theorem internLevel_keeps (k : EStore) (p : Pins) (u : ConLeche.Level) :
    ⦃fun s => ⌜Inv k p s⌝⦄ internLevel u ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction u with
  | zero => mvcgen [internLevel]
  | succ u ih => mvcgen [internLevel, ih]
  | max u v ihu ihv => mvcgen [internLevel, ihu, ihv]
  | imax u v ihu ihv => mvcgen [internLevel, ihu, ihv]
  | param n => mvcgen [internLevel]

@[spec] theorem internLevelList_keeps (k : EStore) (p : Pins) (us : List ConLeche.Level) :
    ⦃fun s => ⌜Inv k p s⌝⦄ internLevelList us ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction us with
  | nil => mvcgen [internLevelList]
  | cons u us ih => mvcgen [internLevelList, ih]

#keeps internLevels

end ConRon.Bridge.Grouping
