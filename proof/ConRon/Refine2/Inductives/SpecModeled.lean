/-
# `ConRon.Refine2.Inductives.SpecModeled` — the transcriptions for `arena::inductives::modeled`

**Task #97-P5-Ind** (DESIGN.md §8.2).  This file is
`Refine2/Inductives/Spec.lean`'s continuation for the modeled route, and it is
apart from it only because the two were written concurrently: the rules are
the same ones that file's module note states, and a reader should read the two
as one.

* a **`…Spec`** definition is a fragment of a twin, TRANSCRIBED — a claim
  about nothing, checked against `proof/ConRon/Arena/Inductives/Modeled.lean`
  clause for clause;
* an **`…_unfold`** equation IS a claim: *the named twin is its transcription
  composed*.  They are the only obligations of this file about the TWIN rather
  than about the port.

**`arena::inductives::modeled` is the tier's densest split: 91 `pub fn`s
against 21 twin `def`s.**  `checkIotaThm` and `checkIotaThmN` alone are two
hundred-line `do` blocks whose `let`-bound handles outlive a `match` arm, and
DESIGN §3.4 cuts them into eight and eleven functions; `checkEtaThm`,
`checkUnitThm`, `checkProjIota` and `checkModeled` are cut four to eight ways
each.

**The messages are the port's constants** (task #97-T2-LOCKSTEP lane
Inductives).  The twin fragments used to interpolate the recursor's name into
their declines, which made them read a name the port never reads; the twin now
declines with the port's constant messages, and the transcriptions spell the
same strings (an `_unfold` equation is an equality of TWIN terms).

The twin is edited only where it and the port did different things (task
#97-T2-LOCKSTEP): the tag-first reads, the short-circuits and the name reads.
-/
import ConRon.Refine2.Inductives.NativeInstallF

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2

open ConRon.Arena

/-! # `arena::inductives::modeled` -/

/-! ## `checkIotaSidesTy`'s TT-lane tail -/

/-- `checkIotaSidesTy`'s `if mode.ttChecks` tail, which the port calls
`check_iota_slot_ty`. -/
def checkIotaSlotTySpec (mode : ConLeche.CheckMode) (feSelf : IFEnv) (depth : Nat)
    (alphaS : EIdx) (lA : LIdx) : AM Unit := do
  if mode.ttChecks then
    let ta ← inferTypeCore mode feSelf checkFuel depth alphaS
    let s ← internE (.sort lA)
    unless ← isDefEqCore mode feSelf checkFuel depth ta s do
      fail (.notImplemented "iota statement type slot sort")

/-- The owed equation: `checkIotaSidesTy` IS its two side certifications and
`checkIotaSlotTySpec`. -/
theorem checkIotaSidesTy_unfold (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (depth : Nat) (alphaS lhsS rhsS : EIdx) (lA : LIdx) :
    checkIotaSidesTy mode feSelf depth alphaS lhsS rhsS lA = (do
      let tl ← inferTypeCore mode feSelf checkFuel depth lhsS
      unless ← isDefEqCore mode feSelf checkFuel depth tl alphaS do
        fail (.notImplemented "iota statement lhs type")
      let tr ← inferTypeCore mode feSelf checkFuel depth rhsS
      unless ← isDefEqCore mode feSelf checkFuel depth tr alphaS do
        fail (.notImplemented "iota statement rhs type")
      checkIotaSlotTySpec mode feSelf depth alphaS lA) := by
  rfl

/-! ## `projBack` and `projFwd`'s two inner `let rec`s

The twin writes the two `go`s out; they differ only in which side of the pair
is which, and both intern the same two names in the same order, so the port
shares one body at a `back : bool` flag and the transcription does too. -/

/-- `projBack.go` at `back := true` and `projFwd.go` at `back := false`: the
projection family's `nF` pairs, from field `j` on. -/
def projPairsFromSpec (T : NIdx) (back : Bool) : Nat → Nat → AM (List (NIdx × NIdx))
  | 0, _ => pure []
  | k + 1, j => do
    let a ← if back then projModelName T j else projFnName T j
    let b ← if back then projFnName T j else projModelName T j
    let rest ← projPairsFromSpec T back k (j + 1)
    pure ((a, b) :: rest)

/-- The owed equation: `projBack` IS the two model names and
`projPairsFromSpec` at `true`. -/
theorem projBack_unfold (T ctor : NIdx) (nF : Nat) :
    projBack T ctor nF = (do
      let tm ← internNNode (.str T "_model")
      let cm ← internNNode (.str ctor "_model")
      pure ((tm, T) :: (cm, ctor) :: (← projPairsFromSpec T true nF 0))) := by
  have hgo : ∀ k j, projBack.go T k j = projPairsFromSpec T true k j := by
    intro k
    induction k with
    | zero => intro j; rfl
    | succ k ih => intro j; simp only [projBack.go, projPairsFromSpec, ih]; rfl
  simp only [projBack, hgo]

/-- The owed equation: `projFwd` IS the two model names and
`projPairsFromSpec` at `false`. -/
theorem projFwd_unfold (T ctor : NIdx) (nF : Nat) :
    projFwd T ctor nF = (do
      let tm ← internNNode (.str T "_model")
      let cm ← internNNode (.str ctor "_model")
      pure ((T, tm) :: (ctor, cm) :: (← projPairsFromSpec T false nF 0))) := by
  have hgo : ∀ k j, projFwd.go T k j = projPairsFromSpec T false k j := by
    intro k
    induction k with
    | zero => intro j; rfl
    | succ k ih => intro j; simp only [projFwd.go, projPairsFromSpec, ih]; rfl
  simp only [projFwd, hgo]

/-! ## The prologue both statement checks share

**Findings 20 and 21 are fixed in the twin** (task #97-T2-LOCKSTEP lane
Inductives): `checkIotaThm`/`checkIotaThmN` read `eqHeadLevel` in the
prologue, where the port's `iota_stmt_open_at` does, and no longer read the
recursor's name for their messages; the transcriptions below are therefore the
twin's own fragments, with no `nm` argument. -/

/-- The prologue's tail: the theorem's telescope opened at free variables, the
body's equation head and its arity.  `iota_stmt_open_at` is the port's. -/
def iotaStmtOpenAtSpec (depth : Nat) (tty : EIdx) :
    AM (List EIdx × List EIdx × LIdx) := do
  let (fvs, tbody) ← unwrapOr (← openPisAtFvarsF depth tty 0)
    (.notImplemented "iota statement shape mismatch")
  let targs ← getAppArgs coreWalkFuel tbody
  let tfn ← getAppFn coreWalkFuel tbody
  unless ← isEqHead tfn do
    fail (.notImplemented "iota statement not an equation")
  unless targs.length = 3 do
    fail (.notImplemented "iota statement not an equation")
  pure (fvs, targs, ← eqHeadLevel tfn)

/-- The prologue: the stored `iota_j` theorem, its level parameters, and
`iotaStmtOpenAtSpec`. -/
def iotaStmtOpenSpec (fe' : IFEnv) (cvName : NIdx) (lps : List NIdx)
    (depth j : Nat) : AM (List EIdx × List EIdx × LIdx) := do
  let cvt ← unwrapOr (← fe'.findCV? (← iotaThmName cvName j))
    (.notImplemented "missing iota theorem")
  unless cvt.levelParams = lps do
    fail (.notImplemented "iota theorem level mismatch")
  iotaStmtOpenAtSpec depth cvt.type

/-- The left side's head, arity and prefix pins, shared by the plain and the
nested statement checks.  The twin declines each of the three with its own
message; the port merges them, which is DESIGN §3.1's licence and is why the
transcription answers a `Bool`. -/
def iotaLhsPrefixOkSpec (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx)
    (mI rP : Nat) (fvs : List EIdx) (lfn : EIdx) (largs : List EIdx) : AM Bool := do
  let lus ← paramLevels lps
  let wantHd ← internE (.const (renameBy f cvName) lus)
  if !(lfn == wantHd) then pure false
  else if !(largs.length = mI + 1) then pure false
  else pure (largs.take rP == fvs.take rP)

/-! ## `checkIotaThm`, split eight ways -/

/-- The major premise: the renamed constructor at its own level parameters,
applied to the leading parameter variables and the field variables. -/
def checkIotaMajorSpec (f : List (NIdx × NIdx)) (r : IRecRule) (cvj : IConstantVal)
    (cnP : Nat) (fvs xFvs largs : List EIdx) (b0 : EIdx) : AM Bool := do
  let major := largs.getLastD b0
  let cus ← paramLevels cvj.levelParams
  let cHd ← internE (.const (renameBy f r.ctor) cus)
  let wantMajor ← mkAppN cHd (fvs.take cnP ++ xFvs)
  pure (major == wantMajor)

/-- The right side is definitionally the rule's renamed right-hand side
applied to the whole opened frame, and both sides inhabit the type slot. -/
def checkIotaThmRhsSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (depth : Nat) (rhsA : EIdx) (fvs targs : List EIdx)
    (rhsS : EIdx) (lA : LIdx) (b0 : EIdx) (cvName : NIdx) :
    AM Unit := do
  let rhsR ← renameConstsFast coreWalkFuel (renameBy f) rhsA
  let rhsApplied ← mkAppN rhsR fvs
  unless ← isDefEqCore mode feSelf checkFuel depth rhsS rhsApplied do
    fail (.notImplemented "iota statement mismatch")
  checkIotaSidesTy mode feSelf depth (targs.getD 0 b0) (targs.getD 1 b0) rhsS lA

/-- The rule's λ-domains against the opened frame. -/
def checkIotaThmLamsSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (depth : Nat) (rhsA : EIdx) (fvs targs : List EIdx)
    (rhsS : EIdx) (lA : LIdx) (b0 : EIdx) (all : List EIdx) (cvName : NIdx) : AM Unit := do
  let (ldoms, _) ← unwrapOr (← instLamsAtF coreWalkFuel all rhsA)
    (.notImplemented "rule shape mismatch")
  checkDefEqList mode feSelf depth (← all.mapM fvarTypeD) ldoms
  checkIotaThmRhsSpec mode feSelf f depth rhsA fvs targs rhsS lA b0 cvName

/-- The public frame: the recursor's telescope opened afresh, the
constructor's instantiated at its first `cnP` variables and then opened at
`cnF` more. -/
def checkIotaThmFramesSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (tyA : EIdx) (rP : Nat) (cvj : IConstantVal)
    (cnP depth : Nat) (rhsA : EIdx) (fvs targs : List EIdx) (rhsS : EIdx)
    (lA : LIdx) (b0 : EIdx) (cvName : NIdx) : AM Unit := do
  let cnF := depth - rP
  let (fvsP, _) ← unwrapOr (← openPisAtFvarsF rP tyA 0)
    (.notImplemented "iota recursor telescope")
  let (cdomsP, crestP) ← unwrapOr
      (← instPisAtF coreWalkFuel (fvsP.take cnP) cvj.type)
      (.notImplemented "iota constructor telescope")
  checkDefEqList mode feSelf depth (← (fvsP.take cnP).mapM fvarTypeD) cdomsP
  let (xFvsP, _) ← unwrapOr (← openPisAtFvarsF cnF crestP rP)
    (.notImplemented "iota constructor telescope")
  checkIotaThmLamsSpec mode feSelf f depth rhsA fvs targs rhsS lA b0
    (fvsP ++ xFvsP) cvName

/-- The statement's prefix domains are the recursor's (renamed). -/
def checkIotaThmPrefixSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (tyA : EIdx) (rP : Nat) (cvj : IConstantVal)
    (cnP depth : Nat) (rhsA : EIdx) (fvs targs : List EIdx) (rhsS : EIdx)
    (lA : LIdx) (b0 : EIdx) (cvName : NIdx) : AM Unit := do
  let tyAR ← renameConstsFast coreWalkFuel (renameBy f) tyA
  let (rdoms, _) ← unwrapOr (← instPisAtF coreWalkFuel (fvs.take rP) tyAR)
    (.notImplemented "iota recursor telescope")
  checkDefEqList mode feSelf depth (← (fvs.take rP).mapM fvarTypeD) rdoms
  checkIotaThmFramesSpec mode feSelf f tyA rP cvj cnP depth rhsA fvs targs rhsS lA
    b0 cvName

/-- The index tuple's arity and the two index/domain comparisons. -/
def checkIotaThmIdxSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (tyA : EIdx) (mI rP : Nat) (cvj : IConstantVal)
    (cnP depth : Nat) (rhsA : EIdx) (fvs xFvs largs targs : List EIdx)
    (rhsS : EIdx) (lA : LIdx) (b0 : EIdx) (cdoms : List EIdx) (cres : EIdx)
    (cvName : NIdx) : AM Unit := do
  let cargs ← getAppArgs coreWalkFuel cres
  unless cargs.length = cnP + (mI - rP) do
    fail (.notImplemented "iota constructor indices")
  checkDefEqList mode feSelf depth ((largs.drop rP).take (mI - rP)) (cargs.drop cnP)
  checkDefEqList mode feSelf depth (← xFvs.mapM fvarTypeD) (cdoms.drop cnP)
  checkIotaThmPrefixSpec mode feSelf f tyA rP cvj cnP depth rhsA fvs targs rhsS lA
    b0 cvName

/-- The constructor's telescope (renamed), instantiated at the major's
arguments. -/
def checkIotaThmCtorSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (tyA : EIdx) (mI rP : Nat) (cvj : IConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (fvs xFvs largs targs : List EIdx)
    (rhsS : EIdx) (lA : LIdx) (b0 : EIdx) (cvName : NIdx) :
    AM Unit := do
  let depth := rP + cnF
  unless (← stripPis (cnP + cnF) cvj.type).isSome do
    fail (.notImplemented "iota constructor telescope")
  let ctyR ← renameConstsFast coreWalkFuel (renameBy f) cvj.type
  let (cdoms, cres) ← unwrapOr
      (← instPisAtF coreWalkFuel (fvs.take cnP ++ xFvs) ctyR)
      (.notImplemented "iota constructor telescope")
  checkIotaThmIdxSpec mode feSelf f tyA mI rP cvj cnP depth rhsA fvs xFvs largs
    targs rhsS lA b0 cdoms cres cvName

/-- The owed equation: `checkIotaThm` IS the name read, the prologue, the
head/arity/prefix pins, the major and `checkIotaThmCtorSpec`. -/
theorem checkIotaThm_unfold (mode : ConLeche.CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat)
    (rhsA : EIdx) :
    checkIotaThm mode fe' feSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA = (do
      let depth := rP + cnF
      let (fvs, targs, lA) ← iotaStmtOpenSpec fe' cvName lps depth j
      let b0 ← internE (.bvar 0)
      let rhsS := targs.getD 2 b0
      let xFvs := fvs.drop rP
      let largs ← getAppArgs coreWalkFuel (targs.getD 1 b0)
      let lfn ← getAppFn coreWalkFuel (targs.getD 1 b0)
      unless ← iotaLhsPrefixOkSpec f cvName lps mI rP fvs lfn largs do
        fail (.notImplemented "iota statement head mismatch")
      unless ← checkIotaMajorSpec f r cvj cnP fvs xFvs largs b0 do
        fail (.notImplemented "iota statement major mismatch")
      checkIotaThmCtorSpec mode feSelf f tyA mI rP cvj cnP cnF rhsA fvs xFvs largs
        targs rhsS lA b0 cvName) := by
  -- TRUE since task #97-T2-LOCKSTEP lane Inductives (round 4's defect was the
  -- twin's three distinct head/arity/prefix messages against this ONE; the twin
  -- now declines all three with the port's `M_IOTA_HEAD`).  The peel through the
  -- tier's longest `do` block exhausts the default heartbeats at the prologue's
  -- `unwrapOr`; left for the round that states the fragments' lockstep proofs.
  sorry

/-! ## `nestedRuleShape`, split six ways -/

/-- `(args.take cnP).mapM (lowerBVarsFast coreWalkFuel k 0)`, as the cursor
recursion DESIGN §3.4 asks for. -/
def lowerBVarsListSpec (k : Nat) : List EIdx → AM (List EIdx)
  | [] => pure []
  | x :: xs => do
    let r ← lowerBVarsFast coreWalkFuel k 0 x
    let rest ← lowerBVarsListSpec k xs
    pure (r :: rest)

/-- `pins.mapM (liftLooseBVarsFast coreWalkFuel k 0)`, likewise. -/
def liftBVarsListSpec (k : Nat) : List EIdx → AM (List EIdx)
  | [] => pure []
  | x :: xs => do
    let r ← liftLooseBVarsFast coreWalkFuel k 0 x
    let rest ← liftBVarsListSpec k xs
    pure (r :: rest)

/-- `nestedRuleShape`'s `pins.allM`: each pin is fvar-free, scoped at the
recursor prefix, resolving and level-closed.  **All four conjuncts run for
every pin**, as the twin's `do` does. -/
def nestedPinsOkSpec (feSelf : IFEnv) (lps : List NIdx) (rP : Nat) :
    List EIdx → AM Bool
  | [] => pure true
  | p :: ps => do
    let w1 ← hasFvarFast coreWalkFuel p
    let w2 ← looseBVarsBoundedFast coreWalkFuel rP p
    let w3 ← constsResolveFFast feSelf p
    let w4 ← allLevelParamsDefined lps p
    if !w1 && w2 && w3 && w4 then nestedPinsOkSpec feSelf lps rP ps else pure false

/-- The major-premise domain's argument spine: the leading `cnP` are the pins
(lowered out of the `k` index binders and lifted back to compare), the
trailing `k` are the index spine, and the pins are well-scoped. -/
def nestedRuleShapeArgsSpec (feSelf : IFEnv) (lps : List NIdx) (mI rP cnP : Nat)
    (dom : EIdx) (lvlsIdx : LsIdx) : AM (Option (List LIdx × List EIdx)) := do
  let args ← getAppArgs coreWalkFuel dom
  let k := mI - rP
  let pins ← lowerBVarsListSpec k (args.take cnP)
  let lifted ← liftBVarsListSpec k pins
  let idxSpine ← bvarsDesc k
  let ks ← readNames lps
  let lvls ← viewLs lvlsIdx
  let lvlVals ← readLevels lvlsIdx
  let pinsOk ← nestedPinsOkSpec feSelf lps rP pins
  if args.length = cnP + k ∧ args.take cnP == lifted ∧
      args.drop cnP == idxSpine ∧ pinsOk ∧
      lvlVals.all (ConLeche.Level.allParamsDefined ks) then
    pure (some (lvls, pins))
  else pure none

/-- `nestedRuleShape`'s body past the `iota_j` guard: the recursor type's
major-premise domain and its head's level arguments. -/
def nestedRuleShapeAtSpec (feSelf : IFEnv) (lps : List NIdx) (tyA : EIdx)
    (mI rP cnP : Nat) : AM (Option (List LIdx × List EIdx)) := do
  match ← stripPis mI tyA with
  | some (_, rest) => do
    if rest.tag == ETag.forallE then
      match ← view rest with
      | .forallE dom _ _ => do
        let hd ← getAppFn coreWalkFuel dom
        if hd.tag == ETag.const then
          match ← view hd with
          | .const _D lvlsIdx => nestedRuleShapeArgsSpec feSelf lps mI rP cnP dom lvlsIdx
          | _ => pure none
        else pure none
      | _ => pure none
    else pure none
  | _ => pure none

/-- The owed equation: `nestedRuleShape` IS the `iota_j` guard and
`nestedRuleShapeAtSpec`. -/
theorem nestedRuleShape_unfold (fe' feSelf : IFEnv) (cvName : NIdx)
    (lps : List NIdx) (tyA : EIdx) (mI rP cnP j : Nat) :
    nestedRuleShape fe' feSelf cvName lps tyA mI rP cnP j = (do
      let thm ← iotaThmName cvName j
      if !((← fe'.findCV? thm).isSome && decide (rP ≤ mI)) then pure none
      else nestedRuleShapeAtSpec feSelf lps tyA mI rP cnP) := by
  rw [nestedRuleShape]
  refine am_bind_congr _ ?_; intro thm
  refine am_bind_congr _ ?_; intro fcv
  refine if_congr Iff.rfl rfl ?_
  rw [nestedRuleShapeAtSpec]
  refine am_bind_congr _ ?_; intro sp
  rcases sp with _ | ⟨_, rest⟩ <;> simp only []
  refine if_congr Iff.rfl ?_ rfl
  refine am_bind_congr _ ?_; intro v
  cases v <;> simp only []
  refine am_bind_congr _ ?_; intro fn
  refine if_congr Iff.rfl ?_ rfl
  refine am_bind_congr _ ?_; intro v2
  cases v2 <;> simp only []
  rw [nestedRuleShapeArgsSpec]
  refine am_bind_congr _ ?_; intro args
  refine am_bind_congr₂ ?_ ?_
  · exact list_mapM_counted _ (lowerBVarsListSpec (mI - rP)) rfl (fun a l => rfl) _
  intro pins
  refine am_bind_congr₂ ?_ ?_
  · exact list_mapM_counted _ (liftBVarsListSpec (mI - rP)) rfl (fun a l => rfl) _
  intro lifted
  refine am_bind_congr _ ?_; intro idxSpine
  refine am_bind_congr _ ?_; intro ks
  refine am_bind_congr _ ?_; intro lvls
  refine am_bind_congr _ ?_; intro lvlVals
  refine am_bind_congr₂ ?_ (fun _ => rfl)
  refine list_allM_counted _ (nestedPinsOkSpec feSelf lps rP) rfl ?_ _
  intro a l
  rw [nestedPinsOkSpec]
  twin_reduce

/-! ## `checkIotaThmN`, split eleven ways -/

/-- `pins.mapM fun p => instSpine … (← renameConsts f p)` — each pin renamed
and then instantiated at the opened recursor prefix, in that order. -/
def instSpineListRenamedSpec (f : List (NIdx × NIdx)) (args : List EIdx) (t : Nat) :
    List EIdx → AM (List EIdx)
  | [] => pure []
  | p :: ps => do
    let r ← instSpine coreWalkFuel args t (← renameConstsFast coreWalkFuel (renameBy f) p)
    let rest ← instSpineListRenamedSpec f args t ps
    pure (r :: rest)

/-- The same without the renaming — the public frame's. -/
def instSpineListSpec (args : List EIdx) (t : Nat) : List EIdx → AM (List EIdx)
  | [] => pure []
  | p :: ps => do
    let r ← instSpine coreWalkFuel args t p
    let rest ← instSpineListSpec args t ps
    pure (r :: rest)

/-- The constructor's fields opened at the public frame, the residual's arity,
and the rule's λ-domains against the whole frame. -/
def checkIotaThmNFieldsSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (mI rP cnP cnF : Nat) (rhsA : EIdx)
    (fvs targs : List EIdx) (rhsS : EIdx) (lA : LIdx) (b0 : EIdx)
    (fvsP : List EIdx) (crestP : EIdx) (cvName : NIdx) :
    AM Unit := do
  let depth := rP + cnF
  let (xFvsP, crest2P) ← unwrapOr (← openPisAtFvarsF cnF crestP rP)
    (.notImplemented "iota constructor telescope")
  unless (← getAppArgs coreWalkFuel crest2P).length == cnP + (mI - rP) do
    fail (.notImplemented "iota constructor arity")
  checkIotaThmLamsSpec mode feSelf f depth rhsA fvs targs rhsS lA b0
    (fvsP ++ xFvsP) cvName

/-- The PUBLIC frame: the recursor's telescope opened afresh, the pins
instantiated there (annotated, and typed against the constructor's domains at
the stored level instantiations). -/
def checkIotaThmNFramesSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (tyA : EIdx) (mI rP : Nat) (cvj : IConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (fvs targs : List EIdx) (rhsS : EIdx)
    (lA : LIdx) (b0 : EIdx) (lvlsIdx : LsIdx) (pins : List EIdx) (cvName : NIdx) : AM Unit := do
  let depth := rP + cnF
  let (fvsP, _) ← unwrapOr (← openPisAtFvarsF rP tyA 0)
    (.notImplemented "iota recursor telescope")
  let pinsP ← instSpineListSpec (fvsP.take rP) (rP - 1) pins
  checkAnnotList mode feSelf depth pinsP
  let ctyL2 ← instLPFast coreWalkFuel cvj.levelParams lvlsIdx cvj.type
  let (cdomsP, crestP) ← unwrapOr (← instPisAtF coreWalkFuel pinsP ctyL2)
    (.notImplemented "iota constructor telescope")
  checkTypedList mode feSelf depth pinsP cdomsP
  checkIotaThmNFieldsSpec mode feSelf f mI rP cnP cnF rhsA fvs targs rhsS lA b0
    fvsP crestP cvName

/-- The statement's prefix domains are the recursor's (renamed). -/
def checkIotaThmNPrefixSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (tyA : EIdx) (mI rP : Nat) (cvj : IConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (fvs targs : List EIdx) (rhsS : EIdx)
    (lA : LIdx) (b0 : EIdx) (lvlsIdx : LsIdx) (pins : List EIdx) (cvName : NIdx) : AM Unit := do
  let depth := rP + cnF
  let tyAR ← renameConstsFast coreWalkFuel (renameBy f) tyA
  let (rdoms, _) ← unwrapOr (← instPisAtF coreWalkFuel (fvs.take rP) tyAR)
    (.notImplemented "iota recursor telescope")
  checkDefEqList mode feSelf depth (← (fvs.take rP).mapM fvarTypeD) rdoms
  checkIotaThmNFramesSpec mode feSelf f tyA mI rP cvj cnP cnF rhsA fvs targs rhsS
    lA b0 lvlsIdx pins cvName

/-- The index tuple's arity and the two index/domain comparisons. -/
def checkIotaThmNIdxSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (tyA : EIdx) (mI rP : Nat) (cvj : IConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (fvs xFvs largs targs : List EIdx) (rhsS : EIdx)
    (lA : LIdx) (b0 : EIdx) (lvlsIdx : LsIdx) (pins cdoms : List EIdx)
    (cres : EIdx) (cvName : NIdx) : AM Unit := do
  let depth := rP + cnF
  let cargs ← getAppArgs coreWalkFuel cres
  unless cargs.length = cnP + (mI - rP) do
    fail (.notImplemented "iota constructor indices")
  checkDefEqList mode feSelf depth ((largs.drop rP).take (mI - rP)) (cargs.drop cnP)
  checkDefEqList mode feSelf depth (← xFvs.mapM fvarTypeD) (cdoms.drop cnP)
  checkIotaThmNPrefixSpec mode feSelf f tyA mI rP cvj cnP cnF rhsA fvs targs rhsS
    lA b0 lvlsIdx pins cvName

/-- The constructor's telescope at the stored level instantiations (renamed),
instantiated at the pins and the field variables. -/
def checkIotaThmNCtorSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (tyA : EIdx) (mI rP : Nat) (cvj : IConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (fvs xFvs largs targs : List EIdx) (rhsS : EIdx)
    (lA : LIdx) (b0 : EIdx) (lvlsIdx : LsIdx) (pins pinsF : List EIdx)
    (cvName : NIdx) : AM Unit := do
  let (_, cbody0) ← unwrapOr (← stripPis (cnP + cnF) cvj.type)
    (.notImplemented "iota constructor telescope")
  let chd ← getAppFn coreWalkFuel cbody0
  if chd.tag == ETag.const then
    unless (match ← view chd with
        | .const _ _ => true
        | _ => false) do
      fail (.notImplemented "iota constructor residual head")
  else
    fail (.notImplemented "iota constructor residual head")
  let ctyL ← instLPFast coreWalkFuel cvj.levelParams lvlsIdx cvj.type
  let ctyR ← renameConstsFast coreWalkFuel (renameBy f) ctyL
  let (cdoms, cres) ← unwrapOr (← instPisAtF coreWalkFuel (pinsF ++ xFvs) ctyR)
    (.notImplemented "iota constructor telescope")
  checkIotaThmNIdxSpec mode feSelf f tyA mI rP cvj cnP cnF rhsA fvs xFvs largs
    targs rhsS lA b0 lvlsIdx pins cdoms cres cvName

/-- The major premise at the STORED level instantiations, applied to the
instantiated pins and the field variables. -/
def checkIotaThmNMajorSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (tyA : EIdx) (mI rP : Nat) (cvj : IConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (fvs xFvs largs targs : List EIdx) (rhsS : EIdx)
    (lA : LIdx) (b0 : EIdx) (lvls : List LIdx) (pins pinsF : List EIdx)
    (r : IRecRule) (cvName : NIdx) : AM Unit := do
  let major := largs.getLastD b0
  let lvlsIdx ← internLsNode lvls
  let cHd ← internE (.const (renameBy f r.ctor) lvlsIdx)
  let wantMajor ← mkAppN cHd (pinsF ++ xFvs)
  unless major == wantMajor do
    fail (.notImplemented "iota statement major mismatch")
  checkIotaThmNCtorSpec mode feSelf f tyA mI rP cvj cnP cnF rhsA fvs xFvs largs
    targs rhsS lA b0 lvlsIdx pins pinsF cvName

/-- The nested statement's prologue at a recognised shape. -/
def checkIotaThmNAtSpec (mode : ConLeche.CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat)
    (rhsA : EIdx) (lvls : List LIdx) (pins : List EIdx) : AM Unit := do
  let depth := rP + cnF
  let (fvs, targs, lA) ← iotaStmtOpenSpec fe' cvName lps depth j
  let b0 ← internE (.bvar 0)
  let rhsS := targs.getD 2 b0
  let xFvs := fvs.drop rP
  let pinsF ← instSpineListRenamedSpec f (fvs.take rP) (rP - 1) pins
  let largs ← getAppArgs coreWalkFuel (targs.getD 1 b0)
  let lfn ← getAppFn coreWalkFuel (targs.getD 1 b0)
  unless ← iotaLhsPrefixOkSpec f cvName lps mI rP fvs lfn largs do
    fail (.notImplemented "iota statement head mismatch")
  checkIotaThmNMajorSpec mode feSelf f tyA mI rP cvj cnP cnF rhsA fvs xFvs largs
    targs rhsS lA b0 lvls pins pinsF r cvName

/-- The owed equation: `checkIotaThmN` IS the shape recognition and
`checkIotaThmNAtSpec`, with `.nested lvls pins` as the answer. -/
theorem checkIotaThmN_unfold (mode : ConLeche.CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat)
    (rhsA : EIdx) :
    checkIotaThmN mode fe' feSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA = (do
      match ← nestedRuleShape fe' feSelf cvName lps tyA mI rP cnP j with
      | none => pure .inert
      | some (lvls, pins) => do
        checkIotaThmNAtSpec mode fe' feSelf f cvName lps tyA mI rP j r cvj cnP cnF
          rhsA lvls pins
        pure (.nested lvls pins)) := by
  sorry

/-! ## `checkIotaRule`, split four ways -/

/-- The stored rule: `{ r with rhs, ctorParams, fire, paramsBlind := false }`,
with the two rescue bits stamped by `recRuleBits`. -/
def checkIotaRuleBitsSpec (fe' : IFEnv) (cvName : NIdx) (r : IRecRule) (cnP : Nat)
    (rhsA : EIdx) (fire : IRecRuleFire) : AM IRecRule :=
  recRuleBits fe' cvName
    { r with rhs := rhsA, ctorParams := cnP, fire := fire, paramsBlind := false }

/-- The annotated right-hand side's guards, and then the firing mode. -/
def checkIotaRuleFireSpec (mode : ConLeche.CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat)
    (rhsA : EIdx) : AM IRecRule := do
  unless ← allLevelParamsDefined lps rhsA do
    fail (.invalid "undeclared universe parameter in rule")
  unless ← constsResolveFFast feSelf rhsA do
    fail (← unresolvedConstsError "rule" rhsA)
  unless (← stripLams (rP + cnF) rhsA).isSome do
    fail (.notImplemented "rule shape mismatch")
  let _rhsTy ← inferTypeCore mode feSelf checkFuel 0 rhsA
  let fire ← if ← recRulePlain coreWalkFuel tyA mI rP cnP then do
      checkIotaThm mode fe' feSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA
      pure IRecRuleFire.plain
    else
      checkIotaThmN mode fe' feSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA
  checkIotaRuleBitsSpec fe' cvName r cnP rhsA fire

/-- The right-hand side's generic well-formedness, then the annotation. -/
def checkIotaRuleWfSpec (mode : ConLeche.CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) : AM IRecRule := do
  unless ← looseBVarsBoundedFast coreWalkFuel 0 r.rhs do
    fail (.invalid "loose bound variable in rule")
  if ← hasFvarFast coreWalkFuel r.rhs then
    fail (.invalid "free variable in rule")
  let rhsA ← annotateCore mode feSelf checkFuel 0 r.rhs
  checkIotaRuleFireSpec mode fe' feSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA
   

/-- The owed equation: `checkIotaRule` IS the name read, the constructor
lookup, the field-count pin and `checkIotaRuleWfSpec`. -/
theorem checkIotaRule_unfold (mode : ConLeche.CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP j : Nat) (r : IRecRule) :
    checkIotaRule mode fe' feSelf f cvName lps tyA mI rP j r = (do
      match fe'.find? r.ctor with
      | some (.ctorInfo cvj cnP cnF) => do
        unless r.nfields = cnF do
          fail (.invalid "rule field count mismatch")
        checkIotaRuleWfSpec mode fe' feSelf f cvName lps tyA mI rP j r cvj cnP cnF
      | _ => fail (.invalid "iota rule constructor not stored")) := by
  rfl

/-! ## `checkMemberVal`, split two ways -/

/-- The model counterpart: it exists, at the member's level parameters, and
its type is the member's under the block renaming. -/
def checkMemberModelSpec (f : List (NIdx × NIdx)) (fe' : IFEnv)
    (cvA : IConstantVal) (blockNames : List NIdx) (an : ConLeche.Name) :
    AM IConstantVal := do
  let mn ← internNNode (.str cvA.name "_model")
  let some (.defnInfo cvm _mval _) := fe'.find? mn
    | fail (.notImplemented s!"no install route for an inductive block: no direct \
        route recognises it and no model for {an} was generated")
  unless cvm.levelParams = cvA.levelParams do
    fail (.notImplemented s!"model level parameters mismatch for {an}")
  let renamed ← renameConstsFast coreWalkFuel (renameBy f) cvA.type
  unless renamed == cvm.type do
    fail (.notImplemented s!"model type mismatch for {an}")
  pure cvA

/-- The owed equation: `checkMemberVal` IS the rename table, the constant
check, the model-suffix guard and `checkMemberModelSpec`. -/
theorem checkMemberVal_unfold (mode : ConLeche.CheckMode) (blockNames : List NIdx)
    (fe' : IFEnv) (cv : IConstantVal) :
    checkMemberVal mode blockNames fe' cv = (do
      let f ← blockRenameTable blockNames
      let cvA ← checkConstantVal mode fe' cv
      let an ← readName cvA.name
      if ConLeche.Name.isModelSuffix an then
        fail (.invalid s!"model-shaped member name {an}")
      checkMemberModelSpec f fe' cvA blockNames an) := by
  rfl

/-! ## `checkProjLookups` and `checkProjTy`, split two ways each -/

/-- The model artifact, the free public name, the stored parent and the pinned
`Eq` basis. -/
def checkProjLookupsModelSpec (fe' : IFEnv) (T : NIdx) (lps : List NIdx) (i : Nat)
    (cvj : IConstantVal) : AM (IConstantVal × IConstantVal) := do
  let some (.defnInfo mcv _ _) := fe'.find? (← projModelName T i)
    | fail (.notImplemented "missing projection model")
  unless mcv.levelParams = lps do
    fail (.notImplemented "projection model level mismatch")
  unless (fe'.find? (← projFnName T i)).isNone do
    fail (.invalid "projection name taken")
  unless (fe'.find? T).isSome do
    fail (.notImplemented "projection parent not stored")
  unless ← eqBasisStored fe' do
    fail (.notImplemented "projection iota requires the pinned Eq basis")
  pure (cvj, mcv)

/-- The owed equation: `checkProjLookups` IS the constructor lookup, the arity
pin and `checkProjLookupsModelSpec`. -/
theorem checkProjLookups_unfold (fe' : IFEnv) (T ctorName : NIdx)
    (lps : List NIdx) (nP nF i : Nat) :
    checkProjLookups fe' T ctorName lps nP nF i = (do
      let some (.ctorInfo cvj cnP cnF) := fe'.find? ctorName
        | fail (.notImplemented "projection constructor not stored")
      unless cnP = nP ∧ cnF = nF do
        fail (.notImplemented "projection constructor arity mismatch")
      checkProjLookupsModelSpec fe' T lps i cvj) := by
  rfl

/-- The public type's resolution, well-formedness and parameter telescope. -/
def checkProjTyWfSpec (fe' : IFEnv) (lps : List NIdx) (nP : Nat) (pty : EIdx) :
    AM EIdx := do
  unless ← constsResolveFFast fe' pty do
    fail (.notImplemented "projection type resolution")
  unless (← looseBVarsBoundedFast coreWalkFuel 0 pty) &&
      !(← hasFvarFast coreWalkFuel pty) &&
      (← allLevelParamsDefined lps pty) do
    fail (.notImplemented "projection type wellformedness")
  unless (← stripPis (nP + 1) pty).isSome do
    fail (.notImplemented "projection type telescope")
  pure pty

/-- The owed equation: `checkProjTy` IS the two tables, the renaming roundtrip
and `checkProjTyWfSpec`. -/
theorem checkProjTy_unfold (fe' : IFEnv) (T ctorName : NIdx) (lps : List NIdx)
    (mty : EIdx) (nP nF : Nat) :
    checkProjTy fe' T ctorName lps mty nP nF = (do
      let back ← projBack T ctorName nF
      let fwd ← projFwd T ctorName nF
      let pty ← renameConstsFast coreWalkFuel (renameBy back) mty
      unless (← renameConstsFast coreWalkFuel (renameBy fwd) pty) == mty do
        fail (.notImplemented "projection type roundtrip")
      checkProjTyWfSpec fe' lps nP pty) := by
  rfl

/-! ## `checkProjIota`, split five ways -/

/-- The right side is field `i`, and both equation sides inhabit the
statement's type slot. -/
def checkProjIotaFieldSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (nP nF i : Nat) (tty sbody rhsC : EIdx) (pmn : NIdx) : AM Unit := do
  let depth := nP + nF
  let fld ← internE (.bvar (nF - 1 - i))
  unless rhsC == fld do
    fail (.notImplemented "projection iota field mismatch")
  let (_, sbodyO) ← unwrapOr (← openPisAtFvarsF depth tty 0)
    (.notImplemented "projection iota telescope")
  let targsO ← getAppArgs coreWalkFuel sbodyO
  let b0 ← internE (.bvar 0)
  checkIotaSidesTy mode feSelf depth (targsO.getD 0 b0) (targsO.getD 1 b0)
    (targsO.getD 2 b0) (← eqHeadLevel (← getAppFn coreWalkFuel sbody))

/-- The expected redex, and the head and redex pins the statement's body must
meet. -/
def checkProjIotaLhsSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (lps : List NIdx) (nP nF i : Nat) (pmn : NIdx) (tty sbody : EIdx)
    (pArgs : List EIdx) (mkSpine : EIdx) : AM Unit := do
  let pus ← paramLevels lps
  let pHd ← internE (.const pmn pus)
  let lhsS ← mkAppN pHd (pArgs ++ [mkSpine])
  match ← eqApp3? sbody with
  | some (c, _l, _tySlot, lhsC, rhsC) => do
    unless c = (← pinEq) do
      fail (.notImplemented "projection iota head")
    unless lhsC == lhsS do
      fail (.notImplemented "projection iota redex mismatch")
    checkProjIotaFieldSpec mode feSelf nP nF i tty sbody rhsC pmn
  | none => fail (.notImplemented "projection iota body shape")

/-- The statement's body is `proj_i p⃗ (C._model p⃗ x⃗) = x_i`. -/
def checkProjIotaBodySpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (ctorName : NIdx) (lps : List NIdx) (cvj : IConstantVal) (nP nF i : Nat)
    (pmn : NIdx) (tty sbody : EIdx) : AM Unit := do
  let pArgs ← structPsAt nF nP
  let xArgs ← bvarsDesc nF
  let cmn ← internNNode (.str ctorName "_model")
  let cus ← paramLevels cvj.levelParams
  let cHd ← internE (.const cmn cus)
  let mkSpine ← mkAppN cHd (pArgs ++ xArgs)
  checkProjIotaLhsSpec mode feSelf lps nP nF i pmn tty sbody pArgs mkSpine

/-- The statement's binder domains against the constructor's, under the
forward renaming. -/
def checkProjIotaDomsSpec (mode : ConLeche.CheckMode) (feSelf : IFEnv)
    (T ctorName : NIdx) (lps : List NIdx) (cvj : IConstantVal) (nP nF i : Nat)
    (pmn : NIdx) (tty : EIdx) : AM Unit := do
  let some (sbinders, sbody) ← stripPis (nP + nF) tty
    | fail (.notImplemented "projection iota telescope")
  let some (cbindersR, _) ← stripPis (nP + nF) cvj.type
    | fail (.notImplemented "projection constructor telescope")
  let fwd ← projFwd T ctorName nF
  unless ← domsMatchRenamed (renameBy fwd) sbinders cbindersR 0 0 (nP + nF) do
    fail (.notImplemented "projection iota domain mismatch")
  checkProjIotaBodySpec mode feSelf ctorName lps cvj nP nF i pmn tty sbody

/-- The owed equation: `checkProjIota` IS the `proj_i._model.iota` lookup, its
level pin and `checkProjIotaDomsSpec`. -/
theorem checkProjIota_unfold (mode : ConLeche.CheckMode) (fe' feSelf : IFEnv)
    (T ctorName : NIdx) (lps : List NIdx) (cvj : IConstantVal) (nP nF i : Nat) :
    checkProjIota mode fe' feSelf T ctorName lps cvj nP nF i = (do
      let pmn ← projModelName T i
      let itn ← internNNode (.str pmn "iota")
      let some (.thmInfo tcv _) := fe'.find? itn
        | fail (.notImplemented "missing projection iota theorem")
      unless tcv.levelParams = lps do
        fail (.notImplemented "projection iota level mismatch")
      checkProjIotaDomsSpec mode feSelf T ctorName lps cvj nP nF i pmn tcv.type) := by
  rfl

/-! ## `checkProjFn`, split two ways -/

/-- The rule, the model's iota theorem, and the install. -/
def checkProjFnRuleSpec (mode : ConLeche.CheckMode) (fe' : IFEnv)
    (T ctorName : NIdx) (lps : List NIdx) (cvj : IConstantVal) (nP nF i : Nat)
    (pty : EIdx) : AM IFEnv := do
  let rhsA ← checkProjRule mode fe' pty cvj lps nP nF i
  checkProjIota mode fe' fe' T ctorName lps cvj nP nF i
  let pn ← projFnName T i
  let rule ← projFnRule fe' T ctorName pty nP nF i rhsA
  pure (fe'.push (.recInfo ⟨pn, lps, pty⟩ nP nP [rule]))

/-- The owed equation: `checkProjFn` IS the lookups, the public type, the
projection shape, the range pin and `checkProjFnRuleSpec`. -/
theorem checkProjFn_unfold (mode : ConLeche.CheckMode) (fe' : IFEnv)
    (T ctorName : NIdx) (lps : List NIdx) (nP nF i : Nat) :
    checkProjFn mode fe' T ctorName lps nP nF i = (do
      let (cvj, mcv) ← checkProjLookups fe' T ctorName lps nP nF i
      let pty ← checkProjTy fe' T ctorName lps mcv.type nP nF
      checkProjShape pty cvj.type nP nF
      unless i < nF do
        fail (.invalid "projection index out of range")
      checkProjFnRuleSpec mode fe' T ctorName lps cvj nP nF i pty) := by
  rfl

/-! ## `checkEtaThm`, split seven ways -/

/-- The projection models exist at the family's level parameters — the twin's
`(List.range nF).allM`, from field `j` on. -/
def projModelsOkSpec (fe' : IFEnv) (T : NIdx) (lps : List NIdx) :
    Nat → Nat → AM Bool
  | 0, _ => pure true
  | k + 1, j => do
    match fe'.find? (← projModelName T j) with
    | some (.defnInfo cvmj _ _) =>
      if cvmj.levelParams == lps then projModelsOkSpec fe' T lps k (j + 1)
      else pure false
    | _ => pure false

/-- `(List.range nF).mapM`: `proj_j._model` at the parameter spine and the
subject, from field `j` on. -/
def etaProjArgsSpec (T : NIdx) (lps : List NIdx) (psHi : List EIdx) (b0 : EIdx) :
    Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | k + 1, j => do
    let pHd ← internE (.const (← projModelName T j) (← paramLevels lps))
    let a ← mkAppN pHd (psHi ++ [b0])
    let rest ← etaProjArgsSpec T lps psHi b0 k (j + 1)
    pure (a :: rest)

/-- The equation itself: `x = C._model p⃗ (proj_j p⃗ x)…`, at the family's type,
with the TT-lane check on the model former's residual. -/
def checkEtaThmEqSpec (mode : ConLeche.CheckMode) (T : NIdx) (lps : List NIdx)
    (nF : Nat) (cm : NIdx) (sbody tbodyM : EIdx) (psHi : List EIdx)
    (famHi : EIdx) : AM Bool := do
  match ← eqApp3? sbody with
  | some (c, lA, tySlot, lhsC, rhsC) => do
    let b0 ← internE (.bvar 0)
    let us ← paramLevels lps
    let cHd ← internE (.const cm us)
    let projArgs ← etaProjArgsSpec T lps psHi b0 nF 0
    let wantRhs ← mkAppN cHd (psHi ++ projArgs)
    let sortA ← internE (.sort lA)
    pure (c == (← pinEq) && lhsC == b0 && tySlot == famHi &&
      rhsC == wantRhs && (!mode.ttChecks || tbodyM == sortA))
  | none => pure false

/-- The subject binder's domain and the equation body. -/
def checkEtaThmBodySpec (mode : ConLeche.CheckMode) (T : NIdx) (lps : List NIdx)
    (nP nF : Nat) (tHd : EIdx) (cm : NIdx)
    (sbinders : List (EIdx × ConLeche.BinderMeta)) (sbody tbodyM : EIdx) :
    AM Bool := do
  let psLo ← structPsAt 0 nP
  let famLo ← mkAppN tHd psLo
  let xdomOk ← match sbinders[nP]? with
    | some (xdom, _) => pure (xdom == famLo)
    | none => pure false
  if !xdomOk then pure false else do
  let psHi ← structPsAt 1 nP
  let famHi ← mkAppN tHd psHi
  checkEtaThmEqSpec mode T lps nF cm sbody tbodyM psHi famHi

/-- The statement's shape: the parameter domains are the model former's. -/
def checkEtaThmShapeSpec (mode : ConLeche.CheckMode) (T : NIdx) (lps : List NIdx)
    (nP nF : Nat) (tm cm : NIdx) (tty mtty : EIdx) : AM Bool := do
  match ← stripPis (nP + 1) tty with
  | none => pure false
  | some (sbinders, sbody) =>
    match ← stripPis nP mtty with
    | none => pure false
    | some (tbindersM, tbodyM) => do
      if !(domsMatchAux sbinders.toArray tbindersM.toArray 0 0 nP) then pure false else do
      let us ← paramLevels lps
      let tHd ← internE (.const tm us)
      checkEtaThmBodySpec mode T lps nP nF tHd cm sbinders sbody tbodyM

/-- The pinned `Eq` basis, the three level-parameter pins and the projection
models' own level parameters. -/
def checkEtaThmAtSpec (mode : ConLeche.CheckMode) (fe' : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nF : Nat) (tm cm : NIdx)
    (tcv cvmT cvmC : IConstantVal) : AM Bool := do
  if !(← eqBasisStored fe') then pure false else
  if !(tcv.levelParams == lps && cvmT.levelParams == lps &&
      cvmC.levelParams == lps) then pure false else do
  if !(← projModelsOkSpec fe' T lps nF 0) then pure false else
  checkEtaThmShapeSpec mode T lps nP nF tm cm tcv.type cvmT.type

/-- The owed equation: `checkEtaThm` IS the three lookups and
`checkEtaThmAtSpec`. -/
theorem checkEtaThm_unfold (mode : ConLeche.CheckMode) (fe' : IFEnv)
    (T ctorName : NIdx) (lps : List NIdx) (nP nF : Nat) :
    checkEtaThm mode fe' T ctorName lps nP nF = (do
      let tm ← internNNode (.str T "_model")
      let etn ← internNNode (.str tm "eta")
      let cm ← internNNode (.str ctorName "_model")
      match fe'.find? etn, fe'.find? tm, fe'.find? cm with
      | some (.thmInfo tcv _), some (.defnInfo cvmT _ _),
        some (.defnInfo cvmC _ _) =>
        checkEtaThmAtSpec mode fe' T lps nP nF tm cm tcv cvmT cvmC
      | _, _, _ => pure false) := by
  rw [checkEtaThm]
  refine am_bind_congr _ ?_; intro tm
  refine am_bind_congr _ ?_; intro etn
  refine am_bind_congr _ ?_; intro cm
  rcases fe'.find? etn with _ | ci1 <;> rcases fe'.find? tm with _ | ci2 <;>
    rcases fe'.find? cm with _ | ci3 <;> simp only [] <;> (try rfl)
  cases ci1 <;> cases ci2 <;> cases ci3 <;> simp only [] <;> (try rfl)
  rw [checkEtaThmAtSpec]
  refine am_bind_congr _ ?_; intro eb
  refine if_congr Iff.rfl rfl ?_
  refine if_congr Iff.rfl rfl ?_
  rw [List.range_eq_range']
  refine am_bind_congr₂
    (range_allM_counted _ (projModelsOkSpec fe' T lps) (fun i => rfl) ?_ nF 0) ?_
  · intro m i
    rw [projModelsOkSpec]
    twin_reduce
    refine am_bind_congr _ ?_; intro pn
    split <;> split <;> (try simp_all)
  intro po
  refine if_congr Iff.rfl rfl ?_
  rw [checkEtaThmShapeSpec]
  refine am_bind_congr _ ?_; intro sp1
  rcases sp1 with _ | ⟨sbinders, sbody⟩
  · rfl
  simp only []
  refine am_bind_congr _ ?_; intro sp2
  rcases sp2 with _ | ⟨tbindersM, tbodyM⟩
  · rfl
  simp only []
  refine if_congr Iff.rfl rfl ?_
  refine am_bind_congr _ ?_; intro us
  refine am_bind_congr _ ?_; intro tHd
  rw [checkEtaThmBodySpec]
  refine am_bind_congr _ ?_; intro psLo
  refine am_bind_congr _ ?_; intro famLo
  rcases hx : sbinders[nP]? with _ | ⟨xdom, xm⟩
  · simp only [pure_bind, Bool.not_false, if_true]
  simp only [pure_bind]
  refine if_congr Iff.rfl rfl ?_
  refine am_bind_congr _ ?_; intro psHi
  refine am_bind_congr _ ?_; intro famHi
  rw [checkEtaThmEqSpec]
  refine am_bind_congr _ ?_; intro eq3
  rcases eq3 with _ | ⟨c, lA, tySlot, lhsC, rhsC⟩
  · rfl
  simp only []
  refine am_bind_congr _ ?_; intro b0
  refine am_bind_congr _ ?_; intro us2
  refine am_bind_congr _ ?_; intro cHd
  refine am_bind_congr₂
    (range_mapM_counted _ (etaProjArgsSpec T lps psHi b0) (fun i => rfl) ?_ nF 0) ?_
  · intro m i
    rw [etaProjArgsSpec]
    twin_reduce
  intro projArgs
  rfl

/-! ## `checkUnitThm`, split five ways -/

/-- `mkAppN tHd (← structPsAt o nP)` — the model family at an offset.  The
twin writes the same expression at three offsets; the port names it once. -/
def famAtSpec (tHd : EIdx) (o nP : Nat) : AM EIdx := do
  mkAppN tHd (← structPsAt o nP)

/-- The equation `bvar 1 = bvar 0` at the family's type. -/
def checkUnitThmEqSpec (mode : ConLeche.CheckMode) (sbody tbodyM fam2 : EIdx) :
    AM Bool := do
  match ← eqApp3? sbody with
  | some (c, lA, tySlot, lhsC, rhsC) => do
    let b0 ← internE (.bvar 0)
    let b1 ← internE (.bvar 1)
    let sortA ← internE (.sort lA)
    pure (c == (← pinEq) && lhsC == b1 && rhsC == b0 &&
      tySlot == fam2 && (!mode.ttChecks || tbodyM == sortA))
  | none => pure false

/-- The two subject binders' domains and the equation `x = y`. -/
def checkUnitThmShapeSpec (mode : ConLeche.CheckMode) (lps : List NIdx) (nP : Nat)
    (tm : NIdx) (sbinders : List (EIdx × ConLeche.BinderMeta))
    (sbody tbodyM : EIdx) : AM Bool := do
  let us ← paramLevels lps
  let tHd ← internE (.const tm us)
  let fam0 ← famAtSpec tHd 0 nP
  let fam1 ← famAtSpec tHd 1 nP
  let fam2 ← famAtSpec tHd 2 nP
  let xOk ← match sbinders[nP]? with
    | some (xdom, _) => pure (xdom == fam0)
    | none => pure false
  let yOk ← match sbinders[nP + 1]? with
    | some (ydom, _) => pure (ydom == fam1)
    | none => pure false
  if !(xOk && yOk) then pure false else
  checkUnitThmEqSpec mode sbody tbodyM fam2

/-- The pinned `Eq` basis, the level-parameter pins and the statement's
shape. -/
def checkUnitThmAtSpec (mode : ConLeche.CheckMode) (fe' : IFEnv) (lps : List NIdx)
    (nP : Nat) (tm : NIdx) (tty : EIdx) (tlps : List NIdx) (mtty : EIdx)
    (mlps : List NIdx) : AM Bool := do
  if !(← eqBasisStored fe') then pure false else
  if !(tlps == lps && mlps == lps) then pure false else
  match ← stripPis (nP + 2) tty with
  | none => pure false
  | some (sbinders, sbody) =>
    match ← stripPis nP mtty with
    | none => pure false
    | some (tbindersM, tbodyM) => do
      if !(domsMatchAux sbinders.toArray tbindersM.toArray 0 0 nP) then pure false else
      checkUnitThmShapeSpec mode lps nP tm sbinders sbody tbodyM

/-- The owed equation: `checkUnitThm` IS the two lookups and
`checkUnitThmAtSpec`. -/
theorem checkUnitThm_unfold (mode : ConLeche.CheckMode) (fe' : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP : Nat) :
    checkUnitThm mode fe' T lps nP = (do
      let tm ← internNNode (.str T "_model")
      let utn ← internNNode (.str tm "unitlike")
      match fe'.find? utn, fe'.find? tm with
      | some (.thmInfo tcv _), some (.defnInfo cvmT _ _) =>
        checkUnitThmAtSpec mode fe' lps nP tm tcv.type tcv.levelParams cvmT.type
          cvmT.levelParams
      | _, _ => pure false) := by
  rw [checkUnitThm]
  refine am_bind_congr _ ?_; intro tm
  refine am_bind_congr _ ?_; intro utn
  rcases fe'.find? utn with _ | ci1 <;> rcases fe'.find? tm with _ | ci2 <;>
    simp only [] <;> (try rfl)
  cases ci1 <;> cases ci2 <;> simp only [] <;> (try rfl)
  rw [checkUnitThmAtSpec]
  refine am_bind_congr _ ?_; intro eb
  refine if_congr Iff.rfl rfl ?_
  refine if_congr Iff.rfl rfl ?_
  refine am_bind_congr _ ?_; intro sp1
  rcases sp1 with _ | ⟨sbinders, sbody⟩
  · rfl
  simp only []
  refine am_bind_congr _ ?_; intro sp2
  rcases sp2 with _ | ⟨tbindersM, tbodyM⟩
  · rfl
  simp only []
  refine if_congr Iff.rfl rfl ?_
  rw [checkUnitThmShapeSpec]
  simp only [famAtSpec]
  simp only [checkUnitThmEqSpec]
  twin_reduce
  rfl

/-! ## `checkModeled`, split eight ways

`filterRecsSpec`, `blockNamesOfSpec`, `filterKindSpec` and
`singleIndCtorSpec` are the four PURE readers `checkModeled`'s opening lines
are; `projFnFamilyFreeSpec` is `Refine2/Inductives/Spec.lean`'s, reused here
because the twin spells the same `(List.range nF).allM` at both routes. -/

/-- `block.filter isRecInfo` and its complement, as one reader at a flag. -/
def filterRecsSpec (block : List IConstantInfo) (want : Bool) :
    List IConstantInfo := block.filter fun ci => isRecInfo ci == want

/-- `block.map (·.name)`. -/
def blockNamesOfSpec (block : List IConstantInfo) : List NIdx :=
  block.map (·.name)

/-- The two constructor filters, at a tag (`0` the type formers, `1` the
constructors). -/
def filterKindSpec (block : List IConstantInfo) (kind : Nat) :
    List IConstantInfo :=
  block.filter fun ci => match ci with
    | .indInfo _ _ => kind == 0
    | .ctorInfo _ _ _ => kind == 1
    | _ => false

/-- The twin's two-list match `[.indInfo cvT _], [.ctorInfo cvC nP nF]`, as
the one reader the port makes of it. -/
def singleIndCtorSpec (block : List IConstantInfo) :
    Option (IConstantVal × IConstantVal × Nat × Nat) :=
  match filterKindSpec block 0, filterKindSpec block 1 with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] => some (cvT, cvC, nP, nF)
  | _, _ => none

/-- The eta constructor residual, the projection name family's freshness and
the projection installs. -/
def checkModeledProjsSpec (mode : ConLeche.CheckMode) (fe₃ : IFEnv)
    (cvT cvC : IConstantVal) (nP nF : Nat) (eta : Bool) : AM IFEnv := do
  unless ← ctorResidualOk mode fe₃ cvT.name cvC.name cvT.levelParams nP nF eta do
    fail (.notImplemented "modeled structure: eta constructor residual")
  unless ← projFnFamilyFreeSpec fe₃ cvT.name nF 0 do
    fail (.invalid "projection name family taken")
  if ← ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF then
    installProjFns mode cvT.name cvC.name cvT.levelParams nP nF fe₃ nF 0
  else pure fe₃

/-- The single-type-former, single-constructor arm. -/
def checkModeledStructSpec (mode : ConLeche.CheckMode) (fe : IFEnv)
    (blockNames : List NIdx) (nonrecs recs : List IConstantInfo)
    (cvT cvC : IConstantVal) (nP nF : Nat) : AM IFEnv := do
  let caps ← indBlockCaps mode fe cvT cvC nP nF
  let fe₂ ← checkIndMembers mode blockNames caps fe nonrecs
  let fe₃ ← checkIndRecs mode blockNames fe₂ recs
  checkModeledProjsSpec mode fe₃ cvT cvC nP nF caps.eta

/-- The owed equation: `checkModeled` IS the two filters, the suffix pin, the
names and one of its two arms. -/
theorem checkModeled_unfold (mode : ConLeche.CheckMode) (fe : IFEnv)
    (block : List IConstantInfo) :
    checkModeled mode fe block = (do
      let recs := filterRecsSpec block true
      let nonrecs := filterRecsSpec block false
      unless recsFormSuffix block do
        fail (.notImplemented "recursor before other block members")
      let blockNames := blockNamesOfSpec block
      match singleIndCtorSpec block with
      | some (cvT, cvC, nP, nF) =>
        checkModeledStructSpec mode fe blockNames nonrecs recs cvT cvC nP nF
      | none => do
        let fe₂ ← checkIndMembers mode blockNames {} fe nonrecs
        checkIndRecs mode blockNames fe₂ recs) := by
  sorry

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.projBack_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms projBack_unfold

/-- info: 'ConRon.Refine2.checkProjFn_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkProjFn_unfold

/-- info: 'ConRon.Refine2.nestedRuleShape_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nestedRuleShape_unfold

/-- info: 'ConRon.Refine2.checkUnitThm_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkUnitThm_unfold

/-- info: 'ConRon.Refine2.checkEtaThm_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkEtaThm_unfold

end ConRon.Refine2
