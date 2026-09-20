/-
# `ConRon.Arena.Inductives.Modeled` — the modeled-inductive install
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/Modeled.lean` whole, over handles: the member
checks against the `_model` artifacts under the group-local renaming, the
iota-rule checks against the `_model.iota_j` theorems, the capability checks
and the projection-function installs.

**The deviations of this module** (task #97c's six are inherited and not
repeated):

* **`env` becomes `fe : IFEnv`**, so `env'`/`envSelf` are `fe'`/`feSelf` and
  the `…F` twins of `ConLeche/Kernel/DeclCheck.lean` collapse into these.
* **The renaming maps are TABLES.**  con-leche's `f : Name → Name`,
  `projBack` and `projFwd` build a name by `n.str "_model"`; over handles
  building a name means INTERNING one, so a pure `NIdx → NIdx` cannot do it.
  Each map is therefore precomputed as an association list — finitely many
  entries, all of them interned once — and `renameBy` is its lookup.  This is
  what task #97b's closure audit predicted for the only higher-order argument
  it left standing (`renameConstsGo (f : NIdx → NIdx)`): "the only call site
  is the modeled-block contract, whose map is a lookup in a table, so a
  concrete map type is likely and no closure need survive".  `renameBy tbl`
  is still a partial application at the call; making `renameConsts` take the
  table itself is a one-line change to `Arena/ExprOps.lean` that the Rust
  side (P4) should make, and it is recorded in DESIGN.md.
* **The three `foldlM`s are explicit recursions** (`checkIndMembers`,
  `installIndRecs`, `installProjFns`), per DESIGN §3.4's rule that a list
  fold with a partially applied step is a helper of its own.
* **`eqApp3?` spells con-leche's nested `Expr` pattern once.**
  `.app (.app (.app (.const c [ℓ]) ty) l) r` is four `view`s over handles and
  three of this module's checks match it; the twin reads it in one function.
-/
import ConRon.Arena.Inductives.SumParts

namespace ConRon.Arena

open ConLeche
open ConRon.Arena.IndBase (unwrapOr checkConstantVal checkDefEqList checkTypedList
  checkAnnotList isEqHead eqHeadLevel findCV? openPisAtFvars allLevelParamsDefined
  domsMatch domsMatchRenamed checkProjShape checkProjRule unresolvedConstsError
  recsFormSuffix eqBasisStored)

/-! ## The renaming tables -/

/-- con-leche: none — look a name up in a precomputed rename table; a name the
table does not mention is its own image.  See the module note. -/
def renameBy (tbl : List (NIdx × NIdx)) (n : NIdx) : NIdx :=
  match tbl.find? (·.1 == n) with
  | some p => p.2
  | none => n

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
The block renaming as a table: every member name maps to its `_model`
companion, every other name to itself. -/
def blockRenameTable (blockNames : List NIdx) : AM (List (NIdx × NIdx)) :=
  match blockNames with
  | [] => pure []
  | n :: ns => do
    let m ← internNNode (.str n "_model")
    pure ((n, m) :: (← blockRenameTable ns))

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack —
rename a model-side projection type back to public names, as a table. -/
def projBack (T ctor : NIdx) (nF : Nat) : AM (List (NIdx × NIdx)) := do
  let tm ← internNNode (.str T "_model")
  let cm ← internNNode (.str ctor "_model")
  let rec go : Nat → Nat → AM (List (NIdx × NIdx))
    | 0, _ => pure []
    | k + 1, j => do
      let a ← projModelName T j
      let b ← projFnName T j
      pure ((a, b) :: (← go k (j + 1)))
  pure ((tm, T) :: (cm, ctor) :: (← go nF 0))

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd — the
forward (public → model) map on the projection family, as a table. -/
def projFwd (T ctor : NIdx) (nF : Nat) : AM (List (NIdx × NIdx)) := do
  let tm ← internNNode (.str T "_model")
  let cm ← internNNode (.str ctor "_model")
  let rec go : Nat → Nat → AM (List (NIdx × NIdx))
    | 0, _ => pure []
    | k + 1, j => do
      let a ← projFnName T j
      let b ← projModelName T j
      pure ((a, b) :: (← go k (j + 1)))
  pure ((T, tm) :: (ctor, cm) :: (← go nF 0))

/-! ## The equation pattern -/

/-- con-leche: none — con-leche's `.app (.app (.app (.const c [ℓ]) ty) l) r`,
the shape of every pinned iota/eta/unit statement body, read in one function:
the head's name, its single level, the type slot and the two sides. -/
def eqApp3? (h : EIdx) : AM (Option (NIdx × LIdx × EIdx × EIdx × EIdx)) := do
  match ← view h with
  | .app f1 r => do
    match ← view f1 with
    | .app f2 l => do
      match ← view f2 with
      | .app f3 ty => do
        match ← view f3 with
        | .const c us => do
          match ← viewLs us with
          | [lv] => pure (some (c, lv, ty, l, r))
          | _ => pure none
        | _ => pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-! ## The iota certificates -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:31-53 checkIotaSidesTy
Certify that both sides of a modeled iota equation inhabit the equation's
type, and that the equation's type slot itself inhabits the sort the
statement's own `Eq.{ℓA}` names. -/
def checkIotaSidesTy (mode : CheckMode) (feSelf : IFEnv) (depth : Nat)
    (alphaS lhsS rhsS : EIdx) (lA : LIdx) (cvName : NIdx) : AM Unit := do
  let tl ← inferTypeCore mode feSelf checkFuel depth lhsS
  unless ← isDefEqCore mode feSelf checkFuel depth tl alphaS do
    let n ← readName cvName
    fail (.notImplemented s!"iota statement lhs type for {n}")
  let tr ← inferTypeCore mode feSelf checkFuel depth rhsS
  unless ← isDefEqCore mode feSelf checkFuel depth tr alphaS do
    let n ← readName cvName
    fail (.notImplemented s!"iota statement rhs type for {n}")
  -- TT-lane check (task #147): the slot-sort certification is skipped unless
  -- `mode.ttChecks`.
  if mode.ttChecks then
    let ta ← inferTypeCore mode feSelf checkFuel depth alphaS
    let s ← internE (.sort lA)
    unless ← isDefEqCore mode feSelf checkFuel depth ta s do
      let n ← readName cvName
      fail (.notImplemented s!"iota statement type slot sort for {n}")

/-- con-leche: none — the name of a recursor's `j`-th model iota theorem,
`(cvName.str "_model").str "iota_j"`, interned. -/
def iotaThmName (cvName : NIdx) (j : Nat) : AM NIdx := do
  let m ← internNNode (.str cvName "_model")
  internNNode (.str m ("iota_" ++ toString j))

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
Check a *canonical* recursor rule's `iota_j` theorem, semantically. -/
def checkIotaThm (mode : CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) : AM Unit := do
  let nm ← readName cvName
  let cvt ← unwrapOr (← findCV? fe' (← iotaThmName cvName j))
    (.notImplemented s!"missing iota theorem for {nm}")
  unless cvt.levelParams = lps do
    fail (.notImplemented s!"iota theorem level mismatch for {nm}")
  -- open the theorem's telescope: params, motives, minors, fields
  let depth := rP + cnF
  let (fvs, tbody) ← unwrapOr (← openPisAtFvars depth cvt.type 0)
    (.notImplemented s!"iota statement shape mismatch for {nm}")
  -- the body is an equation (at one level, like the pinned `Eq`)
  let targs ← getAppArgs coreWalkFuel tbody
  let tfn ← getAppFn coreWalkFuel tbody
  unless ← isEqHead tfn do
    fail (.notImplemented s!"iota statement not an equation for {nm}")
  unless targs.length = 3 do
    fail (.notImplemented s!"iota statement not an equation for {nm}")
  let b0 ← internE (.bvar 0)
  let lhsS := targs.getD 1 b0
  let rhsS := targs.getD 2 b0
  -- the equation's left side: structurally the renamed recursor applied to
  -- the opened prefix variables, `mI - rP` index arguments, and the
  -- constructor at its own level parameters applied to the leading parameter
  -- variables and the field variables
  let xFvs := fvs.drop rP
  let largs ← getAppArgs coreWalkFuel lhsS
  let lfn ← getAppFn coreWalkFuel lhsS
  let lus ← paramLevels lps
  let wantHd ← internE (.const (renameBy f cvName) lus)
  unless lfn == wantHd do
    fail (.notImplemented s!"iota statement head mismatch for {nm}")
  unless largs.length = mI + 1 do
    fail (.notImplemented s!"iota statement arity mismatch for {nm}")
  unless largs.take rP == fvs.take rP do
    fail (.notImplemented s!"iota statement prefix mismatch for {nm}")
  let major := largs.getLastD b0
  let cus ← paramLevels cvj.levelParams
  let cHd ← internE (.const (renameBy f r.ctor) cus)
  let wantMajor ← mkAppN cHd (fvs.take cnP ++ xFvs)
  unless major == wantMajor do
    fail (.notImplemented s!"iota statement major mismatch for {nm}")
  -- the constructor's telescope (renamed), instantiated at the major's
  -- arguments: field domains and the canonical index tuple
  unless (← stripPis (cnP + cnF) cvj.type).isSome do
    fail (.notImplemented s!"iota constructor telescope for {nm}")
  let ctyR ← renameConstsFast coreWalkFuel (renameBy f) cvj.type
  let (cdoms, cres) ← unwrapOr
      (← instPisAtF coreWalkFuel (fvs.take cnP ++ xFvs) ctyR)
      (.notImplemented s!"iota constructor telescope for {nm}")
  let cargs ← getAppArgs coreWalkFuel cres
  unless cargs.length = cnP + (mI - rP) do
    fail (.notImplemented s!"iota constructor indices for {nm}")
  checkDefEqList mode feSelf depth ((largs.drop rP).take (mI - rP)) (cargs.drop cnP)
  checkDefEqList mode feSelf depth (← xFvs.mapM fvarTypeD) (cdoms.drop cnP)
  -- the statement's prefix domains are the recursor's (renamed)
  let tyAR ← renameConstsFast coreWalkFuel (renameBy f) tyA
  let (rdoms, _) ← unwrapOr (← instPisAtF coreWalkFuel (fvs.take rP) tyAR)
    (.notImplemented s!"iota recursor telescope for {nm}")
  checkDefEqList mode feSelf depth (← (fvs.take rP).mapM fvarTypeD) rdoms
  -- the rule's λ-domains are the public recursor prefix and constructor field
  -- domains
  let (fvsP, _) ← unwrapOr (← openPisAtFvars rP tyA 0)
    (.notImplemented s!"iota recursor telescope for {nm}")
  let (cdomsP, crestP) ← unwrapOr
      (← instPisAtF coreWalkFuel (fvsP.take cnP) cvj.type)
      (.notImplemented s!"iota constructor telescope for {nm}")
  checkDefEqList mode feSelf depth (← (fvsP.take cnP).mapM fvarTypeD) cdomsP
  let (xFvsP, _) ← unwrapOr (← openPisAtFvars cnF crestP rP)
    (.notImplemented s!"iota constructor telescope for {nm}")
  let (ldoms, _) ← unwrapOr (← instLamsAtF coreWalkFuel (fvsP ++ xFvsP) rhsA)
    (.notImplemented s!"rule shape mismatch for {nm}")
  checkDefEqList mode feSelf depth (← (fvsP ++ xFvsP).mapM fvarTypeD) ldoms
  -- the right side: definitionally the rule's applied rhs
  let rhsR ← renameConstsFast coreWalkFuel (renameBy f) rhsA
  let rhsApplied ← mkAppN rhsR fvs
  unless ← isDefEqCore mode feSelf checkFuel depth rhsS rhsApplied do
    fail (.notImplemented s!"iota statement mismatch for {nm}")
  checkIotaSidesTy mode feSelf depth (targs.getD 0 b0) lhsS rhsS
    (← eqHeadLevel tfn) cvName

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
The nested-shape data of a non-canonical rule: the constructor's level and
parameter instantiations, read off the recursor type's major-premise domain.
The level list is a `List LIdx`, the shape `IRecRuleFire.nested` stores
(`Arena/Env.lean`). -/
def nestedRuleShape (fe' feSelf : IFEnv) (cvName : NIdx) (lps : List NIdx)
    (tyA : EIdx) (mI rP cnP j : Nat) : AM (Option (List LIdx × List EIdx)) := do
  let thm ← iotaThmName cvName j
  if !((← findCV? fe' thm).isSome && decide (rP ≤ mI)) then pure none else
  match ← stripPis mI tyA with
  | some (_, rest) => do
    match ← view rest with
    | .forallE dom _ _ => do
      match ← view (← getAppFn coreWalkFuel dom) with
      | .const _D lvlsIdx => do
        let args ← getAppArgs coreWalkFuel dom
        let k := mI - rP
        let pins ← (args.take cnP).mapM (lowerBVarsFast coreWalkFuel k 0)
        let lifted ← pins.mapM (fun p => liftLooseBVarsFast coreWalkFuel k 0 p)
        let idxSpine ← bvarsDesc k
        let ks ← readNames lps
        let lvls ← viewLs lvlsIdx
        let lvlVals ← readLevels lvlsIdx
        let pinsOk ← pins.allM fun p => do
          pure (!(← hasFvarFast coreWalkFuel p) &&
            (← looseBVarsBoundedFast coreWalkFuel rP p) &&
            (← constsResolve feSelf coreWalkFuel p) &&
            (← allLevelParamsDefined lps p))
        if args.length = cnP + k ∧ args.take cnP == lifted ∧
            args.drop cnP == idxSpine ∧ pinsOk ∧
            lvlVals.all (Level.allParamsDefined ks) then
          pure (some (lvls, pins))
        else pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
Check a *nested-auxiliary* recursor rule's `iota_j` theorem — the
generalization of `checkIotaThm` to rules whose constructor parameters and
levels are fixed instantiations. -/
def checkIotaThmN (mode : CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) : AM IRecRuleFire := do
  match ← nestedRuleShape fe' feSelf cvName lps tyA mI rP cnP j with
  | none => pure .inert
  | some (lvls, pins) => do
  let nm ← readName cvName
  let cvt ← unwrapOr (← findCV? fe' (← iotaThmName cvName j))
    (.notImplemented s!"missing iota theorem for {nm}")
  unless cvt.levelParams = lps do
    fail (.notImplemented s!"iota theorem level mismatch for {nm}")
  let depth := rP + cnF
  let (fvs, tbody) ← unwrapOr (← openPisAtFvars depth cvt.type 0)
    (.notImplemented s!"iota statement shape mismatch for {nm}")
  let targs ← getAppArgs coreWalkFuel tbody
  let tfn ← getAppFn coreWalkFuel tbody
  unless ← isEqHead tfn do
    fail (.notImplemented s!"iota statement not an equation for {nm}")
  unless targs.length = 3 do
    fail (.notImplemented s!"iota statement not an equation for {nm}")
  let b0 ← internE (.bvar 0)
  let lhsS := targs.getD 1 b0
  let rhsS := targs.getD 2 b0
  let xFvs := fvs.drop rP
  let pinsF ← pins.mapM fun p => do
    instSpine coreWalkFuel (fvs.take rP) (rP - 1)
      (← renameConstsFast coreWalkFuel (renameBy f) p)
  let largs ← getAppArgs coreWalkFuel lhsS
  let lfn ← getAppFn coreWalkFuel lhsS
  let lus ← paramLevels lps
  let wantHd ← internE (.const (renameBy f cvName) lus)
  unless lfn == wantHd do
    fail (.notImplemented s!"iota statement head mismatch for {nm}")
  unless largs.length = mI + 1 do
    fail (.notImplemented s!"iota statement arity mismatch for {nm}")
  unless largs.take rP == fvs.take rP do
    fail (.notImplemented s!"iota statement prefix mismatch for {nm}")
  let major := largs.getLastD b0
  let lvlsIdx ← internLsNode lvls
  let cHd ← internE (.const (renameBy f r.ctor) lvlsIdx)
  let wantMajor ← mkAppN cHd (pinsF ++ xFvs)
  unless major == wantMajor do
    fail (.notImplemented s!"iota statement major mismatch for {nm}")
  -- the constructor's telescope at the stored level instantiations (renamed)
  let (_, cbody0) ← unwrapOr (← stripPis (cnP + cnF) cvj.type)
    (.notImplemented s!"iota constructor telescope for {nm}")
  unless (match ← view (← getAppFn coreWalkFuel cbody0) with
      | .const _ _ => true
      | _ => false) do
    fail (.notImplemented s!"iota constructor residual head for {nm}")
  let ctyL ← instLPFast coreWalkFuel cvj.levelParams lvlsIdx cvj.type
  let ctyR ← renameConstsFast coreWalkFuel (renameBy f) ctyL
  let (cdoms, cres) ← unwrapOr (← instPisAtF coreWalkFuel (pinsF ++ xFvs) ctyR)
    (.notImplemented s!"iota constructor telescope for {nm}")
  let cargs ← getAppArgs coreWalkFuel cres
  unless cargs.length = cnP + (mI - rP) do
    fail (.notImplemented s!"iota constructor indices for {nm}")
  checkDefEqList mode feSelf depth ((largs.drop rP).take (mI - rP)) (cargs.drop cnP)
  checkDefEqList mode feSelf depth (← xFvs.mapM fvarTypeD) (cdoms.drop cnP)
  -- the statement's prefix domains are the recursor's (renamed)
  let tyAR ← renameConstsFast coreWalkFuel (renameBy f) tyA
  let (rdoms, _) ← unwrapOr (← instPisAtF coreWalkFuel (fvs.take rP) tyAR)
    (.notImplemented s!"iota recursor telescope for {nm}")
  checkDefEqList mode feSelf depth (← (fvs.take rP).mapM fvarTypeD) rdoms
  -- the rule's λ-domains are the public recursor prefix and the constructor's
  -- field domains at the public instantiations
  let (fvsP, _) ← unwrapOr (← openPisAtFvars rP tyA 0)
    (.notImplemented s!"iota recursor telescope for {nm}")
  let pinsP ← pins.mapM fun p => instSpine coreWalkFuel (fvsP.take rP) (rP - 1) p
  checkAnnotList mode feSelf depth pinsP
  let ctyL2 ← instLPFast coreWalkFuel cvj.levelParams lvlsIdx cvj.type
  let (cdomsP, crestP) ← unwrapOr (← instPisAtF coreWalkFuel pinsP ctyL2)
    (.notImplemented s!"iota constructor telescope for {nm}")
  checkTypedList mode feSelf depth pinsP cdomsP
  let (xFvsP, crest2P) ← unwrapOr (← openPisAtFvars cnF crestP rP)
    (.notImplemented s!"iota constructor telescope for {nm}")
  unless (← getAppArgs coreWalkFuel crest2P).length == cnP + (mI - rP) do
    fail (.notImplemented s!"iota constructor arity for {nm}")
  let (ldoms, _) ← unwrapOr (← instLamsAtF coreWalkFuel (fvsP ++ xFvsP) rhsA)
    (.notImplemented s!"rule shape mismatch for {nm}")
  checkDefEqList mode feSelf depth (← (fvsP ++ xFvsP).mapM fvarTypeD) ldoms
  let rhsR ← renameConstsFast coreWalkFuel (renameBy f) rhsA
  let rhsApplied ← mkAppN rhsR fvs
  unless ← isDefEqCore mode feSelf checkFuel depth rhsS rhsApplied do
    fail (.notImplemented s!"iota statement mismatch for {nm}")
  checkIotaSidesTy mode feSelf depth (targs.getD 0 b0) lhsS rhsS
    (← eqHeadLevel tfn) cvName
  pure (.nested lvls pins)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:319-360 checkIotaRule
Check one modeled recursor rule: generic well-formedness of the right-hand
side, then the model's `iota_j` theorem. -/
def checkIotaRule (mode : CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP j : Nat) (r : IRecRule) : AM IRecRule := do
  let nm ← readName cvName
  let some (.ctorInfo cvj cnP cnF) := fe'.find? r.ctor
    | do
      let cn ← readName r.ctor
      fail (.invalid s!"iota rule constructor {cn} not stored")
  unless r.nfields = cnF do
    fail (.invalid "rule field count mismatch")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 r.rhs do
    fail (.invalid s!"loose bound variable in rule of {nm}")
  if ← hasFvarFast coreWalkFuel r.rhs then
    fail (.invalid s!"free variable in rule of {nm}")
  let rhsA ← annotateCore mode feSelf checkFuel 0 r.rhs
  unless ← allLevelParamsDefined lps rhsA do
    fail (.invalid s!"undeclared universe parameter in rule of {nm}")
  unless ← constsResolve feSelf coreWalkFuel rhsA do
    fail (← unresolvedConstsError s!"rule of {nm}" rhsA)
  -- the rule's rhs must be a λ-telescope over the recursor prefix and the
  -- constructor fields (so it can be applied positionally)
  unless (← stripLams (rP + cnF) rhsA).isSome do
    fail (.notImplemented s!"rule shape mismatch for {nm}")
  let _rhsTy ← inferTypeCore mode feSelf checkFuel 0 rhsA
  -- the firing mode is computed once, here, and stored on the rule
  let fire ← if ← recRulePlain coreWalkFuel tyA mI rP cnP then do
      checkIotaThm mode fe' feSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA
      pure IRecRuleFire.plain
    else
      checkIotaThmN mode fe' feSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA
  recRuleBits fe' cvName
    { r with rhs := rhsA, ctorParams := cnP, fire := fire, paramsBlind := false }

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:362-371 checkIotaRules
The per-rule check, folded over a modeled recursor's rules. -/
def checkIotaRules (mode : CheckMode) (fe' feSelf : IFEnv)
    (f : List (NIdx × NIdx)) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx)
    (mI rP : Nat) : Nat → List IRecRule → AM (List IRecRule)
  | _, [] => pure []
  | j, r :: rest => do
    let r' ← checkIotaRule mode fe' feSelf f cvName lps tyA mI rP j r
    let rest' ← checkIotaRules mode fe' feSelf f cvName lps tyA mI rP (j + 1) rest
    pure (r' :: rest')

/-! ## The block's members -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
Check a block member's constant against its `_model` counterpart. -/
def checkMemberVal (mode : CheckMode) (blockNames : List NIdx) (fe' : IFEnv)
    (cv : IConstantVal) : AM IConstantVal := do
  let f ← blockRenameTable blockNames
  let cvA ← checkConstantVal mode fe' cv
  let an ← readName cvA.name
  -- a member may not itself be shaped like a model companion, so the block
  -- renaming can never map onto a member
  if Name.isModelSuffix an then
    fail (.invalid s!"model-shaped member name {an}")
  -- the model counterpart
  let mn ← internNNode (.str cvA.name "_model")
  let some (.defnInfo cvm _mval _) := fe'.find? mn
    | do
      let hd ← readName (blockNames.headD cvA.name)
      fail (.notImplemented s!"no install route for inductive block \
        {hd}: no direct route recognises it and no model for {an} was generated")
  unless cvm.levelParams = cvA.levelParams do
    fail (.notImplemented s!"model level parameters mismatch for {an}")
  let renamed ← renameConstsFast coreWalkFuel (renameBy f) cvA.type
  unless renamed == cvm.type do
    fail (.notImplemented s!"model type mismatch for {an}")
  pure cvA

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:403-414 checkIndMember
Check and install one non-recursor member of a modeled inductive block against
its `_model` counterpart. -/
def checkIndMember (mode : CheckMode) (blockNames : List NIdx) (caps : IIndCaps)
    (fe' : IFEnv) (ci : IConstantInfo) : AM IFEnv := do
  let cvA ← checkMemberVal mode blockNames fe' (← ci.toConstantVal)
  match ci with
  | .indInfo _ _ => pure (fe'.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe'.push (.ctorInfo cvA nP nF))
  | _ => do
    let an ← readName cvA.name
    fail (.invalid s!"non-inductive member {an} in block")

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
The member fold of `checkModeled`, as an explicit recursion (DESIGN §3.4: a
`foldlM` with a partially applied step is a helper of its own). -/
def checkIndMembers (mode : CheckMode) (blockNames : List NIdx) (caps : IIndCaps)
    (fe : IFEnv) : List IConstantInfo → AM IFEnv
  | [] => pure fe
  | ci :: rest => do
    let fe' ← checkIndMember mode blockNames caps fe ci
    checkIndMembers mode blockNames caps fe' rest

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:416-433 provisionRecs
Phase 0 of the recursor group: check each recursor's constant and provision it
*rule-less* on top of the previous ones. -/
def provisionRecs (mode : CheckMode) (blockNames : List NIdx) :
    IFEnv → List IConstantInfo →
    AM (IFEnv × List (IConstantVal × Nat × Nat × List IRecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      let cvA ← checkMemberVal mode blockNames feAcc (← ci.toConstantVal)
      let (feSelf, others) ← provisionRecs mode blockNames
        (feAcc.push (.recInfo cvA mI rP [])) rest
      pure (feSelf, (cvA, mI, rP, rules) :: others)
    | _ => fail (.notImplemented "recursor before other block members")

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
The install fold of `checkIndRecs`, as an explicit recursion. -/
def installIndRecs (mode : CheckMode) (fe₂ feSelf : IFEnv) (f : List (NIdx × NIdx))
    (acc : IFEnv) : List (IConstantVal × Nat × Nat × List IRecRule) → AM IFEnv
  | [] => pure acc
  | c :: cs => do
    let rules' ← checkIotaRules mode fe₂ feSelf f c.1.name c.1.levelParams c.1.type
      c.2.1 c.2.2.1 0 c.2.2.2
    installIndRecs mode fe₂ feSelf f (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')) cs

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
Check and install a block's recursors *as a group*: every rule right-hand side
may mention any of them, so all are provisioned rule-less together and
installed together. -/
def checkIndRecs (mode : CheckMode) (blockNames : List NIdx) (fe₂ : IFEnv)
    (recs : List IConstantInfo) : AM IFEnv := do
  if recs.isEmpty then
    pure fe₂
  else do
    let f ← blockRenameTable blockNames
    -- iota statements are equations: pin the pinned equality former
    unless ← eqBasisStored fe₂ do
      fail (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (feSelf, checked) ← provisionRecs mode blockNames fe₂ recs
    installIndRecs mode fe₂ feSelf f fe₂ checked

/-! ## The projection functions -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:475-495 checkProjLookups
Stage 1 of `checkProjFn`: the stored constants the projection depends on. -/
def checkProjLookups (fe' : IFEnv) (T ctorName : NIdx) (lps : List NIdx)
    (nP nF i : Nat) : AM (IConstantVal × IConstantVal) := do
  let some (.ctorInfo cvj cnP cnF) := fe'.find? ctorName
    | fail (.notImplemented "projection constructor not stored")
  unless cnP = nP ∧ cnF = nF do
    fail (.notImplemented "projection constructor arity mismatch")
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

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:497-511 checkProjTy
Stage 2: the public projection type — the model's, renamed back (pinned by the
renaming roundtrip), well-formed and parameter-led. -/
def checkProjTy (fe' : IFEnv) (T ctorName : NIdx) (lps : List NIdx)
    (mty : EIdx) (nP nF : Nat) : AM EIdx := do
  let back ← projBack T ctorName nF
  let fwd ← projFwd T ctorName nF
  let pty ← renameConstsFast coreWalkFuel (renameBy back) mty
  unless (← renameConstsFast coreWalkFuel (renameBy fwd) pty) == mty do
    fail (.notImplemented "projection type roundtrip")
  unless ← constsResolve fe' coreWalkFuel pty do
    fail (.notImplemented "projection type resolution")
  unless (← looseBVarsBoundedFast coreWalkFuel 0 pty) &&
      !(← hasFvarFast coreWalkFuel pty) &&
      (← allLevelParamsDefined lps pty) do
    fail (.notImplemented "projection type wellformedness")
  unless (← stripPis (nP + 1) pty).isSome do
    fail (.notImplemented "projection type telescope")
  pure pty

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
Stage 4: the model's `proj_i.iota` theorem pins the rule. -/
def checkProjIota (mode : CheckMode) (fe' feSelf : IFEnv) (T ctorName : NIdx)
    (lps : List NIdx) (cvj : IConstantVal) (nP nF i : Nat) : AM Unit := do
  let pmn ← projModelName T i
  let itn ← internNNode (.str pmn "iota")
  let some (.thmInfo tcv _) := fe'.find? itn
    | fail (.notImplemented "missing projection iota theorem")
  unless tcv.levelParams = lps do
    fail (.notImplemented "projection iota level mismatch")
  let some (sbinders, sbody) ← stripPis (nP + nF) tcv.type
    | fail (.notImplemented "projection iota telescope")
  let some (cbindersR, _) ← stripPis (nP + nF) cvj.type
    | fail (.notImplemented "projection constructor telescope")
  let fwd ← projFwd T ctorName nF
  unless ← domsMatchRenamed (renameBy fwd) sbinders cbindersR 0 0 (nP + nF) do
    fail (.notImplemented "projection iota domain mismatch")
  let depth := nP + nF
  let pArgs ← structPsAt (nF + 1) nP
  let xArgs ← bvarsDesc nF
  let cmn ← internNNode (.str ctorName "_model")
  let cus ← paramLevels cvj.levelParams
  let cHd ← internE (.const cmn cus)
  let mkSpine ← mkAppN cHd (pArgs ++ xArgs)
  let pus ← paramLevels lps
  let pHd ← internE (.const pmn pus)
  let lhsS ← mkAppN pHd (pArgs ++ [mkSpine])
  match ← eqApp3? sbody with
  | some (c, _l, _tySlot, lhsC, rhsC) => do
    unless c = (← pin eqName) do
      fail (.notImplemented "projection iota head")
    unless lhsC == lhsS do
      fail (.notImplemented "projection iota redex mismatch")
    let fld ← internE (.bvar (nF - 1 - i))
    unless rhsC == fld do
      fail (.notImplemented "projection iota field mismatch")
  | none => fail (.notImplemented "projection iota body shape")
  -- certify both equation sides against the statement's type slot
  let (_, sbodyO) ← unwrapOr (← openPisAtFvars depth tcv.type 0)
    (.notImplemented "projection iota telescope")
  let targsO ← getAppArgs coreWalkFuel sbodyO
  let b0 ← internE (.bvar 0)
  checkIotaSidesTy mode feSelf depth (targsO.getD 0 b0) (targsO.getD 1 b0)
    (targsO.getD 2 b0) (← eqHeadLevel (← getAppFn coreWalkFuel sbody)) pmn

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:565-584 checkProjFn
Check and install the public projection function for field `i` of a modeled
single-constructor structure.  The function is stored as a degenerate recursor
(no motive, no minors) carrying one rule. -/
def checkProjFn (mode : CheckMode) (fe' : IFEnv) (T ctorName : NIdx)
    (lps : List NIdx) (nP nF i : Nat) : AM IFEnv := do
  let (cvj, mcv) ← checkProjLookups fe' T ctorName lps nP nF i
  let pty ← checkProjTy fe' T ctorName lps mcv.type nP nF
  checkProjShape pty cvj.type nP nF
  unless i < nF do
    fail (.invalid "projection index out of range")
  let rhsA ← checkProjRule mode fe' pty cvj lps nP nF i
  checkProjIota mode fe' fe' T ctorName lps cvj nP nF i
  let pn ← projFnName T i
  let rule ← projFnRule fe' T ctorName pty nP nF i rhsA
  pure (fe'.push (.recInfo ⟨pn, lps, pty⟩ nP nP [rule]))

/-! ## The capabilities -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
Does the model document structural eta for this single-constructor block — a
`T._model.eta` theorem with the pinned statement? -/
def checkEtaThm (mode : CheckMode) (fe' : IFEnv) (T ctorName : NIdx)
    (lps : List NIdx) (nP nF : Nat) : AM Bool := do
  let tm ← internNNode (.str T "_model")
  let etn ← internNNode (.str tm "eta")
  let cm ← internNNode (.str ctorName "_model")
  match fe'.find? etn, fe'.find? tm, fe'.find? cm with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _ _), some (.defnInfo cvmC _ _) => do
    if !(← eqBasisStored fe') then pure false else
    if !(tcv.levelParams == lps && cvmT.levelParams == lps &&
        cvmC.levelParams == lps) then pure false else do
    -- the projection models exist at the family's level parameters
    let projsOk ← (List.range nF).allM fun j => do
      match fe'.find? (← projModelName T j) with
      | some (.defnInfo cvmj _ _) => pure (cvmj.levelParams == lps)
      | _ => pure false
    if !projsOk then pure false else
    match ← stripPis (nP + 1) tcv.type, ← stripPis nP cvmT.type with
    | some (sbinders, sbody), some (tbindersM, tbodyM) => do
      if !domsMatch sbinders tbindersM 0 0 nP then pure false else do
      let us ← paramLevels lps
      let tHd ← internE (.const tm us)
      let psLo ← structPsAt 0 nP
      let famLo ← mkAppN tHd psLo
      let xdomOk ← match sbinders[nP]? with
        | some (xdom, _) => pure (xdom == famLo)
        | none => pure false
      if !xdomOk then pure false else do
      let psHi ← structPsAt 1 nP
      let famHi ← mkAppN tHd psHi
      match ← eqApp3? sbody with
      | some (c, lA, tySlot, lhsC, rhsC) => do
        let b0 ← internE (.bvar 0)
        let cHd ← internE (.const cm us)
        let projArgs ← (List.range nF).mapM fun j => do
          let pHd ← internE (.const (← projModelName T j) us)
          mkAppN pHd (psHi ++ [b0])
        let wantRhs ← mkAppN cHd (psHi ++ projArgs)
        let sortA ← internE (.sort lA)
        pure (c == (← pin eqName) && lhsC == b0 && tySlot == famHi &&
          rhsC == wantRhs && (!mode.ttChecks || tbodyM == sortA))
      | none => pure false
    | _, _ => pure false
  | _, _, _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
Does the model document unit-likeness for this block — a `T._model.unitlike`
theorem with the pinned statement `∀ p⃗ (x y : T._model p⃗), x = y`? -/
def checkUnitThm (mode : CheckMode) (fe' : IFEnv) (T : NIdx) (lps : List NIdx)
    (nP : Nat) : AM Bool := do
  let tm ← internNNode (.str T "_model")
  let utn ← internNNode (.str tm "unitlike")
  match fe'.find? utn, fe'.find? tm with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _ _) => do
    if !(← eqBasisStored fe') then pure false else
    if !(tcv.levelParams == lps && cvmT.levelParams == lps) then pure false else
    match ← stripPis (nP + 2) tcv.type, ← stripPis nP cvmT.type with
    | some (sbinders, sbody), some (tbindersM, tbodyM) => do
      if !domsMatch sbinders tbindersM 0 0 nP then pure false else do
      let us ← paramLevels lps
      let tHd ← internE (.const tm us)
      let fam0 ← mkAppN tHd (← structPsAt 0 nP)
      let fam1 ← mkAppN tHd (← structPsAt 1 nP)
      let fam2 ← mkAppN tHd (← structPsAt 2 nP)
      let xOk ← match sbinders[nP]? with
        | some (xdom, _) => pure (xdom == fam0)
        | none => pure false
      let yOk ← match sbinders[nP + 1]? with
        | some (ydom, _) => pure (ydom == fam1)
        | none => pure false
      if !(xOk && yOk) then pure false else
      match ← eqApp3? sbody with
      | some (c, lA, tySlot, lhsC, rhsC) => do
        let b0 ← internE (.bvar 0)
        let b1 ← internE (.bvar 1)
        let sortA ← internE (.sort lA)
        pure (c == (← pin eqName) && lhsC == b1 && rhsC == b0 &&
          tySlot == fam2 && (!mode.ttChecks || tbodyM == sortA))
      | none => pure false
    | _, _ => pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:682-710 ctorTargetsFam
**Official's structure-likeness, read off the block's own constructor**: one
constructor and no indices, i.e. the constructor targets the family at exactly
its parameters. -/
def ctorTargetsFam (ctorTy : EIdx) (T : NIdx) (lps : List NIdx) (nP nF : Nat) :
    AM Bool := do
  match ← stripPis (nP + nF) ctorTy with
  | some (_, cbody) => do
    let fam ← structFam T lps nP nF
    pure (cbody == fam)
  | none => pure false

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:712-722 installProjFnStep
One projection-function install step (skipped where the model's projection
artifact is absent). -/
def installProjFnStep (mode : CheckMode) (T ctorName : NIdx) (lps : List NIdx)
    (nP nF : Nat) (e : IFEnv) (i : Nat) : AM IFEnv := do
  if (e.find? (← projModelName T i)).isSome then
    checkProjFn mode e T ctorName lps nP nF i
  else pure e

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
The projection fold of `checkModeled`, as an explicit recursion. -/
def installProjFns (mode : CheckMode) (T ctorName : NIdx) (lps : List NIdx)
    (nP nF : Nat) (fe : IFEnv) : Nat → Nat → AM IFEnv
  | 0, _ => pure fe
  | k + 1, i => do
    let fe' ← installProjFnStep mode T ctorName lps nP nF fe i
    installProjFns mode T ctorName lps nP nF fe' k (i + 1)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:724-735 indBlockCaps
The capabilities recorded for a single-constructor modeled block. -/
def indBlockCaps (mode : CheckMode) (fe : IFEnv) (cvT cvC : IConstantVal)
    (nP nF : Nat) : AM IIndCaps := do
  let eta := (cvC.levelParams = cvT.levelParams) &&
    (← checkEtaThm mode fe cvT.name cvC.name cvT.levelParams nP nF)
  pure { eta := eta
         etaCtor := cvC.name
         etaParams := nP
         etaFields := nF
         unitlike := ← checkUnitThm mode fe cvT.name cvT.levelParams nP
         unitParams := nP
         ruleK := nF == 0 && (← piResultIsProp cvT.type)
         sortZ := ← piResultZ cvT.type }

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:744-779 ctorResidualOk
**Task #136: an eta-capable family's constructor returns the family applied to
its parameters.**  The subject is the STORED constant. -/
def ctorResidualOk (mode : CheckMode) (fe' : IFEnv) (T ctorName : NIdx)
    (lps : List NIdx) (nP nF : Nat) (eta : Bool) : AM Bool := do
  if !mode.ttChecks || !eta then pure true else
  match fe'.find? ctorName with
  | some (.ctorInfo cvCA _ _) => do
    match ← stripPis (nP + nF) cvCA.type with
    | some (_, cbody) => do
      let fam ← structFam T lps nP nF
      pure (cbody == fam)
    | none => pure false
  | _ => pure false

/-! ## The install -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
Check and install a modeled inductive block: every member is checked against
its `_model` counterpart, then stored as a real inductive-kind constant. -/
def checkModeled (mode : CheckMode) (fe : IFEnv) (block : List IConstantInfo) :
    AM IFEnv := do
  -- the recursors must form a suffix of the block: their rules may mention
  -- each other, so they install as a group after everything else
  let recs := block.filter IndBase.isRecInfo
  let nonrecs := block.filter (fun ci => !IndBase.isRecInfo ci)
  -- the tag pass, not the derived structural equality on the members' types
  unless recsFormSuffix block do
    fail (.notImplemented "recursor before other block members")
  let blockNames := block.map (·.name)
  match block.filter (fun ci => match ci with | .indInfo _ _ => true | _ => false),
    block.filter (fun ci => match ci with | .ctorInfo _ _ _ => true | _ => false) with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] => do
    let caps ← indBlockCaps mode fe cvT cvC nP nF
    let fe₂ ← checkIndMembers mode blockNames caps fe nonrecs
    let fe₃ ← checkIndRecs mode blockNames fe₂ recs
    -- the eta capability's constructor returns the family (task #136)
    unless ← ctorResidualOk mode fe₃ cvT.name cvC.name cvT.levelParams nP nF caps.eta do
      fail (.notImplemented "modeled structure: eta constructor residual")
    -- the whole projection name family must be ours to install
    unless ← (List.range nF).allM (fun j => do
        pure (fe₃.find? (← projFnName cvT.name j)).isNone) do
      fail (.invalid "projection name family taken")
    -- the projection functions: structure-like blocks only (task #175)
    if ← ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF then
      installProjFns mode cvT.name cvC.name cvT.levelParams nP nF fe₃ nF 0
    else pure fe₃
  | _, _ => do
    let fe₂ ← checkIndMembers mode blockNames {} fe nonrecs
    checkIndRecs mode blockNames fe₂ recs

end ConRon.Arena
