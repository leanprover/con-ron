/-
# `ConRon.Arena.Inductives.Base` — P2d-1's checker helpers, borrowed
(DESIGN.md §8, task #97d-2)

**This module is not one of the ten.**  The inductive installs of
`ConLeche/Kernel/Inductives/*` call a dozen declarations that belong to
`ConLeche/Kernel/{CheckerBase,Env,Level}.lean`, i.e. to the SIBLING task
(P2d-1: `Arena/{CheckerBase,DeclCheck,Checker,Canon,Pins,Basis,StdAxioms}.lean`).
The two tasks run at the same time, so — per the coordinator's concurrency
contract — the twins those installs need are written here, cited to the same
con-leche declarations P2d-1 cites, in a namespace of their own
(`ConRon.Arena.IndBase`) so that nothing clashes at merge.  **Every
declaration in this file is a duplicate to be deleted at merge**, replaced by
P2d-1's in `ConRon.Arena`; the list is in DESIGN.md's task section.

The one exception is `internExpr` / `internCI`, which exist here only to
intern con-leche's pinned `Eq` basis constant (`eqA`) — the comparand of
`checkIndRecs`' and `checkProjLookups`' "requires the pinned `Eq` basis"
guard.  P2d-1's `Arena/Basis.lean` builds that constant properly (the arena's
own `BasisKind.declsA`); until it lands, interning con-leche's own value is
the only spelling that makes the guard say what con-leche's says.  Weakening
it to "some `Eq` is stored" would make the arena ACCEPT blocks con-leche
rejects, which no placeholder may do.
-/
import ConRon.Arena.Inductives.StructParts
import ConRon.Arena.CheckerBase
import ConLeche.Kernel.BasisA

namespace ConRon.Arena.IndBase

open ConLeche
open ConRon.Arena

/-! ## `Option` unwrapping -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:233-239 unwrapOr — unwrap an
optional value or fail with the given error. -/
def unwrapOr {α : Type} (o : Option α) (err : CheckError) : AM α :=
  match o with
  | some a => pure a
  | none => fail err

/-! ## Level parameters -/

/-- con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup — are the names
pairwise distinct?  Over handles a name comparison is a handle comparison
(`denoteN` is injective, task #97a). -/
def nidxNodup : List NIdx → Bool
  | [] => true
  | n :: ns => !ns.contains n && nidxNodup ns

/-- con-leche: ConLeche/Kernel/Level.lean:251-268 Expr.allLevelParamsDefined
con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
Are all level parameters occurring in `e` among `params` (binder prop-ness
data included)?  con-leche's pure walk and its memoized twin are one function
here (task #97b's rule); the levels are READ BACK and con-leche's own
`Level.allParamsDefined` / `PropWhen.paramsDefined` decide them (DESIGN §8.3
lesson 4), and the memo is con-leche's own per-call table keyed by the node —
`params` is fixed for the walk. -/
def allLevelParamsDefinedGo (ks : List Name) (memo : Std.HashMap EIdx Bool) :
    Nat → EIdx → AM (Bool × Std.HashMap EIdx Bool)
  | 0, _ => fail (.internal "fuel exhausted: allLevelParamsDefined")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure (true, memo)
    | .lit _ => pure (true, memo)
    | .sort u => pure ((← readLevel u).allParamsDefined ks, memo)
    | v =>
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let (r, memo) ← match v with
          | .const _ us => pure ((← readLevels us).all (Level.allParamsDefined ks), memo)
          | .fvar _ t => allLevelParamsDefinedGo ks memo fuel t
          | .app f a => do
            let (b₁, memo) ← allLevelParamsDefinedGo ks memo fuel f
            if !b₁ then pure (false, memo) else
              allLevelParamsDefinedGo ks memo fuel a
          | .lam t b m | .forallE t b m => do
            let (b₁, memo) ← allLevelParamsDefinedGo ks memo fuel t
            if !b₁ then pure (false, memo) else do
              let (b₂, memo) ← allLevelParamsDefinedGo ks memo fuel b
              pure (b₂ && m.pw.paramsDefined ks, memo)
          | .letE t v b => do
            let (b₁, memo) ← allLevelParamsDefinedGo ks memo fuel t
            if !b₁ then pure (false, memo) else do
              let (b₂, memo) ← allLevelParamsDefinedGo ks memo fuel v
              if !b₂ then pure (false, memo) else
                allLevelParamsDefinedGo ks memo fuel b
          | .proj _ _ e => allLevelParamsDefinedGo ks memo fuel e
          | _ => pure (true, memo)
        pure (r, memo.insert h r)

/-- con-leche: ConLeche/Kernel/Level.lean:405-407 Expr.allLevelParamsDefinedFast
The executed `allLevelParamsDefined` (one memoized DAG walk). -/
def allLevelParamsDefined (params : List NIdx) (e : EIdx) : AM Bool := do
  let ks ← readNames params
  pure (← allLevelParamsDefinedGo ks ∅ coreWalkFuel e).1

/-! ## Telescopes opened at free variables -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:130-140 openPisAtFvars — open
the first `n` `∀`-binders at fresh free variables `0..n-1` (each fvar's type
is the binder domain, instantiated with the earlier fvars). -/
def openPisAtFvarsPlain : Nat → EIdx → Nat → AM (Option (List EIdx × EIdx))
  | 0, e, _ => pure (some ([], e))
  | n + 1, h, i => do
    match ← view h with
    | .forallE dom body _ => do
      let fv ← internE (.fvar i dom)
      let b ← instantiate1Fast coreWalkFuel body fv 0
      match ← openPisAtFvarsPlain n b (i + 1) with
      | some (fvs, e) => pure (some (fv :: fvs, e))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:153-167 openPisAtFvarsFGo —
core of the one-pass opening: `acc` holds the already-created fvars,
innermost binder first. -/
def openPisAtFvarsFGo (acc : List EIdx) :
    Nat → EIdx → Nat → AM (Option (List EIdx × EIdx))
  | 0, e, _ => do
    let r ← instantiateListFast coreWalkFuel e acc 0
    pure (some ([], r))
  | n + 1, h, i => do
    match ← view h with
    | .forallE dom body _ => do
      let d ← instantiateListFast coreWalkFuel dom acc 0
      let fv ← internE (.fvar i d)
      match ← openPisAtFvarsFGo (fv :: acc) n body (i + 1) with
      | some (fvs, e) => pure (some (fv :: fvs, e))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:169-176 openPisAtFvarsF —
one-pass `openPisAtFvars`; the fallback covers telescopes whose binders only
appear after substitution. -/
def openPisAtFvars (n : Nat) (e : EIdx) (i : Nat) :
    AM (Option (List EIdx × EIdx)) := do
  match ← openPisAtFvarsFGo [] n e i with
  | some r => pure (some r)
  | none => openPisAtFvarsPlain n e i

/-! ## Binder-domain comparisons

con-leche's `domsMatchAux` takes the right side's view as a function
`g : Nat → Expr → Expr` and is called at exactly two of them — the identity
and one `renameConsts`.  A function argument is a closure, which DESIGN §3.4
forbids in code Aeneas must translate (task #97b's closure audit), so the twin
is split into the two concrete forms.  The array variant `domsMatchAuxA` is
the same function at `List.toArray` and collapses into them. -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux
con-leche: ConLeche/Kernel/CheckerBase.lean:142-151 domsMatchAuxA
Compare binder domains at offsets `o₁`/`o₂` for `n` positions, the right side
taken as it stands (con-leche's `g = fun _ e => e`). -/
def domsMatch (bs₁ bs₂ : List (EIdx × BinderMeta)) (o₁ o₂ : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    match bs₁[o₁ + k]?, bs₂[o₂ + k]? with
    | some b₁, some b₂ => b₁.1 == b₂.1 && domsMatch bs₁ bs₂ o₁ o₂ k
    | _, _ => false

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux —
`domsMatch` with the right side renamed (`g = fun _ e => e.renameConsts f`,
`checkProjIota`'s instance). -/
def domsMatchRenamed (f : NIdx → NIdx) (bs₁ bs₂ : List (EIdx × BinderMeta))
    (o₁ o₂ : Nat) : Nat → AM Bool
  | 0 => pure true
  | k + 1 => do
    match bs₁[o₁ + k]?, bs₂[o₂ + k]? with
    | some b₁, some b₂ => do
      let r ← renameConstsFast coreWalkFuel f b₂.1
      if b₁.1 == r then domsMatchRenamed f bs₁ bs₂ o₁ o₂ k else pure false
    | _, _ => pure false

/-! ## The declaration front door -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:71-91 unresolvedConstsError —
**the verdict at a term whose constants do not all resolve**: a term that
mentions `sorryAx` DECLINES, anything else REJECTS as an unknown constant. -/
def unresolvedConstsError (where_ : String) (e : EIdx) : AM CheckError := do
  let sa ← pin sorryAxName
  if ← mentionsConst sa e then
    pure (.notImplemented s!"use of the sorryAx axiom in {where_}")
  else pure (.invalid s!"unknown constant in {where_}")

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal —
checks common to all declarations: fresh name, well-formed universe
parameters, and a type that is a type and mentions only declared parameters.
Returns the constant with its type **annotated**. -/
def checkConstantVal (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    AM IConstantVal := do
  if (fe.find? cv.name).isSome then do
    let n ← readName cv.name
    fail (.invalid s!"duplicate declaration {n}")
  if (← reservedBasisNames).contains cv.name then do
    let n ← readName cv.name
    fail (.invalid s!"reserved basis name {n}")
  if Name.isProjFnShape (← readName cv.name) then do
    let n ← readName cv.name
    fail (.invalid s!"reserved projection name {n}")
  unless nidxNodup cv.levelParams do
    let n ← readName cv.name
    fail (.invalid s!"duplicate universe parameters in {n}")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    let n ← readName cv.name
    fail (.invalid s!"loose bound variable in type of {n}")
  if ← hasFvarFast coreWalkFuel cv.type then do
    let n ← readName cv.name
    fail (.invalid s!"unexpected free variable in type of {n}")
  let type ← annotateCore mode fe checkFuel 0 cv.type
  unless ← allLevelParamsDefined cv.levelParams type do
    let n ← readName cv.name
    fail (.invalid s!"undeclared universe parameter in type of {n}")
  unless ← constsResolveFFast fe type do
    let n ← readName cv.name
    fail (← unresolvedConstsError s!"type of {n}" type)
  let stype ← inferTypeCore mode fe checkFuel 0 type
  let _u ← ensureSortCore mode fe checkFuel 0 stype
  pure { cv with type := type }

/-! ## The list checks -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList — check
each expression's inferred type against the corresponding expected type
(definitionally); throws on a length mismatch. -/
def checkTypedList (mode : CheckMode) (fe : IFEnv) (depth : Nat) :
    List EIdx → List EIdx → AM Unit
  | [], [] => pure ()
  | a :: as, t :: ts => do
    let ty ← inferTypeCore mode fe checkFuel depth a
    unless ← isDefEqCore mode fe checkFuel depth ty t do
      fail (.notImplemented "nested pin type mismatch")
    checkTypedList mode fe depth as ts
  | _, _ => fail (.notImplemented "nested pin arity mismatch")

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList — check
that each expression is a fixed point of the annotation pass in the given
context. -/
def checkAnnotList (mode : CheckMode) (fe : IFEnv) (depth : Nat) :
    List EIdx → AM Unit
  | [] => pure ()
  | a :: as => do
    let aA ← annotateCore mode fe checkFuel depth a
    unless aA == a do
      fail (.notImplemented "nested pin annotation mismatch")
    checkAnnotList mode fe depth as

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList —
pairwise definitional-equality check of two spines (throws on any mismatch,
including a length difference). -/
def checkDefEqList (mode : CheckMode) (fe : IFEnv) (depth : Nat) :
    List EIdx → List EIdx → AM Unit
  | [], [] => pure ()
  | a :: as, b :: bs => do
    unless ← isDefEqCore mode fe checkFuel depth a b do
      fail (.notImplemented "iota statement component mismatch")
    checkDefEqList mode fe depth as bs
  | _, _ => fail (.notImplemented "iota statement component arity")

/-! ## The pinned equality former -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:208-211 isEqHead — is the
expression the pinned equality former at one level? -/
def isEqHead (h : EIdx) : AM Bool := do
  match ← view h with
  | .const c us => do
    match ← viewLs us with
    | [_] => do pure (c == (← pin eqName))
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:213-220 eqHeadLevel — the level
an equality head carries.  Off shape it is `.zero`, which `isEqHead` has
already rejected wherever the result is used. -/
def eqHeadLevel (h : EIdx) : AM LIdx := do
  match ← view h with
  | .const _ us => do
    match ← viewLs us with
    | [l] => pure l
    | _ => zeroLevel
  | _ => zeroLevel

/-! ## Reading a stored constant -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:241-247 Env.findCV? — the
stored constant under `n`, as an `IConstantVal`, if any. -/
def findCV? (fe : IFEnv) (n : NIdx) : AM (Option IConstantVal) := do
  match fe.find? n with
  | some ci => pure (some (← ci.toConstantVal))
  | none => pure none

/-! ## The projection function's shape and rule -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:257-272 checkProjShape — the
projection type's parameter telescope is *syntactically* the constructor's,
and the constructor's residual is the family applied to exactly the
parameters. -/
def checkProjShape (pty ctorTy : EIdx) (nP nF : Nat) : AM Unit := do
  let some _ ← stripPis nP pty
    | fail (.notImplemented "projection type telescope")
  let some (_, cbody) ← stripPis (nP + nF) ctorTy
    | fail (.notImplemented "projection constructor telescope")
  unless (← getAppArgs coreWalkFuel cbody).length == nP do
    fail (.notImplemented "projection constructor residual arity")
  match ← view (← getAppFn coreWalkFuel cbody) with
  | .const _ _ => pure ()
  | _ => fail (.notImplemented "projection constructor residual head")

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule — stage
3 of the projection install: the reduction rule — λ over the constructor
telescope returning field `i`, annotated; its λ-domains stay the
constructor's. -/
def checkProjRule (mode : CheckMode) (fe : IFEnv) (pty : EIdx)
    (cvj : IConstantVal) (lps : List NIdx) (nP nF i : Nat) : AM EIdx := do
  let b ← internE (.bvar (nF - 1 - i))
  let some rhs ← pisToLams (nP + nF) cvj.type b
    | fail (.notImplemented "projection rule telescope")
  unless !(← hasFvarFast coreWalkFuel rhs) &&
      (← looseBVarsBoundedFast coreWalkFuel 0 rhs) do
    fail (.notImplemented "projection rule scoping")
  let rhsA ← annotateCore mode fe checkFuel 0 rhs
  unless (← allLevelParamsDefined lps rhsA) && (← constsResolveFFast fe rhsA) &&
      (← looseBVarsBoundedFast coreWalkFuel 0 rhsA) &&
      !(← hasFvarFast coreWalkFuel rhsA) do
    fail (.notImplemented "projection rule wellformedness")
  let some (rbinders, rrbody) ← stripLams (nP + nF) rhsA
    | fail (.notImplemented "projection rule telescope")
  unless rrbody == b do
    fail (.notImplemented "projection rule body")
  let some (cbindersR, _) ← stripPis (nP + nF) cvj.type
    | fail (.notImplemented "projection constructor telescope")
  unless domsMatch rbinders cbindersR 0 0 (nP + nF) do
    fail (.notImplemented "projection rule domain mismatch")
  -- the frame walks and the definitional parameter/domain pins (task #58)
  let some (fvsP, _) ← openPisAtFvars nP pty 0
    | fail (.notImplemented "projection type telescope")
  let some (cdomsP, crestP) ← instPisAtF coreWalkFuel fvsP cvj.type
    | fail (.notImplemented "projection constructor telescope")
  checkDefEqList mode fe (nP + nF) (← fvsP.mapM fvarTypeD) cdomsP
  let some (xFvs, _) ← openPisAtFvars nF crestP nP
    | fail (.notImplemented "projection constructor telescope")
  let some (ldoms, _) ← instLamsAtF coreWalkFuel (fvsP ++ xFvs) rhsA
    | fail (.notImplemented "projection rule telescope")
  checkDefEqList mode fe (nP + nF) (← (fvsP ++ xFvs).mapM fvarTypeD) ldoms
  let _rhsTy ← inferTypeCore mode fe checkFuel 0 rhsA
  pure rhsA

/-! ## The block's partition and its declared parameter count -/

/-- con-leche: ConLeche/Kernel/Env.lean:716-719 ConstantInfo.isRecInfo — is
this member a recursor record? -/
def isRecInfo : IConstantInfo → Bool
  | .recInfo _ _ _ _ => true
  | _ => false

/-- con-leche: ConLeche/Kernel/Env.lean:721-727 recsFormSuffix — do the
recursors form a suffix of the block?  The tag pass. -/
def recsFormSuffix : List IConstantInfo → Bool
  | [] => true
  | ci :: rest =>
    if isRecInfo ci then rest.all isRecInfo
    else recsFormSuffix rest

/-- con-leche: ConLeche/Kernel/Env.lean:588-622 indParamsOk — **the stream's
declared parameter count, checked as official checks it** (task #228).  Both
halves are one-sided on purpose: `false` means official rejects. -/
def indParamsOk (nP : Nat) : List IConstantInfo → AM Bool
  | [] => pure true
  | ci :: rest => do
    let ok ← match ci with
      | .indInfo cvT _ => do
        match ← piSortTeleLen? coreWalkFuel cvT.type with
        | some n => pure (decide (nP ≤ n))
        | none => pure true
      | .ctorInfo _ nPc _ => pure (nPc == nP)
      | _ => pure true
    if ok then indParamsOk nP rest else pure false

/-! ## The pinned `Eq` basis constant

The two "requires the pinned `Eq` basis" guards of the modeled route compare a
STORED constant with con-leche's own `eqA` — the annotated pin
(`ConLeche/Kernel/BasisA.lean`).  Over handles that comparison is handle
equality on an interned copy of the same value, which is the same predicate
because `denoteE` and `denoteN` are injective (task #97a).  P2d-1's
`Arena/Basis.lean` owns this; see the module note. -/

/-- con-leche: none — intern a con-leche `Level` list.  `internLevelList` of
`Arena/Monad.lean` under the name the interning of a basis constant wants. -/
def internLevelsL (us : List Level) : AM (List LIdx) := internLevelList us

/-- con-leche: none — intern a con-leche `Expr` into the store.  The arena's
terms come from the parser, which builds them node by node; a basis PIN is a
`ConLeche.Expr` VALUE, so it needs this one converter. -/
def internExpr : ConLeche.Expr → AM EIdx
  | .bvar i => internE (.bvar i)
  | .fvar idx ty => do internE (.fvar idx (← internExpr ty))
  | .sort u => do internE (.sort (← internLevel u))
  | .const n us => do internE (.const (← internName n) (← internLevels us))
  | .app f a => do internE (.app (← internExpr f) (← internExpr a))
  | .lam ty b m => do internE (.lam (← internExpr ty) (← internExpr b) m)
  | .forallE ty b m => do internE (.forallE (← internExpr ty) (← internExpr b) m)
  | .letE ty v b => do
    internE (.letE (← internExpr ty) (← internExpr v) (← internExpr b))
  | .lit l => internE (.lit l)
  | .proj s i e => do internE (.proj (← internName s) i (← internExpr e))

/-- con-leche: none — intern a con-leche `ConstantVal`. -/
def internCV (cv : ConstantVal) : AM IConstantVal := do
  pure ⟨← internName cv.name, ← cv.levelParams.mapM internName, ← internExpr cv.type⟩

/-- con-leche: none — intern a con-leche `IndCaps`. -/
def internCaps (c : IndCaps) : AM IIndCaps := do
  pure { eta := c.eta, etaCtor := ← internName c.etaCtor, etaParams := c.etaParams,
         etaFields := c.etaFields, unitlike := c.unitlike, unitParams := c.unitParams,
         ruleK := c.ruleK, sortZ := c.sortZ }

/-- con-leche: none — the pinned `Eq` basis constant, interned.  Task #97d-2
interned `ConLeche/Kernel/BasisA.lean`'s `eqA` here because P2d's part 1 did
not exist yet; it does, so this is `Arena/StdAxioms.lean`'s `eqA` — the same
`ConstantInfo` through the same store, hence the same handle. -/
def eqBasisCI : AM IConstantInfo := ConRon.Arena.eqA

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs —
`env.find? eqName = some eqA`, the "requires the pinned `Eq` basis" guard,
factored out because three call sites make it. -/
def eqBasisStored (fe : IFEnv) : AM Bool := do
  match fe.find? (← pin eqName) with
  | some ci => pure (ci == (← eqBasisCI))
  | none => pure false

end ConRon.Arena.IndBase
