/-
# `ConRon.Arena.Inductives.RecCheck` — the recursor stage's class kit
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/RecCheck.lean` over handles: the member
abstraction (`targetAbs`), the per-component class match (`targetClassMatch`)
and the table entries it selects (`targetMajorNfs`), a class resolved from a
major (`targetMajorOf`) and typed (`targetMajorPins`), the recursor records'
pins (`targetRecPins`), node agreement (`targetK53`), and the stored family's
rules (`tgtStoredRules`, `consBlockRecsTF`) with the container bit
(`blockNestedBit`).  The Rust twin is `arena::inductives::rec_check`.

**The deviations** (the Rust's, item for item):

* **`ShadowOps` is not a record**: con-leche writes the stage against a record
  of operations per index so that the pure install and the cached fold run the
  same code; the arena has one core and one environment representation, so the
  operations are `Arena/Core.lean`'s entry points at the `IFEnv` they are
  handed (its visibility bound included), and the cached driver's flushes are
  where `shadowOpsC` puts them (`Arena/Inductives/GenRec.lean`).  `ShadowOps`,
  `ShadowOps.ofOps` and `ShadowOps.fueled` are on the skip list, and so are
  `TargetAbsMemoInv` and its lemmas (`Prop`-only apparatus).
* **`targetAbs` is ONE memoised walk** (`targetAbs`, `targetAbsGo` and
  `targetAbsFast` collapse), as `Arena/Inductives/Positivity.lean`'s walks:
  `targetAbsGo` carries the memo and a fuel, `targetAbs` is the fresh-memo
  entry.
* **A function argument is specialised**: `targetParamsDefEq`'s `absM` is
  always `targetAbs names lvls holes` (its one caller), so it takes `names`,
  `lvls` and `holes`; `tgtStoredRules`' `find?`/`resolves` are the
  constructors' environment `fe`; `eraseFVarTys`/`targetCanonParams` are
  `FvMap` variants of `replaceFVars`.
* **`Ms.getD c default` is `targetMajorAt`**: the default record interns the
  anonymous name and reads the pinned empty level list (`targetMajorDefault`),
  as the Rust builds it, so the lookup is an `AM` function.
* **`tgtRs` is not ported**: nothing the executed checker runs reads the
  install's old recursor-list format.
* **`tgtStoredRules`' fire is computed once per recursor**: con-leche's
  `rules.map fun rl => { rl with fire := auxRuleFireR … }` recomputes the same
  pure reading per rule.
* **`consBlockRecsTF` takes the constructors' visibility bound `vis₂`**, not
  `find?`/`resolves`: the rules are read at `fe.restrictTo vis₂` while the
  recursors are pushed above it, as the Rust passes `vis2` beside the growing
  index.
* **Terms read from the store take the state**: `targetHoles`,
  `targetCtorAt`, `targetPiDomsWith`, `eraseFVarTys`, `targetCanonParams`,
  `auxRuleFireR` and `tgtStoredRules` are `AM` functions.
-/
import ConRon.Arena.Inductives.BlockInstall

namespace ConRon.Arena

open ConLeche

/-! ## The holes: the block's members abstracted to free variables -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:89-109 targetAbs
con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:130-170 targetAbsGo
**The member abstraction of one term**: every member at the block's levels
`lvls` becomes its hole; `fvar` annotations are not entered.  Memoised on the
node. -/
def targetAbsGo (names : List NIdx) (lvls : LsIdx) (holes : List EIdx)
    (memo : Std.HashMap EIdx EIdx) : Nat → EIdx → AM (EIdx × Std.HashMap EIdx EIdx)
  | 0, _ => fail (.internal "fuel exhausted: targetAbs")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure (h, memo)
    | .sort _ => pure (h, memo)
    | .lit _ => pure (h, memo)
    | .fvar _ _ => pure (h, memo)
    | .const n us =>
      if us == lvls then
        match names.findIdx? (· == n) with
        | some t =>
          match holes[t]? with
          | some x => pure (x, memo)
          | none => pure (h, memo)
        | none => pure (h, memo)
      else pure (h, memo)
    | v =>
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let (r, memo) ← match v with
          | .app a b => do
            let (a', memo) ← targetAbsGo names lvls holes memo fuel a
            let (b', memo) ← targetAbsGo names lvls holes memo fuel b
            let r ← internAppE a' b'
            pure (r, memo)
          | .lam ty body bm => do
            let (t', memo) ← targetAbsGo names lvls holes memo fuel ty
            let (b', memo) ← targetAbsGo names lvls holes memo fuel body
            let r ← internLamE t' b' bm
            pure (r, memo)
          | .forallE ty body bm => do
            let (t', memo) ← targetAbsGo names lvls holes memo fuel ty
            let (b', memo) ← targetAbsGo names lvls holes memo fuel body
            let r ← internForallEE t' b' bm
            pure (r, memo)
          | .letE ty val body => do
            let (t', memo) ← targetAbsGo names lvls holes memo fuel ty
            let (v', memo) ← targetAbsGo names lvls holes memo fuel val
            let (b', memo) ← targetAbsGo names lvls holes memo fuel body
            let r ← internLetEE t' v' b'
            pure (r, memo)
          | .proj s i sub => do
            let (u, memo) ← targetAbsGo names lvls holes memo fuel sub
            let r ← internProjE s i u
            pure (r, memo)
          | _ => pure (h, memo)
        pure (r, memo.insert h r)

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:240-242 targetAbsFast
The executed member abstraction (one memoised DAG walk, a fresh memo). -/
def targetAbs (names : List NIdx) (lvls : LsIdx) (holes : List EIdx) (e : EIdx) :
    AM EIdx := do
  let (r, _) ← targetAbsGo names lvls holes {} coreWalkFuel e
  pure r

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:248-251 targetHoles
The holes of a rule frame of width `base`: member `t` is `.fvar (base + t)` at
its former's type, interned in member order. -/
def targetHoles : List EIdx → Nat → AM (List EIdx)
  | [], _ => pure []
  | ty :: tys, base => do
    let v ← internFVarE base ty
    let vs ← targetHoles tys (base + 1)
    pure (v :: vs)

/-! ## The major -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor
**A recursor's major, resolved**: `ind.{lvls} ds ı⃗`, its parameter and index
counts at the instantiation, its constructors, the member it is (`none`: an
outside inductive), the table's entries for its constructors and the recursor
prefix's openers it is compared in. -/
structure TargetMajor where
  ind : NIdx
  lvls : LsIdx
  ds : List EIdx
  nPc : Nat
  nIdx : Nat
  ctors : List (IConstantVal × Nat)
  member : Option Nat
  /-- the positivity walk's recorded normal forms of this class's constructors
  (`targetMajorNfs`, K.53′) -/
  nfs : List NestCtorNf := []
  /-- the recursor's prefix openers, the context the class is compared in -/
  pfvs : List EIdx := []
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor
The cited `deriving Inhabited` default, `Ms.getD c default`'s fallback: the
anonymous inductive at no level and no parameter, its name interned and its
level list the pinned empty one (as the Rust builds it).  Only an out-of-range
class index reads it, which the stage never forms. -/
def targetMajorDefault : AM TargetMajor := do
  let anon ← internNNode .anonymous
  let ls ← pinEmptyLevels
  pure { ind := anon, lvls := ls, ds := [], nPc := 0, nIdx := 0, ctors := [],
         member := none, nfs := [], pfvs := [] }

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor
`Ms.getD c default`: the class at `c`, else `targetMajorDefault`. -/
def targetMajorAt (ms : List TargetMajor) (c : Nat) : AM TargetMajor :=
  match ms[c]? with
  | some m => pure m
  | none => targetMajorDefault

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:277-281 Expr.eraseFVarTys
A term with every free variable's ANNOTATION erased (the variable kept at
`Sort 0`). -/
def eraseFVarTys (e : EIdx) : AM EIdx :=
  replaceFVars .erase e

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:305-308 targetCanonParams
A term over the walk's canonical parameter variables, moved to the class's
openers `pfvs` (variables `0 … |pfvs|-1`, the rest kept). -/
def targetCanonParams (pfvs : List EIdx) (e : EIdx) : AM EIdx :=
  replaceFVars (.canon pfvs) e

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:310-329 targetParamsDefEq
**Per-component parameter defeq** at depth `d`, each side moved to the openers
and member-abstracted (`absM` is `targetAbs names lvls holes`, its one
instantiation): both sides closed over the openers (the four reads in order,
short-circuiting), then syntactically equal, or inferred and defeq. -/
def targetParamsDefEq (mode : CheckMode) (fe : IFEnv) (d : Nat) (names : List NIdx)
    (lvls : LsIdx) (holes pfvs : List EIdx) : List EIdx → List EIdx → AM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    let closed ← do
      if (← bvarB coreWalkFuel a) != 0 then pure false
      else if (← bvarB coreWalkFuel b) != 0 then pure false
      else if (← fvarB coreWalkFuel a) > pfvs.length then pure false
      else pure ((← fvarB coreWalkFuel b) ≤ pfvs.length)
    if !closed then pure false
    else
      let ac ← targetCanonParams pfvs a
      let a' ← targetAbs names lvls holes ac
      let bc ← targetCanonParams pfvs b
      let b' ← targetAbs names lvls holes bc
      if a' == b' then targetParamsDefEq mode fe d names lvls holes pfvs as bs
      else
        let _ ← inferTypeCore mode fe checkFuel d a'
        let _ ← inferTypeCore mode fe checkFuel d b'
        if ← isDefEqCore mode fe checkFuel d a' b' then
          targetParamsDefEq mode fe d names lvls holes pfvs as bs
        else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:331-340 targetClassMatch
**A class matches a recorded instantiation `(lvls, eds)`**: levels up to
`Level.isEquivList` (an exhausted comparison is no match), parameters pairwise
defeq with the members abstracted, over the class's recursor prefix `pfvs`
with the holes on top. -/
def targetClassMatch (mode : CheckMode) (fe : IFEnv) (p : BlockShape)
    (formerTys pfvs : List EIdx) (us : LsIdx) (ds : List EIdx) (lvls : LsIdx)
    (eds : List EIdx) : AM Bool := do
  match ← lvlsEq? us lvls with
  | some true => do
    let names := p.memberNames
    let blvls ← paramLevels p.lps
    let holes ← targetHoles formerTys pfvs.length
    targetParamsDefEq mode fe (pfvs.length + formerTys.length) names blvls holes pfvs ds eds
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:342-354 targetMajorNfs
**The walk's recorded constructor normal forms of a class**: the entries of
the class's constructors whose instantiation the class matches.  The tail
first, so the entries are examined from the last to the first (the Rust counts
down over the table and reverses its collection back). -/
def targetMajorNfs (mode : CheckMode) (fe : IFEnv) (p : BlockShape)
    (formerTys pfvs : List EIdx) (us : LsIdx) (ds : List EIdx)
    (ctors : List (IConstantVal × Nat)) : List NestCtorNf → AM (List NestCtorNf)
  | [] => pure []
  | e :: es => do
    let rest ← targetMajorNfs mode fe p formerTys pfvs us ds ctors es
    if ctors.any (·.1.name == e.ctor) then
      if ← targetClassMatch mode fe p formerTys pfvs us ds e.lvls e.ds then
        pure (e :: rest)
      else pure rest
    else pure rest

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:356-360 targetCtorsOf
The constructors of a stored inductive `I` and its parameter count
(`nestContainer`'s reading, which reads nothing of its context but the
lookup). -/
def targetCtorsOf (fe : IFEnv) (I : NIdx) : AM (Option (Nat × List (IConstantVal × Nat))) :=
  nestContainer fe I

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:362-376 targetOutsideInst
The instantiated type former of an OUTSIDE major `I.{us} ds`: its index count
and its result sort. -/
def targetOutsideInst (fe : IFEnv) (I : NIdx) (us : LsIdx) (ds : List EIdx) :
    AM (Nat × LIdx) := do
  match fe.find? I with
  | some (.indInfo cvI _) => do
    let tl ← instLPFast coreWalkFuel cvI.levelParams us cvI.type
    match ← instPisWith ds tl with
    | none => fail (.invalid "target rec: the major's type former does not bind its \
        parameters (official: ill-formed inductive type)")
    | some ty => do
      let (ibs, s) ← piBinders coreWalkFuel ty
      match ← view s with
      | .sort l => pure (ibs.length, l)
      | _ => fail (.invalid "target rec: the major's type former is not a telescope ending \
          in a sort (official: type expected)")
  | _ => fail (.invalid "target rec: the recursor's major is not a stored inductive")

/-! ## A recursor's class, resolved -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:380-439 targetMajorOf
**A recursor's major, resolved** from its opened type `mty`: a MEMBER of the
block at the block's levels and parameters, or — a nested block's container —
any other stored inductive at one of the block's auxiliary types: not `Quot`,
stored, its parameters closed over the recursor's, some parameter naming a
member (`nestOcc` at an empty hole range), in the block's universe (Q1). -/
def targetMajorOf (fe : IFEnv) (p : BlockShape)
    (ctorsAs : List (List (IConstantVal × Nat))) (pfvs fvs : List EIdx) (mty : EIdx) :
    AM TargetMajor := do
  let args ← getAppArgs coreWalkFuel mty
  let hd ← getAppFn coreWalkFuel mty
  if hd.tag == ETag.const then
    match ← viewConst hd with
    | none => failDanglingE
    | some (I, us) =>
      match p.memberNames.findIdx? (· == I) with
      | some t => do
        -- a MEMBER: at the block's levels and parameters
        let ms ← unwrapOr p.members[t]? (.internal "target rec: member")
        let ctorsA ← unwrapOr ctorsAs[t]? (.internal "target rec: member constructors")
        let blvls ← paramLevels p.lps
        let pf := fvs.take p.nP
        if us == blvls && args.take p.nP == pf then
          pure { ind := I, lvls := us, ds := pf, nPc := p.nP, nIdx := ms.nIdx,
                 ctors := ctorsA, member := some t, nfs := [], pfvs := pfvs }
        else
          fail (.invalid "target rec: the recursor's major premise is not the member at its \
            parameters and its index binders")
      | none => do
        -- an OUTSIDE inductive (a nested block's container)
        let q ← pinQuot
        if I == q then
          fail (.invalid "target rec: the recursor's major is Quot, which is no inductive")
        else
          match ← targetCtorsOf fe I with
          | none => fail (.invalid "target rec: the recursor's major is not a stored inductive")
          | some (nPc, ctors) => do
            let ds := args.take nPc
            if ds.length != nPc then
              fail (.invalid "target rec: the major's parameters mention more than the \
                recursor's parameters")
            else
              let closed ← ds.allM fun x => do
                if (← bvarB coreWalkFuel x) != 0 then pure false
                else pure ((← fvarB coreWalkFuel x) ≤ p.nP)
              if !closed then
                fail (.invalid "target rec: the major's parameters mention more than the \
                  recursor's parameters")
              else
                let names := p.memberNames
                unless ← ds.anyM (fun x => nestOcc names 0 0 x) do
                  fail (.invalid "target rec: the recursor's major is an outside inductive \
                    at an instantiation that is no auxiliary type of the block (official \
                    generates no such auxiliary recursor: `elim_nested_inductive`, \
                    `is_nested`)")
                let (nIdx, sI) ← targetOutsideInst fe I us ds
                unless ← liftFueled "level comparison" (← lvlEq? sI p.resSort) do
                  fail (.invalid "target rec: the recursor's major lives in another \
                    universe than the block (Q1)")
                pure { ind := I, lvls := us, ds := ds, nPc := nPc, nIdx := nIdx,
                       ctors := ctors, member := none, nfs := [], pfvs := pfvs }
  else
    fail (.invalid "target rec: the recursor's major premise is not an inductive's \
      application")

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:441-458 targetPinTys
**An outside major's parameters, typed at the rule prefix** (depth `d`), in
order. -/
def targetPinTys (mode : CheckMode) (fe : IFEnv) (d : Nat) : List EIdx → AM Unit
  | [] => pure ()
  | x :: xs => do
    let _ ← inferTypeCore mode fe checkFuel d x
    targetPinTys mode fe d xs

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:460-476 targetMajorPins
The check at a resolved major: an outside major's parameters typed at the rule
prefix, and the instantiation `I.{us} D⃗` itself typed there.  Nothing at a
member. -/
def targetMajorPins (mode : CheckMode) (fe : IFEnv) (rP : Nat) (M : TargetMajor) :
    AM Unit := do
  match M.member with
  | some _ => pure ()
  | none => do
    targetPinTys mode fe rP M.ds
    let hd ← internConstE M.ind M.lvls
    let app ← mkAppN hd M.ds
    let _ ← inferTypeCore mode fe checkFuel rP app
    pure ()

/-! ## The recursor records' pins -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:480-518 targetRecPins
**The recursor records' pins**: the level parameters, the reserved names, the
member recursors' names as the set `{T_m.rec}`, the auxiliary ones as
`T_0.rec_1 … T_0.rec_n` (member 0's name, `.anonymous` at no member,
interned only then), all names distinct, and the constructor grouping against
the stream's own order. -/
def targetRecPins (p : BlockShape) (block : List IConstantInfo) : AM Unit := do
  unless blockRecLpsOk p do
    fail (.invalid "target rec: the recursor's level parameters are not the generated ones")
  unless ← blockRecNamesUnreserved p.recs do
    fail (.invalid "target rec: a recursor is named for a pinned basis constant, a literal \
      guard's slot or a certified Nat operation")
  let own := p.recs.filter fun rc => rc.tgt < p.k
  unless ← blockRecNameSetOk p.members own do
    fail (.invalid "target rec: the block's recursor names are not the generated ones \
      (one T.rec per member)")
  let n₀ ← match p.members with
    | [] => internNNode .anonymous
    | ms :: _ => pure ms.cvT.name
  let aux := p.recs.filter fun rc => !(rc.tgt < p.k)
  let wantAux ← (List.range aux.length).mapM fun i =>
    internNNode (.str n₀ s!"rec_{i + 1}")
  let gotAux := aux.map (·.cvR.name)
  unless gotAux.length == wantAux.length && wantAux.all (gotAux.contains ·) &&
      gotAux.all (wantAux.contains ·) do
    fail (.invalid "target rec: the block's auxiliary recursor names are not the generated \
      ones (T.rec_1 … T.rec_n)")
  unless nameNodup (p.recs.map (·.cvR.name)) do
    fail (.invalid "target rec: two recursors of the block share a name")
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    unless cvTs.length == p.k && rs.length == p.recs.length &&
        p.allCtors.map (·.1.name) == cs.map (·.1.name) do
      fail (.invalid "target rec: the recursor record is not the generated recursor \
        (constructor grouping)")
  | none => fail (.invalid "target rec: the block does not split")

/-! ## A class's constructors, and node agreement (K.53′) -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:522-528 targetCtorAt
A constructor's type at the major's LEVELS: a member's as stored, an outside
inductive's instantiated at the major's. -/
def targetCtorAt (M : TargetMajor) (c : IConstantVal) : AM EIdx :=
  match M.member with
  | some _ => pure c.type
  | none => instLPFast coreWalkFuel c.levelParams M.lvls c.type

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:530-556 targetK53
**K.53′ at one recorded field** `f`: its telescope is the call's `tele` and its
leaf the callee's major `majDom`, up to the free variables' annotations, the
leaf's head and arity the major's, its indices up to annotations, its class
naming a member (official's `is_nested`), and that class matching the callee's
class `Mc` per component.  The cited `&&` chain, left to right; both sides of
each erased comparison are computed before it is read. -/
def targetK53 (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx)
    (Mc : TargetMajor) (tele : List (EIdx × BinderMeta)) (majDom f : EIdx) : AM Bool := do
  match ← stripPis tele.length f with
  | none => pure false
  | some (teleW, leafW) => do
    let ew ← teleW.mapM fun b => do pure ((← eraseFVarTys b.1), b.2)
    let et ← tele.mapM fun b => do pure ((← eraseFVarTys b.1), b.2)
    if ew != et then pure false
    else
      let lh ← getAppFn coreWalkFuel leafW
      let mh ← getAppFn coreWalkFuel majDom
      if lh.tag == ETag.const && mh.tag == ETag.const then
        match ← viewConst lh with
        | none => failDanglingE
        | some (I', us') =>
          match ← viewConst mh with
          | none => failDanglingE
          | some (I, _) => do
            let la ← getAppArgs coreWalkFuel leafW
            let ma ← getAppArgs coreWalkFuel majDom
            if !(I' == I && la.length == ma.length) then pure false
            else
              let le ← (la.drop Mc.nPc).mapM eraseFVarTys
              let me ← (ma.drop Mc.nPc).mapM eraseFVarTys
              if le != me then pure false
              else
                let lp := la.take Mc.nPc
                let hd ← internConstE I' us'
                let app ← mkAppN hd lp
                if ← nestOcc p.memberNames 0 0 app then
                  targetClassMatch mode fe p formerTys Mc.pfvs Mc.lvls Mc.ds us' lp
                else pure false
      else pure false

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:558-563 targetPiDomsWith
The domains of the first `|xs|` `∀` binders, each instantiated at the earlier
`xs`. -/
def targetPiDomsWith : List EIdx → EIdx → AM (Option (List EIdx))
  | [], _ => pure (some [])
  | x :: xs, e => do
    if e.tag == ETag.forallE then
      match ← viewBind e with
      | none => failDanglingE
      | some (d, b, _) => do
        let b' ← instantiate1Fast coreWalkFuel b x 0
        match ← targetPiDomsWith xs b' with
        | some ds => pure (some (d :: ds))
        | none => pure none
    else pure none

/-! ## The stored family -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:574-585 auxRuleFireR
**The firing mode of a rule at an OUTSIDE major**: `.nested` at the syntactic
reading of the recursor type's major domain, `.inert` when it fails.
`resolves` is the constructors' environment `fe`. -/
def auxRuleFireR (fe : IFEnv) (cv : IConstantVal) (mI rP nPc : Nat) : AM IRecRuleFire := do
  match ← nestedRuleSyn fe cv.levelParams cv.type mI rP nPc with
  | some (lvls, pins) => pure (.nested lvls pins)
  | none => pure .inert

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:587-597 tgtStoredRules
**One checked recursor's stored rules, at its major**: `sumRules` at the
major's parameter count and constructors, every rule firing as `auxRuleFireR`
reads it at an OUTSIDE major (the reading computed once, the module note). -/
def tgtStoredRules (fe : IFEnv) (cv : IConstantVal) (mI rP : Nat) (M : TargetMajor)
    (rhss : List EIdx) : AM (List IRecRule) := do
  let rules ← sumRules fe cv.name M.nPc mI rP cv.type M.ctors rhss
  match M.member with
  | some _ => pure rules
  | none => do
    let f ← auxRuleFireR fe cv mI rP M.nPc
    pure (rules.map fun rl => { rl with fire := f })

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:599-605 blockNestedBit
**The block's container bit**: some field kind is not flat or some recursor's
major is not a member. -/
def blockNestedBit (p : BlockShape) (kinds : List (List (List NestFieldKind))) : Bool :=
  if nestKindsFlat kinds then p.recs.any (fun rc => !(rc.tgt < p.k)) else true

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:607-617 consBlockRecsTF
con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:93-106 consBlockRecsT
**The checked family consed through the index, at its majors**: each recursor
with its rules at ITS major, the rules' lookups at the constructors'
environment, i.e. at its visibility bound `vis₂` while the recursors are pushed
above it. -/
def consBlockRecsTF (vis₂ : Nat) (p : BlockShape) :
    Nat → List (IConstantVal × TargetMajor × List EIdx) → IFEnv → AM IFEnv
  | _, [], fe => pure fe
  | m, (cv, M, rhss) :: rest, fe => do
    let mI := p.majorIdxAt m
    let rP := p.rulePrefixAt m
    let rules ← tgtStoredRules (fe.restrictTo vis₂) cv mI rP M rhss
    consBlockRecsTF vis₂ p (m + 1) rest (fe.push (.recInfo cv mI rP rules))

end ConRon.Arena
