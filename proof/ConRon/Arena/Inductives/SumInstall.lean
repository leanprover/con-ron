/-
# `ConRon.Arena.Inductives.SumInstall` — the direct install's stages
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/SumInstall.lean` whole, over handles: official's
telescope loop, the type former's stage, the per-field universe bound,
official's positivity walk as a normalisation, the constructors' stage and the
stored rules.

**The deviations of this module:**

* **The `…F` twins collapse into these** (task #97c's deviation 1), as in
  `StructInstall.lean`: `ConLeche/Kernel/Inductives/SumInstallF.lean`'s eight
  declarations are the same functions over an `FEnv`, and
  `checkStructFieldSortsIFA` is one of them over `Array`.  The names live on
  as `abbrev`s in `Arena/Inductives/SumInstallF.lean`.
* **`sumRules` takes `fe : IFEnv`, not `find?`**: con-leche abstracts the
  lookup so that the pure and the indexed tier share one body; the arena has
  one environment, and a `find?` passed as an argument is a closure
  (DESIGN §3.4).
* **`checkSumInd` takes `isRec : Bool`, not `capsOf : InductiveShape →
  IndCaps`.**  A function argument is a closure, and there is exactly ONE
  instantiation left in con-leche (`fun p₁ => nativeCapsAt p₁ isRec`; the sum
  route's `sumCaps` was deleted at its task #210 Part C).  So `nativeCapsAt`
  is twinned HERE, one module earlier than con-leche places it, and
  `checkSumInd` calls it — the same relocation task #97c made for
  `TypeChecker.lean`'s seven entries, and for the same reason: the arena's
  import order is fixed by what CALLS what, not by con-leche's file split.
* **`sumSplit`-shaped functions that touch no term stay pure**
  (`consSumCtors`, `InductiveShape.rulePrefix`, `InductiveShape.majorIdx`);
  see `Arena/Inductives/SumParts.lean`'s module note.
* **The fields' sorts are `List LIdx`** — `Arena/Inductives/StructParts.lean`'s
  note.
-/
import ConRon.Arena.Inductives.StructInstallF

namespace ConRon.Arena

open ConLeche
open ConRon.Arena.IndBase (unwrapOr checkConstantVal openPisAtFvars)

/-! ## The type former's stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:45-68 whnfTelescope
**Official's telescope loop** (`check_inductive_types`): peel `n` Π binders off
`e`, reducing the residual to weak head normal form before each binder and at
the end, where it must be a sort. -/
def whnfTelescope (mode : CheckMode) (fe : IFEnv) :
    Nat → Nat → EIdx → AM (List (EIdx × BinderMeta) × LIdx)
  | i, 0, e => do
    let e' ← whnf mode fe checkFuel i e
    match ← view e' with
    | .sort s => pure ([], s)
    | _ => fail (.invalid "direct sum: type former does not reduce to a sort \
        after its parameters and indices")
  | i, n + 1, e => do
    let e' ← whnf mode fe checkFuel i e
    match ← view e' with
    | .forallE dom body bm => do
      let fv ← internE (.fvar i dom)
      let b ← instantiate1Fast coreWalkFuel body fv 0
      let (bs, s) ← whnfTelescope mode fe (i + 1) n b
      pure ((dom, bm) :: bs, s)
    | _ => fail (.invalid "direct sum: type former does not reduce to a telescope \
        of its parameters and indices")

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:70-78 closeTelescope
Close a telescope opened at the free variables `i ..< i + bs.length` back into
a syntactic Π-telescope over `body`. -/
def closeTelescope : List (EIdx × BinderMeta) → Nat → EIdx → AM EIdx
  | [], _, body => pure body
  | (dom, bm) :: bs, i, body => do
    let inner ← closeTelescope bs (i + 1) body
    let closed ← abstract1Fast coreWalkFuel inner i 0
    internE (.forallE dom closed bm)

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:80-94 checkSumTele
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
The type former's TELESCOPE (task #195): the checked declared type when it is
already a syntactic telescope of `n` Π binders ending in a sort, else the
declared type's whnf'd telescope, closed and checked as the former's type in
its place. -/
def checkSumTele (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) (n : Nat)
    (cvTa₀ : IConstantVal) : AM (IConstantVal × LIdx) := do
  match ← stripPis n cvTa₀.type with
  | some (_, body) => do
    match ← view body with
    | .sort s => pure (cvTa₀, s)
    | _ => checkSumTeleSlow mode fe cv n cvTa₀
  | none => checkSumTeleSlow mode fe cv n cvTa₀
where
  /-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:91-94 checkSumTele
  The `_` arm of `checkSumTele`'s match, named because over handles the
  syntactic test is two `view`s and duplicating the arm would duplicate the
  whnf loop. -/
  checkSumTeleSlow (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) (n : Nat)
      (cvTa₀ : IConstantVal) : AM (IConstantVal × LIdx) := do
    let (bs, s) ← whnfTelescope mode fe 0 n cvTa₀.type
    let sortS ← internE (.sort s)
    let ty ← closeTelescope bs 0 sortS
    let cvTa ← checkConstantVal mode fe { cv with type := ty }
    pure (cvTa, s)

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:59-98 nativeCapsAt
The capabilities a block on the fixpoint route earns (task #210 Part A):
structure eta at a non-`Prop` structure-like block, unit-likeness at a
fieldless constructor, rule K at official's `is_K_target`, nothing at any
other block.  Twinned here rather than in `Arena/Inductives/NativeInstall.lean`
— see the module note. -/
def nativeCapsAt (p : InductiveShape) (isRec : Bool) : AM IIndCaps := do
  match p.ctors with
  | [c] => do
    let l ← readLevel p.resSort
    pure { eta := p.nIdx == 0 && !p.isProp && !isRec
           etaCtor := c.1.name
           etaParams := p.nP
           etaFields := c.2
           unitlike := p.nIdx == 0 && c.2 == 0
           unitParams := p.nP
           ruleK := c.2 == 0 && p.isProp
           sortZ := Level.zeronessOf l }
  | _ => pure {}

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:96-112 checkSumInd
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-43 checkSumIndF
Stage 1: the type former, stored with the block's capability record at its
telescope; returns the record completed with the result sort. -/
def checkSumInd (mode : CheckMode) (fe : IFEnv) (p : InductiveShape)
    (isRec : Bool) : AM (IFEnv × IConstantVal × InductiveShape) := do
  let cvTa₀ ← checkConstantVal mode fe p.cvT
  let (cvTa, s) ← checkSumTele mode fe p.cvT (p.nP + p.nIdx) cvTa₀
  let (_, tbody) ← unwrapOr (← stripPis (p.nP + p.nIdx) cvTa.type)
    (.internal "direct sum: type former telescope")
  let sortS ← internE (.sort s)
  unless tbody == sortS do
    fail (.internal "direct sum: type former result sort")
  let p' ← p.withSort s
  let caps ← nativeCapsAt p' isRec
  pure (fe.push (.indInfo cvTa caps), cvTa, p')

/-! ## The constructors' stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:114-139 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:45-61 checkStructFieldSortsIF
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:63-81 checkStructFieldSortsIFA
The fields' sorts over the opened constructor telescope, with the official
per-field universe bound unless the family is propositional.  Walks the fields
from the last to the first and returns the sorts in field order. -/
def checkStructFieldSortsI (mode : CheckMode) (fe : IFEnv) (isProp large : Bool)
    (s : LIdx) (nP : Nat) (fvs idxArgs : List EIdx) : Nat → AM (List LIdx)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← inferTypeCore mode fe checkFuel (nP + j) (← fvarTypeD fv)
    let u ← ensureSortCore mode fe checkFuel (nP + j) ty
    if !isProp then do
      let lu ← readLevel u
      let ls ← readLevel s
      unless ← liftFueled "level comparison" (Level.leq lu ls) do
        fail (.invalid "direct sum: field universe too large")
    else if large then do
      let z ← zeroLevel
      unless (← lvlEq? u z) == some true || idxArgs.contains fv do
        fail (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    let rest ← checkStructFieldSortsI mode fe isProp large s nP fvs idxArgs j
    pure (rest ++ [u])

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:141-175 normPosDom
**Official's positivity walk, as a normalisation** (task #210 Part D): the
field's domain is REPLACED by the form official classifies — whnf'd at its own
depth, and, while the block occurs, walked under its Π binders. -/
def normPosDom (mode : CheckMode) (fe : IFEnv) (T : NIdx) :
    Nat → Nat → EIdx → AM EIdx
  | _, 0, _ => fail (.notImplemented "direct sum: positivity walk fuel")
  | d, fuel + 1, e => do
    if !(← mentionsConst T e) then pure e else do
    let w ← whnf mode fe checkFuel d e
    if !(← mentionsConst T w) then pure w else
    match ← view w with
    | .forallE dom body bm => do
      if ← mentionsConst T dom then
        fail (.invalid "direct sum: non positive occurrence of the inductive type")
      else do
        let fv ← internE (.fvar d dom)
        let opened ← instantiate1Fast coreWalkFuel body fv 0
        let body' ← normPosDom mode fe T (d + 1) fuel opened
        let closed ← abstract1Fast coreWalkFuel body' d 0
        internE (.forallE dom closed bm)
    | _ => pure w

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:177-188 normFieldDoms
The constructor's field binders with their domains normalised, opened at the
free variables `i ..< i + n`; the residual returned scoped at those
variables. -/
def normFieldDoms (mode : CheckMode) (fe : IFEnv) (T : NIdx) :
    Nat → Nat → EIdx → AM (List (EIdx × BinderMeta) × EIdx)
  | _, 0, e => pure ([], e)
  | i, n + 1, h => do
    match ← view h with
    | .forallE dom body bm => do
      let dom' ← normPosDom mode fe T i 1024 dom
      let fv ← internE (.fvar i dom)
      let opened ← instantiate1Fast coreWalkFuel body fv 0
      let (bs, r) ← normFieldDoms mode fe T (i + 1) n opened
      pure ((dom', bm) :: bs, r)
    | _ => fail (.notImplemented "direct sum: constructor field telescope")

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:201 normCtorVal
`List.zipWith (fun x b => (x.fvarTypeD, b.2)) fvsP cbs`, as an explicit
recursion: the map's body reads the store, so con-leche's `zipWith` closure
becomes a helper (DESIGN §3.4). -/
def zipFvarDoms : List EIdx → List (EIdx × BinderMeta) →
    AM (List (EIdx × BinderMeta))
  | x :: xs, b :: bs => do
    let t ← fvarTypeD x
    pure ((t, b.2) :: (← zipFvarDoms xs bs))
  | _, _ => pure []

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:83-95 normCtorValF
The checked constructor with its field domains normalised, closed back into a
telescope and — when anything changed — checked as the constructor's type in
its place, from scratch. -/
def normCtorVal (mode : CheckMode) (fe : IFEnv) (T : NIdx) (nP nF : Nat)
    (cvC cvCa : IConstantVal) : AM IConstantVal := do
  let (cbs, _) ← unwrapOr (← stripPis nP cvCa.type)
    (.notImplemented "direct sum: constructor telescope")
  let (fvsP, crest) ← unwrapOr (← openPisAtFvars nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let pbs ← zipFvarDoms fvsP cbs
  let (fbs, resid) ← normFieldDoms mode fe T nP nF crest
  let ty' ← closeTelescope (pbs ++ fbs) 0 resid
  if ty' == cvCa.type then pure cvCa
  else checkConstantVal mode fe { cvC with type := ty' }

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:97-128 checkSumCtorF
Stage 2, one constructor's type: the ordinary constant check, the annotated
result shape, the parameter pins against the type former's opened telescope,
the pre-block resolution of the field domains, and the per-field universe
bound. -/
def checkSumCtor (mode : CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) :
    AM (IConstantVal × List LIdx) := do
  let cvCa₀ ← checkConstantVal mode fe cvC
  let cvCa ← normCtorVal mode fe T nP nF cvC cvCa₀
  let (_, cbody) ← unwrapOr (← stripPis (nP + nF) cvCa.type)
    (.notImplemented "direct sum: constructor telescope")
  -- official's `is_valid_ind_app` on the constructor's result: a REJECT, not a
  -- decline (task #220)
  unless ← structCtorResidOk T lps nP nF nIdx cbody do
    fail (.invalid "direct sum: invalid constructor return type")
  let cq ← unwrapOr (← openPisAtFvars nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (← openPisAtFvars nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkStructDomsAt mode fe 0 cq.1 (← tq.1.mapM fvarTypeD) nP
  let xq ← unwrapOr (← openPisAtFvars nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  -- the opened residual is the family at the opened parameter variables
  -- followed by the index expressions
  let us ← paramLevels lps
  let hd ← internE (.const T us)
  let xfn ← getAppFn coreWalkFuel xq.2
  let xargs ← getAppArgs coreWalkFuel xq.2
  unless xfn == hd && xargs.take nP == cq.1 && xargs.length == nP + nIdx do
    fail (.notImplemented "direct sum: opened constructor residual")
  unless ← xq.1.allM (fun x => do constsResolve fe₀ coreWalkFuel (← fvarTypeD x)) do
    fail (.notImplemented "direct sum: field domain after the block")
  -- the index expressions never mention the block
  unless ← (xargs.drop nP).allM (fun e => constsResolve fe₀ coreWalkFuel e) do
    fail (.invalid "direct sum: index expression mentions the block")
  let sorts ← checkStructFieldSortsI mode fe isProp large resSort nP xq.1
    (xargs.drop nP) nF
  pure (cvCa, sorts)

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:255-267 checkSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:130-140 checkSumCtorsF
Stage 2, all constructors' types, at the environment holding the type
former. -/
def checkSumCtors (mode : CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (cvTa : IConstantVal) :
    List (IConstantVal × Nat) → AM (List (IConstantVal × Nat) × List (List LIdx))
  | [] => pure ([], [])
  | c :: cs => do
    let (cvCa, sorts) ← checkSumCtor mode fe₀ fe T lps nP nIdx resSort isProp large
      c.1 c.2 cvTa
    let (rest, srest) ← checkSumCtors mode fe₀ fe T lps nP nIdx resSort isProp large
      cvTa cs
    pure ((cvCa, c.2) :: rest, sorts :: srest)

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:269-272 consSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:142-145 consSumCtorsF
The constructors' conses, in order (the first constructor deepest).  Pure: the
index push touches no term. -/
def consSumCtors (nP : Nat) : List (IConstantVal × Nat) → IFEnv → IFEnv
  | [], fe => fe
  | c :: cs, fe => consSumCtors nP cs (fe.push (.ctorInfo c.1 nP c.2))

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:274-290 sumRules
The stored rules: constructor `j`'s with the generated right-hand side `j`,
plain when the generated type's major is the family at the parameters, with
the two rescue bits `recRuleBits` reads off the block's own store and
`paramsBlind`, because the route's rule law holds at any pair of fitting
parameter spines. -/
def sumRules (fe : IFEnv) (recName : NIdx) (nP mI rP : Nat) (recTy : EIdx) :
    List (IConstantVal × Nat) → List EIdx → AM (List IRecRule)
  | c :: cs, rhs :: rhss => do
    let plain ← recRulePlain coreWalkFuel recTy mI rP nP
    let r ← recRuleBits fe recName
      { ctor := c.1.name, nfields := c.2, ctorParams := nP,
        fire := if plain then .plain else .inert,
        rhs := rhs, paramsBlind := true }
    pure (r :: (← sumRules fe recName nP mI rP recTy cs rhss))
  | _, _ => pure []

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:292-294 InductiveShape.rulePrefix
The recursor's rule prefix (parameters, motive, minors). -/
def InductiveShape.rulePrefix (p : InductiveShape) : Nat := p.nP + 1 + p.ctors.length

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:295 InductiveShape.majorIdx
The recursor's major index (the rule prefix, then the indices). -/
def InductiveShape.majorIdx (p : InductiveShape) : Nat := p.rulePrefix + p.nIdx

end ConRon.Arena
