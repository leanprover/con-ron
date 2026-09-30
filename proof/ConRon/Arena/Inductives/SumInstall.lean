/-
# `ConRon.Arena.Inductives.SumInstall` — the block install's shared stages
(DESIGN.md §8, task #97d-2; task #105)

`ConLeche/Kernel/Inductives/SumInstall.lean` whole, over handles: official's
telescope loop, the type former's telescope, the per-field universe bound,
the constructors' stage (every constructor stored AS DECLARED) and the stored
rules.  The Rust twin is `arena::inductives::sum_install`.

**The deviations of this module:**

* **The `…F` twins collapse into these** (task #97c's deviation 1), as in
  `StructInstall.lean`: `ConLeche/Kernel/Inductives/SumInstallF.lean`'s
  declarations are the same functions over an `FEnv`, and
  `checkStructFieldSortsIFA` is one of them over `Array`.
* **`sumRules` takes `fe : IFEnv`, not `find?`**: con-leche abstracts the
  lookup so that the pure and the indexed tier share one body; the arena has
  one environment, and a `find?` passed as an argument is a closure
  (DESIGN §3.4).
* **`consSumCtors` stays pure** — the index push touches no term.
* **`closeTelescope` is `Arena/Inductives/Positivity.lean`'s**, con-leche's
  own home for it, which this module imports as con-leche's does; the Rust
  carries two identical copies (`sum_install::close_telescope`,
  `positivity::close_telescope`) and both are that one twin.
* **The fields' sorts are `List LIdx`** — `Arena/Inductives/StructParts.lean`'s
  note.
-/
import ConRon.Arena.Inductives.StructInstall
import ConRon.Arena.Inductives.Positivity

namespace ConRon.Arena

open ConLeche

/-! ## The type former's stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:34-57 whnfTelescope
**Official's telescope loop** (`check_inductive_types`): peel `n` Π binders off
`e`, reducing the residual to weak head normal form before each binder and at
the end, where it must be a sort. -/
def whnfTelescope (mode : CheckMode) (fe : IFEnv) :
    Nat → Nat → EIdx → AM (List (EIdx × BinderMeta) × LIdx)
  | i, n, e => do
    let e' ← whnf mode fe checkFuel i e
    match ← view e', n with
    | .sort s, 0 => pure ([], s)
    | .sort _, _ + 1 => fail (.invalid "direct sum: type former does not reduce to a telescope")
    | .forallE _ _ _, 0 => fail (.invalid "direct sum: type former does not reduce to a sort")
    | .forallE dom body bm, n + 1 => do
      let fv ← internE (.fvar i dom)
      let b ← instantiate1Fast coreWalkFuel body fv 0
      let (bs, s) ← whnfTelescope mode fe (i + 1) n b
      pure ((dom, bm) :: bs, s)
    | _, 0 => fail (.invalid "direct sum: type former does not reduce to a sort")
    | _, _ + 1 => fail (.invalid "direct sum: type former does not reduce to a telescope")

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:59-73 checkSumTele
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
The type former's TELESCOPE (task #195): the checked declared type when it is
already a syntactic telescope of `n` Π binders ending in a sort, else the
declared type's whnf'd telescope, closed and checked as the former's type in
its place. -/
def checkSumTele (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) (n : Nat)
    (cvTa₀ : IConstantVal) : AM (IConstantVal × LIdx) := do
  match ← stripPis n cvTa₀.type with
  | some (_, body) => do
    if body.tag == ETag.sort then
      match ← viewSort body with
      | none => failDanglingE
      | some s => pure (cvTa₀, s)
    else checkSumTeleSlow mode fe cv n cvTa₀
  | none => checkSumTeleSlow mode fe cv n cvTa₀
where
  /-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:59-73 checkSumTele
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

/-! ## The constructors' stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:75-100 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-48 checkStructFieldSortsIF
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:50-68 checkStructFieldSortsIFA
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
      let lu ← readLevelM u
      let ls ← readLevelM s
      unless ← liftFueled "level comparison" (Level.leq lu ls) do
        fail (.invalid "direct sum: field universe too large")
    else if large then do
      let z ← zeroLevel
      unless (← lvlEq? u z) == some true || idxArgs.contains fv do
        fail (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    let rest ← checkStructFieldSortsI mode fe isProp large s nP fvs idxArgs j
    pure (rest ++ [u])

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
Every field domain resolves at the PRE-BLOCK environment. -/
def fieldDomsResolve (fe₀ : IFEnv) : List EIdx → AM Bool
  | [] => pure true
  | x :: xs => do
    let t ← fvarTypeD x
    if ← constsResolveFFast fe₀ t then fieldDomsResolve fe₀ xs else pure false

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
The index expressions never mention the block. -/
def idxArgsResolve (fe₀ : IFEnv) : List EIdx → AM Bool
  | [] => pure true
  | e :: es => do
    if ← constsResolveFFast fe₀ e then idxArgsResolve fe₀ es else pure false

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:70-100 checkSumCtorF
Stage 2, one constructor's type: the ordinary constant check, the annotated
result shape, the parameter pins against the type former's opened telescope,
the pre-block resolution of the field domains, and the per-field universe
bound. -/
def checkSumCtor (mode : CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) :
    AM (IConstantVal × List LIdx) := do
  let cvCa ← checkConstantVal mode fe cvC
  let (_, cbody) ← unwrapOr (← stripPis (nP + nF) cvCa.type)
    (.notImplemented "direct sum: constructor telescope")
  -- official's `is_valid_ind_app` on the constructor's result: a REJECT, not a
  -- decline (task #220)
  unless ← structCtorResidOk T lps nP nF nIdx cbody do
    fail (.invalid "direct sum: invalid constructor return type")
  -- the opened frames (the Rust's `check_sum_ctor_frames`)
  let cq ← unwrapOr (← openPisAtFvarsF nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  let tdoms ← fvarTypeDs tq.1
  checkStructDomsAt mode fe 0 cq.1 tdoms nP
  let xq ← unwrapOr (← openPisAtFvarsF nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  -- the opened residual is the family at the opened parameter variables
  -- followed by the index expressions (the Rust's `check_sum_ctor_resid`)
  let us ← paramLevels lps
  let hd ← internE (.const T us)
  let xfn ← getAppFn coreWalkFuel xq.2
  let xargs ← getAppArgs coreWalkFuel xq.2
  unless xfn == hd && xargs.take nP == cq.1 && xargs.length == nP + nIdx do
    fail (.notImplemented "direct sum: opened constructor residual")
  let idxArgs := xargs.drop nP
  -- the field domains and the index expressions resolve BEFORE the block
  -- (the Rust's `check_sum_ctor_sorts`)
  unless ← fieldDomsResolve fe₀ xq.1 do
    fail (.notImplemented "direct sum: field domain after the block")
  unless ← idxArgsResolve fe₀ idxArgs do
    fail (.invalid "direct sum: index expression mentions the block")
  let sorts ← checkStructFieldSortsI mode fe isProp large resSort nP xq.1
    idxArgs nF
  pure (cvCa, sorts)

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:149-161 checkSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:102-112 checkSumCtorsF
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

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:163-166 consSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:114-117 consSumCtorsF
The constructors' conses, in order (the first constructor deepest).  Pure: the
index push touches no term. -/
def consSumCtors (nP : Nat) : List (IConstantVal × Nat) → IFEnv → IFEnv
  | [], fe => fe
  | c :: cs, fe => consSumCtors nP cs (fe.push (.ctorInfo c.1 nP c.2))

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:168-184 sumRules
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

end ConRon.Arena
