/-
# `ConRon.Arena.Inductives.SumInstall` — the block install's shared stages
(DESIGN.md §8, task #97d-2; task #105)

`ConLeche/Kernel/Inductives/SumInstall.lean` whole, over handles: the type
former's telescope, the per-field universe bound, the constructors' stage
(every constructor stored AS DECLARED, every stage a check returning nothing)
and the stored rules.  The Rust twin is `arena::inductives::sum_install`.

**The deviations of this module:**

* **The `…F` twins collapse into these** (task #97c's deviation 1), as in
  `StructInstall.lean`: `ConLeche/Kernel/Inductives/SumInstallF.lean`'s
  declarations are the same functions over an `FEnv`, and
  `checkStructFieldSortsIFA` is one of them over `Array`.
* **`consSumCtors` stays pure** — the index push touches no term.
-/
module

public import ConRon.Arena.Inductives.StructInstall

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## The type former's stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:33-38 checkSumTele
The type former's TELESCOPE: `n` Π binders ending in a sort (the block's check
puts a former at its telescope, `reduceMember`).  Returns the former and its
sort. -/
def checkSumTele (n : Nat) (cvTa₀ : IConstantVal) : AM (IConstantVal × LIdx) := do
  match ← stripPis n cvTa₀.type with
  | some (_, body) =>
    if body.tag == ETag.sort then
      match ← viewSort body with
      | none => failDanglingE
      | some s => pure (cvTa₀, s)
    else fail (.invalid "direct sum: type former does not reduce to a sort")
  | none => fail (.invalid "direct sum: type former does not reduce to a sort")

/-! ## The constructors' stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:40-64 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-35 checkStructFieldSortsIF
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove SumInstall.checkStructFieldSortsI_bridge, then delete this line
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:37-54 checkStructFieldSortsIFA
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove SumInstall.checkStructFieldSortsI_bridge, then delete this line
Every field's domain has a sort over the opened constructor telescope, under
the official per-field universe bound unless the family is propositional.
Walks the fields from the last to the first. -/
def checkStructFieldSortsI (mode : CheckMode) (fe : IFEnv) (isProp large : Bool)
    (s : LIdx) (nP : Nat) (fvs idxArgs : List EIdx) : Nat → AM Unit
  | 0 => pure ()
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
    checkStructFieldSortsI mode fe isProp large s nP fvs idxArgs j

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:66-107 checkSumCtor
Every field domain resolves at the PRE-BLOCK environment. -/
def fieldDomsResolve (fe₀ : IFEnv) : List EIdx → AM Bool
  | [] => pure true
  | x :: xs => do
    let t ← fvarTypeD x
    if ← constsResolveFFast fe₀ t then fieldDomsResolve fe₀ xs else pure false

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:66-107 checkSumCtor
The index expressions never mention the block. -/
def idxArgsResolve (fe₀ : IFEnv) : List EIdx → AM Bool
  | [] => pure true
  | e :: es => do
    if ← constsResolveFFast fe₀ e then idxArgsResolve fe₀ es else pure false

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:66-107 checkSumCtor
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:56-84 checkSumCtorF
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove SumInstall.checkSumCtor_bridge, then delete this line
Stage 2, one constructor's type: the ordinary constant check (the constructor
is stored AS DECLARED), the result shape, the parameter pins against the type
former's opened telescope, the pre-block resolution of the field domains, and
the per-field universe bound. -/
def checkSumCtor (mode : CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) : AM Unit := do
  checkConstantVal mode fe cvC false
  let (_, cbody) ← unwrapOr (← stripPis (nP + nF) cvC.type)
    (.notImplemented "direct sum: constructor telescope")
  -- official's `is_valid_ind_app` on the constructor's result: a REJECT, not a
  -- decline (task #220)
  unless ← structCtorResidOk T lps nP nF nIdx cbody do
    fail (.invalid "direct sum: invalid constructor return type")
  -- the opened frames (the Rust's `check_sum_ctor_frames`)
  let cq ← unwrapOr (← openPisAtFvarsF nP cvC.type 0)
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
  checkStructFieldSortsI mode fe isProp large resSort nP xq.1 idxArgs nF

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:109-117 checkSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:86-93 checkSumCtorsF
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove SumInstall.checkSumCtors_bridge, then delete this line
Stage 2, all constructors' types, at the environment holding the type
former. -/
def checkSumCtors (mode : CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (cvTa : IConstantVal) : List (IConstantVal × Nat) → AM Unit
  | [] => pure ()
  | c :: cs => do
    checkSumCtor mode fe₀ fe T lps nP nIdx resSort isProp large c.1 c.2 cvTa
    checkSumCtors mode fe₀ fe T lps nP nIdx resSort isProp large cvTa cs

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:119-122 consSumCtors
con-leche: ConLeche/Cached/IndBlock.lean:37-40 consSumCtorsF
The constructors' conses, in order (the first constructor deepest).  Pure: the
index push touches no term. -/
def consSumCtors (nP : Nat) : List (IConstantVal × Nat) → IFEnv → IFEnv
  | [], fe => fe
  | c :: cs, fe => consSumCtors nP cs (fe.push (.ctorInfo c.1 nP c.2))

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:124-130 sumRules
The stored rules: constructor `j`'s with the generated right-hand side `j`,
`.plain` (the major is the family at the recursor's parameters). -/
def sumRules : List (IConstantVal × Nat) → List EIdx → List IRecRule
  | c :: cs, rhs :: rhss =>
    { ctor := c.1.name, nfields := c.2, fire := .plain, rhs := rhs } :: sumRules cs rhss
  | _, _ => []

end ConRon.Arena
