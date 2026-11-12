/-
# `ConRon.Arena.CheckerBase` — the declaration checker's common ground

The twin of `ConLeche/Kernel/CheckerBase.lean`: the common per-declaration
constant check and the strategy-independent helpers the install paths share.

## The two systematic deviations

1. **`env : Env` becomes `fe : IFEnv`** — `Arena/Core.lean`'s deviation 1.
   con-leche carries each of these functions twice, once reading the linear
   association list (`CheckerBase.lean`, `Checker.lean`) and once the index
   (`DeclCheck.lean`'s `…F` mirrors); the arena has ONE environment type, so
   each pair collapses into one twin carrying a `con-leche:` line per
   collapsed declaration.
2. **`CheckerOps` is not a record here.**  DESIGN §8.2 is explicit that the
   record is "a program seam at HEAD, not a proof seam" and that (B) "calls
   its own bodies"; DESIGN §3.4 forbids a record of function values in code
   Aeneas must translate.  So every body below calls `Arena/Core.lean`'s
   fueled entry points directly.
-/
module

public import ConRon.Arena.Inductives.StructParts

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## Name-shape tests

`ConLeche/Kernel/Level.lean`'s three `Name` predicates are P2a's file and were
not twinned there (the store layer needed the representation, not the
predicates); the declaration front door is their only reader, so they are
here.  Each is a handle comparison or one `viewN`. -/

/-- con-leche: ConLeche/Kernel/Level.lean:227-230 Name.nodup — no duplicates
in a list of name HANDLES.  A name comparison is a handle comparison (DESIGN
§8.3: `denoteN` is injective). -/
def nameNodup : List NIdx → Bool
  | [] => true
  | n :: ns => !ns.contains n && nameNodup ns

/-! ## Level parameters, defined

`Expr.allLevelParamsDefined` is `ConLeche/Kernel/Level.lean`'s and was not
twinned by P2a either.  It is read at every declaration front door, and on a
DAG-shared type a tree walk does not finish (con-leche's task #210 Part B
memoized it for exactly that reason), so the twin carries the memo — threaded
explicitly as the census's twin column has it, because the answer depends on
the parameter list and `Memos` is the per-CALL record.

The parameter list is read BACK once at the entry, as `instLPFast` reads its
`ks`: `Level.allParamsDefined` and `PropWhen.paramsDefined` are con-leche's
own functions on transient values, and DESIGN §8.3's lesson 4 says a level
algorithm runs on trees. -/

/-- con-leche: ConLeche/Kernel/Level.lean:249-265 Expr.allLevelParamsDefined
con-leche: ConLeche/Cached/ExprOpsC.lean:2325-2395 allLevelParamsDefinedXP
The memoized walk.  `params` are transient names (see the section note); the
memo is keyed on the node, which is what makes a shared subterm cost one
probe. -/
def allLevelParamsDefinedGo (params : List ConLeche.Name)
    (memo : Std.HashMap EIdx Bool) : Nat → EIdx → AM (Bool × Std.HashMap EIdx Bool)
  | 0, _ => fail (.internal "fuel exhausted: allLevelParamsDefined")
  | fuel + 1, h => do
    match memo[h]? with
    | some r => pure (r, memo)
    | none => do
      let p : Bool × Std.HashMap EIdx Bool ← match ← view h with
        | .bvar _ | .lit _ => pure (true, memo)
        | .sort u => do
          let l ← readLevel u
          pure (l.allParamsDefined params, memo)
        | .const _ us => do
          let ls ← readLevels us
          pure (ls.all (Level.allParamsDefined params), memo)
        | .fvar _ t => allLevelParamsDefinedGo params memo fuel t
        | .app f a => do
          let (b₁, memo) ← allLevelParamsDefinedGo params memo fuel f
          if b₁ then allLevelParamsDefinedGo params memo fuel a
          else pure (false, memo)
        | .lam t b | .forallE t b => do
          let (b₁, memo) ← allLevelParamsDefinedGo params memo fuel t
          if !b₁ then pure (false, memo) else allLevelParamsDefinedGo params memo fuel b
        | .letE t v b => do
          let (b₁, memo) ← allLevelParamsDefinedGo params memo fuel t
          if !b₁ then pure (false, memo) else do
            let (b₂, memo) ← allLevelParamsDefinedGo params memo fuel v
            if !b₂ then pure (false, memo)
            else allLevelParamsDefinedGo params memo fuel b
        | .proj _ _ e => allLevelParamsDefinedGo params memo fuel e
      pure (p.1, p.2.insert h p.1)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:2397-2401 allLevelParamsDefinedC
The executed `allLevelParamsDefined`: one memoized DAG walk, at the parameter
list read back once. -/
def allLevelParamsDefined (lps : List NIdx) (e : EIdx) : AM Bool := do
  let ks ← readNames lps
  pure (← allLevelParamsDefinedGo ks ∅ coreWalkFuel e).1

/-! ## `constsResolve`, memoized

`Arena/Core.lean` twins `ConLeche/Kernel/Core.lean`'s `Expr.constsResolve` —
the pure walk, which is con-leche's specification.  What the checker runs is
`ConLeche/Kernel/DeclCheck.lean`'s memoized `constsResolveFFast` (`@[csimp]`),
and it must: every declaration front door asks it of a stream term, and on a
DAG-shared type the pure walk unfolds the DAG (con-leche's task #210 Part B,
`tests/e2e/tower_struct.ndjson`).  So the memoized twin is here, beside its
only callers; the memo is threaded explicitly — the census's own twin column
— because the answer depends on `fe` and `Memos` is the per-CALL record. -/

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:30-51 Expr.constsResolveF
con-leche: ConLeche/Cached/StateC.lean:614-671 constsResolveFXP
The memoized walk.  The leaf clauses are `Arena/Core.lean`'s `constsResolve`
at one node, exactly as con-leche's `…Go` calls the pure walk at its four
non-recursive constructors.  The node is viewed ONCE and the miss arm
dispatches on that view, as the port does (`consts_resolve_f_node` takes the
view; task #97-T2-LOCKSTEP lane Checker Base/Top round 2). -/
def constsResolveFGo (fe : IFEnv) (memo : Std.HashMap EIdx Bool) :
    Nat → EIdx → AM (Bool × Std.HashMap EIdx Bool)
  | 0, _ => fail (.internal "fuel exhausted: constsResolveF")
  | fuel + 1, h => do
    let v ← view h
    match v with
    | .bvar _ | .sort _ | .lit _ | .const _ _ =>
      pure (← constsResolve fe coreWalkFuel h, memo)
    | _ => do
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let p : Bool × Std.HashMap EIdx Bool ← match v with
          | .fvar _ ty => constsResolveFGo fe memo fuel ty
          | .app f a => do
            let (b₁, memo) ← constsResolveFGo fe memo fuel f
            let (b₂, memo) ← constsResolveFGo fe memo fuel a
            pure (b₁ && b₂, memo)
          | .lam ty body | .forallE ty body => do
            let (b₁, memo) ← constsResolveFGo fe memo fuel ty
            let (b₂, memo) ← constsResolveFGo fe memo fuel body
            pure (b₁ && b₂, memo)
          | .letE ty val body => do
            let (b₁, memo) ← constsResolveFGo fe memo fuel ty
            let (b₂, memo) ← constsResolveFGo fe memo fuel val
            let (b₃, memo) ← constsResolveFGo fe memo fuel body
            pure (b₁ && b₂ && b₃, memo)
          | .proj s _ sub => do
            let (b, memo) ← constsResolveFGo fe memo fuel sub
            pure ((fe.find? s).isSome && b, memo)
          | _ => pure (← constsResolve fe coreWalkFuel h, memo)
        pure (p.1, p.2.insert h p.1)

/-- con-leche: ConLeche/Cached/StateC.lean:673-675 constsResolveFC
The executed `constsResolve` (one memoized DAG walk), which is what every
front door below calls. -/
def constsResolveFFast (fe : IFEnv) (e : EIdx) : AM Bool := do
  pure (← constsResolveFGo fe ∅ coreWalkFuel e).1

/-- con-leche: none — `xs.map Expr.fvarTypeD` over a list of handles.  DESIGN
§3.4 forbids the closure `List.map` takes, and its rule for a `List`
recursion is a helper. -/
def fvarTypeDs : List EIdx → AM (List EIdx)
  | [] => pure []
  | h :: hs => do
    let t ← fvarTypeD h
    let ts ← fvarTypeDs hs
    pure (t :: ts)

/-! ## The front door's verdict at an unresolved constant

`mentionsConst` — the memoized DAG walk `unresolvedConstsError` runs on a
term `constsResolve` has just walked, con-leche's `mentionsAnyConst
[sorryAxName]` — is `Arena/Inductives/StructParts.lean`'s, at one name.
That module sits below this one, so there is ONE walk. -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:46-65 unresolvedConstsError —
**the verdict at a term whose constants do not all resolve.**  A term that
mentions `sorryAx` DECLINES (the axiom is tolerated as a declaration and
installs nothing, so a use of it is a positively detected unsupported
feature); anything else is an unknown constant and REJECTS.  Monadic here
because the walk reads the store. -/
def unresolvedConstsError (where_ : String) (e : EIdx) : AM CheckError := do
  let sa ← pinSorryAx
  if ← mentionsConst sa e then
    pure (.notImplemented s!"use of the sorryAx axiom in {where_}")
  else pure (.invalid s!"unknown constant in {where_}")

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:67-89 Expr.hasStrLitGo — does
the term contain a string literal?  (Error path only.)  A memoized DAG walk:
con-leche's visited set is the memo's key set (the Rust's `HashMap<EIdx,
bool>`, every entry `false`), threaded as con-leche threads its
`Std.HashSet`.  The node is viewed first and the leaves decided off the view,
before the memo is consulted, as con-leche's first two clauses are and in the
Rust's order. -/
def hasStrLitGo (memo : Std.HashMap EIdx Bool) :
    Nat → EIdx → AM (Bool × Std.HashMap EIdx Bool)
  | 0, _ => fail (.internal "fuel exhausted: hasStrLit")
  | fuel + 1, e => do
    match ← view e with
    | .lit (.strVal _) => pure (true, memo)
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (false, memo)
    | v =>
      match memo[e]? with
      | some _ => pure (false, memo)
      | none => do
        let memo := memo.insert e false
        match v with
        | .fvar _ ty => hasStrLitGo memo fuel ty
        | .app f a => do
          let (r, memo) ← hasStrLitGo memo fuel f
          if r then pure (true, memo) else hasStrLitGo memo fuel a
        | .lam ty b | .forallE ty b => do
          let (r, memo) ← hasStrLitGo memo fuel ty
          if r then pure (true, memo) else hasStrLitGo memo fuel b
        | .letE ty v b => do
          let (r, memo) ← hasStrLitGo memo fuel ty
          if r then pure (true, memo) else do
            let (r, memo) ← hasStrLitGo memo fuel v
            if r then pure (true, memo) else hasStrLitGo memo fuel b
        | .proj _ _ x => hasStrLitGo memo fuel x
        | _ => pure (false, memo)

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:91-97 unresolvedConstsErrorL
con-leche: ConLeche/Cached/IndPass.lean:23-30 unresolvedConstsErrorLC —
`unresolvedConstsError` with a string-literal guard ahead of it: a string
literal is declined here, before resolution, when the String support
declarations are not yet present (con-leche's task #342: the guard the retired
annotate pass ran). -/
def unresolvedConstsErrorL (strOk : Bool) (where_ : String) (e : EIdx) :
    AM CheckError := do
  if !strOk then do
    let (r, _) ← hasStrLitGo {} coreWalkFuel e
    if r then
      pure (.notImplemented "string literals before the String support declarations")
    else unresolvedConstsError where_ e
  else unresolvedConstsError where_ e

/-! ## The per-declaration constant check -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:101-123 checkConstantVal
con-leche: ConLeche/Kernel/DeclCheck.lean:218-238 checkConstantValF
con-leche: ConLeche/Cached/IndPass.lean:36-58 checkConstantValC
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove CheckerBase.checkConstantVal_bridge, then delete this line
Checks common to all declarations: fresh name, a certified
operation's name only at a definition (`allowOp`, the cited default `false`,
spelled at every call as the Rust must), a literal's name only at its shape,
well-formed universe parameters, and a type that is a type and mentions only
declared parameters.  Returns nothing: the constant is stored as declared.
The messages drop con-leche's interpolated name (§3.1), except the certified
operation's, which names it as upstream's does (upstream's `.olean` gate reads
it): the name read back from the store. -/
def checkConstantVal (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (allowOp : Bool) : AM Unit := do
  if (fe.find? cv.name).isSome then
    fail (.invalid "duplicate declaration")
  if (← natOpName cv.name) && !allowOp then
    fail (.invalid s!"a certified Nat operation's name, not a definition: {← readName cv.name}")
  unless ← litShapeOk (.axiomInfo cv) do
    fail (.notImplemented "a declaration at a literal's name with another shape")
  unless nameNodup cv.levelParams do
    fail (.invalid "duplicate universe parameters")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.invalid "loose bound variable in type")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.invalid "unexpected free variable in type")
  unless ← allLevelParamsDefined cv.levelParams cv.type do
    fail (.invalid
      "undeclared universe parameter in type")
  unless ← constsResolveFFast fe cv.type do
    fail (← unresolvedConstsErrorL (← strLitStored fe) "type" cv.type)
  let stype ← inferTypeCore mode fe checkFuel 0 cv.type
  let _u ← ensureSortCore mode fe checkFuel 0 stype

/-! ## The strategy-independent helpers -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:125-131 unwrapOr — unwrap an
optional value or fail with the given error. -/
def unwrapOr {α : Type} (o : Option α) (err : CheckError) : AM α :=
  match o with
  | some a => pure a
  | none => fail err

/-! ## The block's partition and its declared parameter count

A `ConLeche/Kernel/Env.lean` declaration, placed at its only reader — the
`.indDecl` arm — exactly as the `Level.lean` declarations above are. -/

/-- con-leche: ConLeche/Kernel/Env.lean:390-423 indParamsOk — **the stream's
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove CheckerBase.indParamsOk_bridge, then delete this line
declared parameter count, checked as official checks it** (con-leche's task
#228).  Both halves are one-sided on purpose: `false` means official rejects. -/
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

end ConRon.Arena
