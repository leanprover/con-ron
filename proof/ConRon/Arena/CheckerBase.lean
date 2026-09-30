/-
# `ConRon.Arena.CheckerBase` — the declaration checker's common ground

The twin of `ConLeche/Kernel/CheckerBase.lean`: the core entry-point record,
the common per-declaration constant check, and the strategy-independent
helpers the install paths share.

## The three systematic deviations

1. **`env : Env` becomes `fe : IFEnv`** — `Arena/Core.lean`'s deviation 1.
   con-leche carries each of these functions twice, once reading the linear
   association list (`CheckerBase.lean`, `Checker.lean`) and once the index
   (`DeclCheck.lean`'s `…F` mirrors); the arena has ONE environment type, so
   each pair collapses into one twin carrying a `con-leche:` line per
   collapsed declaration.
2. **`CheckerOps` is present but not passed.**  DESIGN §8.2 is explicit that
   the record is "a program seam at HEAD, not a proof seam" and that (B)
   "calls its own bodies"; DESIGN §3.4 forbids a record of function values in
   code Aeneas must translate, and `crates/con-ron-core/src/kernel/checker.rs`
   drops the `ops` binder for exactly that reason.  So `CheckerOpsA` and its
   ONE instantiation are twinned here — they are the statement subjects P3
   will need, as `Arena/CoreIO.lean` is — and
   every body below calls `Arena/Core.lean`'s fueled entry points directly.
3. **`orElse` is `orElseAttempt`, the four-way step**, and it is the one place
   in (B) that recovers from a thrown error.  See its own note.
-/
import ConRon.Arena.NatOpPinSet
import ConRon.Arena.Inductives.StructParts

namespace ConRon.Arena

open ConLeche

/-! ## The core entry-point record -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:22-50 CheckerOps — the core
entry points the declaration checker runs on.  con-leche is polymorphic in
the monad and instantiates the record twice (the pure knot for the proofs, the
memoized one in `ConLeche/Cached/CheckerC.lean` for the binary); the arena is
at `AM` with ONE knot, so the `m` parameter is gone and the name carries an
`A`, exactly as `Arena/Core.lean`'s `CoreFnsA` does.

**Not passed to anything** (module note 2): the record is the statement
subject P3 needs, and the bodies call `Arena/Core.lean`'s entries by name. -/
structure CheckerOpsA where
  annotate : IFEnv → Nat → EIdx → AM EIdx
  inferType : IFEnv → Nat → EIdx → AM EIdx
  isDefEq : IFEnv → Nat → EIdx → EIdx → AM Bool
  ensureSort : IFEnv → Nat → EIdx → AM LIdx
  whnf : IFEnv → Nat → EIdx → AM EIdx
  /-- The variant-fallback combinator.  See `orElseAttempt`, which is what
  the checker actually runs. -/
  orElse : AM Bool → (Option CheckError → AM Unit) → AM Unit

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:54-63 fueledOps — **the one
instantiation** (DESIGN §8.2: "one knot, the memoized one").  con-leche's
`fueledOps` is the PURE knot and `ConLeche/Cached/CheckerC.lean`'s `sharedOpsC`
the memoized one the binary runs; the arena's `pureFnsA` already carries the
memo probes, so this is both. -/
def fueledOpsA (mode : CheckMode) (F : Nat) : CheckerOpsA where
  annotate fe d e := annotateCore mode fe F d e
  inferType fe d e := inferTypeCore mode fe F d e
  isDefEq fe d a b := isDefEqCore mode fe F d a b
  ensureSort fe d e := ensureSortCore mode fe F d e
  whnf fe d e := ConRon.Arena.whnf mode fe F d e
  orElse x k := fun s =>
    match x s with
    | .ok (true, s') => .ok ((), s')
    | .ok (false, s') => k none s'
    | .error _ => k none s

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:65-66 pureOps — the one
instantiation at the standard fuel. -/
def pureOpsA (mode : CheckMode) : CheckerOpsA := fueledOpsA mode checkFuel

/-! ## The variant fallback

DESIGN §8.3 and OVERVIEW §6.5 (the `Native` kind) describe con-ron's
`or_else_attempt` (`crates/con-ron-core/src/arena/checker_base.rs`), and this
section is its twin. -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:22-50 CheckerOps — what
`orElse` decides once the attempt has run.  con-leche's clause is three-way;
the port's is four, and the arena's is the port's:

    | .ok (true,  s') => .ok ((), s')     ->  matched
    | .ok (false, s') => k none      s'   ->  continued   (post-attempt state)
    | .error e        => k (some e)  s    ->  recovered e (PRE-attempt state)
                                          ->  failed e    when e is `native`

`failed` carries **only** a `native` error (DESIGN §8.3's ruling, and task
#67's for the Rust port): the arena's own machine-word limit has no `throw`
behind it in con-leche, so "con-leche would have recovered from this too" is
a claim about a run the cited checker never has.  The stream declines instead;
an accept-direction deviation that can only lose acceptances. -/
inductive OrElseStep where
  | matched
  | continued
  | recovered (e : CheckError)
  | failed (e : CheckError)

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:22-50 CheckerOps — take the
snapshot a variant attempt is restored from: the WHOLE state (task
#97-T2-LOCKSTEP D4b).  In Lean it is the state itself; the port copies it
(`attempt_snapshot`: the four stores with both tiers, the memos, the caches
and the pins). -/
@[inline] def attemptSnapshot (st : AState) : AState := st

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:22-50 CheckerOps — the restore
of `OrElseStep.recovered`: the snapshot becomes the state, so everything the
attempt did goes.  The port moves its copy back (`attempt_restore`). -/
@[inline] def attemptRestore (_st : AState) (snap : AState) : AState := snap

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:22-50 CheckerOps — **the
four-way step itself**, as a PURE function of the attempt's outcome, which is
the shape the port has. -/
@[inline] def orElseStepOf : Except CheckError Bool → OrElseStep
  | .ok true => .matched
  | .ok false => .continued
  | .error (.native m) => .failed (.native m)
  | .error e => .recovered e

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:22-50 CheckerOps — **the
attempt, with the memo state snapshotted and restored on a mirrored error.**

This is the ONE place (B) recovers from a thrown error, and it is scoped to
one `Nat.div`/`Nat.mod` pin variant's attempt: a certificate blob generated by
another toolchain can be ill-typed against this stream, and that is "this
variant does not match", not a checker bug.

Written as a state function rather than with `try`/`catch`: `AM = StateT AState
(Except CheckError)`, so the PRE-attempt state `s` is what the error arm has
in hand, and `attemptRestore s (attemptSnapshot s)` is `s` itself.

**The port and the twin resume at the same state** (tasks #97-T2-LOCKSTEP
D4, D4b).  A throw in `StateT σ (Except ε)` carries no state, so the twin's
error arm can only resume at `s`.  The port keeps its `&mut AState` across
the failing attempt and moves back a full copy of the pre-attempt state taken
before it (`arena::decl_check::check_div_mod_pin_attempt`).  (Until D4 the
port kept the attempt's appended nodes, and the two scratch tiers then
differed in length — a difference no lockstep relation absorbs; D4 restored
the scratch tiers only, which is the whole state only given a frame over the
attempt; D4b copies everything.)  The attempt runs **eight times on the whole
of `Init`** (task #97-P6-4a §4).

The continuation is the caller's own tail call (`checkDivModPinLoop`), so it
does not appear here — DESIGN §3.4 forbids the closure con-leche passes. -/
def orElseAttempt (att : AM Bool) : AM OrElseStep := fun s =>
  let snap := attemptSnapshot s
  match att s with
  | .ok (b, s') => .ok (orElseStepOf (.ok b), s')
  | .error e => .ok (orElseStepOf (.error e), attemptRestore s snap)

/-! ## Name-shape tests

`ConLeche/Kernel/Level.lean`'s three `Name` predicates are P2a's file and were
not twinned there (the store layer needed the representation, not the
predicates); the declaration front door is their only reader, so they are
here.  Each is a handle comparison or one `viewN`. -/

/-- con-leche: ConLeche/Kernel/Level.lean:214-217 Name.nodup — no duplicates
in a list of name HANDLES.  A name comparison is a handle comparison (DESIGN
§8.3: `denoteN` is injective). -/
def nameNodup : List NIdx → Bool
  | [] => true
  | n :: ns => !ns.contains n && nameNodup ns

/-- con-leche: ConLeche/Kernel/Level.lean:219-226 Name.isProjFnShape — is
this shaped like an installed projection function's name (`(T.proj).i`) or a
projection table's (`(T.projTable).0`)?  Both shapes are reserved for the
checker's own installs. -/
def NIdx.isProjFnShape (n : NIdx) : AM Bool := do
  if n.tag == NTag.num then
    match ← viewN n with
    | .num p _ => do
      if p.tag == NTag.str then
        match ← viewN p with
        | .str _ s => pure (s == "proj" || s == "projTable")
        | _ => pure false
      else pure false
    | _ => pure false
  else pure false

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

/-- con-leche: ConLeche/Kernel/Level.lean:247-264 Expr.allLevelParamsDefined
con-leche: ConLeche/Kernel/Level.lean:295-328 Expr.allLevelParamsDefinedGo
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
        | .lam t b m | .forallE t b m => do
          let (b₁, memo) ← allLevelParamsDefinedGo params memo fuel t
          if !b₁ then pure (false, memo) else do
            let (b₂, memo) ← allLevelParamsDefinedGo params memo fuel b
            pure (b₂ && m.pw.paramsDefined params, memo)
        | .letE t v b => do
          let (b₁, memo) ← allLevelParamsDefinedGo params memo fuel t
          if !b₁ then pure (false, memo) else do
            let (b₂, memo) ← allLevelParamsDefinedGo params memo fuel v
            if !b₂ then pure (false, memo)
            else allLevelParamsDefinedGo params memo fuel b
        | .proj _ _ e => allLevelParamsDefinedGo params memo fuel e
      pure (p.1, p.2.insert h p.1)

/-- con-leche: ConLeche/Kernel/Level.lean:401-403 Expr.allLevelParamsDefinedFast
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
con-leche: ConLeche/Kernel/DeclCheck.lean:82-117 Expr.constsResolveFGo
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
          | .lam ty body _ | .forallE ty body _ => do
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

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:190-192 Expr.constsResolveFFast
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

/-! ## The front door's verdict at an unresolved constant -/

/-! ## The front door's verdict at an unresolved constant

`mentionsConst` — the memoized DAG walk `unresolvedConstsError` runs on a
term `constsResolve` has just walked — is `Arena/Inductives/StructParts.lean`'s
(P2d-2's half of this phase), which twins con-leche's own
`Expr.mentionsConstGo`/`Fast` because the direct install asks the same
question of a block's field types.  That module imports `Arena/FEnv.lean` and
nothing above it, so it sits below this one and there is ONE walk. -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:68-88 unresolvedConstsError —
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

/-! ## The per-declaration constant check -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:92-116 checkConstantVal
con-leche: ConLeche/Kernel/DeclCheck.lean:352-374 checkConstantValF
Checks common to all declarations: fresh name, well-formed universe
parameters, and a type that is a type and mentions only declared parameters.
Returns the constant with its type **annotated**; the guards run on the
annotated type.

The name is read back for four of the six messages — DESIGN §8.3's "readback
happens only for the environment index's error text". -/
def checkConstantVal (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    AM IConstantVal := do
  if (fe.find? cv.name).isSome then
    fail (.invalid "duplicate declaration")
  if (← reservedBasisNames).contains cv.name then
    fail (.invalid "reserved basis name")
  if ← NIdx.isProjFnShape cv.name then
    fail (.invalid "reserved projection name")
  unless nameNodup cv.levelParams do
    fail (.invalid "duplicate universe parameters")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.invalid "loose bound variable in type")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.invalid "unexpected free variable in type")
  let type ← annotateCore mode fe checkFuel 0 cv.type
  unless ← allLevelParamsDefined cv.levelParams type do
    fail (.invalid
      "undeclared universe parameter in type")
  unless ← constsResolveFFast fe type do
    fail (← unresolvedConstsError "type" type)
  let stype ← inferTypeCore mode fe checkFuel 0 type
  let _u ← ensureSortCore mode fe checkFuel 0 stype
  pure { cv with type := type }

/-! ## The strategy-independent helpers -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:118-128 openPisAtFvars — open
the first `n` `∀`-binders at fresh free variables `0..n-1` (each fvar's type
is the binder domain, instantiated with the earlier fvars).  Structural on
`n`, so no fuel of its own. -/
def openPisAtFvars : Nat → EIdx → Nat → AM (Option (List EIdx × EIdx))
  | 0, e, _ => pure (some ([], e))
  | n + 1, h, i => do
    if h.tag == ETag.forallE then
      match ← view h with
      | .forallE dom body _ => do
        let fv ← internE (.fvar i dom)
        let b ← instantiate1Fast coreWalkFuel body fv 0
        match ← openPisAtFvars n b (i + 1) with
        | some (fvs, e) => pure (some (fv :: fvs, e))
        | none => pure none
      | _ => pure none
    else pure none

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:130-144 openPisAtFvarsFGo —
core of `openPisAtFvarsF`: `acc` holds the already-created fvars, innermost
binder first.  One `instantiateList` pass per domain instead of one
whole-telescope `instantiate1` pass per binder. -/
def openPisAtFvarsFGo (acc : Array EIdx) :
    Nat → EIdx → Nat → AM (Option (List EIdx × EIdx))
  | 0, e, _ => do pure (some ([], ← instantiateListFast coreWalkFuel e acc 0))
  | n + 1, h, i => do
    if h.tag == ETag.forallE then
      match ← view h with
      | .forallE dom body _ => do
        let d ← instantiateListFast coreWalkFuel dom acc 0
        let fv ← internE (.fvar i d)
        match ← openPisAtFvarsFGo (acc.push fv) n body (i + 1) with
        | some (fvs, e) => pure (some (fv :: fvs, e))
        | none => pure none
      | _ => pure none
    else pure none

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:146-153 openPisAtFvarsF —
one-pass `openPisAtFvars` (the fallback covers telescopes whose binders only
appear after substitution). -/
def openPisAtFvarsF (n : Nat) (e : EIdx) (i : Nat) :
    AM (Option (List EIdx × EIdx)) := do
  match ← openPisAtFvarsFGo #[] n e i with
  | some r => pure (some r)
  | none => openPisAtFvars n e i

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:198-204 unwrapOr — unwrap an
optional value or fail with the given error. -/
def unwrapOr {α : Type} (o : Option α) (err : CheckError) : AM α :=
  match o with
  | some a => pure a
  | none => fail err

/-! ## The block's partition and its declared parameter count

A `ConLeche/Kernel/Env.lean` declaration, placed at its only reader — the
`.indDecl` arm — exactly as the `Level.lean` declarations above are. -/

/-- con-leche: ConLeche/Kernel/Env.lean:588-622 indParamsOk — **the stream's
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

/-! ## The syntactic reading of a nested rule's instantiation

The Rust's `expr_ops::nested_rule_syn` group.  It sits HERE rather than in
`Arena/ExprOps.lean` (con-leche's `Kernel/ExprOps.lean` home) because its
`resolves` argument is the checker's `constsResolveFFast` — con-leche passes
it in as a closure, the Rust calls `checker_base` from `expr_ops` (a module
cycle Rust allows and Lean does not).  Module placement only; the functions
are the Rust's, one for one. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn — `pins :=
(args.take cnP).map (lowerBVars k 0)`, left to right. -/
def lowerList (k : Nat) : List EIdx → AM (List EIdx)
  | [] => pure []
  | x :: xs => do
    let y ← lowerBVarsFast coreWalkFuel k 0 x
    let ys ← lowerList k xs
    pure (y :: ys)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn —
`pins.map (liftLooseBVars k 0)`, left to right. -/
def liftList (k : Nat) : List EIdx → AM (List EIdx)
  | [] => pure []
  | x :: xs => do
    let y ← liftLooseBVarsFast coreWalkFuel k 0 x
    let ys ← liftList k xs
    pure (y :: ys)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn — the pins'
well-formedness, `pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
resolves p && p.allLevelParamsDefined lps)`, the `&&` chain left to right. -/
def pinsWf (fe : IFEnv) (lps : List NIdx) (rP : Nat) : List EIdx → AM Bool
  | [] => pure true
  | p :: ps => do
    if ← hasFvarFast coreWalkFuel p then pure false
    else if !(← looseBVarsBoundedFast coreWalkFuel rP p) then pure false
    else if !(← constsResolveFFast fe p) then pure false
    else if !(← allLevelParamsDefined lps p) then pure false
    else pinsWf fe lps rP ps

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn — the
cursor recursion behind `levelsDeclared`. -/
def levelsDeclaredFrom (ps : List ConLeche.Name) : List LIdx → AM Bool
  | [] => pure true
  | l :: ls => do
    let lv ← readLevel l
    if Level.allParamsDefined ps lv then levelsDeclaredFrom ps ls
    else pure false

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn —
`lvls.all (Level.allParamsDefined lps)`, over handles. -/
def levelsDeclared (lps : List NIdx) (lvls : List LIdx) : AM Bool := do
  let ps ← readNames lps
  levelsDeclaredFrom ps lvls

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn — the pins'
and the levels' guards, once the argument shape has matched. -/
def nestedRuleSynGuards (fe : IFEnv) (lps : List NIdx) (lvls : LsIdx) (rP : Nat)
    (pins : List EIdx) : AM (Option (List LIdx × List EIdx)) := do
  if !(← pinsWf fe lps rP pins) then pure none
  else do
    let ls ← viewLs lvls
    if !(← levelsDeclared lps ls) then pure none
    else pure (some (ls, pins))

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn — at the
major's domain `dom = D lvls args`: the parameter prefix lowered past the
`k` indices, the shape tests in con-leche's `∧` order, then the guards. -/
def nestedRuleSynAt (fe : IFEnv) (lps : List NIdx) (dom : EIdx) (lvls : LsIdx)
    (k rP cnP : Nat) : AM (Option (List LIdx × List EIdx)) := do
  let args ← getAppArgs coreWalkFuel dom
  let pre := args.take cnP
  let pins ← lowerList k pre
  if args.length != cnP + k then pure none
  else do
    let back ← liftList k pins
    if pre != back then pure none
    else do
      let want ← bvarRange k k 0
      if args.drop cnP != want then pure none
      else nestedRuleSynGuards fe lps lvls rP pins

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn — **the
syntactic reading of a nested rule's instantiation**: the major's level and
parameter instantiations, read off the recursor's type, when the major's
domain applies a constant to parameters closed below the indices followed by
exactly the index variables. -/
def nestedRuleSyn (fe : IFEnv) (lps : List NIdx) (tyA : EIdx) (mI rP cnP : Nat) :
    AM (Option (List LIdx × List EIdx)) := do
  if rP ≤ mI then
    match ← stripPis mI tyA with
    | none => pure none
    | some q =>
      if q.2.tag == ETag.forallE then
        match ← viewBind q.2 with
        | none => failDanglingE
        | some (dom, _, _) => do
          let hd ← getAppFn coreWalkFuel dom
          if hd.tag == ETag.const then
            match ← viewConst hd with
            | none => failDanglingE
            | some (_, lvls) => nestedRuleSynAt fe lps dom lvls (mI - rP) rP cnP
          else pure none
      else pure none
  else pure none

end ConRon.Arena
