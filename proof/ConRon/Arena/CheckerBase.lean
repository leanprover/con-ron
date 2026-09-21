/-
# `ConRon.Arena.CheckerBase` — the declaration checker's common ground

The twin of `ConLeche/Kernel/CheckerBase.lean`: the core entry-point record,
the common per-declaration constant check, and the strategy-independent
helpers the install paths share.

## The four systematic deviations

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
   will need, as `Arena/CoreIO.lean` and `Arena/CoreGated.lean` are — and
   every body below calls `Arena/Core.lean`'s fueled entry points directly.
3. **`orElse` is `orElseAttempt`, the four-way step**, and it is the one place
   in (B) that recovers from a thrown error.  See its own note.
4. **A `g : Nat → Expr → Expr` argument is not a function value.**
   `domsMatchAux` is called at the identity everywhere in this module and at
   `renameConsts (projFwd …)` in `checkProjIotaF` (the modeled install's,
   P2d-2's), so the twin here is the identity one; over handles the renaming
   one cannot share it anyway, because renaming a constant is monadic.

## What is NOT here

`checkProjShape` and `checkProjRule` are the modeled install's stages 2b and
3; they are twinned here because they need nothing from
`ConLeche/Kernel/Inductives/*`, which is P2d-2's half of this phase.
-/
import ConRon.Arena.NatOpPinSet
import ConRon.Arena.Inductives.StructParts

namespace ConRon.Arena

open ConLeche

/-! ## The core entry-point record -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps — the core
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

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:57-66 fueledOps — **the one
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

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:68-69 pureOps — the one
instantiation at the standard fuel. -/
def pureOpsA (mode : CheckMode) : CheckerOpsA := fueledOpsA mode checkFuel

/-! ## The variant fallback

DESIGN §8.3 and OVERVIEW §4.5 describe con-ron's `or_else_step`
(`crates/con-ron-core/src/cached/checker_c.rs:123-132`), and this is its
twin. -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps — what
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

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps — **the
attempt, with the memo state snapshotted and restored on a mirrored error.**

This is the ONE place (B) recovers from a thrown error, and it is scoped to
one `Nat.div`/`Nat.mod` pin variant's attempt: a certificate blob generated by
another toolchain can be ill-typed against this stream, and that is "this
variant does not match", not a checker bug.

Written as a state function rather than with `try`/`catch`, which is what
makes the snapshot free: `AM = StateT AState (Except CheckError)`, so the
PRE-attempt state `s` is in hand at the error arm and restoring it discards
everything the failed attempt wrote — the memo and cache entries the port's
`state_c::dup` snapshot discards, and, because the arena's state also carries
the store, the nodes the attempt appended.  Discarding an append is sound and
invisible: every handle that existed before the attempt still decodes (the
tiers are append-only and the restored sizes are the old ones), and no handle
the attempt made survives the arm.  The continuation is the caller's own tail
call (`checkDivModPinLoop`), so it does not appear here — DESIGN §3.4 forbids
the closure con-leche passes. -/
def orElseAttempt (att : AM Bool) : AM OrElseStep := fun s =>
  match att s with
  | .ok (true, s') => .ok (.matched, s')
  | .ok (false, s') => .ok (.continued, s')
  | .error e =>
    match e with
    | .native m => .ok (.failed (.native m), s)
    | _ => .ok (.recovered e, s)

/-! ## Name-shape tests

`ConLeche/Kernel/Level.lean`'s three `Name` predicates are P2a's file and were
not twinned there (the store layer needed the representation, not the
predicates); the declaration front door is their only reader, so they are
here.  Each is a handle comparison or one `viewN`. -/

/-- con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup — no duplicates
in a list of name HANDLES.  A name comparison is a handle comparison (DESIGN
§8.3: `denoteN` is injective). -/
def nameNodup : List NIdx → Bool
  | [] => true
  | n :: ns => !ns.contains n && nameNodup ns

/-- con-leche: ConLeche/Kernel/Level.lean:218-221 Name.isModelSuffix — is
this a `_model`-suffixed name (the shape of model companions)? -/
def NIdx.isModelSuffix (n : NIdx) : AM Bool := do
  match ← viewN n with
  | .str _ s => pure (s == "_model")
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Level.lean:223-230 Name.isProjFnShape — is
this shaped like an installed projection function's name (`(T.proj).i`) or a
projection table's (`(T.projTable).0`)?  Both shapes are reserved for the
checker's own installs. -/
def NIdx.isProjFnShape (n : NIdx) : AM Bool := do
  match ← viewN n with
  | .num p _ => do
    match ← viewN p with
    | .str _ s => pure (s == "proj" || s == "projTable")
    | _ => pure false
  | _ => pure false

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

/-- con-leche: ConLeche/Kernel/Level.lean:251-268 Expr.allLevelParamsDefined
con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
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

/-- con-leche: ConLeche/Kernel/Level.lean:405-407 Expr.allLevelParamsDefinedFast
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

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:37-58 Expr.constsResolveF
con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo
The memoized walk.  The leaf clauses are `Arena/Core.lean`'s `constsResolve`
at one node, exactly as con-leche's `…Go` calls the pure walk at its four
non-recursive constructors. -/
def constsResolveFGo (fe : IFEnv) (memo : Std.HashMap EIdx Bool) :
    Nat → EIdx → AM (Bool × Std.HashMap EIdx Bool)
  | 0, _ => fail (.internal "fuel exhausted: constsResolveF")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ | .sort _ | .lit _ | .const _ _ =>
      pure (← constsResolve fe coreWalkFuel h, memo)
    | _ => do
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let p : Bool × Std.HashMap EIdx Bool ← match ← view h with
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

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:197-199 Expr.constsResolveFFast
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

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:71-91 unresolvedConstsError —
**the verdict at a term whose constants do not all resolve.**  A term that
mentions `sorryAx` DECLINES (the axiom is tolerated as a declaration and
installs nothing, so a use of it is a positively detected unsupported
feature); anything else is an unknown constant and REJECTS.  Monadic here
because the walk reads the store. -/
def unresolvedConstsError (where_ : String) (e : EIdx) : AM CheckError := do
  let sa ← pin sorryAxName
  if ← mentionsConst sa e then
    pure (.notImplemented s!"use of the sorryAx axiom in {where_}")
  else pure (.invalid s!"unknown constant in {where_}")

/-! ## The per-declaration constant check -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
con-leche: ConLeche/Kernel/DeclCheck.lean:463-485 checkConstantValF
Checks common to all declarations: fresh name, well-formed universe
parameters, and a type that is a type and mentions only declared parameters.
Returns the constant with its type **annotated**; the guards run on the
annotated type.

The name is read back for four of the six messages — DESIGN §8.3's "readback
happens only for the environment index's error text". -/
def checkConstantVal (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    AM IConstantVal := do
  if (fe.find? cv.name).isSome then
    fail (.invalid s!"duplicate declaration {← readName cv.name}")
  if (← reservedBasisNames).contains cv.name then
    fail (.invalid s!"reserved basis name {← readName cv.name}")
  if ← NIdx.isProjFnShape cv.name then
    fail (.invalid s!"reserved projection name {← readName cv.name}")
  unless nameNodup cv.levelParams do
    fail (.invalid s!"duplicate universe parameters in {← readName cv.name}")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.invalid s!"loose bound variable in type of {← readName cv.name}")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.invalid s!"unexpected free variable in type of {← readName cv.name}")
  let type ← annotateCore mode fe checkFuel 0 cv.type
  unless ← allLevelParamsDefined cv.levelParams type do
    fail (.invalid
      s!"undeclared universe parameter in type of {← readName cv.name}")
  unless ← constsResolveFFast fe type do
    fail (← unresolvedConstsError s!"type of {← readName cv.name}" type)
  let stype ← inferTypeCore mode fe checkFuel 0 type
  let _u ← ensureSortCore mode fe checkFuel 0 stype
  pure { cv with type := type }

/-! ## The strategy-independent helpers -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux
con-leche: ConLeche/Kernel/CheckerBase.lean:142-151 domsMatchAuxA
Compare binder domains at offsets `o₁`/`o₂` for `n` positions, at the
IDENTITY view (module note 4).  con-leche's `List` version is quadratic on a
wide telescope and its `Array` twin is what the checker runs, so the twin is
the array one; and over handles a domain comparison is a handle comparison,
so this is PURE. -/
def domsMatchAux (bs₁ bs₂ : Array (EIdx × BinderMeta)) (o₁ o₂ n : Nat) : Bool :=
  (List.range n).all fun i =>
    match bs₁[o₁ + i]?, bs₂[o₂ + i]? with
    | some b₁, some b₂ => b₁.1 == b₂.1
    | _, _ => false

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:130-140 openPisAtFvars — open
the first `n` `∀`-binders at fresh free variables `0..n-1` (each fvar's type
is the binder domain, instantiated with the earlier fvars).  Structural on
`n`, so no fuel of its own. -/
def openPisAtFvars : Nat → EIdx → Nat → AM (Option (List EIdx × EIdx))
  | 0, e, _ => pure (some ([], e))
  | n + 1, h, i => do
    match ← view h with
    | .forallE dom body _ => do
      let fv ← internE (.fvar i dom)
      let b ← instantiate1Fast coreWalkFuel body fv 0
      match ← openPisAtFvars n b (i + 1) with
      | some (fvs, e) => pure (some (fv :: fvs, e))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:153-167 openPisAtFvarsFGo —
core of `openPisAtFvarsF`: `acc` holds the already-created fvars, innermost
binder first.  One `instantiateList` pass per domain instead of one
whole-telescope `instantiate1` pass per binder. -/
def openPisAtFvarsFGo (acc : Array EIdx) :
    Nat → EIdx → Nat → AM (Option (List EIdx × EIdx))
  | 0, e, _ => do pure (some ([], ← instantiateListFast coreWalkFuel e acc 0))
  | n + 1, h, i => do
    match ← view h with
    | .forallE dom body _ => do
      let d ← instantiateListFast coreWalkFuel dom acc 0
      let fv ← internE (.fvar i d)
      match ← openPisAtFvarsFGo (acc.push fv) n body (i + 1) with
      | some (fvs, e) => pure (some (fv :: fvs, e))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:169-176 openPisAtFvarsF —
one-pass `openPisAtFvars` (the fallback covers telescopes whose binders only
appear after substitution). -/
def openPisAtFvarsF (n : Nat) (e : EIdx) (i : Nat) :
    AM (Option (List EIdx × EIdx)) := do
  match ← openPisAtFvarsFGo #[] n e i with
  | some r => pure (some r)
  | none => openPisAtFvars n e i

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

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:208-211 isEqHead — is the
expression the pinned equality former at one level? -/
def isEqHead (h : EIdx) : AM Bool := do
  match ← view h with
  | .const c us => do
    let en ← pin eqName
    if c == en then pure ((← viewLs us).length == 1) else pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:213-220 eqHeadLevel — the
level an equality head carries.  Off shape it is `.zero`, which `isEqHead` has
already rejected wherever the result is used. -/
def eqHeadLevel (h : EIdx) : AM LIdx := do
  match ← view h with
  | .const _ us => do
    match ← viewLs us with
    | [l] => pure l
    | _ => zeroLevel
  | _ => zeroLevel

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

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:233-239 unwrapOr — unwrap an
optional value or fail with the given error. -/
def unwrapOr {α : Type} (o : Option α) (err : CheckError) : AM α :=
  match o with
  | some a => pure a
  | none => fail err

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:241-247 Env.findCV?
con-leche: ConLeche/Kernel/DeclCheck.lean:33-35 FEnv.findCV?
The stored constant under `n`, as an `IConstantVal`, if any. -/
def IFEnv.findCV? (fe : IFEnv) (n : NIdx) : AM (Option IConstantVal) := do
  match fe.find? n with
  | some ci => pure (some (← ci.toConstantVal))
  | none => pure none

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:249-254 piResultSort — the
result sort of a syntactic pi telescope, if it ends in a sort at all. -/
def piResultSort (e : EIdx) : AM (Option LIdx) := do
  match ← view (← piResult coreWalkFuel e) with
  | .sort u => pure (some u)
  | _ => pure none

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:257-272 checkProjShape — stage
2b: the projection type's parameter telescope is *syntactically* the
constructor's, and the constructor's residual is the family applied to exactly
the parameters. -/
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

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
con-leche: ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF
Stage 3: the reduction rule — λ over the constructor telescope returning field
`i`, annotated; its λ-domains stay the constructor's. -/
def checkProjRule (mode : CheckMode) (fe : IFEnv) (pty : EIdx)
    (cvj : IConstantVal) (lps : List NIdx) (nP nF i : Nat) : AM EIdx := do
  let bv ← internE (.bvar (nF - 1 - i))
  let some rhs ← pisToLams (nP + nF) cvj.type bv
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
  unless rrbody == bv do
    fail (.notImplemented "projection rule body")
  let some (cbindersR, _) ← stripPis (nP + nF) cvj.type
    | fail (.notImplemented "projection constructor telescope")
  unless domsMatchAux rbinders.toArray cbindersR.toArray 0 0 (nP + nF) do
    fail (.notImplemented "projection rule domain mismatch")
  let some (fvsP, _) ← openPisAtFvarsF nP pty 0
    | fail (.notImplemented "projection type telescope")
  let some (cdomsP, crestP) ← instPisAtF coreWalkFuel fvsP cvj.type
    | fail (.notImplemented "projection constructor telescope")
  checkDefEqList mode fe (nP + nF) (← fvarTypeDs fvsP) cdomsP
  let some (xFvs, _) ← openPisAtFvarsF nF crestP nP
    | fail (.notImplemented "projection constructor telescope")
  let some (ldoms, _) ← instLamsAtF coreWalkFuel (fvsP ++ xFvs) rhsA
    | fail (.notImplemented "projection rule telescope")
  checkDefEqList mode fe (nP + nF) (← fvarTypeDs (fvsP ++ xFvs)) ldoms
  let _rhsTy ← inferTypeCore mode fe checkFuel 0 rhsA
  pure rhsA

/-! ## The block's partition and its declared parameter count

Three `ConLeche/Kernel/Env.lean` declarations, placed at their only readers —
the `.indDecl` arm and the modeled install — exactly as the six `Level.lean`
declarations above are.  Task #97d-2 wrote them in
`Arena/Inductives/Base.lean` under the concurrency contract; task #97f's dedup
deleted that file and brought them here. -/

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
