/-
# `ConRon.Arena.PropRead` — the head-symbol prop-ness readers over handles

The twin of `ConLeche/Kernel/PropRead.lean` (con-leche's task #168): two
pure readers that answer "is this type a proposition?" / "is this term a
proof?" off the head symbol, the arity and the residual sorts of stored
types — no inference, no reduction.  `propIrrel`'s two fast arms are their
only callers, and both are on the hot path, so the readers exist to keep
inference out of them.  (Task #119: upstream's task #342 rewrote the readers
binder-datum-free — they peel any syntactic binder and read the residual
sorts, through identity-like wrappers — and the twin follows.)

**Three deviations from con-leche's clause structure, all systematic and
all shared with `Arena/Core.lean`.**

1. **The lookup is not abstracted.**  con-leche writes
   `(find? : Name → Option ConstantInfo)` so that the plain environment and
   the indexed one share the body; the arena has ONE environment type —
   `IFEnv`, the index (DESIGN §8.3, lesson 13) — so the twin takes
   `fe : IFEnv` and calls `fe.find?`.  Passing `fe.find?` would be a
   closure, which DESIGN §3.4 forbids in code Aeneas must translate.
2. **The readers are monadic.**  Every structural match on a term is a
   `view`, so a pure `Expr → Option PropWhen` becomes `EIdx → AM (Option
   PropWhen)`; that is the census's mechanical column, and it is exactly
   what P2b's twins already look like.  A walk structural on a TERM takes
   an explicit fuel (`fuel` below, the caller's `coreWalkFuel`); one
   structural on a count does not.
3. **Levels are read back, not twinned** (DESIGN §8.3, lesson 4).
   `Level.substPW` and `Level.zeronessOf` are con-leche's own, run on
   transient `ConLeche.Level` trees and `List ConLeche.Name`s that
   `readLevels` / `readNames` hand over.  `PropWhen` itself is con-leche's
   (DESIGN §8.7: (B) imports the representation-free types), so
   `PropWhen.isProp` needs no twin at all.
-/
import ConRon.Arena.Env
import ConRon.Arena.ExprOps
import ConLeche.Kernel.PropRead

namespace ConRon.Arena

open ConLeche

/-! ## The syntactic telescope readers -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:40-46 Expr.peelPis — the
residual after peeling `k` *syntactic* ∀ binders, whatever their domains.
Structural on `k`, so no fuel. -/
def peelPis : Nat → EIdx → AM (Option EIdx)
  | 0, h => pure (some h)
  | k + 1, h => do
    -- tag first, then the binder projection, as the port (task #97-P5-Core
    -- round 6, D1)
    if h.tag == ETag.forallE then
      match ← viewBind h with
      | none => failDanglingE
      | some (_, b) => peelPis k b
    else pure none

/-- con-leche: ConLeche/Kernel/PropRead.lean:48-53 Expr.binderDom — the
domain of the `k`-th syntactic ∀ binder (`0` = outermost) of a telescope,
unsubstituted.  Structural on `k`. -/
def binderDom : Nat → EIdx → AM (Option EIdx)
  | 0, h => do
    if h.tag == ETag.forallE then
      match ← viewBind h with
      | none => failDanglingE
      | some (A, _) => pure (some A)
    else pure none
  | k + 1, h => do
    if h.tag == ETag.forallE then
      match ← viewBind h with
      | none => failDanglingE
      | some (_, b) => binderDom k b
    else pure none

/-- con-leche: ConLeche/Kernel/PropRead.lean:55-58 Expr.numArgs — the number
of arguments of an application spine.  A spine walk, hence fuel. -/
def numArgs : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: numArgs")
  | fuel + 1, h => do
    -- tag first, then the `app` projection, as the port (task #97-P5-Core
    -- round 6, D1)
    if h.tag == ETag.app then
      match ← viewApp h with
      | none => failDanglingE
      | some (f, _) => do
        let n ← numArgs fuel f
        pure (n + 1)
    else pure 0

/-- con-leche: ConLeche/Kernel/PropRead.lean:62-68 residualPW — the
zero-ness datum of the sort of a *residual type*.  The level is read back
and `Level.zeronessOf` is con-leche's own (deviation 3). -/
def residualPW : Option EIdx → AM (Option PropWhen)
  | some h => do
    -- tag first, then the `sort` projection, as the port (task #97-P5-Core
    -- round 6, D1)
    if h.tag == ETag.sort then
      match ← viewSort h with
      | none => failDanglingE
      | some u => do
        let l ← readLevel u
        pure (some (Level.zeronessOf l))
    else pure none
  | none => pure none

/-! ## Identity-like wrappers -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:70-76 lamProj? — the body of a
λ-telescope that is a single bound variable: `some (k, j)` for
`fun x₁ … x_k => x_{k-j}`.  A walk down the λ chain, hence fuel. -/
def lamProj? : Nat → Nat → EIdx → AM (Option (Nat × Nat))
  | 0, _, _ => fail (.internal "fuel exhausted: propRead")
  | fuel + 1, k, h => do
    if h.tag == ETag.lam then
      match ← viewBind h with
      | none => failDanglingE
      | some (_, b) => lamProj? fuel (k + 1) b
    else if h.tag == ETag.bvar then
      match ← viewBVar h with
      | none => failDanglingE
      | some j => pure (if j < k then some (k, j) else none)
    else pure none

/-- con-leche: ConLeche/Kernel/PropRead.lean:78-96 unwrapIdDefs — unfold an
identity-like wrapper (a definition whose value is `fun x₁ … x_k => x_i`,
e.g. `outParam`) at the head of a residual type, `n` times at most;
definitional (δ then β).  Structural on `n`; the walks inside run at the
reader's `fuel`. -/
def unwrapIdDefs (fe : IFEnv) (fuel : Nat) : Nat → EIdx → AM EIdx
  | 0, e => pure e
  | n + 1, e => do
    let hh ← getAppFn fuel e
    if hh.tag == ETag.const then
      match ← viewConstName hh with
      | none => failDanglingE
      | some c =>
        match fe.find? c with
        | some (.defnInfo _ v _) =>
          match ← lamProj? fuel 0 v with
          | some (k, j) => do
            let args ← getAppArgs fuel e
            if k ≤ args.length && args.length == k then
              unwrapIdDefs fe fuel n (args.getD (k - 1 - j) e)
            else pure e
          | none => pure e
        | _ => pure e
    else pure e

/-- con-leche: ConLeche/Kernel/PropRead.lean:98-105 peelPisW —
`peelPis` through identity-like wrappers (`outParam (α → Sort u)`).
Structural on `k`. -/
def peelPisW (fe : IFEnv) (fuel : Nat) : Nat → EIdx → AM (Option EIdx)
  | 0, e => do
    let u ← unwrapIdDefs fe fuel 4 e
    pure (some u)
  | k + 1, e => do
    if e.tag == ETag.forallE then
      match ← viewBind e with
      | none => failDanglingE
      | some (_, b) => peelPisW fe fuel k b
    else do
      let u ← unwrapIdDefs fe fuel 4 e
      if u.tag == ETag.forallE then
        match ← viewBind u with
        | none => failDanglingE
        | some (_, b) => peelPisW fe fuel k b
      else pure none

/-! ## The head readers -/

/-- con-leche: none — `Level.substPW ks vs pw` at a stored constant's level
parameters and a use's universe arguments, with **the cutoff hoisted over the
readback** (task #97-P6-10): a datum that names no parameter (`never`, or
`ifAllZero []`) is its own substitution (`bindZ` is the identity there), so
both readbacks would be computed and dropped. -/
def substPWAt (lps : List NIdx) (us : LsIdx) (pw : PropWhen) :
    AM (Option PropWhen) := do
  match pw with
  | .ifAllZero (_ :: _) => do
    let ks ← readNamesM lps
    let vs ← readLevelsM us
    pure (some (Level.substPW ks vs pw))
  | _ => pure (some pw)

/-- con-leche: ConLeche/Kernel/PropRead.lean:107-131 headTypePW — the datum of
a type-former application's *head* at `n` arguments: a constant head reads its
stored type (level-instantiated), an fvar head its declared type, a `bvar`
head (inside the ∀ telescope `root`, `d` binders deep) its binder's domain;
the residual after `n` syntactic binders is read by `residualPW`. -/
def headTypePW (fe : IFEnv) (fuel : Nat) (root : EIdx) (d : Nat) (h : EIdx)
    (n : Nat) : AM (Option PropWhen) := do
  match ← view h with
  | .const I us =>
    match fe.find? I with
    | some ci =>
      if ci.isTowerEntry then pure none else do
        let cv ← ci.toConstantVal
        match ← viewLsLen us with
        | none => failDanglingLs
        | some usl =>
        if usl = cv.levelParams.length then do
          let res ← peelPisW fe fuel n cv.type
          match ← residualPW res with
          | some pw => substPWAt cv.levelParams us pw
          | none => pure none
        else pure none
    | none => pure none
  | .fvar _ ty => do
    let res ← peelPisW fe fuel n ty
    residualPW res
  | .bvar i =>
    if i < d then do
      match ← binderDom (d - 1 - i) root with
      | some D => do
        let res ← peelPisW fe fuel n D
        residualPW res
      | none => pure none
    else pure none
  | _ => pure none

/-- con-leche: ConLeche/Kernel/PropRead.lean:133-140 typeSortPWGo — the walk
of `typeSortPW`: peel the ∀ telescope (a ∀'s prop-ness is its codomain's),
counting the binders, then read the residual's head.  A walk down the
telescope, hence fuel. -/
def typeSortPWGo (fe : IFEnv) (root : EIdx) : Nat → EIdx → Nat →
    AM (Option PropWhen)
  | 0, _, _ => fail (.internal "fuel exhausted: propRead")
  | fuel + 1, R, d => do
    if R.tag == ETag.forallE then
      match ← viewBind R with
      | none => failDanglingE
      | some (_, b) => typeSortPWGo fe root fuel b (d + 1)
    else if R.tag == ETag.sort then pure (some .never)
    else do
      let fn ← getAppFn fuel R
      let n ← numArgs fuel R
      headTypePW fe fuel root d fn n

/-- con-leche: ConLeche/Kernel/PropRead.lean:142-150 typeSortPW — the
zero-ness datum of the sort of the *type* `T` ("is `T` a proposition?"). -/
def typeSortPW (fe : IFEnv) (fuel : Nat) (T : EIdx) : AM (Option PropWhen) :=
  typeSortPWGo fe T fuel T 0

/-- con-leche: ConLeche/Kernel/PropRead.lean:152-183 headProofPW — the datum
of a term's *head* (any arity): a constant head answers from its stored type,
an fvar head from its declared type; sorts, ∀s and literals are never proofs;
a projection answers "not a proof" off its field's stored type when that is
never a proposition. -/
def headProofPW (fe : IFEnv) (fuel : Nat) (h : EIdx) : AM (Option PropWhen) := do
  match ← view h with
  | .const c us =>
    match fe.find? c with
    | some ci =>
      if ci.isTowerEntry then pure none else do
        let cv ← ci.toConstantVal
        match ← viewLsLen us with
        | none => failDanglingLs
        | some usl =>
        if usl = cv.levelParams.length then do
          match ← typeSortPW fe fuel cv.type with
          | some pw => substPWAt cv.levelParams us pw
          | none => pure none
        else pure none
    | none => pure none
  | .fvar _ ty => typeSortPW fe fuel ty
  | .sort _ | .forallE .. | .lit _ => pure (some .never)
  | .proj S i _ =>
    -- the indexed projection-table lookup, as the port (`ifenv_find_proj`:
    -- the table's name, the find, the field-count test, the entry)
    match ← fe.findProj? S i with
    | some entry => do
      match ← typeSortPW fe fuel entry.body with
      | some pw => pure (if pw.isNever then some pw else none)
      | none => pure none
    | none => pure none
  | _ => pure none

/-- con-leche: ConLeche/Kernel/PropRead.lean:185-196 proofPW — the zero-ness
datum of the sort of the *type* of `a` ("is `a` a proof?"): a λ answers from
its body, a `let` from its body, an application from its function, anything
else from its head.  A walk, hence fuel. -/
def proofPW (fe : IFEnv) : Nat → EIdx → AM (Option PropWhen)
  | 0, _ => fail (.internal "fuel exhausted: propRead")
  | fuel + 1, a => do
    -- tag first, then the projection, as the port (task #97-P5-Core round 6,
    -- D1)
    if a.tag == ETag.lam then
      match ← viewBind a with
      | none => failDanglingE
      | some (_, b) => proofPW fe fuel b
    else if a.tag == ETag.letE then
      match ← viewLet a with
      | none => failDanglingE
      | some (_, _, b) => proofPW fe fuel b
    else if a.tag == ETag.app then
      match ← viewApp a with
      | none => failDanglingE
      | some (f, _) => proofPW fe fuel f
    else headProofPW fe fuel a

/-! ## The two arms -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:204-209 notProofFast —
**definitely not a proof**: the datum is known and is not always-zero.
Refusing the proof-irrelevance shortcut is always sound. -/
def notProofFast (fe : IFEnv) (fuel : Nat) (a : EIdx) : AM Bool := do
  match ← proofPW fe fuel a with
  | some pw => pure !pw.isProp
  | none => pure false

/-- con-leche: ConLeche/Kernel/PropRead.lean:211-216 isProofFast —
**definitely a proof**: the datum is known and always-zero (con-leche's
`prf_of_isProofFast`). -/
def isProofFast (fe : IFEnv) (fuel : Nat) (a : EIdx) : AM Bool := do
  match ← proofPW fe fuel a with
  | some pw => pure pw.isProp
  | none => pure false

end ConRon.Arena
