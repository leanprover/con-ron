/-
# `ConRon.Arena.PropRead` — the head-symbol prop-ness readers over handles

The twin of `ConLeche/Kernel/PropRead.lean` (con-leche's task #168): two
pure readers that answer "is this type a proposition?" / "is this term a
proof?" off the head symbol, the arity and the validated `pw` annotations —
no inference, no reduction.  `propIrrel`'s two fast arms and the annotation
pass's two datum computations are their only callers, and all four are on
the hot path, so the readers exist to keep inference out of them.

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
   what P2b's twins already look like.
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

/-! ## The syntactic residual -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:44-56 Expr.peelNeverPis — the
residual after peeling `k` *syntactic* ∀ binders whose data are all
`.never`.  Structural on `k`, so no fuel: con-leche's own recursion
measure survives the change of representation unchanged. -/
def peelNeverPis : Nat → EIdx → AM (Option EIdx)
  | 0, h => pure (some h)
  | k + 1, h => do
    match ← view h with
    | .forallE _ b m => if m.pw.isNever then peelNeverPis k b else pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/PropRead.lean:58-61 Expr.numArgs — the number
of arguments of an application spine.  A spine walk, hence fuel. -/
def numArgs : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: numArgs")
  | fuel + 1, h => do
    match ← view h with
    | .app f _ => do
      let n ← numArgs fuel f
      pure (n + 1)
    | _ => pure 0

/-- con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW — the
zero-ness datum of the sort of a *residual type*.  The level is read back
and `Level.zeronessOf` is con-leche's own (deviation 3). -/
def residualPW : Option EIdx → AM (Option PropWhen)
  | some h => do
    match ← view h with
    | .sort u => do
      let l ← readLevel u
      pure (some (Level.zeronessOf l))
    | _ => pure none
  | none => pure none

/-! ## The head readers -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-90 headTypePW — the datum of
a type-former application's *head* at `n` arguments.  A constant head reads
its stored type, an fvar head its declared type; the residual after `n`
syntactic binders is read by `residualPW`. -/
def headTypePW (fe : IFEnv) : EIdx → Nat → AM (Option PropWhen)
  | h, n => do
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
            let res ← peelNeverPis n cv.type
            match ← residualPW res with
            | some pw => do
              -- **The cutoff hoisted over the readback** (task #97-P6-10):
              -- `Level.substPW ks vs pw = pw` when `pw` names no parameter
              -- (its `never` and `always` arms are exactly where `bindZ` is
              -- the identity), so on a parameter-free datum both readbacks
              -- would be computed and dropped.
              if !pw.hasParams then pure (some pw)
              else do
                let ks ← readNamesM cv.levelParams
                let vs ← readLevelsM us
                pure (some (Level.substPW ks vs pw))
            | none => pure none
          else pure none
      | none => pure none
    | .fvar _ ty => do
      let res ← peelNeverPis n ty
      residualPW res
    | _ => pure none

/-- con-leche: ConLeche/Kernel/PropRead.lean:92-103 typeSortPW — the
zero-ness datum of the sort of the *type* `T` ("is `T` a proposition?").
con-leche's last arm rebinds the scrutinee; the twin keeps the handle. -/
def typeSortPW (fe : IFEnv) (fuel : Nat) (T : EIdx) : AM (Option PropWhen) := do
  match ← view T with
  | .forallE _ _ m => pure (some m.pw)
  | .sort _ => pure (some .never)
  | _ => do
    let fn ← getAppFn fuel T
    let n ← numArgs fuel T
    headTypePW fe fn n

/-- con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW — the datum
of a term's *head* (any arity): a constant head answers from its stored
type, an fvar head from its declared type; sorts, ∀s and literals are never
proofs. -/
def headProofPW (fe : IFEnv) (fuel : Nat) : EIdx → AM (Option PropWhen)
  | h => do
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
            | some pw => do
              -- the same cutoff as `headTypePW`'s (task #97-P6-10)
              if !pw.hasParams then pure (some pw)
              else do
                let ks ← readNamesM cv.levelParams
                let vs ← readLevelsM us
                pure (some (Level.substPW ks vs pw))
            | none => pure none
          else pure none
      | none => pure none
    | .fvar _ ty => typeSortPW fe fuel ty
    | .sort _ | .forallE .. | .lit _ => pure (some .never)
    | _ => pure none

/-- con-leche: ConLeche/Kernel/PropRead.lean:124-134 proofPW — the zero-ness
datum of the sort of the *type* of `a` ("is `a` a proof?"), read off `a`'s
head symbol at any arity. -/
def proofPW (fe : IFEnv) (fuel : Nat) (a : EIdx) : AM (Option PropWhen) := do
  match ← view a with
  | .lam _ _ m => pure (some m.pw)
  | _ => do
    let fn ← getAppFn fuel a
    headProofPW fe fuel fn

/-! ## The two arms -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:141-146 notProofFast —
**definitely not a proof**: the datum is known and is not always-zero.
Refusing the proof-irrelevance shortcut is always sound. -/
def notProofFast (fe : IFEnv) (fuel : Nat) (a : EIdx) : AM Bool := do
  match ← proofPW fe fuel a with
  | some pw => pure !pw.isProp
  | none => pure false

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-153 isProofFast —
**definitely a proof**: the datum is known and always-zero (the
squash-regime licence, con-leche's `prf_of_isProofFast`). -/
def isProofFast (fe : IFEnv) (fuel : Nat) (a : EIdx) : AM Bool := do
  match ← proofPW fe fuel a with
  | some pw => pure pw.isProp
  | none => pure false

end ConRon.Arena
