/-
# `ConRon.Arena.Inductives` — the inductive block's dispatch
(DESIGN.md §8, task #97d-2)

The `.indDecl` arm of con-leche's `checkDecl`
(`ConLeche/Kernel/Checker.lean:566-609`), from the declared parameter count
down to the two routes: this is the single entry point
`Arena/Checker.lean`'s declaration checker calls, and everything under
`Arena/Inductives/` is what it calls.

What is NOT here is the **pinned basis block** (`basisPinHit`): a stream's
`Nat` block arrives as an ordinary `indDecl` and is recognised before this,
in the declaration checker, because its install is `checkBasisDecl`'s and not
an inductive route's.  con-leche's `checkDecl` makes that test first and only
then reaches the two clauses below; the arena's does the same.

Ten modules stand behind it, one per con-leche file of
`ConLeche/Kernel/Inductives/`.  The `CheckerBase`/`Env`/`Level` twins they
call are `Arena/CheckerBase.lean`'s; task #97d-2 wrote a borrowed copy of them
in an `Arena/Inductives/Base.lean` of its own because the two halves of P2d
ran concurrently, and task #97f deleted it.
-/
import ConRon.Arena.Inductives.NativeInstallF

namespace ConRon.Arena.Inductives

open ConLeche
open ConRon.Arena

/-- con-leche: ConLeche/Kernel/Checker.lean:440-609 checkDecl — the `.indDecl`
arm: **the declared parameter count first, and for both routes** (task #228;
`indParamsOk` is official's own check, one-sided, so a `false` is official's
reject), then ONE ROUTE (task #210) — the fixpoint route takes every block its
recogniser recognises, and everything else is the modeled path's, which
DECLINES, naming the block, when there is no model.  The dispatch is the
RECOGNISER alone (task #219): a mutual or nested block carries several type
formers, resp. several recursors, so `sumSplit` refuses it outright and no
model lookup is needed to route it. -/
def checkIndDecl (mode : CheckMode) (fe : IFEnv) (block : List IConstantInfo)
    (numParams : Nat) : AM IFEnv := do
  if ← indParamsOk numParams block then
    match ← nativeParts? numParams block with
    | some p => checkNative mode fe p
    | none => checkModeled mode fe block
  else fail (.invalid "number of parameters mismatch")

end ConRon.Arena.Inductives
