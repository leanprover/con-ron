/-
# `ConRon.Arena.Inductives` — the inductive install, over handles

The seam between the two halves of DESIGN §8.6's phase P2d.  `checkDecl`'s
`.indDecl` arm dispatches a block that is not one of the pinned basis blocks
to `ConLeche/Kernel/Checker.lean:566-610`'s route choice — the declared
parameter count first, then `nativeParts?` deciding between `checkNative`
(the ONE fixpoint route) and `checkModeled` (the in-process modeller's) — and
that is the whole of `ConLeche/Kernel/Inductives/*`, 2 300 con-leche lines.

This module's signature is the contract the two halves were handed out
against; its BODY is the placeholder, and the inductive twins replace it.
Until then a block that reaches here DECLINES, which is the safe direction: a
decline is a positive statement about the checker, never a verdict about the
input.
-/
import ConRon.Arena.DeclCheck

namespace ConRon.Arena.Inductives

open ConLeche
open ConRon.Arena

/-- con-leche: ConLeche/Kernel/Checker.lean:566-610 checkDecl — the `.indDecl`
arm's route choice, once `basisPinHit` has declined the block: the declared
parameter count (`indParamsOk`, one-sided, official's own reject), then
`nativeParts?` between `checkNative` and `checkModeled`.

**Placeholder** (see the module note): the inductive twins are the other half
of phase P2d. -/
def checkIndDecl (_mode : CheckMode) (_fe : IFEnv)
    (_block : List IConstantInfo) (_numParams : Nat) : AM IFEnv :=
  fail (.notImplemented "arena: inductive install not yet wired")

end ConRon.Arena.Inductives
