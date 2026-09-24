/-
# `ConRon.Arena.Inductives.SumParts` — the block's shape record
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/SumParts.lean` whole, over handles: the record a
recognised direct block is read into, the member split that reads it, and the
completion with the result sort the former's install stage measured.

**One deviation.**  `sumSplit` stays PURE.  The census's mechanical column
gives it `AM (Option …)` because every twin of a term-touching function is
monadic; this one touches no term — it matches on the members' CONSTRUCTORS
and moves their fields — so the monad would buy nothing and cost a `do` block
at every call.  The same judgement `Arena/ExprOps.lean` makes for
`exprPtrBEq`.
-/
import ConRon.Arena.CheckerBase

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:78-101 InductiveShape
The pieces of a recognised direct sum block, over handles. -/
structure InductiveShape where
  /-- the type former -/
  cvT : IConstantVal
  /-- the constructors in declaration order, each with its field count -/
  ctors : List (IConstantVal × Nat)
  /-- parameter count -/
  nP : Nat
  /-- index count (`0` at a plain sum) -/
  nIdx : Nat
  /-- the recursor -/
  cvR : IConstantVal
  /-- the recursor's fresh elimination level parameter (`large` only) -/
  elim : NIdx
  /-- the result sort -/
  resSort : LIdx
  /-- the rules' right-hand sides as exported, in constructor order -/
  rhss : List EIdx
  /-- large eliminator (a fresh elimination level parameter in front) -/
  large : Bool
  /-- the result sort is provably `Prop` -/
  isProp : Bool
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:103-110 sumSplit — the
block's members after the type former: the constructors, then the closing
recursor.  Pure; see the module note. -/
def sumSplit : List IConstantInfo →
    Option (List (IConstantVal × Nat × Nat) × IConstantVal × Nat × Nat × List IRecRule)
  | [.recInfo cvR mI rP rules] => some ([], cvR, mI, rP, rules)
  | .ctorInfo cvC nP nF :: rest =>
    (sumSplit rest).map fun q => ((cvC, nP, nF) :: q.1, q.2)
  | _ => none

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:112-119 InductiveShape.withSort
The record completed with the former's result sort (task #195); `isProp` is
recomputed so that the recogniser's invariant holds by definition. -/
def InductiveShape.withSort (p : InductiveShape) (s : LIdx) : AM InductiveShape := do
  let z ← zeroLevel
  pure { p with resSort := s, isProp := (← lvlEq? s z) == some true }

end ConRon.Arena
