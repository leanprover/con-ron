/-
# `ConRon.Bridge.Inductives.SumParts` — Theorem 1 for the block's shape record

`Arena/Inductives/SumParts.lean` is two declarations, and they are the two
extremes of the tier.

* **`sumSplit` is not in `AM` at all** (task #97d-2's one deviation in this
  module: it matches on the members' CONSTRUCTORS and moves their fields, so
  the monad would buy nothing).  Its statement is therefore a plain
  implication between two `Option`s and not a `PSpec`, and it is the only
  such statement in the tier.
* **`InductiveShape.withSort` reads the pin table and the level cache**, so it
  is a `PSpec` like everything else.

## Why `sumSplit`'s statement is two-sided

`checkIndDecl`'s dispatch is the RECOGNISER alone (task #219): a block
`sumSplit` refuses goes to the modeled route and a block it accepts goes to
the fixpoint route.  So a twin that answered `none` where con-leche answers
`some` would take the OTHER route, and Theorem 1 would be about a different
program.  `ROp` (`Bridge/Inductives/Rel.lean`) is that two-sidedness, and it
is why the tier's `Option` relation is not a one-sided implication.
-/
import ConRon.Bridge.Inductives.StructParts

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The member split -/

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:103-110 sumSplit — the
split's answer denotes: the constructors with their two counts, the recursor's
header, its two counts and its rules. -/
structure SplitRel
    (q : List (ConstantVal × Nat × Nat) × ConstantVal × Nat × Nat × List RecRule)
    (st : EStore)
    (r : List (IConstantVal × Nat × Nat) × IConstantVal × Nat × Nat × List IRecRule) :
    Prop where
  ctors : denoteCtors3 st r.1 = some q.1
  cvR : Frontend.denoteCV st r.2.1 = some q.2.1
  mI : r.2.2.1 = q.2.2.1
  rP : r.2.2.2.1 = q.2.2.2.1
  rules : Frontend.denoteRules st r.2.2.2.2 = some q.2.2.2.2

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:103-110 sumSplit — the
block's members after the type former.  **Two-sided** (`ROp`), because the
dispatch reads it.

`sorry`: a structural induction on the block with `Frontend.denoteCIList`
inverted at each constructor — `Bridge/Rel.lean`'s `denoteCI` inversions give
the `.ctorInfo` and `.recInfo` clauses, and the `_ => none` arm needs that a
denoting `IConstantInfo` has con-leche's constructor at the same tag, which is
`denoteCI`'s own case split. -/
theorem sumSplit_spec (st : EStore) (block : List IConstantInfo)
    (blockP : List ConstantInfo)
    (h : Frontend.denoteCIList st block = some blockP) :
    ROp SplitRel (ConLeche.sumSplit blockP) st (Arena.sumSplit block) := by
  sorry

/-! ## The record completed with the former's sort -/

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:112-119 InductiveShape.withSort
The record completed with the result sort the former's install stage measured;
`isProp` is recomputed so the recogniser's invariant holds by definition.

`sorry`: `Bridge/Specs.lean`'s `zeroLevel_spec` and `lvlEq?_spec` (both
closed) plus `ShapeRel.ext` for the nine fields that do not move.  The one
content step is that `lvlEq? s z = some true` iff `Level.isEquiv sP .zero =
some true`, which is `lvlEq?_spec` read at both signs. -/
theorem withSort_spec (p : Arena.InductiveShape) (q : ConLeche.InductiveShape)
    (s : LIdx) (sP : Level) :
    PSpec (fun st => ShapeRel st p q ∧ denoteL st.ls s = some sP)
      (Arena.InductiveShape.withSort p s)
      (RShape (ConLeche.InductiveShape.withSort q sP)) := by
  sorry

end ConRon.Bridge.Inductives
