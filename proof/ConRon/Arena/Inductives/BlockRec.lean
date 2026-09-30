/-
# `ConRon.Arena.Inductives.BlockRec` — the recursor stage's shared pieces
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/BlockRec.lean` over handles, as far as the
executed checker reads it: the elimination guard, official's
`elim_only_at_universe_zero` said declaratively.  The Rust twin is
`arena::inductives::block_rec`.

**The deviation**: the result sort is a handle, so `isNeverZero` reads it
first (`readLevelM`) and the guard is an `AM` function; the cited `||`
short-circuits after that read, which is the only part that touches the
store.
-/
import ConRon.Arena.Inductives.BlockParts

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/BlockRec.lean:50-84 blockLargeElimAllowed
**When a large eliminator is allowed**: always when the block's sort is never
`0`; otherwise only for ONE member with no container occurrence and at most one
constructor, at the large shape. -/
def blockLargeElimAllowed (p : BlockShape) (nested : Bool) : AM Bool := do
  let l ← readLevelM p.resSort
  if Level.isNeverZero l then pure true
  else
    let n := p.numCtors
    if nested then pure false
    else pure (p.large && p.k == 1 && (n == 0 || n == 1))

end ConRon.Arena
