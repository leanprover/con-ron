/-
# `ConRon.Arena.CheckerGated` — the gated `CheckerOps` instantiations

The twin of `ConLeche/Kernel/CheckerGated.lean`: `fueledOps`/`pureOps` over
the GATED knot (`Arena/CoreGated.lean`), which is `ConLeche/Kernel/CoreGated.lean`'s
verification-tier variant of the six bodies.

Census class **(S)** on both rows — "the Rust port skips it", and (B) could
skip it for the same reason it skips a second knot: what the binary runs is
the one memoized instantiation of `Arena/CheckerBase.lean`.  They are twinned
anyway, for the reason task #97c gives for twinning `CoreIO.lean` and
`CoreGated.lean`: they are the STATEMENT SUBJECTS P3 needs for the knot
equations, they cost fourteen lines between them, and having them now means
P3 does not have to invent an arena spelling for them later.
-/
import ConRon.Arena.Checker
import ConRon.Arena.CoreGated

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/CheckerGated.lean:27-37 fueledOpsGated — the
pure instantiation over the **gated** knot, at an arbitrary fuel;
`Arena/CheckerBase.lean`'s `fueledOpsA`, clause for clause. -/
def fueledOpsGated (mode : CheckMode) (F : Nat) : CheckerOpsA where
  annotate fe d e := annotateCoreGated mode fe F d e
  inferType fe d e := inferTypeCoreGated mode fe F d e
  isDefEq fe d a b := isDefEqCoreGated mode fe F d a b
  ensureSort fe d e := ensureSortCoreGated mode fe F d e
  whnf fe d e := whnfGated mode fe F d e
  orElse x k := fun s =>
    match x s with
    | .ok (true, s') => .ok ((), s')
    | .ok (false, s') => k none s'
    | .error _ => k none s

/-- con-leche: ConLeche/Kernel/CheckerGated.lean:39-40 pureOpsGated — the pure
gated instantiation at the standard fuel. -/
def pureOpsGated (mode : CheckMode) : CheckerOpsA := fueledOpsGated mode checkFuel

end ConRon.Arena
