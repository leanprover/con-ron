/-
# `ConRon.Refine2.Checker.KnotHyp` — the Core tier's `KnotRel`, consumed

**Task #97-P5-Checker, reconciled with task #97-P5-Core by task #97-P5-Arms.**
The declaration-checker tier does not prove anything about `arena::core`; it
CONSUMES it, at exactly seven entry points and at exactly one fuel
(`checkFuel`).  Task #97-P5-1 §8 names the shape:

> **The knot's lane dispatch.**  `arena::core`'s six bodies are tied at fuel by
> a dispatcher that takes the lane as a scalar, where the twin's `coreKnot`
> builds a `CoreFnsA` **record** of six closures.  §3.4 forbids closures on the
> Rust side, so the refinement's shape is finding 6's again one level up: a
> relation `KnotRel (fuel) (rec : CoreFnsA)` saying "each field of the twin's
> record is what the port's dispatcher does at that lane", established once by
> induction on the fuel and consumed field-wise at every call site.

## What this file used to be, and why it is not that any more

It declared its own `structure KnotRel (F : Nat)` — six clauses about the
checker's own front doors (`annotate_core`, `infer_type_core`,
`is_def_eq_core`, `ensure_sort_core`, `whnf`, `whnf_core`) — as a HYPOTHESIS,
with its module note saying *"when `Refine2/Core/**` lands its
`knot_rel : ∀ f, KnotRel f`, the hypothesis is discharged at the tier's top"*.

`Refine2/Core/**` landed (task #97-P5-Core) with a `structure KnotRel (f : Nat)`
of its own, in the SAME namespace — about the six `knot_*` dispatchers at a
lane, which is the relation the fuel induction is actually run on.  The two
names collided the moment both tiers were imported by
`proof/ConRon/Refine2.lean`, and `lake build ConRonRefine2` stopped importing
at all (`environment already contains 'ConRon.Refine2.KnotRel.whnfCore'`).
`scripts/gates.sh` does not build `ConRonRefine2` — it is deliberately not a
default target — so the collision survived two merges unnoticed.

**The reconciliation is the one this file predicted**: the structure goes and
the Core tier's is used.  `KnotRel` below is
`Refine2/Core/KnotRel.lean`'s, the six clauses this tier used to declare are
`Refine2/Core/Entries.lean`'s six theorems plus
`Refine2/Core/Arms/Sort.lean`'s seventh, and `∀ f, KnotRel f` is
`Refine2/Core/Arms.lean`'s `knotRel`.  Nothing in `Refine2/Checker/**` or
`Refine2/Promote/**` projected a field of the old structure — every statement
only CARRIES `KnotRel checkFuel` — so the change is this file and nothing else.

## The seven entries, and what each of them additionally needs

| the old field | what it is now |
|---|---|
| `annotate` | `Refine2/Core/Entries.lean`'s `annotate_core_refines` |
| `inferType` | `infer_type_core_refines` (and `infer_type_io_refines` beside it, which the old structure had no field for) |
| `isDefEq` | `is_def_eq_core_refines` |
| `whnf` | `whnf_refines` |
| `whnfCore` | `whnf_core_refines` |
| `ensureSort` | `Refine2/Core/Arms/Sort.lean`'s `ensure_sort_core_refines` |

Three differences are worth naming, because a checker-tier proof meets them at
the call site rather than here:

1. **`StoreWF lst.store` and `EResolves lst h`.**  The Core entries carry task
   #97-P5-0's finding 3 — the tag-first / view-first split is only sound on a
   store that resolves the handle — where the old structure's clauses carried
   neither.  It is the pair P3 owes as a clause of `StateOK`
   (`Refine2/Core/KnotRel.lean` §3), and every checker body that calls a core
   entry will need it in scope.
2. **`CoreCtx vis fe lfe` replaces `IFEnvRel rf lf ∧ absU vis = lf.visibleBelow`.**
   The same two facts, bundled; `IFEnvInv rf`, which the old clauses also
   demanded, is not needed by the Core entries at all.
3. **`AnswerResolves` at `ensure_sort_core`** (task #97-P5-Arms' finding 14):
   it dispatches on the tag of `knot_whnf`'s own answer, which no hypothesis
   of `KnotRel` mentions.
-/
import ConRon.Refine2.Checker.Shape
import ConRon.Refine2.Core.Arms

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- **The knot at the checker's own fuel, unconditionally.**  `checkFuel` is
`Arena.checkFuel = 100000`, and `Refine2/Core/Arms.lean`'s `knotRel` gives
`KnotRel` at every fuel — so the hypothesis the sixty-two statements of this
tier carry is discharged here, once, and `#print axioms` on it reports the
`sorryAx` that `bodyRel_of_knot` still stands on. -/
theorem knotRel_checkFuel' : KnotRel Arena.checkFuel := knotRel _

/-! ## `CoreCtx`, from the checker tier's own three facts

**Task #97-P5-Checker-2, at task #97-P5-Core-2's request.**  Every Core entry
takes `CoreCtx vis fe lfe`, and every checker-tier statement carries
`IFEnvRel rf lf`, `IFEnvInv rf` and — at the sites where the port splits the
counter out of the record (finding 10) — `absU vis = lf.visibleBelow`.  This
is the one line that turns the three into the fourth.

`Refine2/Core/KnotRel.lean` asked for exactly this: its `idxInv` and `idxPos`
clauses say *"both belong to `IFEnvInv` and P3 supplies them; they are spelled
here because the Core tier may not edit that file"*.  They are in `IFEnvInv`
now (`Refine2/Checker/Shape.lean`), and `idxPos` is an INVARIANT rather than a
platform assumption — that file's note walks the four write sites. -/

/-- The Core tier's ambient argument, built from the checker tier's own. -/
theorem IFEnvInv.coreCtx {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) : CoreCtx vis rf lf :=
  ⟨hfe, hvis, hfinv.idxInv, hfinv.idxPos⟩

/-- The same where the counter is the record's own field, which is every site
that does not thread finding 10's scalar: `IFEnvRel.visibleBelow` IS the
equation. -/
theorem IFEnvInv.coreCtxSelf {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) :
    CoreCtx rf.visible_below rf lf :=
  IFEnvInv.coreCtx hfe hfinv hfe.visibleBelow.symm

/-! ## The axiom census

`knotRel_checkFuel'` reads `sorryAx` through `bodyRel_of_knot`, exactly as
task #97-P5-Arms §7 records; `IFEnvInv.coreCtx` is this file's own and reads
nothing. -/

/-- info: 'ConRon.Refine2.IFEnvInv.coreCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IFEnvInv.coreCtx

end ConRon.Refine2
