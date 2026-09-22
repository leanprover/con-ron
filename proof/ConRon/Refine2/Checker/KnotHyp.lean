/-
# `ConRon.Refine2.Checker.KnotHyp` — `KnotRel`, the Core tier's obligation as this tier's hypothesis

**Task #97-P5-Checker** (DESIGN.md §8.2, Theorem 2).  The declaration-checker
tier does not prove anything about `arena::core`; it CONSUMES it, at exactly
six entry points and at exactly one fuel (`checkFuel`).  Task #97-P5-1 §8
names the shape:

> **The knot's lane dispatch.**  `arena::core`'s six bodies are tied at fuel by
> a dispatcher that takes the lane as a scalar, where the twin's `coreKnot`
> builds a `CoreFnsA` **record** of six closures.  §3.4 forbids closures on the
> Rust side, so the refinement's shape is finding 6's again one level up: a
> relation `KnotRel (fuel) (rec : CoreFnsA)` saying "each field of the twin's
> record is what the port's dispatcher does at that lane", established once by
> induction on the fuel and consumed field-wise at every call site.

`KnotRel` here is that relation **at the checker's own six front doors** —
`annotate_core`, `infer_type_core`, `is_def_eq_core`, `ensure_sort_core`,
`whnf` and `whnf_core`, which are `coreKnot`'s six slots wrapped in their
fuelled entries.  It is stated as a conjunction of six `Sim`s rather than
against `CoreFnsA` directly because that is the form every lemma of this tier
uses: a checker body never holds the record, it calls `annotateCore mode fe
checkFuel d e` by name (`Arena/CheckerBase.lean`'s module note 2 — *"the
record is the statement subject P3 needs, and the bodies call
`Arena/Core.lean`'s entries by name"* — sixty-two statements of this tier
carry `KnotRel checkFuel`, and not one of them holds the record).

**This is a HYPOTHESIS of this tier and a THEOREM of P5-Core's.**  Until the
two branches merge, every lemma below the `Core` seam carries `KnotRel
checkFuel`; when `Refine2/Core/**` lands its `knot_rel : ∀ f, KnotRel f`, the
hypothesis is discharged at the tier's top and disappears from every
statement at once.  Nothing else about `arena::core` is assumed anywhere in
`Refine2/Checker/**` or `Refine2/Promote/**`.

**Finding 10's `hvis` is inside `KnotRel`, not outside it.**  The port's core
entries take `vis : u64` beside `fe` (task #97-P6-6b took the visibility
counter out of the record's read path), so each clause quantifies over `vis`
and demands `absU vis = lf.visibleBelow` — the same hypothesis the rest of the
tier carries, stated once here rather than six times at every call site.
-/
import ConRon.Refine2.Checker.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- **The Core tier's six entry points, at one fuel.**  `KnotRel F` says: for
every related state, related environment and matching visibility counter, the
port's fuelled entry at `F` refines the twin's.  `P5-Core` proves
`∀ F, KnotRel F` by induction on `F`; every lemma of the checker tier takes
`KnotRel checkFuel` and consumes one clause of it. -/
structure KnotRel (F : Nat) : Prop where
  annotate : ∀ {pers st lst vis rf lf mode F' depth e o},
    AStateRel pers st lst → AStateInv pers st →
    IFEnvRel rf lf → IFEnvInv rf → absU vis = lf.visibleBelow →
    absU (F' : Std.U64) = F →
    arena.core.annotate_core pers vis st mode rf F' depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (annotateCore (ConRon.Refine.absMode mode) lf F (absU depth) (absEIdx e))
  inferType : ∀ {pers st lst vis rf lf mode F' depth e o},
    AStateRel pers st lst → AStateInv pers st →
    IFEnvRel rf lf → IFEnvInv rf → absU vis = lf.visibleBelow →
    absU (F' : Std.U64) = F →
    arena.core.infer_type_core pers vis st mode rf F' depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (inferTypeCore (ConRon.Refine.absMode mode) lf F (absU depth) (absEIdx e))
  isDefEq : ∀ {pers st lst vis rf lf mode F' depth a b o},
    AStateRel pers st lst → AStateInv pers st →
    IFEnvRel rf lf → IFEnvInv rf → absU vis = lf.visibleBelow →
    absU (F' : Std.U64) = F →
    arena.core.is_def_eq_core pers vis st mode rf F' depth a b = ok o →
    Sim id (fun _ => True) pers lst o
      (isDefEqCore (ConRon.Refine.absMode mode) lf F (absU depth) (absEIdx a)
        (absEIdx b))
  ensureSort : ∀ {pers st lst vis rf lf mode F' depth e o},
    AStateRel pers st lst → AStateInv pers st →
    IFEnvRel rf lf → IFEnvInv rf → absU vis = lf.visibleBelow →
    absU (F' : Std.U64) = F →
    arena.core.ensure_sort_core pers vis st mode rf F' depth e = ok o →
    Sim absLIdx (fun _ => True) pers lst o
      (ensureSortCore (ConRon.Refine.absMode mode) lf F (absU depth) (absEIdx e))
  whnf : ∀ {pers st lst vis rf lf mode F' depth e o},
    AStateRel pers st lst → AStateInv pers st →
    IFEnvRel rf lf → IFEnvInv rf → absU vis = lf.visibleBelow →
    absU (F' : Std.U64) = F →
    arena.core.whnf pers vis st mode rf F' depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (ConRon.Arena.whnf (ConRon.Refine.absMode mode) lf F (absU depth)
        (absEIdx e))
  whnfCore : ∀ {pers st lst vis rf lf mode F' depth e o},
    AStateRel pers st lst → AStateInv pers st →
    IFEnvRel rf lf → IFEnvInv rf → absU vis = lf.visibleBelow →
    absU (F' : Std.U64) = F →
    arena.core.whnf_core pers vis st mode rf F' depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (whnfCore (ConRon.Refine.absMode mode) lf F (absU depth) (absEIdx e))

end ConRon.Refine2
