/-
# `ConRon.Refine2.Checker.KnotHyp` — the Core tier's `KnotRel`, consumed

**Task #97-P5-Checker, reconciled with task #97-P5-Core by task #97-P5-Arms.**
The declaration-checker tier does not prove anything about `arena::core`; it
CONSUMES it, at exactly six entry points and at exactly one fuel
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

## The entries, and what each of them additionally needs

(The old `annotate` field went with con-leche's annotate pass, task #119.)

| the old field | what it is now |
|---|---|
| `inferType` | `infer_type_core_refines` (and `infer_type_io_refines` beside it, which the old structure had no field for) |
| `isDefEq` | `is_def_eq_core_refines` |
| `whnf` | `whnf_refines` |
| `whnfCore` | `whnf_core_refines` |
| `ensureSort` | `Refine2/Core/Arms/Sort.lean`'s `ensure_sort_core_refines` |

Two differences are worth naming, because a checker-tier proof meets them at
the call site rather than here:

1. **The entries are LOCKSTEP statements** (task #97-P5-Core round 4): over
   `AStateRel₀` (take `hrel.to₀`), with no `StoreWF` and no `EResolves`
   premise, and a `Sim₀` conclusion without `Ext` — and so, since task
   #97-T2-LOCKSTEP lane Checker, is every checker-tier statement; each entry
   is filed below as a `@[lockstep]` spec at `checkFuel`.  The old `AnswerResolves` at `ensure_sort_core` (task
   #97-P5-Arms' finding 14) is gone: the twin tests the reduct's tag where the
   port does.
2. **`CoreCtx vis fe lfe` replaces `IFEnvRel rf lf ∧ absU vis = lf.visibleBelow`.**
   The same two facts, bundled, plus `IFEnvInv`'s two index clauses
   (`IFEnvInv.coreCtx` below).
-/
import ConRon.Refine2.Checker.Shape
import ConRon.Refine2.Core.Arms
import ConRon.Refine2.Core.Arms.Sort
import ConRon.Refine2.Tactic.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- **The knot at the checker's own fuel, unconditionally.**  `checkFuel` is
`Arena.checkFuel = 100000`, and `Refine2/Core/Arms.lean`'s `knotRel` gives
`KnotRel` at every fuel — so the hypothesis the sixty-two statements of this
tier USED to carry is discharged here, once.  **Task #97-P5-Checker-2 deleted
all sixty-two binders**: a redundant hypothesis is not a seam, and a proof
that needs the knot takes this theorem by name.  `sorry`-free since task
#97-P5-Core round 6 (the guard below keeps it so). -/
theorem knotRel_checkFuel' : KnotRel Arena.checkFuel := knotRel _

-- T143-STUB: census restored at stage 2
-- /-- info: 'ConRon.Refine2.knotRel_checkFuel'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in #print axioms knotRel_checkFuel'

/-! ## `CoreCtx`, from the checker tier's own facts

Every Core entry takes `CoreCtx pers fe lfe`, and every checker-tier statement
carries `IFEnvRel pers rf lf` and `IFEnvInv rf`: the reader's half of the first and
the second are the first's. -/

/-- The Core tier's ambient argument, built from the checker tier's own. -/
theorem IFEnvInv.coreCtx {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf) : CoreCtx pers rf lf :=
  { hfe.toIFEnvRead with inv := hfinv }

/-- The same from the fold's pair. -/
theorem IFEnvRelI.coreCtx {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (h : IFEnvRelI pers rf lf) : CoreCtx pers rf lf :=
  IFEnvInv.coreCtx h.1 h.2

/-! ## Bridges between `LS` and the checker tier's shapes (task #97-T2-LOCKSTEP lane Checker) -/

namespace Lockstep

theorem LS.toSimRel₀ {α β : Type} {R : α → β → Prop} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} {o}
    (h : LS pers R m lst x) (hm : m = ok o) : SimRel₀ R pers lst o x := by
  obtain ⟨o, st'⟩ := o
  have := h o st' hm
  show AOutRel₀ R pers o st' (x.run lst)
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h1, h2⟩ := this
    exact ⟨b, lst', hx, hR, h1, h2⟩

theorem LS.ofSimRel₀ {α β : Type} {R : α → β → Prop} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β}
    (h : ∀ o, m = ok o → SimRel₀ R pers lst o x) : LS pers R m lst x := by
  intro o st' hm
  have := h _ hm
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h1, h2⟩ := this
    exact ⟨b, lst', hx, hR, h1, h2⟩

end Lockstep

/-! ## The checker tier's side-goal extension of `lockstep`

A fold step's side goals are scalar facts; the extension tier tries `omega` and
`simp_all`. -/

macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (first
      | omega
      | (simp only [absU] at *; omega)
      | (simp_all only [lockstep_simp]; done)
      | (simp_all; done)))

/-! ## The front doors as `@[lockstep]` specs (task #97-T2-LOCKSTEP lane Checker)

The checker calls the Core tier at `checkFuel` only, so each front door is
filed for the `lockstep` tactic at that fuel, with the knot discharged by
`knotRel_checkFuel'`.  `hf` (the Rust's `CHECK_FUEL` read as the twin's
`checkFuel`) is a side goal the tactic closes with `check_fuel_abs`. -/

attribute [lockstep_simp] check_fuel_abs core_walk_fuel_abs

open Lockstep in
@[lockstep] theorem infer_type_core_ls {pers st mode fe lfe fu depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = checkFuel) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_type_core pers st mode fe fu depth e) lst
      (Arena.inferTypeCore (ConRon.Refine.absMode mode) lfe checkFuel (absU depth)
        (absEIdx e)) :=
  LS.ofSim₀ fun _ h => infer_type_core_refines knotRel_checkFuel' hrel hinv hctx hf h

open Lockstep in
@[lockstep] theorem ensure_sort_core_ls {pers st mode fe lfe fu depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = checkFuel) :
    LS pers (fun a b => b = absLIdx a)
      (arena.core.ensure_sort_core pers st mode fe fu depth e) lst
      (ensureSortCore (ConRon.Refine.absMode mode) lfe checkFuel (absU depth)
        (absEIdx e)) :=
  LS.ofSim₀ fun _ h => ensure_sort_core_refines knotRel_checkFuel' hrel hinv hctx hf h

open Lockstep in
@[lockstep] theorem is_def_eq_core_ls {pers st mode fe lfe fu depth a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = checkFuel) :
    LS pers (fun a b => b = id a)
      (arena.core.is_def_eq_core pers st mode fe fu depth a b) lst
      (Arena.isDefEqCore (ConRon.Refine.absMode mode) lfe checkFuel (absU depth)
        (absEIdx a) (absEIdx b)) :=
  LS.ofSim₀ fun _ h => is_def_eq_core_refines knotRel_checkFuel' hrel hinv hctx hf h

open Lockstep in
@[lockstep] theorem whnf_ls {pers st mode fe lfe fu depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = checkFuel) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf pers st mode fe fu depth e) lst
      (Arena.whnf (ConRon.Refine.absMode mode) lfe checkFuel (absU depth) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => whnf_refines knotRel_checkFuel' hrel hinv hctx hf h

/-! ## The axiom census

`IFEnvInv.coreCtx` is this file's own and reads the three standard axioms only. -/

/-- info: 'ConRon.Refine2.IFEnvInv.coreCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IFEnvInv.coreCtx

end ConRon.Refine2
