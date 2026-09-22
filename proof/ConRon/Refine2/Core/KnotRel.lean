/-
# `ConRon.Refine2.Core.KnotRel` — the knot tied, once, at a fuel

**Task #97-P5-Core, the relation task #97-P5-1 asked to be written before any
`core` lemma is stated.**  DESIGN §8.4 gives (B) a knot that is a RECORD of
six closures (`CoreFnsA`) and §3.4 forbids the port a closure at all, so
`arena::core`'s six entry points take **the lane as a `u32` scalar** and
dispatch on it:

| port | twin |
|---|---|
| `knot_whnf_core … lane fuel …` | `(<lane's knot> f).whnfCore` |
| `knot_whnf`, `knot_infer`, `knot_infer_io`, `knot_defeq`, `knot_annotate` | the record's other five slots |
| `LANE_FULL` (`0`) | `Core.lean`'s `coreKnot mode fe id` |
| `LANE_GATED` (`1`) | `CoreGated.lean`'s `coreKnotGated mode fe` |
| `LANE_IO` (`2`) | `CoreIO.lean`'s `coreKnotIO mode fe` |
| `knot_infer_at … io …` | `CoreFnsA.ioView` applied or not — **the port's
  `io : bool` IS the `ioView` substitution** (its own doc comment says so) |

`laneKnot` and `laneKnotAt` are that table as functions, and `KnotRel f` is
*"at fuel `f`, each of the six port entries refines the corresponding slot of
the lane's twin knot"* — one relation, established once by induction on the
fuel (`Core/Induction.lean`) and consumed FIELD-WISE at every call site inside
a body (`hknot.whnf`, `hknot.defeq`, …), exactly as task #97s round 2's rule 8
found the record of knot hypotheses costs nothing.

## Why a structure and not six lemmas

The six are mutually recursive through the bodies, so they are established
together or not at all; and a body arm wants to name one of them
(`hknot.infer`) in a `grind` list without dragging the other five's
instantiations in.  A structure gives both.  `BodyRel f` is its partner —
*"the six BODIES at fuel `f` refine the twin's bodies tied to the lane's knot
at `f`"* — and the two compose:

    BodyRel f → KnotRel (f + 1)        `Core/Induction.lean`'s `knotRel_succ`
    KnotRel f → BodyRel f              `Core/Arms/*`, the tier's real work

## The three ambient arguments

Every port function of this tier carries `pers : &PersTier`, `vis : u64` and
`fe : &IFEnv` where the twin carries one `IFEnv`.  `CoreCtx` bundles the two
clauses that says so: task #97-P6-6b split `visible_below` OUT of the index
so that a phase-B worker copies no environment, and the twin never did, so
the port's scalar has to be tied back to the field it was split from.
-/
import ConRon.Refine2.Core.Probes
import ConRon.Refine2.ExprOps.Read
import ConRon.Arena.CoreIO
import ConRon.Arena.CoreGated

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (EResolves)

/-! ## The lane, as the twin knot it stands for -/

/-- **The twin knot a port lane stands for.**  `LANE_GATED` is the P knot,
`LANE_IO` the leaf knot, anything else (`LANE_FULL`, which is `0`) the
memoized full knot — the port's own `else` arm, so the reading is the code's
and not a case analysis the refinement invents. -/
def laneKnot (mode : ConLeche.CheckMode) (fe : IFEnv) (lane : Std.U32)
    (f : Nat) : CoreFnsA :=
  if lane = arena.core.LANE_GATED then coreKnotGated mode fe f
  else if lane = arena.core.LANE_IO then coreKnotIO mode fe f
  else coreKnot mode fe id f

/-- **The record an `io`-flagged body call resolves `r.infer` through.**
`arena::core::knot_infer_at`'s own doc comment: *"This function IS the
`ioView` substitution in the port — the knot is plain functions, so there is
no record whose `infer` field can be rebound."* -/
def laneKnotAt (mode : ConLeche.CheckMode) (fe : IFEnv) (lane : Std.U32)
    (io : Bool) (f : Nat) : CoreFnsA :=
  if io then (laneKnot mode fe lane f).ioView else laneKnot mode fe lane f

@[simp] theorem laneKnot_gated (mode fe f) :
    laneKnot mode fe arena.core.LANE_GATED f = coreKnotGated mode fe f := by
  rw [laneKnot, if_pos rfl]

@[simp] theorem laneKnot_io (mode fe f) :
    laneKnot mode fe arena.core.LANE_IO f = coreKnotIO mode fe f := by
  rw [laneKnot, if_neg (by rw [arena.core.LANE_IO, arena.core.LANE_GATED]; decide),
    if_pos rfl]

@[simp] theorem laneKnot_full (mode fe f) :
    laneKnot mode fe arena.core.LANE_FULL f = coreKnot mode fe id f := by
  rw [laneKnot,
    if_neg (by rw [arena.core.LANE_FULL, arena.core.LANE_GATED]; decide),
    if_neg (by rw [arena.core.LANE_FULL, arena.core.LANE_IO]; decide)]

@[simp] theorem laneKnotAt_true (mode fe lane f) :
    laneKnotAt mode fe lane true f = (laneKnot mode fe lane f).ioView := by
  rw [laneKnotAt, if_pos rfl]

@[simp] theorem laneKnotAt_false (mode fe lane f) :
    laneKnotAt mode fe lane false f = laneKnot mode fe lane f := by
  rw [laneKnotAt, if_neg (by decide)]

/-- The port's lane is NOT `LANE_GATED` and NOT `LANE_IO` exactly when the
twin's knot is the full one — the reading every `else` arm of the six entries
takes. -/
theorem laneKnot_of_ne (mode fe f) {lane : Std.U32}
    (hg : ¬ lane = arena.core.LANE_GATED) (hi : ¬ lane = arena.core.LANE_IO) :
    laneKnot mode fe lane f = coreKnot mode fe id f := by
  rw [laneKnot, if_neg hg, if_neg hi]

/-! ## The ambient arguments

`pers` needs no clause of its own — `AStateRel pers st lst` already ties the
persistent tier to the twin's single store (`Refine2/AbsStore.lean`'s
`absStore`).  What is left is the environment and the visibility scalar. -/

/-- The port's `(vis, fe)` against the twin's one `IFEnv`. -/
structure CoreCtx (vis : Std.U64) (fe : arena.env.IFEnv) (lfe : IFEnv) : Prop where
  /-- The indexed environment, field for field (`Refine2/AbsState.lean`). -/
  fenv : IFEnvRel fe lfe
  /-- Task #97-P6-6b's split scalar, tied back to the field it came from. -/
  vis : absU vis = lfe.visibleBelow

/-! ## The two relations -/

/-- **`KnotRel f`** — at fuel `f`, each of `arena::core`'s six knot entries
refines the corresponding slot of the lane's twin knot.  Established once by
`Core/Induction.lean`'s fuel induction, consumed field-wise everywhere else.

`knot_infer_at` is not a field: it is `if io then knot_infer_io else
knot_infer` and `Core/Induction.lean`'s `KnotRel.inferAt` derives it. -/
structure KnotRel (f : Nat) : Prop where
  whnfCore : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) →
    (lane = arena.core.LANE_GATED → 1 ≤ f) → absU fu = f →
    arena.core.knot_whnf_core pers vis st mode lane fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).whnfCore
        (absU depth) (absEIdx e))
  /-- **The gated lane's fuel-0 arm, and nothing above it** (task
  #97-P5-Arms, after task #97-P3-CoreWalks' twin fix).  The port tests
  `fuel = 0` FIRST and raises `Internal` there whatever the tag is; the twin's
  `coreKnotGated 0` now answers `pure e` at a stuck tag, so the two agree at
  every fuel EXCEPT zero, and the side condition is exactly that exclusion.

  Before the twin fix this field carried `2 ≤ f` — the twin ran
  `whnfBody (coreKnotGated … (f - 1))` whose first move is `r.whnfCore`, so at
  `f = 1` it threw where the port answered `Ok e`.  Hoisting the tag test into
  `coreKnotGated`'s two reduction slots removed that level and moved the
  disagreement down to `f = 0`, where BOTH reduction fields now need it —
  `whnfCore` did not before.  **A second one-line twin change removes it
  entirely**: hoist the test in the `| fuel + 1 =>` branch ONLY, leaving
  `coreKnotGated 0`'s slots the unconditional `fail` the port's `fuel = 0` arm
  is.  Vacuous at `checkFuel` either way. -/
  whnf : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) →
    (lane = arena.core.LANE_GATED → 1 ≤ f) → absU fu = f →
    arena.core.knot_whnf pers vis st mode lane fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).whnf
        (absU depth) (absEIdx e))
  infer : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
    arena.core.knot_infer pers vis st mode lane fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).infer
        (absU depth) (absEIdx e))
  inferIO : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
    arena.core.knot_infer_io pers vis st mode lane fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).inferIO
        (absU depth) (absEIdx e))
  defeq : ∀ {pers vis st mode lane fu fe lfe depth a b lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx a) → EResolves lst (absEIdx b) →
    absU fu = f →
    arena.core.knot_defeq pers vis st mode lane fu fe depth a b = ok o →
    Sim id (fun _ => True) pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).defeq
        (absU depth) (absEIdx a) (absEIdx b))
  annotate : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
    arena.core.knot_annotate pers vis st mode lane fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).annotate
        (absU depth) (absEIdx e))

/-- **`knot_infer_at`, derived.**  `if io then knot_infer_io else knot_infer`
against `(laneKnotAt … io f).infer`, which is `r.inferIO` under the io view
and `r.infer` without it — the two halves of `CoreFnsA.ioView` by iota. -/
theorem KnotRel.inferAt {f : Nat} (h : KnotRel f)
    {pers vis st mode lane io fu fe lfe depth e lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hrun : arena.core.knot_infer_at pers vis st mode lane io fu fe depth e
      = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      ((laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f).infer
        (absU depth) (absEIdx e)) := by
  rw [arena.core.knot_infer_at] at hrun
  cases io with
  | true =>
    rw [if_pos rfl] at hrun
    rw [laneKnotAt_true]
    exact h.inferIO hrel hinv hctx hwf hres hf hrun
  | false =>
    rw [if_neg (by decide)] at hrun
    rw [laneKnotAt_false]
    exact h.infer hrel hinv hctx hwf hres hf hrun

/-- **`BodyRel f`** — the six bodies at fuel `f`, against the twin's bodies
tied to the lane's knot at `f`.  This is what `Core/Arms/*` owes and what
`knotRel_succ` consumes; the port's body carries the same `lane` it was called
at, and its own recursive `knot_*` calls are at the SAME fuel, which is why
`KnotRel f → BodyRel f` is the induction step's premise and not its
conclusion.

`whnfCoreGated` is a seventh field because the gated lane's `whnfCore` slot is
a different body (`arena::core_gated::whnf_core_body_gated`); the other five
slots of `coreKnotGated` are the same bodies at the gated knot. -/
structure BodyRel (f : Nat) : Prop where
  /-- **The gated lane has NO tag test in the twin, and the port tests the tag
  at EVERY lane.**  `knot_whnf_core` answers `Ok(e.dup2())` off
  `whnf_core_stuck_tag` *before* it looks at the lane, where
  `coreKnotGated`'s `whnfCore` slot is `whnfCoreBodyGated … d e` with no such
  test.  The two agree because the body's first clause is `pure e` at exactly
  those six views — which is what `whnfCoreStuckTag`'s own doc comment states
  as its obligation — and getting from the TAG to the VIEW is task #97-P5-0's
  finding 3, hence the two `StoreWF` / `EResolves` hypotheses. -/
  stuckGatedCore : ∀ {mode lfe h d lst},
    StoreWF lst.store → EResolves lst h → whnfCoreStuckTag h = true →
    ∀ (r : CoreFnsA), (whnfCoreBodyGated mode r lfe d h).run lst = .ok (h, lst)
  /-- The same one rung up, and this one **needs the fuel**: the twin's
  `whnfBody` runs `r.whnfCore` before it can return, so at `f = 0` — the
  port's `fuel = 1` — the twin throws `internal` where the port answers
  `Ok e`.  That is a REAL divergence, confined to one fuel level and named in
  the task's report; above it the chain is `whnfCore`'s identity, then
  `reduceNat = none` and `unfoldDefinition = none`, which are the two extra
  obligations `whnfStuckTag`'s doc comment names. -/
  stuckGatedWhnf : ∀ {mode lfe h d lst},
    StoreWF lst.store → EResolves lst h → whnfStuckTag h = true → 1 ≤ f →
    (whnfBody (coreKnotGated mode lfe f) lfe d h).run lst = .ok (h, lst)
  whnfCore : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
    arena.core.whnf_core_body pers vis st mode lane fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (whnfCoreBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))
  whnfCoreGated : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
    arena.core_gated.whnf_core_body_gated pers vis st mode lane fu fe depth e
      = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (whnfCoreBodyGated (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))
  whnf : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
    arena.core.whnf_body pers vis st mode lane fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (whnfBody (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))
  infer : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
    arena.core.infer_body pers vis st mode lane fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (inferBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))
  inferIO : ∀ {pers vis st mode lane io fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
    arena.core.infer_body_io pers vis st mode lane io fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (inferBodyIO (ConRon.Refine.absMode mode)
        (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe
        (absU depth) (absEIdx e))
  defeq : ∀ {pers vis st mode lane fu fe lfe depth a b lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx a) → EResolves lst (absEIdx b) →
    absU fu = f →
    arena.core.defeq_body pers vis st mode lane fu fe depth a b = ok o →
    Sim id (fun _ => True) pers lst o
      (defeqBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx a) (absEIdx b))
  annotate : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    StoreWF lst.store → EResolves lst (absEIdx e) → absU fu = f →
    arena.core.annotate_body pers vis st mode lane fu fe depth e = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (annotateBody (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))

end ConRon.Refine2
