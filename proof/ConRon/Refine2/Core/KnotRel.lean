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

## Lockstep statements (task #97-P5-Core round 4)

Both relations are stated over `AStateRel₀` — the port/twin relation WITHOUT
the twin's own `StoreWF` — with no `EResolves` premise on the argument and a
`Sim₀` conclusion (no `Ext`).  Round 3 found the older statements false for
`f ≥ 1`/`f ≥ 2`: a cache value that dangles (the caches are related KEY for
key and say nothing of the values' resolution) is answered by the knot's hit,
and the next step read its TAG in the port and its VIEW in the twin.  Round 4's
audit found that split at ≈ 60 sites of the knot and its `ExprOps` helpers and
made the twin test the tag first wherever the port does (`Arena/Core.lean`,
`Arena/CoreGated.lean`, `Arena/ExprOps.lean`); and the coordinator's ruling
(i) moved `StoreWF` (and `Ext`, a statement about denotation) out of the
relation into Theorem 1, because the port and the twin both intern over a
dangling child without looking at it and their stores stay equal field for
field — only the twin's DAG invariant fails there.  Nothing about resolution
is premised or concluded any more.

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

/-- The port's `(vis, fe)` against the twin's one `IFEnv`.

The last two clauses are the environment INDEX's own invariant and are the
answer to task #97-P5-Core §8's *"`IFEnvInv rf` is not needed at all"*: that
was true while no body was proved.  `unfold_definition` — the `whnf` loop's
delta leaf — reads `ifenv_find`, and a `ron::HashMap2` probe is a
specification of a WELL-FORMED table only (`Refine2/Checker/Shape.lean`'s
`IFEnvInv` says exactly `idxInv`), so the reader's lemma needs it.  Both
belong to `IFEnvInv` and P3 supplies them; they are spelled here because the
Core tier may not edit that file. -/
structure CoreCtx (vis : Std.U64) (fe : arena.env.IFEnv) (lfe : IFEnv) : Prop where
  /-- **The indexed environment's DATA, field for field**
  (`Refine2/AbsState.lean`) — `IFEnvRel` at the twin environment RESTRICTED to
  the port record's own counter, so that its third clause
  (`lfe.visibleBelow = absU fe.visible_below`) is discharged by the
  restriction and says nothing.  What the counter is, is the next clause's
  business and only the next clause's.

  **Why it is not the plain `IFEnvRel fe lfe`** (task #97-P5-Bracket's
  finding 3, repaired by task #97-P5-Checker round 3).  Paired with `vis`
  below, the plain relation forces `absU vis = absU fe.visible_below`: it says
  the twin's counter is the port record's field and `vis` says it is the split
  scalar, so `CoreCtx` was satisfiable only where the split scalar is NOT
  split.  `arena::checker::check_pending` is the one call site where it is —
  a pending record carries the `vis` its declaration was installed at, `fe` is
  the whole environment phase A ended with, and that difference is the entire
  point of phase B — so every Core entry, and every checker-tier statement
  above them, was unusable at exactly the place the campaign needs them.

  `IFEnv.restrictTo` touches `visibleBelow` alone, so `.env` and `.idx` of
  the restricted environment are `lfe`'s definitionally and every consumer of
  those two clauses is unchanged. -/
  fenv : IFEnvRel fe (lfe.restrictTo (absU fe.visible_below))
  /-- Task #97-P6-6b's split scalar: the twin environment this record stands
  for is viewed at `vis`, which need not be the port record's own field. -/
  vis : absU vis = lfe.visibleBelow
  /-- `Refine2/Checker/Shape.lean`'s `IFEnvInv`: the index is a well-formed
  `ron::HashMap2`, without which `HashMap2.get` specifies nothing. -/
  idxInv : ConRon.Refine.HashMap2.Inv
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable fe.idx
  /-- **Every position the index stores fits a `usize`.**  `IFEnv.idx`'s value
  is `(u64, u64)` and `ifenv_find` indexes `env.consts` with `pos as usize`,
  which Aeneas models as a TRUNCATING cast; on a 64-bit `usize` it is the
  identity, and in general it is the identity exactly here.  A stored position
  is a position in a `Vec`, so this is an invariant of the index and not an
  assumption about the platform — `IFEnvInv` should carry it, and
  `ifenv_find_abs` is the only consumer. -/
  idxPos : ∀ n p, ConRon.Refine.HashMap2.toFun fe.idx n = some p →
    p.2.val ≤ Std.Usize.max

/-- `fenv`'s constant-list clause, at `lfe` itself — `IFEnv.restrictTo` moves
`visibleBelow` alone, so the two are the same statement and this is the
spelling a reader of `lfe` wants. -/
theorem CoreCtx.env {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (h : CoreCtx vis fe lfe) : lfe.env = absIEnv fe.env := h.fenv.env

/-- `fenv`'s index clause, at `lfe` itself.  **This is the one `ifenv_find_abs`
consumes**, and it is stated here rather than projected through `fenv` because
the restriction in `fenv`'s type is not syntactically `lfe`. -/
theorem CoreCtx.idx {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (h : CoreCtx vis fe lfe) : ∀ n,
      ((ConRon.Refine.HashMap2.toFun fe.idx n).bind fun p =>
        (fe.env.consts.val[p.2.val]?).map fun ci => (absU p.1, absIConstantInfo ci))
      = lfe.idx[absNIdx n]? := h.fenv.idx

/-! ## The two relations -/

/-- **`KnotRel f`** — at fuel `f`, each of `arena::core`'s six knot entries
refines the corresponding slot of the lane's twin knot.  Established once by
`Core/Induction.lean`'s fuel induction, consumed field-wise everywhere else.

`knot_infer_at` is not a field: it is `if io then knot_infer_io else
knot_infer` and `Core/Induction.lean`'s `KnotRel.inferAt` derives it. -/
structure KnotRel (f : Nat) : Prop where
  whnfCore : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.knot_whnf_core pers vis st mode lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).whnfCore
        (absU depth) (absEIdx e))
  /-- **No fuel side condition, at any lane** (task #97-P5-Core-2, which made
  task #97-P5-Arms §11(b)'s second one-line twin change).  The history is
  worth keeping because it is a history of the TWIN and not of the proof:

  * task #97-P5-Core found the gated lane's `whnf` slot false at one fuel
    level — the twin ran `whnfBody (coreKnotGated … (f - 1))`, whose first
    move is `r.whnfCore`, so at `f = 1` it threw `internal` where the port
    answered `Ok e` — and this field carried `lane = LANE_GATED → 2 ≤ f`;
  * task #97-P3-CoreWalks hoisted the stuck-tag test over the fuel dispatch in
    `coreKnotGated`'s two reduction slots, which removed that level and moved
    the disagreement to `f = 0` in the OTHER direction (the twin answering
    `pure e` where the port's `fuel = 0` arm declines), so BOTH reduction
    fields carried `lane = LANE_GATED → 1 ≤ f`;
  * this round put the test in the `| fuel + 1 =>` branch ONLY, leaving
    `coreKnotGated 0`'s two slots the unconditional `fail` the port's
    `fuel = 0` arm is.  The two now agree at every fuel and the condition is
    gone from both fields. -/
  whnf : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.knot_whnf pers vis st mode lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).whnf
        (absU depth) (absEIdx e))
  infer : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.knot_infer pers vis st mode lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).infer
        (absU depth) (absEIdx e))
  inferIO : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.knot_infer_io pers vis st mode lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).inferIO
        (absU depth) (absEIdx e))
  defeq : ∀ {pers vis st mode lane fu fe lfe depth a b lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.knot_defeq pers vis st mode lane fu fe depth a b = ok o →
    Sim₀ id pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).defeq
        (absU depth) (absEIdx a) (absEIdx b))
  annotate : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.knot_annotate pers vis st mode lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).annotate
        (absU depth) (absEIdx e))

/-- **`knot_infer_at`, derived.**  `if io then knot_infer_io else knot_infer`
against `(laneKnotAt … io f).infer`, which is `r.inferIO` under the io view
and `r.infer` without it — the two halves of `CoreFnsA.ioView` by iota. -/
theorem KnotRel.inferAt {f : Nat} (h : KnotRel f)
    {pers vis st mode lane io fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.knot_infer_at pers vis st mode lane io fu fe depth e
      = ok o) :
    Sim₀ absEIdx pers lst o
      ((laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f).infer
        (absU depth) (absEIdx e)) := by
  rw [arena.core.knot_infer_at] at hrun
  cases io with
  | true =>
    rw [if_pos rfl] at hrun
    rw [laneKnotAt_true]
    exact h.inferIO hrel hinv hctx hf hrun
  | false =>
    rw [if_neg (by decide)] at hrun
    rw [laneKnotAt_false]
    exact h.infer hrel hinv hctx hf hrun

/-- **`BodyRel f`** — the six bodies at fuel `f`, against the twin's bodies
tied to the lane's knot at `f`.  This is what `Core/Arms/*` owes and what
`knotRel_succ` consumes; the port's body carries the same `lane` it was called
at, and its own recursive `knot_*` calls are at the SAME fuel, which is why
`KnotRel f → BodyRel f` is the induction step's premise and not its
conclusion.

`whnfCoreGated` is a seventh field because the gated lane's `whnfCore` slot is
a different body (`arena::core_gated::whnf_core_body_gated`); the other five
slots of `coreKnotGated` are the same bodies at the gated knot.

**The two `stuckGated*` fields are gone** (task #97-P5-Core-2).  They existed
because the port hoisted the stuck-tag test out of every lane and the twin
hoisted it into the memoized slot only; task #97-P3-CoreWalks put the test in
`coreKnotGated`'s two reduction slots and this round put it in the
`| fuel + 1 =>` branch alone, so the twin's slots now test exactly where the
port's `knot_*` do and `Core/Induction.lean` reads the agreement off the
knot's own equation (`coreKnotGated_succ_whnfCore_stuck`,
`coreKnotGated_succ_whnf_stuck`) instead of off a body obligation.  The first
of the two is nonetheless TRUE and stays proved, as a fact about the twin, in
`Core/Arms/Gated.lean`; the second, which was false at `f = 0` and carried
`1 ≤ f` for it, has no consumer and is not restated. -/
/- **`inferIO`'s call-site premise** (task #97-P5-Core round 5, region E's
finding).  The port's `infer_body_io` is called at exactly two points,
`knot_infer_io`'s `(LANE_IO, false)` and `(LANE_FULL, true)`; its `.lam`
clause always re-enters `knot_infer_io`, while the twin's `inferBodyIO` calls
`r.infer` of `laneKnotAt … io f` — the io slot at `io = true` and at
`LANE_IO` (where `coreKnotIO`'s two infer slots are one function), the FULL
infer otherwise.  The field is therefore stated at the call sites' shape,
`io = true ∨ lane = LANE_IO`, a fact about the port's two scalar arguments. -/
structure BodyRel (f : Nat) : Prop where
  whnfCore : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.whnf_core_body pers vis st mode lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      (whnfCoreBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))
  whnfCoreGated : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core_gated.whnf_core_body_gated pers vis st mode lane fu fe depth e
      = ok o →
    Sim₀ absEIdx pers lst o
      (whnfCoreBodyGated (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))
  whnf : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.whnf_body pers vis st mode lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      (whnfBody (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))
  infer : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.infer_body pers vis st mode lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      (inferBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))
  inferIO : ∀ {pers vis st mode lane io fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    (io = true ∨ lane = arena.core.LANE_IO) →
    arena.core.infer_body_io pers vis st mode lane io fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      (inferBodyIO (ConRon.Refine.absMode mode)
        (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe
        (absU depth) (absEIdx e))
  defeq : ∀ {pers vis st mode lane fu fe lfe depth a b lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.defeq_body pers vis st mode lane fu fe depth a b = ok o →
    Sim₀ id pers lst o
      (defeqBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx a) (absEIdx b))
  annotate : ∀ {pers vis st mode lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
    absU fu = f →
    arena.core.annotate_body pers vis st mode lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      (annotateBody (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e))

end ConRon.Refine2
