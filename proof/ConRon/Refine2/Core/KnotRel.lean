/-
# `ConRon.Refine2.Core.KnotRel` — the knot tied, once, at a fuel

**Task #97-P5-Core, the relation task #97-P5-1 asked to be written before any
`core` lemma is stated.**  DESIGN §8.4 gives (B) a knot that is a RECORD of
five closures (`CoreFnsA`) and §3.4 forbids the port a closure at all, so
`arena::core`'s five entry points take **the lane as a `u32` scalar** and
dispatch on it:

| port | twin |
|---|---|
| `knot_whnf_core … lane fuel … cheap …` | `(<lane's knot> f).whnfCore cheap` (the official `cheap_proj` flag is an argument on both sides) |
| `knot_whnf`, `knot_infer`, `knot_infer_io`, `knot_defeq`, `knot_defeq_e` | the record's other five slots (`knot_defeq_e` is the eager slot, task #125) |
| `LANE_FULL` (`0`) | `Core.lean`'s `coreKnot mode eager fe id` |
| `LANE_IO` (`2`) | `CoreIO.lean`'s `coreKnotIO mode eager fe` |

(`LANE_GATED` and `coreKnotGated` went with con-leche's modeled route, task
#105; `knot_whnf_core`, `knot_whnf` and `knot_defeq` no
longer read the lane at all.)
| `knot_infer_at … io …` | `CoreFnsA.ioView` applied or not — **the port's
  `io : bool` IS the `ioView` substitution** (its own doc comment says so) |

`laneKnot` and `laneKnotAt` are that table as functions, and `KnotRel f` is
*"at fuel `f`, each of the five port entries refines the corresponding slot of
the lane's twin knot"* — one relation, established once by induction on the
fuel (`Core/Induction.lean`) and consumed FIELD-WISE at every call site inside
a body (`hknot.whnf`, `hknot.defeq`, …), exactly as task #97s round 2's rule 8
found the record of knot hypotheses costs nothing.

## Why a structure and not five lemmas

The five are mutually recursive through the bodies, so they are established
together or not at all; and a body arm wants to name one of them
(`hknot.infer`) in a `grind` list without dragging the other five's
instantiations in.  A structure gives both.  `BodyRel f` is its partner —
*"the five BODIES at fuel `f` refine the twin's bodies tied to the lane's knot
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
`Arena/ExprOps.lean`); and the coordinator's ruling
(i) moved `StoreWF` (and `Ext`, a statement about denotation) out of the
relation into Theorem 1, because the port and the twin both intern over a
dangling child without looking at it and their stores stay equal field for
field — only the twin's DAG invariant fails there.  Nothing about resolution
is premised or concluded any more.

## The eager flag

Every port knot function threads `eager : bool` right after `mode`, and the
twin's bodies that only call through the record take no flag: there the flag is
in the record.  So `laneKnot` takes it, and the port's `eager` argument IS the
flag the lane's twin knot was tied at; the relations quantify over it exactly as
they do over `mode`.  `knot_defeq_e` re-enters at `eager = true`, the twin's
`defeqE` slot at `coreKnot mode true`.

## The two ambient arguments

Every port function of this tier carries `pers : &PersTier` and `fe : &IFEnv`
where the twin carries one `IFEnv`: the port's frozen base lives in the tier,
the twin's in the environment's `base`.  `CoreCtx` says they agree.
-/
import ConRon.Refine2.Core.Probes
import ConRon.Refine2.ExprOps.Read
import ConRon.Arena.CoreIO
import ConRon.Arena.WFProofs

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The lane, as the twin knot it stands for -/

/-- **The twin knot a port lane stands for.**  `LANE_IO` is the leaf knot,
anything else (`LANE_FULL`, which is `0`) the memoized full knot — the port's
own `else` arm, so the reading is the code's and not a case analysis the
refinement invents. -/
def laneKnot (mode : ConLeche.CheckMode) (eager : Bool) (fe : IFEnv) (lane : Std.U32)
    (f : Nat) : CoreFnsA :=
  if lane = arena.core.LANE_IO then coreKnotIO mode eager fe f
  else coreKnot mode eager fe id f

/-- **The record an `io`-flagged body call resolves `r.infer` through.**
`arena::core::knot_infer_at`'s own doc comment: *"This function IS the
`ioView` substitution in the port — the knot is plain functions, so there is
no record whose `infer` field can be rebound."* -/
def laneKnotAt (mode : ConLeche.CheckMode) (eager : Bool) (fe : IFEnv) (lane : Std.U32)
    (io : Bool) (f : Nat) : CoreFnsA :=
  if io then (laneKnot mode eager fe lane f).ioView else laneKnot mode eager fe lane f

@[simp] theorem laneKnot_io (mode eager fe f) :
    laneKnot mode eager fe arena.core.LANE_IO f = coreKnotIO mode eager fe f := by
  rw [laneKnot, ite_eq_left rfl]

@[simp] theorem laneKnot_full (mode eager fe f) :
    laneKnot mode eager fe arena.core.LANE_FULL f = coreKnot mode eager fe id f := by
  rw [laneKnot, ite_eq_right (by rw [arena.core.LANE_FULL, arena.core.LANE_IO]; decide)]

@[simp] theorem laneKnotAt_true (mode eager fe lane f) :
    laneKnotAt mode eager fe lane true f = (laneKnot mode eager fe lane f).ioView := by
  rw [laneKnotAt, ite_eq_left rfl]

@[simp] theorem laneKnotAt_false (mode eager fe lane f) :
    laneKnotAt mode eager fe lane false f = laneKnot mode eager fe lane f := by
  rw [laneKnotAt, ite_eq_right (by decide)]

/-- The port's lane is NOT `LANE_IO` exactly when the twin's knot is the full
one — the reading every `else` arm of the five entries takes. -/
theorem laneKnot_of_ne (mode eager fe f) {lane : Std.U32}
    (hi : ¬ lane = arena.core.LANE_IO) :
    laneKnot mode eager fe lane f = coreKnot mode eager fe id f := by
  rw [laneKnot, ite_eq_right hi]

/-! ## The ambient arguments

`pers` needs no clause of its own — `AStateRel pers st lst` already ties the
persistent tier to the twin's single store (`Refine2/AbsStore.lean`'s
`absStore`).  What is left is the environment. -/

/-- The port's `(pers, fe)` against the twin's `IFEnv`: **what a reader sees**
(`IFEnvRead`: the layer's own rows and tables, and the frozen base `pers.env` at
the layer's two bounds), with the layer's maps well formed (`IFEnvInv`), since
`HashMap2.get` specifies nothing otherwise.  It says nothing of the constant
lists, which no reader reads: `IFEnvRel` adds them, for what pushes. -/
structure CoreCtx (pers : arena.store.PersTier) (fe : arena.env.IFEnv) (lfe : IFEnv) :
    Prop extends IFEnvRead pers fe lfe where
  inv : IFEnvInv fe

/-! ## The two relations -/

/-- **`KnotRel f`** — at fuel `f`, each of `arena::core`'s five knot entries
refines the corresponding slot of the lane's twin knot.  Established once by
`Core/Induction.lean`'s fuel induction, consumed field-wise everywhere else.

`knot_infer_at` is not a field: it is `if io then knot_infer_io else
knot_infer` and `Core/Induction.lean`'s `KnotRel.inferAt` derives it. -/
structure KnotRel (f : Nat) : Prop where
  whnfCore : ∀ {pers st mode eager lane fu fe lfe cheap depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.knot_whnf_core pers st mode eager lane fu fe cheap depth e = ok o →
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) eager lfe lane f).whnfCore cheap
        (absU depth) (absEIdx e))
  /-- **No fuel side condition, at any lane**: the twin's slots test the
  stuck tag in their `| fuel + 1 =>` branch only, where the port's `fuel = 0`
  arm has already declined (task #97-P5-Core-2's history of the gated lane,
  deleted with it at task #105, is in git). -/
  whnf : ∀ {pers st mode eager lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.knot_whnf pers st mode eager lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) eager lfe lane f).whnf
        (absU depth) (absEIdx e))
  infer : ∀ {pers st mode eager lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.knot_infer pers st mode eager lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) eager lfe lane f).infer
        (absU depth) (absEIdx e))
  inferIO : ∀ {pers st mode eager lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.knot_infer_io pers st mode eager lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) eager lfe lane f).inferIO
        (absU depth) (absEIdx e))
  defeq : ∀ {pers st mode eager lane fu fe lfe depth a b lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.knot_defeq pers st mode eager lane fu fe depth a b = ok o →
    Sim₀ id pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) eager lfe lane f).defeq
        (absU depth) (absEIdx a) (absEIdx b))
  /-- **The eager slot** (task #125, con-leche #353): `knot_defeq_e` against
  the record's `defeqE` — the defeq body at `eager := true` one level down,
  memoized on the eager tower's own memos, at every lane (`coreKnotIO`'s slot
  is the full knot's). -/
  defeqE : ∀ {pers st mode eager lane fu fe lfe depth a b lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.knot_defeq_e pers st mode eager lane fu fe depth a b = ok o →
    Sim₀ id pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) eager lfe lane f).defeqE
        (absU depth) (absEIdx a) (absEIdx b))

/-- **`knot_infer_at`, derived.**  `if io then knot_infer_io else knot_infer`
against `(laneKnotAt … io f).infer`, which is `r.inferIO` under the io view
and `r.infer` without it — the two halves of `CoreFnsA.ioView` by iota. -/
theorem KnotRel.inferAt {f : Nat} (h : KnotRel f)
    {pers st mode eager lane io fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f)
    (hrun : arena.core.knot_infer_at pers st mode eager lane io fu fe depth e
      = ok o) :
    Sim₀ absEIdx pers lst o
      ((laneKnotAt (ConRon.Refine.absMode mode) eager lfe lane io f).infer
        (absU depth) (absEIdx e)) := by
  rw [arena.core.knot_infer_at] at hrun
  cases io with
  | true =>
    rw [ite_eq_left rfl] at hrun
    rw [laneKnotAt_true]
    exact h.inferIO hrel hinv hctx hf hrun
  | false =>
    rw [ite_eq_right (by decide)] at hrun
    rw [laneKnotAt_false]
    exact h.infer hrel hinv hctx hf hrun

/-- **`BodyRel f`** — the five bodies at fuel `f`, against the twin's bodies
tied to the lane's knot at `f`.  This is what `Core/Arms/*` owes and what
`knotRel_succ` consumes; the port's body carries the same `lane` it was called
at, and its own recursive `knot_*` calls are at the SAME fuel, which is why
`KnotRel f → BodyRel f` is the induction step's premise and not its
conclusion.

The gated lane's seventh field (`whnfCoreGated`) went with the gated knot at
task #105. -/
/- **`inferIO`'s call-site premise** (task #97-P5-Core round 5, region E's
finding).  The port's `infer_body_io` is called at exactly two points,
`knot_infer_io`'s `(LANE_IO, false)` and `(LANE_FULL, true)`; its `.lam`
clause always re-enters `knot_infer_io`, while the twin's `inferBodyIO` calls
`r.infer` of `laneKnotAt … io f` — the io slot at `io = true` and at
`LANE_IO` (where `coreKnotIO`'s two infer slots are one function), the FULL
infer otherwise.  The field is therefore stated at the call sites' shape,
`io = true ∨ lane = LANE_IO`, a fact about the port's two scalar arguments. -/
structure BodyRel (f : Nat) : Prop where
  whnfCore : ∀ {pers st mode eager lane fu fe lfe cheap depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.whnf_core_body pers st mode eager lane fu fe cheap depth e = ok o →
    Sim₀ absEIdx pers lst o
      (whnfCoreBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe cheap
        (absU depth) (absEIdx e))
  whnf : ∀ {pers st mode eager lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.whnf_body pers st mode eager lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      (whnfBody (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe
        (absU depth) (absEIdx e))
  infer : ∀ {pers st mode eager lane fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.infer_body pers st mode eager lane fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      (inferBody
        (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe
        (absU depth) (absEIdx e))
  inferIO : ∀ {pers st mode eager lane io fu fe lfe depth e lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    (io = true ∨ lane = arena.core.LANE_IO) →
    arena.core.infer_body_io pers st mode eager lane io fu fe depth e = ok o →
    Sim₀ absEIdx pers lst o
      (inferBodyIO
        (laneKnotAt (ConRon.Refine.absMode mode) eager lfe lane io f) lfe
        (absU depth) (absEIdx e))
  defeq : ∀ {pers st mode eager lane fu fe lfe depth a b lst o},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe →
    absU fu = f →
    arena.core.defeq_body pers st mode eager lane fu fe depth a b = ok o →
    Sim₀ id pers lst o
      (defeqBody (ConRon.Refine.absMode mode) eager
        (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe
        (absU depth) (absEIdx a) (absEIdx b))

end ConRon.Refine2
