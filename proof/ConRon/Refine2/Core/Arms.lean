/-
# `ConRon.Refine2.Core.Arms` — the bodies, and what `BodyRel` still owes

**Task #97-P5-Core, the tier's open half.**  `Core/Induction.lean` closes the
knot: given `BodyRel f`, `KnotRel (f + 1)` holds, and the fuel induction runs.
What is left is the other direction —

    bodyRel_of_knot : ∀ f, KnotRel f → BodyRel f

— *"given the knot at `f`, the six BODIES at `f` refine the twin's"*, which is
`arena::core`'s 11 719 lines and is **not** closed in this round.  This file
holds that statement, the `sorry`, and the arm statements the bodies are built
from, so that the shape of the remaining work is in the repository rather than
in a report.

## What each body needs, counted

`crates/con-ron-core/src/arena/core.rs` translates to **110 functions** in the
generated model, in two mutual blocks: 100 in the `whnf`/`infer`/`defeq` block
(`arena.core.reduce_nat` … `arena.core.knot_defeq`, plus
`arena::core_gated`'s two) and 10 in the `annotate` block
(`annotate_pis_leaf` … `knot_annotate`).  `knot_*` are six of those and are
closed; `ensure_sort` and the eight `*_probe`/`*_set` are closed
(`Core/Entries.lean`, `Core/Probes.lean`).  The rest — **95 functions** — is
what `bodyRel_of_knot` unfolds into, and the six bodies' own arms are:

| body | arms (twin clauses) | port helpers under it |
|---|---:|---:|
| `whnf_core_body` | 10 views, of which `app` and `proj` recurse | `whnf_app`, `beta_peel`, `whnf_core_stuck_app`, `whnf_core_proj{,_at,_fire}`, `proj_cert{,_at}`, `iota_rec*` (11) |
| `whnf_body` | the loop (`whnf_loop`/`whnf_step` at `WHNF_LOOP_FUEL`) | `reduce_nat{,_succ,_bin,_wf}`, `unfold_definition` |
| `infer_body` | 10 views | `infer_forall`, `infer_proj`, `infer_lam{,_open,_cod}`, `infer_spine`, `infer_app`, `infer_lams{,_leaf,_leaf_check}`, `infer_pis{,_leaf}` |
| `infer_body_io` | 10 views | `infer_forall_io{,_at}`, `infer_app_io_at`, `infer_spine_io`, `infer_proj_io` |
| `defeq_body` | the loop (`defeq_loop`/`defeq_step` at `DEFEQ_LOOP_FUEL`) | `defeq_{spine,binders,peel,peel_leaf,lit_app,lit_const,struct,apps,unfold_both,delta_both,delta,after_whnf}`, `bool_true_shortcut`, `proof_irrel`, `prop_irrel`, `eta_cert*`, `struct_*_cert*`, `major_to_ctor*` (≈40) |
| `annotate_body` | 10 views | `annotate_{binder,let,proj,proj_at,binders_out,pis,pis_leaf,lams,lams_leaf}` |

## Two shapes that are NOT the `ExprOps` tier's

1. **A local loop's continuation is a closure in the twin and a counter in the
   port.**  `whnfStep r fe depth (k : EIdx → AM EIdx) e` takes the rest of the
   loop as a FUNCTION; `whnf_step … n e` takes the remaining step count and
   calls `whnf_loop … (n - 1)`.  So `whnf_step_refines` is stated against
   `whnfStep … (whnfLoop r fe depth (n - 1))` and the loop's own induction is
   on `n`, a SECOND fuel dimension beside the knot's.  `defeq_step` /
   `defeq_loop` are the same pair.  This is task #97-P5-0's finding 6 one level
   up: the port replaces a higher-order argument with a scalar, and the
   refinement names the function the scalar stands for.
2. **The batched clauses carry an `Array` accumulator and a `List` spine at
   once.**  `whnf_app` / `beta_peel` (task #97-P6-9), `infer_spine{,_io}`
   (#97-P6-12), `annotate_pis` / `annotate_lams` (#97-P6-11) and `defeq_peel`
   (#97-P6-14) take `acc : Vec<EIdx>` in PUSH order against the twin's
   `Array EIdx` and `args : Vec<EIdx>` with a cursor against the twin's
   `List EIdx` — `ExprOps/Mut.lean`'s finding 5, which the statements below
   reuse (`absEIdxArr` against `absEIdxList`).

## Why the statements are here and the proofs are not

Round 3's budget is **≈ 20 lines of shape step, 2 lines of idiom and 0.26 s of
`grind` per residual branch** per function.  At 95 functions and the arena's
ten-way bodies that is the tier's whole cost, and it is a round of its own;
what this round owes it is the KNOT (closed), the memo floor (closed) and the
statements (here).
-/
import ConRon.Refine2.Core.Entries
import ConRon.Refine2.ExprOps.Mut

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

set_option maxRecDepth 4000

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (EResolves)

/-! ## The two loops: a closure in the twin, a counter in the port -/

/-- `arena::core::whnf_step` against `Arena.whnfStep` with the rest of the loop
named: the port's `n` IS the twin's continuation `whnfLoop r fe depth (n - 1)`.
-/
theorem whnf_step_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n e lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f) (hn : 1 ≤ absU n)
    (hrun : arena.core.whnf_step pers vis st mode lane fu fe depth n e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (whnfStep (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth)
        (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) (absU n - 1))
        (absEIdx e)) := by
  sorry

/-- `arena::core::whnf_loop` against `Arena.whnfLoop`: the SECOND fuel
dimension, an induction on `n` inside the knot's induction on `f`. -/
theorem whnf_loop_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n e lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hrun : arena.core.whnf_loop pers vis st mode lane fu fe depth n e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (whnfLoop (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absU n) (absEIdx e)) := by
  sorry

/-- `arena::core::defeq_step` against `Arena.defeqStep`, the same pair. -/
theorem defeq_step_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n pi a b lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hra : EResolves lst (absEIdx a)) (hrb : EResolves lst (absEIdx b))
    (hf : absU fu = f) (hn : 1 ≤ absU n)
    (hrun : arena.core.defeq_step pers vis st mode lane fu fe depth n pi a b
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (defeqStep (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (defeqLoop (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
          (absU n - 1))
        pi (absEIdx a) (absEIdx b)) := by
  sorry

/-- `arena::core::defeq_loop` against `Arena.defeqLoop`. -/
theorem defeq_loop_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n pi a b lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hra : EResolves lst (absEIdx a)) (hrb : EResolves lst (absEIdx b))
    (hf : absU fu = f)
    (hrun : arena.core.defeq_loop pers vis st mode lane fu fe depth n pi a b
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (defeqLoop (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absU n) pi (absEIdx a) (absEIdx b)) := by
  sorry

/-! ## `ensureSort`, the seventh entry point's body -/

/-- `arena::core::ensure_sort` against `Arena.ensureSort`: `r.whnf` and then
one view read.  The entry `ensure_sort_core` is this at `LANE_FULL`. -/
theorem ensure_sort_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hrun : arena.core.ensure_sort pers vis st mode lane fu fe depth e = ok o) :
    Sim absLIdx (fun _ => True) pers lst o
      (ensureSort (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) := by
  sorry

/-! ## The batched clauses (tasks #97-P6-9, -11, -12, -14)

`acc` is an `Array` in PUSH order and `args` a `List` read from a cursor;
`ExprOps/Mut.lean`'s `absEIdxArr` / `absEIdxList` are those two readings and
getting them the wrong way round does not typecheck. -/

/-- `arena::core::whnf_app` against `Arena.whnfApp` — the batched β spine's
head (task #97-P6-9). -/
theorem whnf_app_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth v hd vargs same args nodes i lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store) (hf : absU fu = f)
    (hrun : arena.core.whnf_app pers vis st mode lane fu fe depth v hd vargs
      same args nodes i = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (whnfApp (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx v) (absEIdx hd) (absEIdxArr vargs) same (absEIdxArr args)
        (absEIdxArr nodes) (absSz i)) := by
  sorry

/-- `arena::core::beta_peel` against `Arena.betaPeel` — the consecutive λ run
peeled into ONE `instantiateList` walk. -/
theorem beta_peel_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth t acc args nodes i lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store) (hf : absU fu = f)
    (hrun : arena.core.beta_peel pers vis st mode lane fu fe depth t acc args
      nodes i = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (betaPeel (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx t) (absEIdxArr acc) (absEIdxArr args) (absEIdxArr nodes)
        (absSz i)) := by
  sorry

/-- `arena::core::iota_rec_at` against `Arena.iotaRecAt` — the ι step at a
spine the caller already has. -/
theorem iota_rec_at_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth hd sargs n lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx hd)) (hf : absU fu = f)
    (hrun : arena.core.iota_rec_at pers vis st mode lane fu fe depth hd sargs n
      = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (iotaRecAt (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx hd) (absEIdxArr sargs) (absSz n)) := by
  sorry

/-- `arena::core::defeq_peel_leaf` against `Arena.defeqPeelLeaf` — the batched
binder descent's leaf (task #97-P6-14). -/
theorem defeq_peel_leaf_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d a b k fvs mism mismLam lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hra : EResolves lst (absEIdx a)) (hrb : EResolves lst (absEIdx b))
    (hf : absU fu = f)
    (hrun : arena.core.defeq_peel_leaf pers vis st mode lane fu fe d a b k fvs
      mism mismLam = ok o) :
    Sim id (fun _ => True) pers lst o
      (defeqPeelLeaf (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        (absU d) (absEIdx a) (absEIdx b) (absU k) (absEIdxArr fvs) mism
        mismLam) := by
  sorry

/-- `arena::core::whnf_core_stuck_app` against `Arena.whnfCoreStuckApp` — the
gated lane's only caller since the batched β landed. -/
theorem whnf_core_stuck_app_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth h same fp a lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store) (hf : absU fu = f)
    (hrun : arena.core.whnf_core_stuck_app pers vis st mode lane fu fe depth h
      same fp a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (whnfCoreStuckApp (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx h) same (absEIdx fp) (absEIdx a)) := by
  sorry

/-! ## The six bodies, and the tier's one open obligation -/

/-- **`KnotRel f → BodyRel f`.**  The six bodies' ten-way dispatches, the two
loops, the batched clauses and the ≈ 95 helpers under them.  This is what
`Core/Induction.lean`'s `knot_rel` consumes and what the next round owes; the
census is in this file's module note.

Its two gated fields (`stuckGatedCore`, `stuckGatedWhnf`) are the two
divergences `Core/Induction.lean` names: the port hoists the stuck-tag test
out of every lane and the twin hoists it only into the memoized slot, and at
`f = 0` the second of them is FALSE, which is why it carries `1 ≤ f`. -/
theorem bodyRel_of_knot : ∀ f, KnotRel f → BodyRel f := by
  sorry

/-- **The knot, unconditionally** — the theorem the Checker tier wants, and the
only `sorry` between it and `Core/Induction.lean`'s closed induction. -/
theorem knotRel (f : Nat) : KnotRel f := knot_rel bodyRel_of_knot f

/-- `KnotRel` at the checker's own fuel. -/
theorem knotRel_check : KnotRel (absU arena.core.CHECK_FUEL) :=
  knotRel _

end ConRon.Refine2
