/-
# `ConRon.Refine2.Core.Arms` — the bodies, and what `BodyRel` still owes

**Task #97-P5-Core opened this file; task #97-P5-Arms split it.**
`Core/Induction.lean` closes the knot — given `BodyRel f`, `KnotRel (f + 1)`
holds and the fuel induction runs — and what is left is the other direction,

    bodyRel_of_knot : ∀ f, KnotRel f → BodyRel f

— *"given the knot at `f`, the six BODIES at `f` refine the twin's"*, which is
`arena::core`'s 11 719 lines.  This file is the tier's index and that one
statement; the arms themselves live in `Core/Arms/`:

| file | what | closed |
|---|---|---|
| `Core/Eqns.lean` | the 109 `partial_fixpoint` unfolding equations of `arena::core`'s two mutual blocks, derived ONCE (≈ 9.4 s each; ≈ 17 min, once) and cached into one `.olean` that every arm file imports | — |
| `Core/Arms/Sort.lean` | the `view`/tag agreement — the ten-way `EStore_view_tagOf` and the `sort` projection — and **`ensure_sort_refines`** | **all** |
| `Core/Arms/Delta.lean` | the `whnf` loop's DELTA leaf (task #97-P5-Core-2): `ifenv_find_abs` (the environment index's one reader), the `const` tag/view agreement, `nidx_vec_dup_val`, `const_val_at_refines` and **`unfold_definition_refines`** — lockstep since task #97-P5-Core round 4, closed modulo `ExprOpsHyp` (the `ExprOps` migration's two walks) | **all** (modulo `ExprOpsHyp`) |
| `Core/Arms/Loops.lean` | the two loops' SECOND fuel dimension: `whnf_step` / `whnf_loop` / `whnf_body` **closed** modulo `reduce_nat` and `ExprOpsHyp`; the `defeq` triple stated at the corrected shape (all lockstep since round 4) | 11 of 14 |
| `Core/Arms/Batched.lean` | the five batched clauses of tasks #97-P6-9, -11, -12 and -14, each against the twin's own batched form | 0 of 5 |

## What each body needs, counted

`crates/con-ron-core/src/arena/core.rs` translates to **109 functions** in the
generated model, in two mutual blocks: 100 in the `whnf`/`infer`/`defeq` block
(`arena.core.reduce_nat` … `arena.core.knot_defeq`, plus `arena::core_gated`'s
two) and 9 in the `annotate` block (`annotate_pis_leaf` … `knot_annotate`).
`knot_*` are six of those and are closed; `ensure_sort` and the eight
`*_probe`/`*_set` are closed (`Core/Arms/Sort.lean`, `Core/Probes.lean`).  The
rest — **≈ 95 functions** — is what `bodyRel_of_knot` unfolds into, and the six
bodies' own arms are:

| body | arms (twin clauses) | port helpers under it |
|---|---:|---:|
| `whnf_core_body` | 10 views, of which `app` and `proj` recurse | `whnf_app`, `beta_peel`, `whnf_core_stuck_app`, `whnf_core_proj{,_at,_fire}`, `proj_cert{,_at}`, `iota_rec*` (11) |
| `whnf_body` | the loop (`whnf_loop`/`whnf_step` at `WHNF_LOOP_FUEL`) — **closed**, `Core/Arms/Loops.lean` | `reduce_nat{,_succ,_bin,_wf}` (open); `unfold_definition` **closed**, `Core/Arms/Delta.lean` |
| `infer_body` | 10 views | `infer_forall`, `infer_proj`, `infer_lam{,_open,_cod}`, `infer_spine`, `infer_app`, `infer_lams{,_leaf,_leaf_check}`, `infer_pis{,_leaf}` |
| `infer_body_io` | 10 views | `infer_forall_io{,_at}`, `infer_app_io_at`, `infer_spine_io`, `infer_proj_io` |
| `defeq_body` | the loop (`defeq_loop`/`defeq_step` at `DEFEQ_LOOP_FUEL`) | `defeq_{spine,binders,peel,peel_leaf,lit_app,lit_const,struct,apps,unfold_both,delta_both,delta,after_whnf}`, `bool_true_shortcut`, `proof_irrel`, `prop_irrel`, `eta_cert*`, `struct_*_cert*`, `major_to_ctor*` (≈ 40) |
| `annotate_body` | 10 views | `annotate_{binder,let,proj,proj_at,binders_out,pis,pis_leaf,lams,lams_leaf}` |

## Two shapes that are NOT the `ExprOps` tier's

1. **A local loop's continuation is a closure in the twin and a counter in the
   port** — `Core/Arms/Loops.lean`, where it is closed for `whnf` and where the
   off-by-one in task #97-P5-Core's two statements is corrected (its
   finding 13).
2. **The batched clauses carry an `Array` accumulator and a cursor at once** —
   `Core/Arms/Batched.lean`, which is task #97-P5-0's finding 5.

## Why the six bodies' own dispatches are still open

Round 3's budget is **≈ 20 lines of shape step, 2 lines of idiom and 0.26 s of
`grind` per residual branch** per function.  At ≈ 95 functions and the arena's
ten-way bodies that is the tier's whole cost, and it is more than one round;
what this round owes it is the equation floor (`Core/Eqns.lean`, which turns a
per-file 17 minutes into a once-and-for-all 17 minutes), the two shapes above,
and the exemplar (`ensure_sort`, closed end to end).
-/
import ConRon.Refine2.Core.Arms.Sort
import ConRon.Refine2.Core.Arms.Delta
import ConRon.Refine2.Core.Arms.Loops
import ConRon.Refine2.Core.Arms.Batched
import ConRon.Refine2.Core.LS.Infer
import ConRon.Refine2.Core.LS.Annotate

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PB.CoreLSReg ConRon.Refine2.Lockstep.PC1.CoreLSReg ConRon.Refine2.Lockstep.PC2.CoreLSReg ConRon.Refine2.Lockstep.PD.CoreLSReg ConRon.Refine2.Lockstep.PE.CoreLSReg ConRon.Refine2.Lockstep.PF.CoreLSReg ConRon.Refine2.Lockstep.PG.CoreLSReg ConRon.Refine2.Lockstep.PG2.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The six bodies, and the tier's open obligations

**Task #97-P5-Core round 4: the skeleton.**  `bodyRel_of_knot` is no longer
one `sorry`: it is the seven `BodyRel` fields assembled from one child per
body, every child a LOCKSTEP statement over `AStateRel₀` (no `StoreWF`, no
`EResolves`, `Sim₀`).  Two of the seven are already the loops of
`Core/Arms/Loops.lean` (`whnf_body_refines`, closed modulo `reduce_nat` and
the `ExprOpsHyp` seam; `defeq_body_refines`, whose loop is open); the other
five are the ten-way dispatches below. -/

/-- `arena::core::whnf_core_body` against `Arena.whnfCoreBody` — the
head-normalization body.  **Open.** -/
theorem whnf_core_body_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.whnf_core_body pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfCoreBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) :=
  Lockstep.LS.toSim₀ (Lockstep.whnf_core_body_ls hk hx hrel hinv hctx hf) hrun

/-- `arena::core_gated::whnf_core_body_gated` against `Arena.whnfCoreBodyGated`
— the gated lane's `whnfCore` body.  **Open.** -/
theorem whnf_core_body_gated_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core_gated.whnf_core_body_gated pers vis st mode lane fu fe depth e
      = ok o) :
    Sim₀ absEIdx pers lst o
      (whnfCoreBodyGated (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) :=
  Lockstep.LS.toSim₀ (Lockstep.whnf_core_body_gated_ls hk hx hrel hinv hctx hf) hrun

/-- `arena::core::infer_body` against `Arena.inferBody`.  **Open.** -/
theorem infer_body_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.infer_body pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      (inferBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) :=
  Lockstep.LS.toSim₀ (Lockstep.infer_body_ls hk hx hrel hinv hctx hf) hrun

/-- `arena::core::infer_body_io` against `Arena.inferBodyIO`.  **Open.** -/
theorem infer_body_io_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane io fu fe lfe depth e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hio : io = true ∨ lane = arena.core.LANE_IO)
    (hrun : arena.core.infer_body_io pers vis st mode lane io fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      (inferBodyIO (ConRon.Refine.absMode mode)
        (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe
        (absU depth) (absEIdx e)) :=
  Lockstep.LS.toSim₀ (Lockstep.infer_body_io_ls hk hx hrel hinv hctx hf hio) hrun

/-- `arena::core::annotate_body` against `Arena.annotateBody`.  **Open.** -/
theorem annotate_body_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.annotate_body pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      (annotateBody (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) :=
  Lockstep.LS.toSim₀ (Lockstep.annotate_body_ls hk hx hrel hinv hctx hf) hrun

/-- **The `ExprOps` tier's lockstep obligations, named once** — the two walks
the delta leaf borrows (`Core/Arms/Delta.lean`'s `ExprOpsHyp`), which the
`ExprOps` tier's migration to `AStateRel₀` owes.  **Open**, and deliberately
a single named seam rather than a hypothesis of `bodyRel_of_knot`: nothing
below the knot can supply it until that migration. -/
theorem exprOpsHyp (pers : arena.store.PersTier) : ExprOpsHyp pers := by
  sorry

/-- **`KnotRel f → BodyRel f`**, assembled from its seven children.  Since
task #97-P5-Core round 4 this is a skeleton, not a `sorry`: the open work is
the five dispatches above, `reduce_nat_refines` and `defeq_loop_refines`
(`Core/Arms/Loops.lean`), and the `exprOpsHyp` seam. -/
theorem bodyRel_of_knot : ∀ f, KnotRel f → BodyRel f := fun _ hk =>
  { whnfCore := fun h1 h2 h3 h4 h5 =>
      whnf_core_body_refines hk (exprOpsHyp _) h1 h2 h3 h4 h5
    whnfCoreGated := fun h1 h2 h3 h4 h5 =>
      whnf_core_body_gated_refines hk (exprOpsHyp _) h1 h2 h3 h4 h5
    whnf := fun h1 h2 h3 h4 h5 =>
      whnf_body_refines hk (exprOpsHyp _) h1 h2 h3 h4 h5
    infer := fun h1 h2 h3 h4 h5 => infer_body_refines hk (exprOpsHyp _) h1 h2 h3 h4 h5
    inferIO := fun h1 h2 h3 h4 hio h5 =>
      infer_body_io_refines hk (exprOpsHyp _) h1 h2 h3 h4 hio h5
    defeq := fun h1 h2 h3 h4 h5 => defeq_body_refines hk (exprOpsHyp _) h1 h2 h3 h4 h5
    annotate := fun h1 h2 h3 h4 h5 =>
      annotate_body_refines hk (exprOpsHyp _) h1 h2 h3 h4 h5 }

/-- **The knot, unconditionally** — the theorem the Checker tier wants, and the
only `sorry` between it and `Core/Induction.lean`'s closed induction. -/
theorem knotRel (f : Nat) : KnotRel f := knot_rel bodyRel_of_knot f

/-- `KnotRel` at the checker's own fuel. -/
theorem knotRel_check : KnotRel (absU arena.core.CHECK_FUEL) :=
  knotRel _

end ConRon.Refine2
