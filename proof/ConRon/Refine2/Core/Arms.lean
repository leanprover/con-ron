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
| `Core/Arms/Gated.lean` | `bodyRel_stuckGatedCore` — the gated body's identity at a stuck tag (task #97-P5-Core's finding 12, first half).  It was a `BodyRel` FIELD until task #97-P5-Core-2 put the port's fuel-0 arm back in `coreKnotGated`; the fact stays true and stays proved | **all** |
| `Core/Arms/Delta.lean` | the `whnf` loop's DELTA leaf (task #97-P5-Core-2): `ifenv_find_abs` (the environment index's one reader), the `const` tag/view agreement, `nidx_vec_dup_val`, `const_val_at_refines` and **`unfold_definition_refines`** | **all** |
| `Core/Arms/Loops.lean` | the two loops' SECOND fuel dimension: `whnf_step` / `whnf_loop` / `whnf_body` **closed** modulo ONE leaf (`reduce_nat`); the `defeq` triple stated at the corrected shape | 7 of 8 |
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
import ConRon.Refine2.Core.Arms.Gated
import ConRon.Refine2.Core.Arms.Delta
import ConRon.Refine2.Core.Arms.Loops
import ConRon.Refine2.Core.Arms.Batched

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The six bodies, and the tier's one open obligation -/

/-- **`KnotRel f → BodyRel f`.**  The six bodies' ten-way dispatches, the two
loops, the batched clauses and the ≈ 95 helpers under them.  This is what
`Core/Induction.lean`'s `knot_rel` consumes and what the next round owes; the
census is in this file's module note.

Its two gated fields are GONE (task #97-P5-Core-2): the twin's
`coreKnotGated` now tests the stuck tag exactly where the port's `knot_*` do
and fails unconditionally at fuel `0`, so `Core/Induction.lean` reads the
agreement off the knot's own equation and neither relation carries anything
for it. -/
theorem bodyRel_of_knot : ∀ f, KnotRel f → BodyRel f := by
  sorry

/-- **The knot, unconditionally** — the theorem the Checker tier wants, and the
only `sorry` between it and `Core/Induction.lean`'s closed induction. -/
theorem knotRel (f : Nat) : KnotRel f := knot_rel bodyRel_of_knot f

/-- `KnotRel` at the checker's own fuel. -/
theorem knotRel_check : KnotRel (absU arena.core.CHECK_FUEL) :=
  knotRel _

end ConRon.Refine2
