/-
# The arms, assembled (task #55, `CORE_PLAN.md` step 6)

`Arms/Shape.lean` fixes the shape, the sixteen files of `Arms/` prove the
helpers of `cached/core_c.rs`'s `partial_fixpoint` block one group each, and
this file ties them together:

* each file's `<File>Deps` — the statements it had to assume of the helpers
  living in *another* file, so that the sixteen could be proved in parallel —
  is discharged here from those files' own theorems;
* the seven body lemmas become `Bodies mode fuel` through
  `RefinesE.ofSim`/`RefinesB.ofSim`;
* `arms : ∀ fuel, Wrappers mode fuel → Bodies mode fuel`, which is what
  `Refine/Core/Knot.lean`'s `knot_induction` (task #53) consumes;
* `knot_spec : ∀ fuel, KnotSpec mode fuel` — the twelve statements at every
  fuel, and the point of `CORE_PLAN.md` step 6.
-/
import ConRon.Refine.Core.Knot
import ConRon.Refine.Core.Arms.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-! ## The seven bodies

Each is the body file's `<body>_refines`, in `Sim` form. -/

-- sorry: placeholder for `Arms/WhnfCore.lean`'s `whnf_core_body_i_refines`
theorem whnf_core_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.whnf_core_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.whnfCoreBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr e)) := sorry

-- sorry: placeholder for `Arms/Whnf.lean`'s `whnf_body_i_refines`
theorem whnf_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.whnf_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.whnfBodyI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) := sorry

-- sorry: placeholder for `Arms/Infer.lean`'s `infer_body_i_refines`
theorem infer_body_sim (hw : Wrappers mode fuel) (d : Std.U64) (io : Bool)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_body_i mode fuel st fe d e io)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode) (knotV mode lfe fuel.val io) lfe
        d.val (absExpr e)) := sorry

-- sorry: placeholder for `Arms/InferIO.lean`'s `infer_body_io_i_refines`
theorem infer_body_io_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_body_io_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.inferBodyIOI (absMode mode)
        (knot mode lfe fuel.val).ioView lfe d.val (absExpr e)) := sorry

-- sorry: placeholder for `Arms/DefEq.lean`'s `defeq_body_i_refines`
theorem defeq_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True) (fun st fe => cached.core_c.defeq_body_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.defeqBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr a) (absExpr b)) := sorry

-- sorry: placeholder for `Arms/Annotate.lean`'s `annotate_body_i_refines`
theorem annotate_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.annotate_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) := sorry

end

/-! ## `Bodies`, `arms` and the knot

The `infer` body is the one stated twice: `Bodies.infer` is `infer_body_sim`
at `io = false` and `Bodies.inferView` the same at `io = true` (`knotV`). -/

/-- The arms: given the six wrappers at `fuel`, the seven bodies at `fuel`. -/
theorem arms {mode : env.CheckMode} (fuel : Std.U64) (hw : Wrappers mode fuel) :
    Bodies mode fuel where
  whnfCore := RefinesE.ofSim fun d _e he => whnf_core_body_sim hw d he
  whnf := RefinesE.ofSim fun d _e he => whnf_body_sim hw d he
  infer := RefinesE.ofSim fun d _e he => infer_body_sim hw d false he
  inferView := RefinesE.ofSim fun d _e he => infer_body_sim hw d true he
  defeq := RefinesB.ofSim fun d _a _b ha hb => defeq_body_sim hw d ha hb
  annotate := RefinesE.ofSim fun d _e he => annotate_body_sim hw d he
  inferIO := RefinesE.ofSim fun d _e he => infer_body_io_sim hw d he

/-- **The knot** (`CORE_PLAN.md` step 6): at every fuel, the six wrappers
refine `coreKnotI … fuel` and the seven bodies refine con-leche's bodies at
that knot.  Task #53's `knot_induction` plus this task's `arms`. -/
theorem knot_spec {mode : env.CheckMode} (fuel : Std.U64) : KnotSpec mode fuel :=
  knot_induction (fun f hw => arms f hw) fuel

end ConRon.Refine.Core
