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

## What is and is not closed

Four of the seven bodies are assembled from their files here — `whnf`,
`infer` (at both grades), `infer_io` and `annotate` — each with its `Deps`
discharged by `exact` from the sibling files' theorems, which is the check
that the sixteen parallel statements really did line up.

Three are not, and the reasons are recorded rather than papered over:

* **`whnf_core`** and **`defeq`** wait on `Arms/Major.lean` and
  `Arms/DefEqStruct.lean`, whose `Deps` fields (`projLitToCtor`,
  `defeqStruct`, `structEtaCert`, `structUnitCert`) those two files own.
* Two of the four assembled bodies are not *axiom*-clean, and one of the
  three open ones cannot be: the task's three findings, recorded in DESIGN.md
  §"Task #55" — the `nat_op_result` shift deviation under `whnf`/`defeq`, the
  `Bodies.inferView` statement bug under `infer`, and the `as usize` casts
  under `whnf_core`.  `#print axioms` below says exactly which.
-/
import ConRon.Refine.Core.Knot
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.Core.Arms.Shared
import ConRon.Refine.Core.Arms.Lits
import ConRon.Refine.Core.Arms.Whnf
import ConRon.Refine.Core.Arms.InferSpine
import ConRon.Refine.Core.Arms.InferSpineIO
import ConRon.Refine.Core.Arms.InferTele
import ConRon.Refine.Core.Arms.Infer
import ConRon.Refine.Core.Arms.InferIO
import ConRon.Refine.Core.Arms.Annotate

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-! ## The `Deps` discharges

Each is an `exact` from the owning file's theorem — the check that sixteen
agents' statements, written in parallel against `Shape.lean` alone, agree. -/

/-- `Arms/Whnf.lean`'s two `Arms/Lits.lean` callees. -/
theorem whnfDeps (hw : Wrappers mode fuel) : WhnfDeps mode fuel where
  reduceNat := by intro d e he; exact reduce_nat_i_refines hw d he
  unfoldDefinition := by intro e he; exact unfold_definition_i_refines he

/-- `Arms/Infer.lean`'s three spine and telescope callees. -/
theorem inferDeps (hw : Wrappers mode fuel) : InferDeps mode fuel where
  inferSpine := by
    intro d ty acc args i hty hacc hargs
    exact infer_spine_i_refines hw d hty hacc hargs
  inferPis := by
    intro d peel t k fvs stk ht hfvs hstk
    exact infer_pis_i_refines hw d peel k ht hfvs hstk
  inferLams := by
    intro d peel t k fvs stk ht hfvs hstk
    exact infer_lams_i_refines hw d peel k ht hfvs hstk

/-- `Arms/InferIO.lean`'s three callees. -/
theorem inferIODeps (hw : Wrappers mode fuel) : InferIODeps mode fuel where
  inferBody := by
    intro d e io he
    exact infer_body_i_refines hw (inferDeps hw) d io he
  inferSpineIO := by
    intro d t acc args i ht hacc hargs
    exact infer_spine_io_i_refines hw d ht hacc hargs
  ensureSort := by intro d e he; exact ensure_sort_i_refines hw d he

/-- `Arms/Annotate.lean`'s two `Arms/Shared.lean` callees. -/
theorem annotateDeps (hw : Wrappers mode fuel) : AnnotateDeps mode fuel where
  ensureSort := by intro d e he; exact ensure_sort_i_refines hw d he
  inferIOWhnf := by intro d e he; exact infer_io_whnf_i_refines hw d he

/-! ## The seven bodies

Four are the files' own theorems with their `Deps` supplied; three wait on
`Arms/Major.lean` and `Arms/DefEqStruct.lean` (see the module note). -/

-- sorry: `WhnfCoreDeps` and `AppDeps` are mutually unconstructible as stated.
-- `whnf_core_loop_i`, `whnf_core_step_i`, `whnf_app_i` and `beta_peel_i` are
-- one strongly connected component of the Rust block, and the partition put
-- it in *two* files: `AppDeps.whnfCoreLoop` asks for the loop at every budget
-- and `WhnfCoreDeps.whnfApp` asks for the spine at every budget, so neither
-- structure can be built without the other.  The recursion itself is
-- well-founded — loop(n) needs step(n-1) needs whnfApp(n-1) needs loop(n-1) —
-- so the fix is mechanical and is *this task's own* mistake, not either
-- file's: the two files must be merged, or both `Deps` must be indexed by the
-- budget so the discharge can go by induction on it.  Both files are proved
-- (App has one `sorry`, `InstCSize`; WhnfCore has none).
theorem whnf_core_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.whnf_core_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.whnfCoreBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr e)) := sorry

theorem whnf_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.whnf_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.whnfBodyI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) :=
  whnf_body_i_refines hw (whnfDeps hw) d he

theorem infer_body_sim (hw : Wrappers mode fuel) (d : Std.U64) (io : Bool)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_body_i mode fuel st fe d e io)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode) (knotV mode lfe fuel.val io) lfe
        d.val (absExpr e)) :=
  infer_body_i_refines hw (inferDeps hw) d io he

theorem infer_body_io_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_body_io_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.inferBodyIOI (absMode mode)
        (knot mode lfe fuel.val).ioView lfe d.val (absExpr e)) :=
  infer_body_io_i_refines hw (inferIODeps hw) d he

-- sorry: waits on `Arms/DefEqStruct.lean`'s `defeq_struct_i_refines`,
-- `struct_eta_cert_i_refines` and `struct_unit_cert_i_refines`, three of
-- `Arms/DefEq.lean`'s eight `DefEqDeps` fields (the other five have landed).
theorem defeq_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True) (fun st fe => cached.core_c.defeq_body_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.defeqBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr a) (absExpr b)) := sorry

theorem annotate_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.annotate_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) :=
  annotate_body_i_refines hw (annotateDeps hw) d he

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

/-! ## The axiom census

Honest, and the point of the exercise.  **`annotate` is closed**: its body,
its eighteen arms and everything they rest on carry only the three standard
axioms.  The other three assembled bodies carry `sorryAx`, each from a named
finding rather than from an unfinished proof (DESIGN.md, task #55):

* `whnf` — the `nat_op_result` shift-amount deviation, through
  `Arms/Lits.lean`'s `reduce_nat_i`;
* `infer` and `infer_io` — `Statements.lean`'s `Bodies.inferView`, false at
  the three views that are unreachable at `io = true`;

and `whnf_core`/`defeq` are still placeholders here (`Arms/Major.lean`,
`Arms/DefEqStruct.lean`), so `arms` and `knot_spec` inherit `sorryAx` too. -/

/-- info: 'ConRon.Refine.Core.annotate_body_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms annotate_body_sim

/-- info: 'ConRon.Refine.Core.whnf_body_sim' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms whnf_body_sim

/-- info: 'ConRon.Refine.Core.infer_body_sim' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infer_body_sim

/-- info: 'ConRon.Refine.Core.infer_body_io_sim' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infer_body_io_sim

/-- info: 'ConRon.Refine.Core.knot_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms knot_spec

end ConRon.Refine.Core
