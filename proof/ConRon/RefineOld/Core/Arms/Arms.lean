/-
# The arms, assembled (task #55, closed by task #61; `CORE_PLAN.md` step 6)

`Arms/Shape.lean` fixes the shape, the sixteen files of `Arms/` prove the
helpers of `cached/core_c.rs`'s `partial_fixpoint` block one group each, and
this file ties them together:

* each file's `<File>Deps` — the statements it had to assume of the helpers
  living in *another* file, so that the sixteen could be proved in parallel —
  is discharged here from those files' own theorems;
* the six body lemmas become `Bodies mode fuel` through
  `RefinesE.ofSim`/`RefinesB.ofSim`;
* `arms : ∀ fuel, Wrappers mode fuel → Bodies mode fuel`, which is what
  `Refine/Core/Knot.lean`'s `knot_induction` (task #53) consumes;
* `knot_spec : ∀ fuel, KnotSpec mode fuel` — the twelve statements at every
  fuel, and the point of `CORE_PLAN.md` step 6.

## The discharge order

The partition is acyclic *at the function level*, and the discharges below
follow that order exactly, each one an `exact` from the owning file's theorem:

```
Arms/Certs.lean, Arms/Lits.lean, Arms/Shared.lean      no Deps at all
Arms/App.lean's pi_residual_m, fab_scope_ok_i          no Deps either
  → MajorDeps       → Arms/Major.lean
    → IotaDeps      → Arms/Iota.lean
      → AppDeps     → Arms/App.lean's spine and projection certificate
        → WhnfCoreDeps n (one induction on the budget)  → the whnf_core body
DefEqStructDepsA    → struct_eta_cert_i, struct_unit_cert_i
  → DefEqDepsA      → defeq_apps_i, defeq_binders_i, stuck_irrel_i
    → DefEqStructDeps → defeq_struct_i
      → DefEqDeps   → the defeq body
```

**Task #61 closed the two packaging cycles task #55 left.**

* `whnf_core_loop_i`, `whnf_core_step_i`, `whnf_app_i` and `beta_peel_i` are
  **one** strongly connected component of the Rust block, and the partition put
  it in two files whose `Deps` fields were `∀`-quantified over the budget, so
  neither structure could be built.  The recursion is well founded in the
  budget — loop(n+1) is step(n), step(n) calls whnfApp(n) and whnfCoreProj(n),
  and both of those call loop(n) — so `Arms/WhnfCore.lean`'s `WhnfCoreDeps` is
  now *indexed* by the budget, `Arms/App.lean`'s `AppDeps` dropped the loop
  field in favour of the explicit `KSim` hypothesis its `*_of_loop` lemmas
  already took, and `whnfCoreLoopSim` below is the one induction that ties the
  component together, here where both files are in scope.
* `DefEq`/`DefEqStruct` was never a cycle in the code, only in the packaging:
  each theorem asked for the *whole* other file's record.  Splitting both
  records along the call order above (`DefEqDepsA`, `DefEqStructDepsA`) closes
  it, with no statement changed.

## What is closed

All six bodies, `arms` and `knot_spec`: `#print axioms` below is `[propext,
Classical.choice, Quot.sound]` for every one of them.
-/
import ConRon.RefineOld.Core.Knot
import ConRon.RefineOld.Core.Arms.Shape
import ConRon.RefineOld.Core.Arms.Shared
import ConRon.RefineOld.Core.Arms.Lits
import ConRon.RefineOld.Core.Arms.Certs
import ConRon.RefineOld.Core.Arms.Major
import ConRon.RefineOld.Core.Arms.Iota
import ConRon.RefineOld.Core.Arms.App
import ConRon.RefineOld.Core.Arms.WhnfCore
import ConRon.RefineOld.Core.Arms.Whnf
import ConRon.RefineOld.Core.Arms.InferSpine
import ConRon.RefineOld.Core.Arms.InferSpineIO
import ConRon.RefineOld.Core.Arms.InferTele
import ConRon.RefineOld.Core.Arms.Infer
import ConRon.RefineOld.Core.Arms.InferIO
import ConRon.RefineOld.Core.Arms.DefEqStruct
import ConRon.RefineOld.Core.Arms.DefEq
import ConRon.RefineOld.Core.Arms.Annotate

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-! ## The lower-tier ingredients

`Arms/Certs.lean`'s `StateCOpen` is the pair of `cached::state_c` facts
`Refine/StateC.lean` leaves open.  `Arms/Bridge.lean` discharged the first at
task #55; task #61 folded the second into `Refine/State.lean`'s `StateRel`,
so the record is now a two-line `exact`. -/

/-- `Arms/Certs.lean`'s two `cached::state_c` ingredients. -/
theorem stateCOpen : StateCOpen where
  instList := instantiateListRefines
  instSize := fun _ _ hrel => hrel.instCSize

/-! ## The `Deps` discharges

Each is an `exact` from the owning file's theorem — the check that sixteen
agents' statements, written in parallel against `Shape.lean` alone, agree. -/

/-- `Arms/Whnf.lean`'s two `Arms/Lits.lean` callees. -/
theorem whnfDeps (hw : Wrappers mode fuel) : WhnfDeps mode fuel where
  reduceNat := by intro d e he; exact reduce_nat_i_refines hw d he
  unfoldDefinition := by intro e he; exact unfold_definition_i_refines he

/-- `Arms/Major.lean`'s callees: five in `Arms/Certs.lean`, the two
`Deps`-free helpers of `Arms/App.lean`, and `Arms/Shared.lean`'s. -/
theorem majorDeps (hw : Wrappers mode fuel) : MajorDeps mode fuel where
  proofIrrel := by intro d a b ha hb; exact proof_irrel_i_refines hw d ha hb
  structEtaCertWith := by
    intro d a b wtb ha hb hwtb
    exact struct_eta_cert_with_i_refines stateCOpen hw d ha hb hwtb
  iotaCerts := by
    intro d lic ty args hty hargs
    exact iota_certs_i_refines stateCOpen hw d lic hty hargs
  projNodes := by
    intro t b nf res ht hb h
    obtain ⟨habs, hwf⟩ := proj_nodes_i_refines ht hb res h
    exact ⟨fun lst => by rw [← habs]; rfl, hwf⟩
  projApps := by
    intro fe lfe t us targs b nf res hfe hfrel ht hus htargs hb h
    obtain ⟨habs, hwf⟩ := proj_apps_i_refines hfe hfrel ht hus htargs hb res h
    exact ⟨fun lst => by rw [← habs]; rfl, hwf⟩
  fabScopeOk := by
    intro fab major d c hfab hmajor h
    -- `Arms/App.lean` brackets the three conjuncts to the right and the field
    -- to the left; `&&` is associative.  (The two spellings of the bound used
    -- to differ — the cached twin against the spec walk — and this step also
    -- carried `Expr.looseBVarsBounded_spec`; con-leche task #285 merged the
    -- twin away, so one name is left and the rewrite is gone with it.)
    have := (fab_scope_ok_i_refines hfab hmajor c h).1
    simpa [Bool.and_assoc] using this
  inferIOWhnf := by intro d e he; exact infer_io_whnf_i_refines hw d he

/-- `Arms/Iota.lean`'s callees: two in `Arms/Certs.lean`, `pi_residual_m`
(`Arms/App.lean`, `Deps`-free) and the two `Arms/Major.lean` entry points. -/
theorem iotaDeps (hw : Wrappers mode fuel) : IotaDeps mode fuel where
  defEqList := by intro d xs ys hxs hys; exact def_eq_list_i_refines hw d hxs hys
  iotaCerts := by
    intro d lic ty args hty hargs
    exact iota_certs_i_refines stateCOpen hw d lic hty hargs
  piResidual := by
    intro e args he hargs r h
    obtain ⟨habs, hwf⟩ := pi_residual_m_refines he hargs r h
    refine ⟨?_, hwf⟩
    show (pure (Option.map absExpr r) : ConLeche.Cached.CheckCM _) = _
    rw [habs, ConLeche.Cached.piResidualM]
  litMajorToCtor := by intro d e he; exact lit_major_to_ctor_i_refines hw d he
  majorToCtor := by
    intro d rn rules major hrules hmajor
    exact major_to_ctor_i_refines hw (majorDeps hw) d rn hrules hmajor

/-- `Arms/App.lean`'s callees: three in `Arms/Iota.lean`, one in
`Arms/Certs.lean`.  The fourth, `whnf_core_loop_i`, is the other half of
`App`'s own strongly connected component and is **not** a field (task #61):
`whnfCoreLoopSim` below supplies it as a `KSim`. -/
theorem appDeps (hw : Wrappers mode fuel) : AppDeps mode fuel where
  iotaArityOk := by
    intro fe lfe e b hfe hfrel he h
    exact (iota_arity_ok_refines hfe hfrel he b h).1
  iotaRec := by intro d e he; exact iota_rec_i_refines hw (iotaDeps hw) d he
  isCtorStored := by
    intro fe lfe c b hfe hfrel hc h
    exact (is_ctor_stored_i_refines hfe hfrel hc b h).1
  iotaCerts := by
    intro d lic ty args hty hargs
    exact iota_certs_i_refines stateCOpen hw d lic hty hargs

/-! ## The `whnf_core` component: one induction on the budget

`Arms/WhnfCore.lean` names the `.proj` continuation `whnfCoreProjArmI` and
`Arms/App.lean` names it `whnfCoreProjI`; both are the same subterm of
`whnfCoreStepI`, so each is the other by `rfl`. -/

/-- The two arm files' names for `whnfCoreStepI`'s `.proj` continuation are
the same action — `rfl`, so the `WhnfCoreDeps.whnfCoreProj` field below is
`Arms/App.lean`'s theorem with nothing in between. -/
theorem whnfCoreProjArmI_eq :
    @WhnfCore.whnfCoreProjArmI = @whnfCoreProjI := rfl

/-- **The strongly connected component, untied.**  `whnf_core_loop_i` at every
budget, by induction on the budget: the loop at `n + 1` is the step at `n`,
whose two knot-free callees — `whnf_app_i` and `whnf_core_proj_i`, both
`Arms/App.lean`'s — run the loop at `n` as their continuation. -/
private theorem whnfCoreLoopSim (hw : Wrappers mode fuel) :
    ∀ (N : Nat) (d n : Std.U64), n.val ≤ N →
      KSim mode fuel d n (fun lfe => ConLeche.Cached.whnfCoreLoopI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val n.val) := by
  intro N
  induction N with
  | zero =>
    intro d n hn e he
    exact whnf_core_loop_i_refines hw d n (fun m hm => absurd hm (by omega)) he
  | succ N ih =>
    intro d n hn e he
    refine whnf_core_loop_i_refines hw d n (fun m hm => ?_) he
    have hmN : m.val ≤ N := by omega
    exact
      { whnfApp := fun d' _f _args _i hf hargs =>
          whnf_app_of_loop hw (appDeps hw) d' m (ih d' m hmN) hf hargs
        whnfCoreProj := fun d' _sn _i _e2 hsn he2 =>
          whnf_core_proj_of_loop (appDeps hw) d' m (ih d' m hmN) hsn he2
        projLitToCtor := fun d' _e' he' => proj_lit_to_ctor_i_refines hw d' he' }

/-- `Arms/WhnfCore.lean`'s callees at every budget. -/
theorem whnfCoreDeps (hw : Wrappers mode fuel) (n : Std.U64) :
    WhnfCoreDeps mode fuel n where
  whnfApp := fun d _f _args _i hf hargs =>
    whnf_app_of_loop hw (appDeps hw) d n (whnfCoreLoopSim hw n.val d n le_rfl) hf hargs
  whnfCoreProj := fun d _sn _i _e2 hsn he2 =>
    whnf_core_proj_of_loop (appDeps hw) d n
      (whnfCoreLoopSim hw n.val d n le_rfl) hsn he2
  projLitToCtor := fun d _e he => proj_lit_to_ctor_i_refines hw d he

/-! ## The `defeq` component, in call order

`Arms/DefEq.lean` and `Arms/DefEqStruct.lean` each *name* the three arms of
`defeqStepI` they share — `defeqAppsFrag`/`defeqAppsL`,
`defeqBindersFrag`/`defeqBindersL`, `defeqStructFrag`/`defeqStructL` — because
each file needs the name on its own side of the call.  The two transcriptions
are the same subterm of `defeqStepI`, so each is the other by `rfl`; these
three identities are what says so, and nothing is assumed. -/

theorem defeqAppsL_eq : @defeqAppsL = @DefEq.defeqAppsFrag := rfl

theorem defeqStructL_eq : @defeqStructL = @DefEq.defeqStructFrag := rfl

theorem defeqBindersL_eq (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (depth : Nat) (ty₁ body₁ : ConLeche.Expr)
    (m₁ : ConLeche.BinderMeta) (ty₂ body₂ : ConLeche.Expr)
    (m₂ : ConLeche.BinderMeta) (isForall : Bool) :
    defeqBindersL lmode r lfe depth ty₁ body₁ m₁ ty₂ body₂ m₂ isForall
      = DefEq.defeqBindersFrag lmode r depth
          (if isForall then "sort-annotation mismatch (defeq-forall)"
            else "sort-annotation mismatch (defeq-lam)")
          ty₁ body₁ m₁ ty₂ body₂ m₂ := rfl

/-- `Arms/DefEqStruct.lean`'s two `Arms/Certs.lean` callees — everything
`struct_eta_cert_i` and `struct_unit_cert_i` need. -/
theorem defEqStructDepsA (hw : Wrappers mode fuel) : DefEqStructDepsA mode fuel where
  structEtaCertWith := by
    intro d a b wtb ha hb hwtb
    exact struct_eta_cert_with_i_refines stateCOpen hw d ha hb hwtb
  iotaCerts := by
    intro d lic ty args hty hargs
    exact iota_certs_i_refines stateCOpen hw d lic hty hargs

/-- `Arms/DefEq.lean`'s callees other than `defeq_struct_i`: the two
`Arms/DefEqStruct.lean` certificates, three in `Arms/Certs.lean` and two in
`Arms/Lits.lean`. -/
theorem defEqDepsA (hw : Wrappers mode fuel) : DefEqDepsA mode fuel where
  structEtaCert := by
    intro d a b ha hb
    exact struct_eta_cert_i_refines hw (defEqStructDepsA hw) d ha hb
  structUnitCert := by
    intro d a b ha hb
    exact struct_unit_cert_i_refines hw (defEqStructDepsA hw) d ha hb
  defEqList := by intro d xs ys hxs hys; exact def_eq_list_i_refines hw d hxs hys
  propLegs := by intro d ta b hta hb; exact prop_legs_i_refines hw d hta hb
  proofIrrel := by intro d a b ha hb; exact proof_irrel_i_refines hw d ha hb
  reduceNat := by intro d e he; exact reduce_nat_i_refines hw d he
  unfoldDefinition := by intro e he; exact unfold_definition_i_refines he

/-- `Arms/DefEqStruct.lean`'s callees, in full: its two `Arms/Certs.lean` ones
and the three of `Arms/DefEq.lean` that do not go through `defeq_struct_i`. -/
theorem defEqStructDeps (hw : Wrappers mode fuel) : DefEqStructDeps mode fuel where
  toDefEqStructDepsA := defEqStructDepsA hw
  defeqApps := by
    intro d a b ha hb
    exact defeq_apps_i_refines hw (defEqDepsA hw) d ha hb
  defeqBinders := by
    intro d isForall t1 b1 t2 b2 m1 m2 ht1 hb1 hm1 ht2 hb2 hm2
    exact defeq_binders_i_refines hw d isForall ht1 hb1 hm1 ht2 hb2 hm2
  stuckIrrel := by
    intro d a b ha hb
    exact stuck_irrel_i_refines (defEqDepsA hw) d ha hb

/-- `Arms/DefEq.lean`'s record, in full. -/
theorem defEqDeps (hw : Wrappers mode fuel) : DefEqDeps mode fuel where
  toDefEqDepsA := defEqDepsA hw
  defeqStruct := by
    intro d a b ha hb
    exact defeq_struct_i_refines hw (defEqStructDeps hw) d ha hb

/-! ## The `infer` cluster -/

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

/-- `Arms/InferIO.lean`'s four callees. -/
theorem inferIODeps (hw : Wrappers mode fuel) : InferIODeps mode fuel where
  inferBody := by
    intro d e he
    exact infer_body_i_refines hw (inferDeps hw) d he
  inferProj := by
    intro d sn i pe hsn hpe
    exact infer_proj_i_refines hw d true hsn hpe
  inferSpineIO := by
    intro d t acc args i ht hacc hargs
    exact infer_spine_io_i_refines hw d ht hacc hargs
  ensureSort := by intro d e he; exact ensure_sort_i_refines hw d he

/-- `Arms/Annotate.lean`'s two `Arms/Shared.lean` callees. -/
theorem annotateDeps (hw : Wrappers mode fuel) : AnnotateDeps mode fuel where
  ensureSort := by intro d e he; exact ensure_sort_i_refines hw d he
  inferIOWhnf := by intro d e he; exact infer_io_whnf_i_refines hw d he

/-! ## The six bodies -/

theorem whnf_core_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.whnf_core_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.whnfCoreBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr e)) :=
  whnf_core_body_i_refines hw (whnfCoreDeps hw) d he

theorem whnf_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.whnf_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.whnfBodyI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) :=
  whnf_body_i_refines hw (whnfDeps hw) d he

theorem infer_body_sim (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr e)) :=
  infer_body_i_refines hw (inferDeps hw) d he

theorem infer_body_io_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_body_io_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.inferBodyIOI (absMode mode)
        (knot mode lfe fuel.val).ioView lfe d.val (absExpr e)) :=
  infer_body_io_i_refines hw (inferIODeps hw) d he

theorem defeq_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True) (fun st fe => cached.core_c.defeq_body_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.defeqBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr a) (absExpr b)) :=
  defeq_body_i_refines hw (defEqDeps hw) d ha hb

theorem annotate_body_sim (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.annotate_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) :=
  annotate_body_i_refines hw (annotateDeps hw) d he

end

/-! ## `Bodies`, `arms` and the knot -/

/-- The arms: given the six wrappers at `fuel`, the six bodies at `fuel`. -/
theorem arms {mode : env.CheckMode} (fuel : Std.U64) (hw : Wrappers mode fuel) :
    Bodies mode fuel where
  whnfCore := RefinesE.ofSim fun d _e he => whnf_core_body_sim hw d he
  whnf := RefinesE.ofSim fun d _e he => whnf_body_sim hw d he
  infer := RefinesE.ofSim fun d _e he => infer_body_sim hw d he
  defeq := RefinesB.ofSim fun d _a _b ha hb => defeq_body_sim hw d ha hb
  annotate := RefinesE.ofSim fun d _e he => annotate_body_sim hw d he
  inferIO := RefinesE.ofSim fun d _e he => infer_body_io_sim hw d he

/-- **The knot** (`CORE_PLAN.md` step 6): at every fuel, the six wrappers
refine `coreKnotI … fuel` and the six bodies refine con-leche's bodies at
that knot.  Task #53's `knot_induction` plus task #55's `arms`, closed by
task #61. -/
theorem knot_spec {mode : env.CheckMode} (fuel : Std.U64) : KnotSpec mode fuel :=
  knot_induction (fun f hw => arms f hw) fuel

/-! ## The axiom census

The point of the exercise, and it is machine-checked: every body, `arms` and
`knot_spec` rest on Lean's own three axioms and nothing else — no `sorryAx`,
nothing from Aeneas's library. -/

/-- info: 'ConRon.Refine.Core.whnf_core_body_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms whnf_core_body_sim

/-- info: 'ConRon.Refine.Core.whnf_body_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms whnf_body_sim

/-- info: 'ConRon.Refine.Core.infer_body_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infer_body_sim

/-- info: 'ConRon.Refine.Core.infer_body_io_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infer_body_io_sim

/-- info: 'ConRon.Refine.Core.defeq_body_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms defeq_body_sim

/-- info: 'ConRon.Refine.Core.annotate_body_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms annotate_body_sim

/-- info: 'ConRon.Refine.Core.arms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arms

/-- info: 'ConRon.Refine.Core.knot_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms knot_spec

end ConRon.Refine.Core
