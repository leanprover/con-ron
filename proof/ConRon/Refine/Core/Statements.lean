import ConRon.Generated
import ConRon.Refine.State
import ConRon.Refine.FEnv
import ConLeche.Cached.CoreC

/-! # The knot: the twelve statements (CORE_PLAN step 6, Fable)

The six memoising wrappers of `cached/core_c.rs` (`whnf_core`, `whnf`,
`infer`, `defeq`, `annotate`, `infer_io`) and their bodies (`*_body_i`) are
refined against con-leche's `coreKnotI` (`ConLeche/Cached/CoreC.lean:1916`)
and its body functions.  This file holds the *statements* only, bundled as
one proposition indexed by the fuel, so that the induction
(`Refine/Core/Knot.lean`) and the per-arm lemmas (`Refine/Core/Arms/*`) can
be written against a fixed interface.

Conventions (DESIGN.md §3, the ruling of 2026-09-13; task #67): the **full
outcome** through `Refine/State.lean`'s `Out` — exact result on success,
con-leche's own throw at the same *kind* on a mirrored failure, nothing on
the port's own `Native` one and nothing on an Aeneas `fail`; states and
environments through the relations `StateRel`/`FEnvRel`; the Rust wrapper at
`fuel` is con-leche's knot at `fuel` (the Rust probes, runs the body at
`fuel - 1`, inserts — `memoEI`); a Rust body at `fuel` is con-leche's body
applied to the knot at `fuel`.

Fuel exhaustion is *mirrored*: at `fuel = 0` the Rust wrapper throws
`internal "fuel exhausted: …"` and so does `coreKnotI … 0`, at the same step,
so `wrappers_zero` is a real proof now rather than a vacuous one.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-- The Lean knot at `fuel`, for the abstracted mode and environment. -/
abbrev knot (mode : env.CheckMode) (lfe : ConLeche.FEnv) (fuel : Nat) :
    ConLeche.Cached.CoreFnsI :=
  ConLeche.Cached.coreKnotI (absMode mode) lfe fuel

/-- A Rust term-valued knot operation `f` refines a Lean one `g` at every
input **and at every outcome** (`Out`): exact result on success with the
states and environments related and WF preserved, con-leche's own throw at
the same kind on a mirrored failure, nothing on a `Native` one. -/
def RefinesE
    (f : cached.state_c.CState → fenv.FEnv → Std.U64 → expr.Expr →
      Result ((core.result.Result expr.Expr core_types.CheckError) × cached.state_c.CState))
    (g : ConLeche.FEnv → Nat → ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Expr) : Prop :=
  ∀ st fe d e o st',
    StateWF st → FEnvWF fe → ExprWF e →
    f st fe d e = ok (o, st') →
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      Out absExpr ExprWF o st' ((g lfe d.val (absExpr e)).run lst)

/-- The `Bool`-valued twin (`defeq`). -/
def RefinesB
    (f : cached.state_c.CState → fenv.FEnv → Std.U64 → expr.Expr → expr.Expr →
      Result ((core.result.Result Bool core_types.CheckError) × cached.state_c.CState))
    (g : ConLeche.FEnv → Nat → ConLeche.Expr → ConLeche.Expr → ConLeche.Cached.CheckCM Bool) : Prop :=
  ∀ st fe d a b o st',
    StateWF st → FEnvWF fe → ExprWF a → ExprWF b →
    f st fe d a b = ok (o, st') →
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      Out id (fun _ => True) o st' ((g lfe d.val (absExpr a) (absExpr b)).run lst)

/-! ### The two halves at a call site

`RefinesE`/`RefinesB` are *used* in two ways: a successful Rust call gives
con-leche's value and the related state (`.ok`, exactly the pre-task-#67
statement, so that every existing call site reads unchanged but for the
suffix), and a failed one gives con-leche's throw (`.err`). -/

theorem RefinesE.ok {f g} (h : RefinesE f g) (st fe d e r st')
    (hst : StateWF st) (hfe : FEnvWF fe) (he : ExprWF e)
    (hok : f st fe d e = ok (.Ok r, st')) (lst lfe)
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe) :
    ∃ lst', (g lfe d.val (absExpr e)).run lst = .ok (absExpr r, lst')
      ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r :=
  h st fe d e (.Ok r) st' hst hfe he hok lst lfe hrel hfrel

theorem RefinesE.err {f g} (h : RefinesE f g) (st fe d e)
    (ce : core_types.CheckError) (st')
    (hst : StateWF st) (hfe : FEnvWF fe) (he : ExprWF e)
    (hok : f st fe d e = Aeneas.Std.Result.ok (core.result.Result.Err ce, st')) (lst lfe)
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe) :
    ErrSim ce ((g lfe d.val (absExpr e)).run lst) :=
  h st fe d e (.Err ce) st' hst hfe he hok lst lfe hrel hfrel

theorem RefinesB.ok {f g} (h : RefinesB f g) (st fe d a b r st')
    (hst : StateWF st) (hfe : FEnvWF fe) (ha : ExprWF a) (hb : ExprWF b)
    (hok : f st fe d a b = ok (.Ok r, st')) (lst lfe)
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe) :
    ∃ lst', (g lfe d.val (absExpr a) (absExpr b)).run lst = .ok (r, lst')
      ∧ StateRel st' lst' ∧ StateWF st' := by
  obtain ⟨lst', hrun, hrel', hwf', _⟩ :=
    h st fe d a b (.Ok r) st' hst hfe ha hb hok lst lfe hrel hfrel
  exact ⟨lst', hrun, hrel', hwf'⟩

theorem RefinesB.err {f g} (h : RefinesB f g) (st fe d a b)
    (ce : core_types.CheckError) (st')
    (hst : StateWF st) (hfe : FEnvWF fe) (ha : ExprWF a) (hb : ExprWF b)
    (hok : f st fe d a b = Aeneas.Std.Result.ok (core.result.Result.Err ce, st')) (lst lfe)
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe) :
    ErrSim ce ((g lfe d.val (absExpr a) (absExpr b)).run lst) :=
  h st fe d a b (.Err ce) st' hst hfe ha hb hok lst lfe hrel hfrel

/-- The six wrappers at `fuel` refine the knot at `fuel`. -/
structure Wrappers (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  whnfCore : RefinesE (cached.core_c.whnf_core mode fuel)
    (fun lfe => (knot mode lfe fuel.val).whnfCore)
  whnf : RefinesE (cached.core_c.whnf mode fuel)
    (fun lfe => (knot mode lfe fuel.val).whnf)
  infer : RefinesE (cached.core_c.infer mode fuel)
    (fun lfe => (knot mode lfe fuel.val).infer)
  defeq : RefinesB (cached.core_c.defeq mode fuel)
    (fun lfe => (knot mode lfe fuel.val).defeq)
  annotate : RefinesE (cached.core_c.annotate mode fuel)
    (fun lfe => (knot mode lfe fuel.val).annotate)
  inferIO : RefinesE (cached.core_c.infer_io mode fuel)
    (fun lfe => (knot mode lfe fuel.val).inferIO)

/-- The six bodies at `fuel` refine the Lean bodies applied to the knot at
`fuel` (a body's recursive calls are wrappers at the same fuel; the
decrement lives in the wrapper). -/
structure Bodies (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  whnfCore : RefinesE (cached.core_c.whnf_core_body_i mode fuel)
    (fun lfe => ConLeche.Cached.whnfCoreBodyI (absMode mode) (knot mode lfe fuel.val) lfe)
  whnf : RefinesE (cached.core_c.whnf_body_i mode fuel)
    (fun lfe => ConLeche.Cached.whnfBodyI (knot mode lfe fuel.val) lfe)
  /-- Task #61: `infer_body_i` **is** `inferBodyI` at the knot itself.  It
  used to carry con-leche's `ioView` as a `Bool` (task #18, deviation 4) and
  the statement had a second field for `io = true`, which was *false*: the
  Rust's `.app`/`.forallE`/`.lam` clauses called the full-grade wrappers
  where `inferBodyI` at `ioView` calls the io slot.  Those three views are
  overridden by `inferBodyIOI`, so the flag only ever mattered at `.proj`,
  which now has its own clause in `infer_body_io_i`. -/
  infer : RefinesE (cached.core_c.infer_body_i mode fuel)
    (fun lfe => ConLeche.Cached.inferBodyI (absMode mode) (knot mode lfe fuel.val) lfe)
  defeq : RefinesB (cached.core_c.defeq_body_i mode fuel)
    (fun lfe => ConLeche.Cached.defeqBodyI (absMode mode) (knot mode lfe fuel.val) lfe)
  annotate : RefinesE (cached.core_c.annotate_body_i mode fuel)
    (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe)
  inferIO : RefinesE (cached.core_c.infer_body_io_i mode fuel)
    (fun lfe => ConLeche.Cached.inferBodyIOI (absMode mode) (knot mode lfe fuel.val).ioView lfe)

/-- What the induction carries: at `fuel`, the wrappers refine the knot and
the bodies refine the bodies.  `Knot.lean` proves
`Wrappers mode 0` (every wrapper fails at fuel 0: nothing to show),
`Bodies mode fuel → Wrappers mode (fuel + 1)` (the memo argument, once per
wrapper), and `Wrappers mode fuel → Bodies mode fuel` (the arms). -/
def KnotSpec (mode : env.CheckMode) (fuel : Std.U64) : Prop :=
  Wrappers mode fuel ∧ Bodies mode fuel

end ConRon.Refine.Core
