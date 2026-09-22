/-
# The arms of the knot: the shared shape (task #55, `CORE_PLAN.md` step 6)

`Refine/Core/Statements.lean` states the twelve propositions the induction
carries: `Wrappers mode fuel` (the six memoising entry points refine
con-leche's `coreKnotI … fuel`) and `Bodies mode fuel` (the seven bodies
refine con-leche's bodies applied to that knot).  Task #53 proves the
skeleton — `Wrappers mode 0`, `Bodies mode fuel → Wrappers mode (fuel+1)`,
and the induction.  This directory proves the remaining implication,

```
arms : ∀ fuel, Wrappers mode fuel → Bodies mode fuel
```

— for each body, the arms of its `match`: every helper of
`crates/con-ron-core/src/cached/core_c.rs`'s big `partial_fixpoint` block
against its cited con-leche twin (`ConLeche/Cached/CoreC.lean`), with the
six wrappers available throughout as the `Wrappers mode fuel` hypothesis.

## The shape every helper lemma has

A helper is a Rust function
`f mode fuel st fe <args> : Result (Result α CheckError × CState)` whose
con-leche twin is `g (knot …) lfe <args'> : CheckCM β`.  Its refinement is
`Sim A WF (fun st fe => f mode fuel st fe args) (fun lfe => g … args')`
where `A : α → β` is the value abstraction (`absExpr`, `absLevel`, `id`, …)
and `WF` the well-formedness the caller may rely on downstream.  `Sim`
unfolds to exactly the `CORE_PLAN` shape:

```
f st fe = ok (o, st') → ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
  Out A WF o st' ((g lfe).run lst)
```

— the **full outcome** (`Refine/State.lean`'s `Out`, DESIGN.md §3's ruling of
2026-09-13): exact result on success, con-leche's own throw at the same kind
on a mirrored failure, nothing on the port's own `Native` one — and the input
well-formedness (`ExprWF` on the term arguments, …) quantified *outside*
`Sim` by the lemma itself, so that a caller discharges it at the call site
from what it knows.

**How a proof is shaped.**  `SimS.apply`/`Sim.apply` are unchanged, so every
*call site* reads as it did; what a proof of a `Sim` now adds is the error
half of each case.  Three moves cover it:

* a bind whose sub-computation threw — `Sim.apply_err` gives
  `ErrSim e (sub.run lst)`, and `ErrSim.bind` carries it through the rest of
  the con-leche `do` block (`Out.bind` is the same move at `Out`);
* an explicit `throw` arm — the guard has already been shown to agree in the
  accept direction, so rewriting the con-leche side to its `throw` and
  applying `ErrSim.invalid`/`.internal`/`.notImplemented` closes it;
* a `Native` arm — `ErrSim.native` closes it without naming con-leche at all.

`SimS.mk'` splits a proof into its two halves where they do not share the
case analysis.

Three shapes cover the block: `Sim` (state and environment threaded),
`SimS` (state only — the helpers con-leche writes without an `FEnv`), and
`SimP` (neither: a pure `Result`, an equation).  `Sim` is `SimS` under the
environment relation, so a lemma proved in either form is usable in the
other (`Sim.mk`, `Sim.toSimS`).

## What a helper may assume

* the six wrappers, through `Wrappers mode fuel` — `RefinesE`/`RefinesB`,
  which `Wrappers.whnfCoreSim`, … re-expose in `Sim` form;
* every lower tier: `Refine/State.lean`'s probe/insert lemmas,
  `Refine/StateC.lean`'s `*M` wrappers, `Refine/ExprOpsC*.lean`'s cached
  operations, task #49's `CoreK*`/`PropRead` leaves;
* the helper lemmas of the files it depends on (the partition in
  `Arms/Arms.lean` is acyclic once the four genuinely mutually recursive
  groups are each kept in one file).
-/
import ConRon.RefineOld.Core.Statements
import ConRon.RefineOld.StateC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! ## The monad plumbing

`CheckCM = StateT CState (Except CheckError)`: a con-leche action's `run` is
an `Except`, `pure` is `Except.ok`.  This is `Refine/StateC.lean`'s set,
re-exported for the arms. -/

/-- `pure` in `Except` is `ok`. -/
@[local simp] theorem except_pure' {E A : Type} (a : A) :
    (pure a : Except E A) = .ok a := rfl

attribute [local simp] StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-! ## The three shapes -/

/-- The core notion: a Rust state-passing computation `f` refines the
con-leche action `g` **at every outcome**.  `A` abstracts the returned value,
`WF` is what the caller may rely on about it. -/
def SimS {α β : Type} (A : α → β) (WF : α → Prop)
    (f : cached.state_c.CState →
      Result ((core.result.Result α core_types.CheckError) × cached.state_c.CState))
    (g : ConLeche.Cached.CheckCM β) : Prop :=
  ∀ st o st', StateWF st → f st = Aeneas.Std.Result.ok (o, st') →
    ∀ lst, StateRel st lst → Out A WF o st' (g.run lst)

/-- The same with the environment threaded: `Refine/FEnv.lean`'s `FEnvRel`
relates the Rust `FEnv` to con-leche's, and con-leche reads it only through
`find?`/`findProj?`. -/
def Sim {α β : Type} (A : α → β) (WF : α → Prop)
    (f : cached.state_c.CState → fenv.FEnv →
      Result ((core.result.Result α core_types.CheckError) × cached.state_c.CState))
    (g : ConLeche.FEnv → ConLeche.Cached.CheckCM β) : Prop :=
  ∀ fe lfe, FEnvWF fe → FEnvRel fe lfe → SimS A WF (fun st => f st fe) (g lfe)

/-- The pure shape: a Rust computation that touches neither state nor
environment is a plain equation against its con-leche value. -/
def SimP {α β : Type} (A : α → β) (WF : α → Prop)
    (f : Result α) (b : β) : Prop :=
  ∀ r, f = ok r → A r = b ∧ WF r

/-! ## Moving between the shapes -/

theorem Sim.mk {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : ∀ fe lfe, FEnvWF fe → FEnvRel fe lfe → SimS A WF (fun st => f st fe) (g lfe)) :
    Sim A WF f g := h

theorem Sim.toSimS {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : Sim A WF f g) {fe lfe} (hfe : FEnvWF fe) (hrel : FEnvRel fe lfe) :
    SimS A WF (fun st => f st fe) (g lfe) := h fe lfe hfe hrel

/-- Unfolding: what a `SimS` gives at one call site **that succeeded**.  This
is the pre-task-#67 statement verbatim, so that no existing call site
changes. -/
theorem SimS.apply {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : SimS A WF f g) {st r st' lst} (hwf : StateWF st)
    (hok : f st = Aeneas.Std.Result.ok (.Ok r, st')) (hrel : StateRel st lst) :
    ∃ lst', g.run lst = .ok (A r, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r :=
  h st (.Ok r) st' hwf hok lst hrel

/-- What a `SimS` gives at one call site **that threw**: con-leche throws too,
at the same kind — unless the error is the port's own `Native`, when `ErrSim`
is vacuous. -/
theorem SimS.apply_err {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : SimS A WF f g) {st st' lst} {e : core_types.CheckError} (hwf : StateWF st)
    (hok : f st = Aeneas.Std.Result.ok (.Err e, st')) (hrel : StateRel st lst) :
    ErrSim e (g.run lst) :=
  h st (.Err e) st' hwf hok lst hrel

/-- Unfolding: what a `Sim` gives at one call site. -/
theorem Sim.apply {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : Sim A WF f g) {st fe r st' lst lfe} (hwf : StateWF st) (hfe : FEnvWF fe)
    (hok : f st fe = Aeneas.Std.Result.ok (.Ok r, st')) (hrel : StateRel st lst)
    (hfrel : FEnvRel fe lfe) :
    ∃ lst', (g lfe).run lst = .ok (A r, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r :=
  h fe lfe hfe hfrel st (.Ok r) st' hwf hok lst hrel

/-- The failure half at one call site. -/
theorem Sim.apply_err {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : Sim A WF f g) {st fe st' lst lfe} {e : core_types.CheckError}
    (hwf : StateWF st) (hfe : FEnvWF fe)
    (hok : f st fe = Aeneas.Std.Result.ok (.Err e, st')) (hrel : StateRel st lst)
    (hfrel : FEnvRel fe lfe) :
    ErrSim e ((g lfe).run lst) :=
  h fe lfe hfe hfrel st (.Err e) st' hwf hok lst hrel

/-- **Building a `SimS` from its two halves**, for the proofs where the
success and failure cases do not share a case analysis. -/
theorem SimS.mk' {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (hok : ∀ st r st', StateWF st → f st = Aeneas.Std.Result.ok (.Ok r, st') →
      ∀ lst, StateRel st lst →
        ∃ lst', g.run lst = .ok (A r, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r)
    (herr : ∀ st (e : core_types.CheckError) st', StateWF st →
      f st = Aeneas.Std.Result.ok (.Err e, st') →
      ∀ lst, StateRel st lst → ErrSim e (g.run lst)) :
    SimS A WF f g := by
  intro st o st' hwf h lst hrel
  cases o with
  | Ok r => exact hok st r st' hwf h lst hrel
  | Err e => exact herr st e st' hwf h lst hrel

/-- The same for `Sim`. -/
theorem Sim.mk'' {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (hok : ∀ fe lfe, FEnvWF fe → FEnvRel fe lfe → ∀ st r st', StateWF st →
      f st fe = Aeneas.Std.Result.ok (.Ok r, st') → ∀ lst, StateRel st lst →
        ∃ lst', (g lfe).run lst = .ok (A r, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r)
    (herr : ∀ fe lfe, FEnvWF fe → FEnvRel fe lfe →
      ∀ st (e : core_types.CheckError) st', StateWF st →
        f st fe = Aeneas.Std.Result.ok (.Err e, st') → ∀ lst, StateRel st lst →
          ErrSim e ((g lfe).run lst)) :
    Sim A WF f g := fun fe lfe hfe hfrel =>
  SimS.mk' (hok fe lfe hfe hfrel) (herr fe lfe hfe hfrel)

/-! ## The `RunOk` introduction forms (task #69's prerequisite (4))

`Refine/AUTOMATION.md` measured that a conclusion about a run must not be an
existential for `grind` to reach it.  The idiom itself is **not adopted** —
task #70 is diagnosing its elaboration cost — but the shape is free to carry,
because it is purely additive: `Sim`/`SimS` keep their statements and every
existing proof and call site stands; what these add is an introduction rule
that leaves a `RunOk` goal. -/

theorem SimS.ofRun {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : ∀ st r st', StateWF st → f st = Aeneas.Std.Result.ok (.Ok r, st') →
      ∀ lst, StateRel st lst →
        RunOk (g.run lst) (fun v lst' => v = A r ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r))
    (herr : ∀ st (e : core_types.CheckError) st', StateWF st →
      f st = Aeneas.Std.Result.ok (.Err e, st') →
      ∀ lst, StateRel st lst →
        ∀ k, absErrKind e = some k → RunErr (g.run lst) (fun le => lErrKind le = k)) :
    SimS A WF f g := by
  refine SimS.mk' (fun st r st' hwf hok lst hrel => ?_)
    (fun st e st' hwf hok lst hrel => ErrSim.ofRunErr (herr st e st' hwf hok lst hrel))
  exact Out.dest (Out.ofRun (h st r st' hwf hok lst hrel))

theorem Sim.ofRun {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : ∀ fe lfe, FEnvWF fe → FEnvRel fe lfe → ∀ st r st', StateWF st →
      f st fe = Aeneas.Std.Result.ok (.Ok r, st') → ∀ lst, StateRel st lst →
        RunOk ((g lfe).run lst)
          (fun v lst' => v = A r ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r))
    (herr : ∀ fe lfe, FEnvWF fe → FEnvRel fe lfe →
      ∀ st (e : core_types.CheckError) st', StateWF st →
        f st fe = Aeneas.Std.Result.ok (.Err e, st') → ∀ lst, StateRel st lst →
          ∀ k, absErrKind e = some k →
            RunErr ((g lfe).run lst) (fun le => lErrKind le = k)) :
    Sim A WF f g := fun fe lfe hfe hfrel =>
  SimS.ofRun (h fe lfe hfe hfrel) (herr fe lfe hfe hfrel)

/-- The con-leche `run` of a bind, unconditionally (`AUTOMATION.md`: the
conditional spelling never fires, its right-hand side having variables outside
the pattern). -/
theorem run_bind_eq {α β : Type} (x : ConLeche.Cached.CheckCM α)
    (f : α → ConLeche.Cached.CheckCM β) (lst : ConLeche.Cached.CState) :
    (x >>= f).run lst = (x.run lst >>= fun p => (f p.1).run p.2) := rfl

theorem run_pure_eq {α : Type} (a : α) (lst : ConLeche.Cached.CState) :
    (pure a : ConLeche.Cached.CheckCM α).run lst = .ok (a, lst) := rfl

/-! ## The wrappers in `Sim` form

`Wrappers mode fuel` is stated with `RefinesE`/`RefinesB` (the shape the
induction of `Knot.lean` wants); an arm calls a wrapper at one argument
list, which is what these five re-expose. -/

section
variable {mode : env.CheckMode} {fuel : Std.U64}

theorem RefinesE.toSim {f g} (h : RefinesE f g) (d : Std.U64) {e : expr.Expr}
    (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => f st fe d e)
      (fun lfe => g lfe d.val (absExpr e)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  exact h st fe d e o st' hwf hfe he hok lst lfe hrel hfrel

theorem RefinesB.toSim {f g} (h : RefinesB f g) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True) (fun st fe => f st fe d a b)
      (fun lfe => g lfe d.val (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  exact h st fe d a b o st' hwf hfe ha hb hok lst lfe hrel hfrel

/-- `r.whnfCore depth e` at one call site. -/
theorem Wrappers.whnfCoreSim (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.whnf_core mode fuel st fe d e)
      (fun lfe => (knot mode lfe fuel.val).whnfCore d.val (absExpr e)) :=
  hw.whnfCore.toSim d he

/-- `r.whnf depth e` at one call site. -/
theorem Wrappers.whnfSim (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.whnf mode fuel st fe d e)
      (fun lfe => (knot mode lfe fuel.val).whnf d.val (absExpr e)) :=
  hw.whnf.toSim d he

/-- The same wrapper hypothesis as an **E-matching entry point** for the task-#71
idiom: the Rust success equation first, so that a `rust_norm`'d body triggers it
(`Refine/README.md` §"Writing a new refinement lemma"; `Refine/Automation/Study.
lean` is where it was measured).  The other five wrappers take the same shape;
they are written when an arm that needs them is proved this way. -/
theorem Wrappers.whnf_use {st : cached.state_c.CState} {fe : fenv.FEnv} {d : Std.U64}
    {e r : expr.Expr} {st' : cached.state_c.CState}
    (hok : cached.core_c.whnf mode fuel st fe d e = ok (.Ok r, st'))
    (hw : Wrappers mode fuel)
    {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe)
    (hwf : StateWF st) (hfe : FEnvWF fe) (he : ExprWF e) :
    ∃ lst', ((knot mode lfe fuel.val).whnf d.val (absExpr e)).run lst = .ok (absExpr r, lst')
      ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r :=
  (hw.whnfSim d he).apply hwf hfe hok hrel hfrel

/-- `r.infer depth e` at one call site. -/
theorem Wrappers.inferSim (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer mode fuel st fe d e)
      (fun lfe => (knot mode lfe fuel.val).infer d.val (absExpr e)) :=
  hw.infer.toSim d he

/-- `r.inferIO depth e` at one call site. -/
theorem Wrappers.inferIOSim (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_io mode fuel st fe d e)
      (fun lfe => (knot mode lfe fuel.val).inferIO d.val (absExpr e)) :=
  hw.inferIO.toSim d he

/-- `r.annotate depth e` at one call site. -/
theorem Wrappers.annotateSim (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.annotate mode fuel st fe d e)
      (fun lfe => (knot mode lfe fuel.val).annotate d.val (absExpr e)) :=
  hw.annotate.toSim d he

/-- `r.defeq depth a b` at one call site. -/
theorem Wrappers.defeqSim (hw : Wrappers mode fuel) (d : Std.U64)
    {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True) (fun st fe => cached.core_c.defeq mode fuel st fe d a b)
      (fun lfe => (knot mode lfe fuel.val).defeq d.val (absExpr a) (absExpr b)) :=
  hw.defeq.toSim d ha hb

end

/-! ## Back to the body statements

A body's lemma is proved in `Sim` form (the shape the arms compose in) and
handed to `Bodies` through these two. -/

theorem RefinesE.ofSim {f g}
    (h : ∀ (d : Std.U64) (e : expr.Expr), ExprWF e →
      Sim absExpr ExprWF (fun st fe => f st fe d e) (fun lfe => g lfe d.val (absExpr e))) :
    RefinesE f g := by
  intro st fe d e o st' hwf hfe he hok lst lfe hrel hfrel
  exact h d e he fe lfe hfe hfrel st o st' hwf hok lst hrel

theorem RefinesB.ofSim {f g}
    (h : ∀ (d : Std.U64) (a b : expr.Expr), ExprWF a → ExprWF b →
      Sim id (fun _ => True) (fun st fe => f st fe d a b)
        (fun lfe => g lfe d.val (absExpr a) (absExpr b))) :
    RefinesB f g := by
  intro st fe d a b o st' hwf hfe ha hb hok lst lfe hrel hfrel
  exact h d a b ha hb fe lfe hfe hfrel st o st' hwf hok lst hrel


/-! ## The io grade as a flag

Task #18, deviation 4: where con-leche hands a body the record's io view
(`CoreFnsI.ioView`, whose `infer` slot is the io slot), the Rust carries a
`Bool`.  `knotV` names the record the flag selects, so that the `infer`
cluster's helpers — which run under both — are stated once. -/

/-- The record an `infer`-cluster helper runs against at the io flag. -/
def knotV (mode : env.CheckMode) (lfe : ConLeche.FEnv) (fuel : Nat) (io : Bool) :
    ConLeche.Cached.CoreFnsI :=
  if io then (knot mode lfe fuel).ioView else knot mode lfe fuel

@[simp] theorem knotV_false (mode lfe fuel) : knotV mode lfe fuel false = knot mode lfe fuel := rfl

@[simp] theorem knotV_true (mode lfe fuel) :
    knotV mode lfe fuel true = (knot mode lfe fuel).ioView := rfl

/-- `(knotV … io).infer` is the graded entry point: `r.inferIO` at the flag,
`r.infer` without it. -/
@[simp] theorem knotV_infer (mode lfe fuel io) :
    (knotV mode lfe fuel io).infer
      = if io then (knot mode lfe fuel).inferIO else (knot mode lfe fuel).infer := by
  cases io <;> rfl

/-- The other five slots do not change under the view. -/
@[simp] theorem knotV_whnfCore (mode lfe fuel io) :
    (knotV mode lfe fuel io).whnfCore = (knot mode lfe fuel).whnfCore := by cases io <;> rfl

@[simp] theorem knotV_whnf (mode lfe fuel io) :
    (knotV mode lfe fuel io).whnf = (knot mode lfe fuel).whnf := by cases io <;> rfl

@[simp] theorem knotV_defeq (mode lfe fuel io) :
    (knotV mode lfe fuel io).defeq = (knot mode lfe fuel).defeq := by cases io <;> rfl

@[simp] theorem knotV_annotate (mode lfe fuel io) :
    (knotV mode lfe fuel io).annotate = (knot mode lfe fuel).annotate := by cases io <;> rfl

@[simp] theorem knotV_inferIO (mode lfe fuel io) :
    (knotV mode lfe fuel io).inferIO = (knot mode lfe fuel).inferIO := by cases io <;> rfl

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `infer_at_i` (`core_c.rs:2638`) — the graded call every `infer` helper
makes, `r.infer` at the record the flag selects. -/
theorem Wrappers.inferAtSim (hw : Wrappers mode fuel) (d : Std.U64) (io : Bool)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_at_i mode fuel st fe d e io)
      (fun lfe => (knotV mode lfe fuel.val io).infer d.val (absExpr e)) := by
  cases io with
  | false =>
    have := hw.inferSim d he
    intro fe lfe hfe hfrel st o st' hwf hok lst hrel
    unfold cached.core_c.infer_at_i at hok
    simpa using this fe lfe hfe hfrel st o st' hwf (by simpa using hok) lst hrel
  | true =>
    have := hw.inferIOSim d he
    intro fe lfe hfe hfrel st o st' hwf hok lst hrel
    unfold cached.core_c.infer_at_i at hok
    simpa [ConLeche.Cached.CoreFnsI.ioView] using
      this fe lfe hfe hfrel st o st' hwf (by simpa using hok) lst hrel

end

end ConRon.Refine.Core
