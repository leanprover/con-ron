import ConRon.Refine.State
import ConRon.Refine.FEnv
import ConLeche.Cached.CheckerC

/-! # `cached::checker_c` — `orElse`, the checker's one error-recovery point

`CORE_PLAN.md` step 7 (task #56).  `Cached/CheckerC.lean`'s `opE`/`opB`/`opS`
and the five core slots of `sharedOpsC` collapse into
`kernel::type_checker` (`Refine/TypeChecker.lean`); its phase drivers are the
inductive family's (`Refine/IndSpec.lean`, task #57).  What is left, and what
this file is about, is `CheckerOps.orElse`
(`ConLeche/Kernel/CheckerBase.lean:36-53`, instantiated at
`Cached/CheckerC.lean:81-96`):

```text
orElse x k := fun s => match x s with
  | .ok (true, s')  => .ok ((), s')
  | .ok (false, s') => k none s'
  | .error e        => k (some e) s
```

the **only** place the checker recovers from a thrown error, scoped to the
Nat-op pin gate's per-variant attempt (`checkDivModPinAt`).  The continuation
`k` is a closure §3.4 forbids, so the port keeps it at the one call site
(`checker::check_div_mod_pin_loop`'s own tail call) and ports the
combinator's *decision* as the three-way `OrElseStep`.  `or_else_step` is
therefore refined here as the **branch selector**, exactly; the loop that
consumes it is `Refine/CheckerPins.lean`.

## The state deviation, stated rather than glossed

The error arm is `k (some e) s` — the **pre-attempt** state: con-leche throws
away the memo entries a failed attempt wrote.  The port's state is a
`&mut CState`, so the continuation runs on the *post*-attempt state.  Every
entry a failed attempt wrote is still a correct answer (the maps are pure
function caches, and `StateWF` is preserved), so no verdict changes — but the
port's state is a *superset* of con-leche's there, and `StateRel` is
lookup-agreement, which a superset breaks.  Task #24's module note flagged
this and said it must be reconciled "before any `check_decl_refines` is stated
against `checkDeclsPure`".  This file is where that comes due:
`OrElseErrorStateSound` names precisely the missing fact, and
`Refine/CheckerPins.lean`'s pin-loop lemma carries it as a hypothesis.  The
port-side fix is a `CState` snapshot in `cached::state_c` (or an upstream
change making con-leche keep the entries); neither is this task's, and
nothing below hides the gap.

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.CheckerC

/-! ## The combinator, run

`sharedOpsC.orElse` in the state monad, one lemma per arm.  Each is the cited
`match`, so each is `rfl` after the attempt's `run` is known. -/

open ConLeche.Cached in
/-- The attempt matched: `orElse` is the whole, and the attempt's state
stands. -/
theorem orElse_run_matched {mode : ConLeche.CheckMode} {lfe : ConLeche.FEnv}
    {x : CheckCM Bool} {k : Option ConLeche.CheckError → CheckCM Unit}
    {lst lst' : CState} (h : x.run lst = .ok (true, lst')) :
    ((sharedOpsC mode lfe).orElse x k).run lst = .ok ((), lst') := by
  show (match x.run lst with
    | Except.ok (true, s') => Except.ok ((), s')
    | Except.ok (false, s') => (k none).run s'
    | Except.error e => (k (some e)).run lst) = _
  rw [h]

open ConLeche.Cached in
/-- The attempt declined: the continuation runs on the attempt's state, told
nothing. -/
theorem orElse_run_declined {mode : ConLeche.CheckMode} {lfe : ConLeche.FEnv}
    {x : CheckCM Bool} {k : Option ConLeche.CheckError → CheckCM Unit}
    {lst lst' : CState} (h : x.run lst = .ok (false, lst')) :
    ((sharedOpsC mode lfe).orElse x k).run lst = (k none).run lst' := by
  show (match x.run lst with
    | Except.ok (true, s') => Except.ok ((), s')
    | Except.ok (false, s') => (k none).run s'
    | Except.error e => (k (some e)).run lst) = _
  rw [h]

open ConLeche.Cached in
/-- **The recovery arm**: the attempt threw, and the continuation runs on the
**pre-attempt** state, told which error.  This is the clause that makes a
certificate blob from another toolchain read as "this variant does not match"
rather than as a checker bug — and it is the clause the port's `&mut CState`
deviates from (module note). -/
theorem orElse_run_error {mode : ConLeche.CheckMode} {lfe : ConLeche.FEnv}
    {x : CheckCM Bool} {k : Option ConLeche.CheckError → CheckCM Unit}
    {lst : CState} {e : ConLeche.CheckError} (h : x.run lst = .error e) :
    ((sharedOpsC mode lfe).orElse x k).run lst = (k (some e)).run lst := by
  show (match x.run lst with
    | Except.ok (true, s') => Except.ok ((), s')
    | Except.ok (false, s') => (k none).run s'
    | Except.error e => (k (some e)).run lst) = _
  rw [h]

/-! ## The port's decision

`or_else_step` is the cited match's *branch selector*, with the state left to
the caller's `&mut`.  Three closed computations; nothing is assumed. -/

/-- A matched attempt is the whole (`pure ()`). -/
@[simp] theorem or_else_step_matched :
    cached.checker_c.or_else_step (.Ok true) = ok .Matched := by
  rw [cached.checker_c.or_else_step]; rfl

/-- A declined attempt continues, carrying no diagnosis — the `fueledOps`
clause is this one for *both* failure shapes. -/
@[simp] theorem or_else_step_declined :
    cached.checker_c.or_else_step (.Ok false) = ok (.Continue none) := by
  rw [cached.checker_c.or_else_step]; rfl

/-- A **thrown error** continues, carrying the error: the combinator's point. -/
@[simp] theorem or_else_step_error (e : core_types.CheckError) :
    cached.checker_c.or_else_step (.Err e) = ok (.Continue (some e)) := by
  rw [cached.checker_c.or_else_step]

/-! ## The one thing the port owes

What the error arm needs for the refinement to go through unchanged: the
state the port hands the continuation after a *failed* attempt still stands in
`StateRel` to the state con-leche hands it, which is the pre-attempt one.
Equivalently: a failed attempt's memo writes are invisible to `StateRel`.

This is **not** provable of the current port — a failed attempt does write
entries and `StateRel` is lookup agreement — which is exactly task #24's
flagged deviation.  It is stated as a `Prop` so that the pin loop can take it
as a hypothesis, so that the gap is visible in every lemma that depends on it,
and so that the port-side fix (a `CState` snapshot around
`check_div_mod_pin_at`) discharges it in one place. -/

/-- **The task-#24 deviation, named.**  `f` is a failing attempt run over the
port's threaded state; the Prop says its writes leave the abstract state
where it was. -/
def OrElseErrorStateSound
    (f : cached.state_c.CState →
      Result ((core.result.Result Bool core_types.CheckError) × cached.state_c.CState)) :
    Prop :=
  ∀ st e st', StateWF st → f st = ok (.Err e, st') →
    StateWF st' ∧ ∀ lst, StateRel st lst → StateRel st' lst

end ConRon.Refine.CheckerC
