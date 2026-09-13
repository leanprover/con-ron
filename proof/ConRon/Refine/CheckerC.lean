import ConRon.Refine.State
import ConRon.Refine.FEnv
import ConLeche.Cached.CheckerC

/-! # `cached::checker_c` — `orElse`, the pin loop's variant fallback

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

the only place *con-leche* recovers from a thrown error, scoped to the
Nat-op pin gate's per-variant attempt (`checkDivModPinAt`); the port's third
arm is task #65's ruling below.  The continuation
`k` is a closure §3.4 forbids, so the port keeps it at the one call site
(`checker::check_div_mod_pin_loop`'s own tail call) and ports the
combinator's *decision* as the three-way `OrElseStep`.  `or_else_step` is
therefore refined here as the **branch selector**, exactly; the loop that
consumes it is `Refine/CheckerPins.lean`.

## The deviation, ruled (task #65): an attempt's error is the verdict

con-leche's error arm is `k (some e) s` — the **pre-attempt** state: the memo
entries a failed attempt wrote are discarded with it.  The port's state is a
`&mut CState`, which cannot discard them, and the accept-direction tower
(DESIGN.md §3.5) cannot tell when con-leche takes that arm either, since it
says nothing about a port-side `.Err`.  Tasks #24/#56/#58 carried those two
gaps as hypotheses (`OrElseErrorStateSound` here, `OrElseErrorDeclines` in
`Refine/CheckerPins.lean`, packaged as `CheckerDecl.DivModOrElse`).

Task #65 rules instead: **the port does not recover.**  `or_else_step` maps
`.Err e` to `.Failed e` and `check_div_mod_pin_loop` returns it, so the pin
check declines with the error that variant failed on.  Only `.Ok false`
continues, and it continues with the attempt's own state — which is
con-leche's `false` arm exactly.  So the error arm is *unreachable* on the
port side of every accept-direction statement, both hypotheses are gone, and
the capstones are hypothesis-free here.  The price is a documented
accept-direction deviation, recorded in `cached::checker_c`'s module note and
DESIGN.md §3: a stream whose variant `i` has a definitionally matching pin
with a throwing certificate and whose later variant `j` matches in full is
accepted by con-leche and declined by con-ron.  Acceptances lost, never
gained.

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
rather than as a checker bug, and since task #67 it is a clause the port
*takes*: `or_else_step` answers `Recovered e` on a mirrored error and
`check_div_mod_pin_loop` restores its `state_c::dup` snapshot, which is this
lemma's `lst`.  (Task #65 had ruled the port out of it; that ruling is
superseded.)  Only the port's own `Native` error stops here instead. -/
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

/-- A declined attempt continues — the cited `false` arm, and the only arm
that reaches the loop's next variant. -/
@[simp] theorem or_else_step_declined :
    cached.checker_c.or_else_step (.Ok false) = ok .Continue := by
  rw [cached.checker_c.or_else_step]; rfl

/-- A **mirrored thrown error** is recovered from, carrying the error: the
cited `k (some e) s`, with the pre-attempt state restored by the caller
(task #67, `cached::checker_c`'s module note).  Stated by cases so that the
three mirrored constructors are visibly the ones it covers. -/
@[simp] theorem or_else_step_error_not_implemented (m : alloc.vec.Vec Std.U32) :
    cached.checker_c.or_else_step (.Err (.NotImplemented m))
      = ok (.Recovered (.NotImplemented m)) := by
  rw [cached.checker_c.or_else_step]

@[simp] theorem or_else_step_error_invalid (m : alloc.vec.Vec Std.U32) :
    cached.checker_c.or_else_step (.Err (.Invalid m))
      = ok (.Recovered (.Invalid m)) := by
  rw [cached.checker_c.or_else_step]

@[simp] theorem or_else_step_error_internal (m : alloc.vec.Vec Std.U32) :
    cached.checker_c.or_else_step (.Err (.Internal m))
      = ok (.Recovered (.Internal m)) := by
  rw [cached.checker_c.or_else_step]

/-- The port's **own** failure is the verdict: a `Native` error has no cited
`throw` to recover from (DESIGN.md §3's ruling of 2026-09-13). -/
@[simp] theorem or_else_step_error_native (m : alloc.vec.Vec Std.U32) :
    cached.checker_c.or_else_step (.Err (.Native m)) = ok (.Failed (.Native m)) := by
  rw [cached.checker_c.or_else_step]

/-- The three mirrored constructors in one: a non-`Native` error is
recovered from, unchanged. -/
theorem or_else_step_error_mirrored {e : core_types.CheckError}
    (h : ∀ m, e ≠ .Native m) :
    cached.checker_c.or_else_step (.Err e) = ok (.Recovered e) := by
  cases e with
  | NotImplemented m => simp
  | Invalid m => simp
  | Internal m => simp
  | Native m => exact absurd rfl (h m)

end ConRon.Refine.CheckerC
