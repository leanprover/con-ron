/-
# `ConRon.Refine2.Tactic.Tests` — regression tests for the shared `lockstep` tactic

Task #97-T2-TACTIC round 2.  Each test is taken from a site where a lane met a
limit of the tactic and worked around it by hand; the test is the site closed
by a plain `lockstep`, so a regression shows up here as a build failure, not as
a hand tail reappearing in some lane.

1. **Twin-only arguments** — a `@[lockstep]` lemma whose TWIN side has an
   argument the Rust does not determine (the message of `liftFueled what` and
   `unresolvedConstsError what`, the div/mod loop's `tried` list).  The
   argument is fixed by unifying the lemma's twin action with the goal's, not
   left as a side goal.
2. **A Rust bind against a twin `if`** — the Rust takes a bind step while the
   twin still tests an `if` (in bind position: `(if c then a else b) >>= k`,
   the `… >>= pure` of a twin `do` block's last line, or undecided by the
   context).  The twin `if` is distributed over its continuation, decided, or
   split, and the zip continues.
3. **No rewrite cycle** — a Rust state step with no twin partner against a
   twin `if` the context cannot decide: `lockstep` must STOP, leaving the goals
   it cannot move (task #97-T2-LOCKSTEP lane ExprOps §7: the `LS.twin_bind_pure`
   fallback once rewrote `x` to `x >>= pure`, the next step normalised it back,
   and `inst_lp_fast_ls` never terminated).  Run under a heartbeat budget, so a
   loop is an error here rather than a hang.
-/
import ConRon.Refine2.Checker.KnotHyp
import ConRon.Refine2.Inductives.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.Tests

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## 1. Twin-only arguments -/

/-- `lift_fueled` ⊑ `liftFueled what`, for EVERY message `what`: the Rust's
message is a constant (`M_FUEL_LEVEL_CMP`), the twin's is its argument, and
the messages are not compared (DESIGN §3.1).  The Checker lane filed this at
the one message its call site uses (`"level comparison"`) because a free
`what` was never picked. -/
@[lockstep] theorem lift_fueled_any_ls {pers st lst} {what : String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (o : Option Bool) :
    LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst (liftFueled what o) := by
  intro r h
  cases o with
  | some b =>
    simp only [arena.core.lift_fueled, Result.ok.injEq] at h
    subst h
    exact ⟨b, lst, rfl, rfl, hrel, hinv⟩
  | none =>
    simp only [arena.core.lift_fueled] at h
    obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [fail_run h]
    exact errSim_fail rfl

/-- The lemma above picked at a message it was not stated at. -/
example {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (o : Option Bool) :
    LS pers (fun a b => b = a) (arena.core.lift_fueled o >>= fun r => ok (r, st)) lst
      (liftFueled "level comparison" o) := by
  lockstep

/-- `unresolved_consts_error` at a fixed subject, through the generic
`unresolved_consts_error_ls` (free `w`). -/
example {pers st lst} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e) lst
      (unresolvedConstsError "value" (absEIdx e)) := by
  lockstep

/-- A twin-only argument of a LOCAL hypothesis (an induction hypothesis over
the div/mod loop, quantified over the twin's `tried` list), at a list the goal
builds (`tried ++ [msg]`). -/
example {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx} {value2 : arena.handle.EIdx}
    {variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.Usize}
    {tried : alloc.vec.Vec Std.U32} {ltried : List String}
    (hloop : ∀ {st lst} (ltried' : List String), AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = (fun _ : Unit => ()) a)
        (arena.decl_check.check_div_mod_pin_loop pers vis st mode rf c value2 variants i tried)
        lst
        (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c) (absEIdx value2)
          (absINatOpPinSetLFrom variants i) ltried'))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.check_div_mod_pin_loop pers vis st mode rf c value2 variants i tried) lst
      (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c) (absEIdx value2)
        (absINatOpPinSetLFrom variants i) (ltried ++ ["absent"])) := by
  lockstep

/-! ## 1–2. The reported sites: `install_value_tail`, `install_constant_val_tail`

The Checker lane closed both with `lockstep`, then `rw [bind_pure, if_neg …]`
by hand, then `unresolved_consts_error` at a specialised copy fixed at
`"value"`/`"type"`.  Both are one `lockstep` call now. -/

theorem install_value_tail_refines' {pers st lst} {vis : Std.U64} {rf lf}
    {cv : arena.env.IConstantVal} {value_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_split.install_value_tail pers vis st rf cv value_a = ok o) :
    Sim₀ absEIdx pers lst o
      (installValueTailSpec (lf.restrictTo (absU vis)) (absIConstantVal cv)
        (absEIdx value_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine LS.toSim₀ ?_ hrun
  rw [arena.checker_split.install_value_tail]
  unfold installValueTailSpec
  lockstep

/-! ## 2. A Rust bind against a twin `if` in bind position -/

/-- The twin's last line is an `if` bound to `pure` (`(if c then a else b) >>=
pure`); the Rust has already decided `c` and steps a bind. -/
example {pers st lst} {e : arena.handle.EIdx} {b : Bool} (hb : b = true)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e >>= fun p => ok p) lst
      ((if b then unresolvedConstsError "value" (absEIdx e)
        else unresolvedConstsError "type" (absEIdx e)) >>= fun r => pure r) := by
  lockstep

/-- The twin's next step is an `if` the last Rust test decided, the Rust's is
a state bind whose partner is inside the branch (the Checker Base/Top lane's
`unresolved_consts_error` and axiom-arm gates): the `if` is decided from the
context, not taken whole as the partner (`twin_bind_pure` skips an `if`). -/
example {pers st lst} {e : arena.handle.EIdx} {b : Bool} (hb : ¬ b = true)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e >>= fun p => ok p) lst
      (if b then (pure (.invalid "a") : AM Arena.CheckError)
        else unresolvedConstsError "type" (absEIdx e)) := by
  lockstep

/-- The twin tests `c` where the Rust does not test at all (both branches are
the same operation): the twin `if` is split and each branch zips. -/
example {pers st lst} {e : arena.handle.EIdx} {b : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e >>= fun p => ok p) lst
      (if b then unresolvedConstsError "value" (absEIdx e)
        else unresolvedConstsError "type" (absEIdx e)) := by
  lockstep

/-! ## 3. No rewrite cycle -/

-- A Rust state step whose twin partner is missing (the twin's branches are
-- `pure`s), against a twin `if` the context does not decide: `lockstep` stops
-- with the goals it cannot move, inside the heartbeat budget.
#guard_msgs (drop warning) in
set_option maxHeartbeats 20000 in
example {pers st lst} {e : arena.handle.EIdx} {b : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e >>= fun p => ok p) lst
      (if b then (pure (.invalid "a") : AM Arena.CheckError) else pure (.invalid "b")) := by
  lockstep
  all_goals sorry

/-! ## The axiom census -/

#print axioms lift_fueled_any_ls
#print axioms install_value_tail_refines'

end ConRon.Refine2.Lockstep.Tests
