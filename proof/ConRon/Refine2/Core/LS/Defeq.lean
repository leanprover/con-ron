/-
# `ConRon.Refine2.Core.LS.Defeq` — region F: the `defeq` loop, lockstep

Task #97-P5-Core round 5, region F.  The Theorem-2 lockstep lemmas of the
`defeq` half of `arena::core` against `Arena/Core.lean`:

| twin | Rust |
|---|---|
| `defeqPeelLeaf` | `defeq_peel_leaf` |
| `defeqPeel` | `defeq_peel` (a loop: induction on `peel`) |
| `defeqBinders` | `defeq_binders` |
| `defeqSpine` | `defeq_spine` |
| `boolTrueShortcut` | `bool_true_shortcut` |
| `defeqStep` | `defeq_step` + the fragments `defeq_after_whnf`, `defeq_delta`, `defeq_delta_both`, `defeq_unfold_both`, `defeq_struct`, `defeq_apps`, `defeq_lit_app`, `defeq_lit_const` |
| `defeqLoop` | `defeq_loop` (the second fuel dimension) |
| `defeqBody` | `defeq_body` |

The loop is `Core/Arms/Loops.lean`'s `whnf_loop_aux` shape: the step is proved
parametric in the continuation (a hypothesis `hcont` on `defeq_loop … n`,
found by `lockstep_core` in the context under its head constant), and the loop
by induction on the port's counter — finding 13: the port's `n` IS the twin's
continuation `defeqLoop … (absU n)`, no `- 1`.
-/
import ConRon.Refine2.Core.LS.PrimsF

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

/-! ## A local move: a Rust bind against a twin tail

`lockstep`'s bind rules want the twin to be a bind too.  When the Rust binds a
READ (`LSR`) and then returns it — `let r ← defeq_peel_done …; ok (r, st)` —
the twin's partner is a TAIL (`defeqPeelDone …`).  `x = x >>= pure` makes the
twin a bind; the continuation is then `LS.pure`. -/

theorem LS.twin_bind_pure {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R m lst (x >>= (Pure.pure : β → AM β))) :
    LS pers R m lst x := by
  rwa [bind_pure] at h

open Lean Meta Elab Tactic in
/-- Apply `LS.twin_bind_pure` when the Rust side is a bind and the twin side
is not. -/
elab "lockstep_twin_tail" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``LS 7 do throwError "not LS"
  let m := (ty.getArg! 4).headBeta
  let x := (ty.getArg! 6).headBeta
  unless m.isAppOfArity ``Bind.bind 6 do throwError "rust not a bind"
  if x.isAppOfArity ``Bind.bind 6 then throwError "twin already a bind"
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``LS.twin_bind_pure)
  replaceMainGoal gs

open Lean Meta Elab Tactic in
/-- The twin matches on a `Bool` the Rust already tested (`match some b with
| some true => …`, where the Rust wrote `if b then …`): case-split the
`Bool`, so that the match reduces and the Rust test's hypothesis decides the
branch. -/
elab "lockstep_bool_cases" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``LS 7 do throwError "not LS"
    let x := (ty.getArg! 6).headBeta
    let x := if x.isAppOfArity ``Bind.bind 6 then (x.getArg! 4).headBeta else x
    unless (← matchMatcherApp? x).isSome do throwError "twin not a match"
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type).isConstOf ``Bool && x.containsFVar d.fvarId then
        let subs ← g.cases d.fvarId
        let gs ← subs.toList.mapM fun sg => do
          let g' ← normGoal sg.mvarId
          pure g'
        replaceMainGoal gs
        return
    throwError "no Bool fvar"

/-- `lockstep_core` with the twin-tail move as a fallback. -/
macro "lockstep_f" : tactic =>
  `(tactic| repeat' (first | lockstep_core_step | lockstep_twin_tail | lockstep_bool_cases))

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

section Stubs

@[lockstep] theorem stub_lvl_eq_ls {pers st u v lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.lvl_eq pers st u v) lst
      (lvlEq? (absLIdx u) (absLIdx v)) := by
  sorry

@[lockstep] theorem stub_lvls_eq_ls {pers st us vs lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.lvls_eq pers st us vs) lst
      (lvlsEq? (absLsIdx us) (absLsIdx vs)) := by
  sorry

@[lockstep] theorem stub_lift_fueled_ls {pers st lst} (what : String) (o : Option Bool)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst (liftFueled what o) := by
  sorry

@[lockstep] theorem stub_empty_levels_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLsIdx a) (arena.core.empty_levels st) st lst emptyLevels := by
  sorry

@[lockstep] theorem stub_is_bool_true_ls {pers st h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.is_bool_true pers st h) lst
      (isBoolTrue (absEIdx h)) := by
  sorry

@[lockstep] theorem stub_quick_pair_ls (a b : arena.handle.EIdx) :
    LSP (arena.core.quick_pair a b) (fun r => TwinEq (quickPair (absEIdx a) (absEIdx b)) r) := by
  sorry

@[lockstep] theorem stub_head_hint_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = ConRon.Refine.absHint a) (arena.core.head_hint pers vis st fe e) lst
      (headHint lfe (absEIdx e)) := by
  sorry

@[lockstep] theorem stub_unfoldable_head_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.unfoldable_head pers vis st fe e) lst
      (unfoldableHead lfe (absEIdx e)) := by
  sorry

@[lockstep] theorem stub_same_const_heads_ls {pers st a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.same_const_heads pers st a b) lst
      (sameConstHeads (absEIdx a) (absEIdx b)) := by
  sorry

@[lockstep] theorem stub_defeq_no_fvars_ls {pers st a b lst} (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.defeq_no_fvars pers st a b) lst
      (defeqNoFvars (absEIdx a) (absEIdx b)) := by
  sorry

@[lockstep] theorem stub_defeq_peel_done_ls {pers st lst} (mism mismLam : Bool)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = a) (arena.core.defeq_peel_done mism mismLam) st lst
      (defeqPeelDone mism mismLam) := by
  sorry

@[lockstep] theorem stub_reduce_nat_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.reduce_nat pers vis st mode lane fu fe depth e) lst
      (reduceNat (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx e)) := by
  sorry

@[lockstep] theorem stub_str_lit_supported_ls {pers vis st fe lfe lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.str_lit_supported pers vis st fe) lst
      (strLitSupported lfe) := by
  sorry

@[lockstep] theorem stub_str_lit_to_constructor_ls {pers st s lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.str_lit_to_constructor pers st s) lst
      (strLitToConstructor (ConRon.Refine.absString s)) := by
  sorry

@[lockstep] theorem stub_def_eq_list_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth xs ys i lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.def_eq_list pers vis st mode lane fu fe depth xs ys i) lst
      (defEqList (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdxListFrom xs i) (absEIdxListFrom ys i)) := by
  sorry

@[lockstep] theorem stub_prop_irrel_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.prop_irrel pers vis st mode lane fu fe depth a b) lst
      (propIrrel (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) := by
  sorry

@[lockstep] theorem stub_stuck_irrel_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.stuck_irrel pers vis st mode lane fu fe depth a b) lst
      (stuckIrrel (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx a) (absEIdx b)) := by
  sorry

@[lockstep] theorem stub_eta_cert_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty1 body1 m1 b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.eta_cert pers vis st mode lane fu fe depth ty1 body1 m1 b) lst
      (etaCert (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx ty1) (absEIdx body1) (ConRon.Refine.absBinderMeta m1)
        (absEIdx b)) := by
  sorry

end Stubs

/-! ## The batched binder descent's leaf -/

@[lockstep] theorem defeq_peel_leaf_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d a b k fvs mism mismLam lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_peel_leaf pers vis st mode lane fu fe d a b k fvs mism mismLam) lst
      (defeqPeelLeaf (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        (absU d) (absEIdx a) (absEIdx b) (absU k) (absEIdxArr fvs) mism mismLam) := by
  rw [arena.core.defeq_peel_leaf, defeqPeelLeaf]
  lockstep_f

/-! ## The eq-true shortcut and the same-head spine -/

@[lockstep] theorem bool_true_shortcut_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.bool_true_shortcut pers vis st mode lane fu fe depth a) lst
      (boolTrueShortcut (laneKnot (ConRon.Refine.absMode mode) lfe lane f) (absU depth)
        (absEIdx a)) := by
  rw [arena.core.bool_true_shortcut, boolTrueShortcut]
  lockstep_f

set_option maxHeartbeats 2000000 in
@[lockstep] theorem defeq_spine_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_spine pers vis st mode lane fu fe depth a b) lst
      (defeqSpine (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.defeq_spine, defeqSpine]
  lockstep_f

end ConRon.Refine2.Lockstep
