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

open Lean Meta Elab Tactic in
/-- `simp_all` on a small side goal: first clear every hypothesis that is a
statement about programs or states (the knot, the `ExprOps` bundle, the
context, the relation, the invariant, an induction hypothesis) — `simp_all`
would otherwise try to simplify them all with each other. -/
elab "lockstep_simp_all_small" : tactic => do
  let g ← getMainGoal
  let g ← g.withContext do
    let mut g := g
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      let big := t.isForall || [``KnotRel, ``ExprOpsHyp, ``CoreCtx, ``AStateRel₀,
        ``AStateInv, ``LS].any (t.isAppOf ·)
      if big then
        g ← (try g.clear d.fvarId catch _ => pure g)
    pure g
  replaceMainGoal [g]
  evalTactic (← `(tactic| simp_all))

/-- A twin `if` the side tiers of `lockstep_core` could not decide, decided
by the full `simp_all` on the small facts (the Rust's tag tests are in
`!=`/`decide` form and need `decide_eq_false_iff_not`, which blows the
recursion depth when added to `lockstep_simp`, whose `simpTwin` runs over the
whole twin program). -/
macro "lockstep_twin_ite_full" : tactic =>
  `(tactic| first
    | (apply LS.twin_ite_neg (hc := by lockstep_simp_all_small) ; skip)
    | (apply LS.twin_ite_pos (hc := by lockstep_simp_all_small) ; skip))

/-- `lockstep_core` with the local moves as fallbacks. -/
macro "lockstep_f" : tactic =>
  `(tactic| repeat' (first | lockstep_core_step | lockstep_twin_ite_full | lockstep_twin_tail | lockstep_bool_cases))

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

/-! ## The batched binder descent: induction on the port's `peel` -/

/-! The twin's own equations at `0` and at a successor, by `rfl` with smart
unfolding off.  Lean's generated `defeqPeel.eq_1`/`eq_def` time out (their
generation runs at the default heartbeat budget whatever the file sets), and
with smart unfolding ON the recursive call's `match peel` sits under the
monad's binders, so `rfl` cannot see through the structural recursion. -/

set_option smartUnfolding false in
theorem defeqPeel_zero (mode : ConLeche.CheckMode) (r : CoreFnsA) (d : Nat) (a b : EIdx) (k : Nat)
    (fvs : Array EIdx) (mism mismLam : Bool) :
    defeqPeel mode r d 0 a b k fvs mism mismLam
      = if a == b then defeqPeelDone mism mismLam
        else defeqPeelLeaf r d a b k fvs mism mismLam := by
  rfl

set_option smartUnfolding false in
theorem defeqPeel_succ (mode : ConLeche.CheckMode) (r : CoreFnsA) (d m : Nat) (a b : EIdx) (k : Nat)
    (fvs : Array EIdx) (mism mismLam : Bool) :
    defeqPeel mode r d (m + 1) a b k fvs mism mismLam
      = (do
    let ta := a.tag
    if a == b then defeqPeelDone mism mismLam
    else if ta != b.tag || !(ETag.isBind ta) then
      defeqPeelLeaf r d a b k fvs mism mismLam
    else
      match ← viewBindI a with
      | none => failDanglingE
      | some (da, ba, ma) =>
        match ← viewBindI b with
        | none => failDanglingE
        | some (db, bb, mb) => do
          let sameDom := da == db
          let t1 ← instantiateListFast coreWalkFuel da fvs 0
          let t2 ← if sameDom then pure t1
                   else instantiateListFast coreWalkFuel db fvs 0
          let dq ← if sameDom then pure true else r.defeq (d + k) t1 t2
          if !dq then pure false
          else do
            let fv ← internFVarE (d + k) t2
            let mm := mode.verifiedChecks && !(ma == mb)
            let m2 := mism || mm
            let ml2 := if mm then ta == ETag.lam else mismLam
            defeqPeel mode r d m ba bb (k + 1) (fvs.push fv) m2 ml2 : AM Bool) := by
  rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem defeq_peel_aux {f : Nat} (hk : KnotRel f) {pers : arena.store.PersTier}
    (hx : ExprOpsHyp pers) {vis mode lane fu fe lfe} (hctx : CoreCtx vis fe lfe)
    (hf : absU fu = f) (d : Std.U64) (n : Nat) :
    ∀ {st : arena.monad.AState} {lst : AState} (peel : Std.U64) (a b : arena.handle.EIdx)
      (k : Std.U64) (fvs : alloc.vec.Vec arena.handle.EIdx) (mism mismLam : Bool),
      peel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.core.defeq_peel pers vis st mode lane fu fe d peel a b k fvs mism mismLam) lst
        (defeqPeel (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
          (absU d) n (absEIdx a) (absEIdx b) (absU k) (absEIdxArr fvs) mism mismLam) := by
  induction n with
  | zero =>
    intro st lst peel a b k fvs mism mismLam hn hrel hinv
    rw [arena.core.defeq_peel, defeqPeel_zero]
    lockstep_f
  | succ m ih =>
    intro st lst peel a b k fvs mism mismLam hn hrel hinv
    rw [arena.core.defeq_peel, defeqPeel_succ]
    sorry

@[lockstep] theorem defeq_peel_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d peel a b k fvs mism mismLam lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_peel pers vis st mode lane fu fe d peel a b k fvs mism mismLam) lst
      (defeqPeel (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        (absU d) (absU peel) (absEIdx a) (absEIdx b) (absU k) (absEIdxArr fvs) mism mismLam) :=
  defeq_peel_aux hk hx hctx hf d _ peel a b k fvs mism mismLam rfl hrel hinv

end ConRon.Refine2.Lockstep
