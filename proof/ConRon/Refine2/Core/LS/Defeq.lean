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
import ConRon.Refine2.Core.LS.Leaves
import ConRon.Refine2.Core.LS.Shapes
import ConRon.Refine2.Core.LS.Lits
import ConRon.Refine2.Core.LS.Certs

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PB.CoreLSReg ConRon.Refine2.Lockstep.PC1.CoreLSReg ConRon.Refine2.Lockstep.PF.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

-- `PrimsB`/`PrimsE` unfold the record abstraction only locally now (the
-- Checker lane reads it folded); the Core region files read it unfolded
attribute [local lockstep_simp] ConRon.Refine2.absIConstantVal

-- `PrimsF`'s `==`-as-`decide` rewrites, local there (they rewrote other tiers'
-- twins)
attribute [local lockstep_simp] ConRon.Refine2.Lockstep.PF.idx_beq_decide
  ConRon.Refine2.Lockstep.PF.beq_of_decEq ConRon.Refine2.Lockstep.PF.nat_beq_decide'

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2
open ConRon.Refine2.Lockstep.PF

/-! ## A local move: a Rust bind against a twin tail

`lockstep`'s bind rules want the twin to be a bind too.  When the Rust binds a
READ (`LSR`) and then returns it — `let r ← defeq_peel_done …; ok (r, st)` —
the twin's partner is a TAIL (`defeqPeelDone …`).  `x = x >>= pure` makes the
twin a bind; the continuation is then `LS.pure` (the move is the shared
`LS.twin_bind_pure`). -/

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

theorem LS.twin_bind_ite_pos {α β δ : Type} {pers : arena.store.PersTier} {R : α → δ → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x y : AM β} {g : β → AM δ} (hc : c) (h : LS pers R m lst (x >>= g)) :
    LS pers R m lst ((if c then x else y) >>= g) := by
  rw [if_pos hc]; exact h

theorem LS.twin_bind_ite_neg {α β δ : Type} {pers : arena.store.PersTier} {R : α → δ → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x y : AM β} {g : β → AM δ} (hc : ¬ c) (h : LS pers R m lst (y >>= g)) :
    LS pers R m lst ((if c then x else y) >>= g) := by
  rw [if_neg hc]; exact h

open Lean Meta Elab Tactic in
/-- Is `T` an inductive type with more than one constructor? -/
def multiCtor (T : Expr) : MetaM Bool := do
  let T ← whnfR T
  let some n := T.getAppFn.constName? | return false
  match (← getEnv).find? n with
  | some (.inductInfo v) => return v.ctors.length > 1
  | _ => return false

open Lean Meta Elab Tactic in
/-- The twin's next action is a `match` that does not reduce (the port tested
the value earlier, with an `if` or a match of its own, and the twin matches on
it again — a `Bool` flag, a literal's payload, `toNat` of a bignum): case-split
the value the match is stuck on, so that the match reduces and the Rust's own
test decides the branch.  An fvar of a multi-constructor type in a
discriminant is split; failing that, a non-fvar discriminant of such a type is
generalized (with its equation) and split. -/
elab "lockstep_twin_cases" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``LS 7 do throwError "not LS"
    let x := (ty.getArg! 6).headBeta
    let x := if x.isAppOfArity ``Bind.bind 6 then (x.getArg! 4).headBeta else x
    let some mapp ← matchMatcherApp? x | throwError "twin not a match"
    let finish (subs : Array MVarId) : TacticM Unit := do
      let gs ← subs.toList.mapM fun sg => normGoal sg
      replaceMainGoal gs
    -- an fvar of a multi-constructor type inside a discriminant
    for d in mapp.discrs do
      let fvs := (collectFVars {} (← instantiateMVars d)).fvarIds
      for fv in fvs do
        let some decl := (← getLCtx).find? fv | continue
        if decl.isImplementationDetail then continue
        if ← multiCtor decl.type then
          let subs ← g.cases fv
          finish (subs.map (·.mvarId))
          return
    -- a non-fvar discriminant of a multi-constructor type (`toNat n`)
    for d in mapp.discrs do
      let d ← instantiateMVars d
      if d.isFVar then continue
      if d.getAppFn.isConst then
        if let some (.ctorInfo _) := (← getEnv).find? d.getAppFn.constName! then continue
      let T ← inferType d
      if ← multiCtor T then
        let (fvs, g') ← g.generalize #[{ expr := d, xName? := `N, hName? := `hN }]
        let subs ← g'.cases fvs[0]!
        finish (subs.map (·.mvarId))
        return
    throwError "lockstep_twin_cases: nothing to split"

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
  evalTactic (← `(tactic| simp_all only [lockstep_simp, decide_eq_false_iff_not,
    Bool.or_eq_false_iff, not_or, bne_iff_ne, ne_eq, ConRon.Refine2.Lockstep.PF.absU32_eq_lam,
    ConRon.Refine2.Lockstep.PF.absU32_eq_forallE, ConRon.Refine2.Lockstep.PF.absU32_eq_absU32,
    not_not]))

/-- A twin `if` the side tiers of `lockstep_core` could not decide, decided
by the full `simp_all` on the small facts (the Rust's tag tests are in
`!=`/`decide` form and need `decide_eq_false_iff_not`, which blows the
recursion depth when added to `lockstep_simp`, whose `simpTwin` runs over the
whole twin program). -/
macro "lockstep_twin_ite_full" : tactic =>
  `(tactic| first
    | (apply LS.twin_ite_neg; case hc => lockstep_simp_all_small)
    | (apply LS.twin_ite_pos; case hc => lockstep_simp_all_small)
    | (apply LS.twin_bind_ite_neg; case hc => lockstep_simp_all_small)
    | (apply LS.twin_bind_ite_pos; case hc => lockstep_simp_all_small))

theorem LS.twin_bind_assoc {α β γ δ : Type} {pers : arena.store.PersTier} {R : α → δ → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} {f : β → AM γ} {g : γ → AM δ}
    (h : LS pers R m lst (x >>= fun a => f a >>= g)) : LS pers R m lst ((x >>= f) >>= g) := by
  rwa [bind_assoc]

open Lean Meta Elab Tactic in
/-- The twin's next action is itself a bind (a `do` block the Rust's tail
wrapped): re-associate it. -/
elab "lockstep_twin_assoc" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``LS 7 do throwError "not LS"
  let x := (ty.getArg! 6).headBeta
  unless x.isAppOfArity ``Bind.bind 6 && (x.getArg! 4).headBeta.isAppOfArity ``Bind.bind 6 do
    throwError "twin head not a bind"
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``LS.twin_bind_assoc)
  replaceMainGoal gs

/-- A branch the port's own tests rule out, found by `simp_all` on the small
facts (the last resort). -/
macro "lockstep_contra_small" : tactic => `(tactic| (exfalso; lockstep_simp_all_small; done))

/-- `lockstep_core` with the local moves as fallbacks. -/
macro "lockstep_f" : tactic =>
  `(tactic| repeat' (first | lockstep_step | lockstep_twin_ite_full | lockstep_twin_cases | lockstep_twin_assoc | lockstep_twin_tail | lockstep_contra_small))


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
    lockstep
  | succ m ih =>
    intro st lst peel a b k fvs mism mismLam hn hrel hinv
    have hpush := @PF.vec_push_eidx_ls
    rw [arena.core.defeq_peel, defeqPeel_succ]
    lockstep_f


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

/-! ## The binder-congruence arm -/

@[lockstep] theorem defeq_binders_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty1 body1 m1 ty2 body2 m2 isLam lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hm1 : ConRon.Refine.PropWhenWF m1.pw) (hm2 : ConRon.Refine.PropWhenWF m2.pw) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_binders pers vis st mode lane fu fe depth ty1 body1 m1 ty2 body2 m2
        isLam) lst
      (defeqBinders (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        (absU depth) (absEIdx ty1) (absEIdx body1) (ConRon.Refine.absBinderMeta m1)
        (absEIdx ty2) (absEIdx body2) (ConRon.Refine.absBinderMeta m2) isLam) := by
  have hpush := @PF.vec_push_eidx_ls
  rw [arena.core.defeq_binders, defeqBinders]
  lockstep_f

/-! ## The lazy-delta loop

`defeq_step`'s fragments have no twin of their own: they are the tail of
`defeqStep` (task #97-P5-0's finding-6 splits), so they are unfolded in place. -/

attribute [lockstep_inline] arena.core.defeq_after_whnf arena.core.defeq_delta
  arena.core.defeq_delta_both arena.core.defeq_unfold_both arena.core.defeq_struct
  arena.core.defeq_apps arena.core.defeq_lit_app arena.core.defeq_lit_const

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
/-- `defeq_step`'s body, once, parametric in the continuation: the port's
`n` IS the twin's `defeqLoop … (absU n)` (finding 13), and `hcont` — the
loop at `n` — is found by `lockstep_core` in the context under
`arena.core.defeq_loop`. -/
theorem defeq_step_of_cont {f : Nat} (hk : KnotRel f) {pers : arena.store.PersTier}
    (hx : ExprOpsHyp pers) {vis mode lane fu fe lfe} (hctx : CoreCtx vis fe lfe)
    (hf : absU fu = f) (depth n : Std.U64)
    (hcont : ∀ {st : arena.monad.AState} {lst : AState} (pi : Bool) (a b : arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.core.defeq_loop pers vis st mode lane fu fe depth n pi a b) lst
        (defeqLoop (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
          lfe (absU depth) (absU n) pi (absEIdx a) (absEIdx b)))
    {st : arena.monad.AState} {lst : AState} (pi : Bool) (a b : arena.handle.EIdx)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_step pers vis st mode lane fu fe depth n pi a b) lst
      (defeqStep (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth)
        (defeqLoop (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
          lfe (absU depth) (absU n)) pi (absEIdx a) (absEIdx b)) := by
  have hview := @PF.view_wf_ls
  have hpush := @PF.vec_push_eidx_ls
  -- `lift_fueled_ls` takes the twin's message as an explicit argument, which
  -- the port's step does not determine: specialised to `defeqStep`'s.
  have hlift : ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState},
      AStateRel₀ pers st lst → AStateInv pers st → ∀ (o : Option Bool),
      LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst
        (liftFueled "level comparison" o) :=
    fun hrel hinv o => lift_fueled_ls hrel hinv o "level comparison"
  rw [arena.core.defeq_step]
  delta defeqStep
  lockstep_f

theorem defeqLoop_zero (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat)
    (pi : Bool) (a b : EIdx) :
    defeqLoop mode r fe d 0 pi a b = Arena.fail (.internal "fuel exhausted: defeq loop") := rfl

theorem defeqLoop_succ (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d m : Nat)
    (pi : Bool) (a b : EIdx) :
    defeqLoop mode r fe d (m + 1) pi a b = defeqStep mode r fe d (defeqLoop mode r fe d m) pi a b :=
  rfl

@[local lockstep_simp] theorem defeq_loop_fuel_val :
    absU arena.core.DEFEQ_LOOP_FUEL = Arena.defeqLoopFuel := by
  rw [arena.core.DEFEQ_LOOP_FUEL, Arena.defeqLoopFuel]; rfl

/-- The loop, by induction on the port's counter (`Core/Arms/Loops.lean`'s
`whnf_loop_aux` shape): the step at `n - 1` is `defeq_step_of_cont` with the
induction hypothesis as its continuation. -/
theorem defeq_loop_aux {f : Nat} (hk : KnotRel f) {pers : arena.store.PersTier}
    (hx : ExprOpsHyp pers) {vis mode lane fu fe lfe} (hctx : CoreCtx vis fe lfe)
    (hf : absU fu = f) (depth : Std.U64) (m : Nat) :
    ∀ {st : arena.monad.AState} {lst : AState} (n : Std.U64) (pi : Bool) (a b : arena.handle.EIdx),
      absU n = m → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.core.defeq_loop pers vis st mode lane fu fe depth n pi a b) lst
        (defeqLoop (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
          lfe (absU depth) m pi (absEIdx a) (absEIdx b)) := by
  induction m with
  | zero =>
    intro st lst n pi a b hn hrel hinv
    rw [arena.core.defeq_loop, defeqLoop_zero]
    lockstep_f
  | succ m ih =>
    intro st lst n pi a b hn hrel hinv
    have hstep : ∀ {st : arena.monad.AState} {lst : AState} (i : Std.U64) (pi : Bool)
        (a b : arena.handle.EIdx), absU i = m → AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = a)
          (arena.core.defeq_step pers vis st mode lane fu fe depth i pi a b) lst
          (defeqStep (ConRon.Refine.absMode mode)
            (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
            (defeqLoop (ConRon.Refine.absMode mode)
              (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) m)
            pi (absEIdx a) (absEIdx b)) := by
      intro st lst i pi a b hi hrel hinv
      subst hi
      exact defeq_step_of_cont hk hx hctx hf depth i
        (fun pi a b hr hv => ih i pi a b rfl hr hv) pi a b hrel hinv
    clear ih
    rw [arena.core.defeq_loop, defeqLoop_succ]
    lockstep_f

/-- `arena::core::defeq_loop` against `Arena.defeqLoop`. -/
@[lockstep] theorem defeq_loop_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n pi a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_loop pers vis st mode lane fu fe depth n pi a b) lst
      (defeqLoop (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absU n) pi (absEIdx a) (absEIdx b)) :=
  defeq_loop_aux hk hx hctx hf depth _ n pi a b rfl hrel hinv

/-- `arena::core::defeq_step` against `Arena.defeqStep` with the rest of the
loop named — the port's `n` IS the twin's continuation `defeqLoop … (absU n)`. -/
@[lockstep] theorem defeq_step_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n pi a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_step pers vis st mode lane fu fe depth n pi a b) lst
      (defeqStep (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth)
        (defeqLoop (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
          lfe (absU depth) (absU n)) pi (absEIdx a) (absEIdx b)) :=
  defeq_step_of_cont hk hx hctx hf depth n
    (fun _ _ _ hr hv => defeq_loop_ls hk hx hr hv hctx hf) pi a b hrel hinv

/-- `arena::core::defeq_body` against `Arena.defeqBody` — `BodyRel`'s `defeq`
field, in `LS` form: the loop at its own step budget, at `pi = true`. -/
@[lockstep] theorem defeq_body_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_body pers vis st mode lane fu fe depth a b) lst
      (defeqBody (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        lfe (absU depth) (absEIdx a) (absEIdx b)) := by
  rw [arena.core.defeq_body, defeqBody]
  lockstep_f

end ConRon.Refine2.Lockstep

/-! The region's `lockstep_simp` rules, registered `scoped` (task #97-P5-Core
round 5): active under `open scoped ConRon.Refine2.Lockstep.CoreLSReg` only, so that they
stay out of the other tiers' `lockstep` runs (the Checker lane imports the
knot since task #97-T2-LOCKSTEP lane Checker DeclCheck). -/
namespace ConRon.Refine2.Lockstep.CoreLSReg
open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Arena ConRon.Refine2
open ConRon.Refine2.Lockstep.PF
attribute [scoped lockstep_simp] defeq_loop_fuel_val
end ConRon.Refine2.Lockstep.CoreLSReg
