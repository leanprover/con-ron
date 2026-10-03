/-
# `ConRon.Refine2.Core.LS.Defeq` — region F: definitional equality, lockstep

Task #97-P5-Core round 5, region F; restructured by task #109 (con-leche
8afe1815: the official kernel's `is_def_eq_core`).  The Theorem-2 lockstep
lemmas of the `defeq` half of `arena::core` against `Arena/Core.lean`:

| twin | Rust |
|---|---|
| `defeqPeelLeaf` | `defeq_peel_leaf` |
| `defeqPeel` | `defeq_peel` (a loop: induction on `peel`) |
| `defeqBinders` | `defeq_binders` |
| `defeqSpine` | `defeq_spine` |
| `boolTrueShortcut` | `bool_true_shortcut` |
| `quickDefEq` | `quick_defeq` |
| `isNatZero`, `natPred?`, `defeqOffset` | `is_nat_zero`, `nat_pred`, `defeq_offset` |
| `headIsProj`, `tryUnfoldProjApp` | `head_is_proj`, `try_unfold_proj_app` |
| `deltaQuick` | `delta_quick` |
| `lazyDeltaStep` | `lazy_delta_step` + the fragments `lazy_delta_side`, `lazy_delta_one` (the two mirrored one-sided arms, a `flipped` flag), `lazy_delta_both`, `lazy_delta_unfold_both` |
| `lazyDeltaReduction` | `lazy_delta_reduction` (its own budget: induction on `n`) + the fragment `lazy_delta_nat` |
| `lazyDeltaProjReduction` | `lazy_delta_proj_reduction` (its own budget: induction on `n`) + the fragment `lazy_delta_proj_fields` |
| `defeqProjPair` | `defeq_proj_pair` |
| `defeqStuck` | `defeq_stuck` + the fragments `defeq_str_app` (the two mirrored string-literal arms, a `flipped` flag), `defeq_apps` |
| `defeqBody` | `defeq_body` + the fragments `defeq_after_whnf`, `defeq_after_lazy` |

The two loops recurse on their OWN budget, `n + 1 ↦ n` in the twin and
`n - 1` at `n ≠ 0` in the port: the port's counter IS the twin's argument
(`absU n`), so each is an induction on it with no continuation — unlike the
old `defeqStep`/`defeqLoop` pair, whose step took the loop as a closure
(`Core/Arms/Loops.lean`'s finding 13).  The port's step and loop results
(`DeltaStepA`, `LazyResA`) are read through `absDeltaStepA`/`absLazyResA`.
-/
import ConRon.Refine2.Core.LS.PrimsF
import ConRon.Refine2.Core.LS.Leaves
import ConRon.Refine2.Core.LS.Shapes
import ConRon.Refine2.Core.LS.Lits
import ConRon.Refine2.Core.LS.Certs
import ConRon.Refine2.Core.LS.WhnfCore

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
  ConRon.Refine2.Lockstep.PF.beq_of_decEq

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
    (_hx : ExprOpsHyp pers)
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

/-! ## `quickDefEq` — the easy cases

The new region's twin tests a handle's tag as a `Prop` equality on the twin's
word (`a.tag == ETag.sort` after `lockstep_simp`'s `beq` rewriting, or
`h.tag == ETag.proj` under a `decide`): one equation per tag, as the port's
scalar test.  `PrimsF` has `lam`/`forallE`/`const`, local there. -/

theorem absU32_eq_sort (t : Std.U32) :
    (absU32 t = ETag.sort) = (t = arena.handle.ETAG_SORT) := by
  rw [← etag_sort_abs, PF.absU32_eq_absU32]

theorem absU32_eq_lit (t : Std.U32) :
    (absU32 t = ETag.lit) = (t = arena.handle.ETAG_LIT) := by
  rw [← etag_lit_abs, PF.absU32_eq_absU32]

theorem absU32_eq_app (t : Std.U32) :
    (absU32 t = ETag.app) = (t = arena.handle.ETAG_APP) := by
  rw [← etag_app_abs, PF.absU32_eq_absU32]

theorem absU32_eq_proj (t : Std.U32) :
    (absU32 t = ETag.proj) = (t = arena.handle.ETAG_PROJ) := by
  rw [← etag_proj_abs, PF.absU32_eq_absU32]

attribute [local lockstep_simp] absU32_eq_sort absU32_eq_lit absU32_eq_app absU32_eq_proj
  PF.absU32_eq_lam PF.absU32_eq_forallE PF.absU32_eq_const


/-- `lift_fueled_ls` takes the twin's message as an explicit argument, which
the port does not determine: specialised to the defeq region's. -/
theorem lift_fueled_level_ls {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (o : Option Bool) :
    LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst
      (liftFueled "level comparison" o) :=
  lift_fueled_ls hrel hinv o "level comparison"

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
@[lockstep] theorem quick_defeq_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.quick_defeq pers vis st mode lane fu fe depth a b) lst
      (quickDefEq (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        (absU depth) (absEIdx a) (absEIdx b)) := by
  have hview := @PF.view_wf_ls
  have hlift := @lift_fueled_level_ls
  rw [arena.core.quick_defeq, quickDefEq]
  lockstep_f

/-! ## Offsets: `isNatZero`, `natPred?`, `defeqOffset` -/

@[lockstep] theorem is_nat_zero_ls {pers st e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.is_nat_zero pers st e) lst
      (isNatZero (absEIdx e)) := by
  rw [arena.core.is_nat_zero, isNatZero]
  lockstep_f

@[lockstep] theorem nat_pred_ls {pers st e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = Option.map absEIdx a) (arena.core.nat_pred pers st e) lst
      (natPred? (absEIdx e)) := by
  rw [arena.core.nat_pred, natPred?]
  lockstep_f

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
@[lockstep] theorem defeq_offset_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_offset pers vis st mode lane fu fe depth a b) lst
      (defeqOffset (laneKnot (ConRon.Refine.absMode mode) lfe lane f) (absU depth)
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.defeq_offset, defeqOffset]
  lockstep_f

/-! ## Projection-headed terms -/

@[lockstep] theorem head_is_proj_ls {pers st e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.head_is_proj pers st e) lst
      (headIsProj (absEIdx e)) := by
  rw [arena.core.head_is_proj, headIsProj]
  lockstep_f

@[lockstep] theorem try_unfold_proj_app_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.try_unfold_proj_app pers vis st mode lane fu fe depth e) lst
      (tryUnfoldProjApp (laneKnot (ConRon.Refine.absMode mode) lfe lane f) (absU depth)
        (absEIdx e)) := by
  rw [arena.core.try_unfold_proj_app, tryUnfoldProjApp]
  lockstep_f

/-! ## One lazy-delta step

The two result types, abstracted: `arena::core::DeltaStepA` /
`LazyResA` carry handles where the twin's carry `EIdx`. -/

/-- The port's lazy-delta step outcome as the twin's. -/
def absDeltaStepA : arena.core.DeltaStepA → DeltaStepA
  | .Cont a b => .cont (absEIdx a) (absEIdx b)
  | .Eq => .eq
  | .Diff => .diff
  | .Unknown => .unknown

/-- The port's lazy-delta loop outcome as the twin's. -/
def absLazyResA : arena.core.LazyResA → LazyResA
  | .Verdict v => .verdict v
  | .Unknown a b => .unknown (absEIdx a) (absEIdx b)

attribute [local lockstep_simp] absDeltaStepA absLazyResA

@[lockstep] theorem delta_quick_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absDeltaStepA a)
      (arena.core.delta_quick pers vis st mode lane fu fe depth a b) lst
      (deltaQuick (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
        (absU depth) (absEIdx a) (absEIdx b)) := by
  rw [arena.core.delta_quick, deltaQuick]
  lockstep_f

/-! The port's step fragments have no twin of their own: `lazy_delta_side`
and `lazy_delta_one` are the twin's two mirrored one-sided arms at once (the
`flipped` flag), `lazy_delta_both` / `lazy_delta_unfold_both` its both-sides
arm; each is unfolded in place, where `flipped` is a literal. -/
attribute [lockstep_inline] arena.core.lazy_delta_side arena.core.lazy_delta_one
  arena.core.lazy_delta_both arena.core.lazy_delta_unfold_both

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
@[lockstep] theorem lazy_delta_step_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absDeltaStepA a)
      (arena.core.lazy_delta_step pers vis st mode lane fu fe depth a b) lst
      (lazyDeltaStep (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx a) (absEIdx b)) := by
  rw [arena.core.lazy_delta_step, lazyDeltaStep]
  lockstep_f

/-! ## The two lazy-delta loops: induction on the port's own budget

Each loop recurses on its own counter, `n - 1` in the port at `n ≠ 0` and the
pattern `n + 1 ↦ n` in the twin, so the port's `n` IS the twin's `absU n` —
no closure and no continuation, unlike the old `defeqLoop` (finding 13 of
`Core/Arms/Loops.lean`). -/

attribute [lockstep_inline] arena.core.lazy_delta_nat arena.core.lazy_delta_proj_fields

theorem lazyDeltaReduction_zero (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv)
    (d : Nat) (a b : EIdx) :
    lazyDeltaReduction mode r fe d 0 a b
      = Arena.fail (.internal "fuel exhausted: defeq loop") := by
  rw [lazyDeltaReduction]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem lazy_delta_reduction_aux {f : Nat} (hk : KnotRel f) {pers : arena.store.PersTier}
    (hx : ExprOpsHyp pers) {vis mode lane fu fe lfe} (hctx : CoreCtx vis fe lfe)
    (hf : absU fu = f) (depth : Std.U64) (m : Nat) :
    ∀ {st : arena.monad.AState} {lst : AState} (n : Std.U64) (a b : arena.handle.EIdx),
      absU n = m → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absLazyResA a)
        (arena.core.lazy_delta_reduction pers vis st mode lane fu fe depth n a b) lst
        (lazyDeltaReduction (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) m
          (absEIdx a) (absEIdx b)) := by
  induction m with
  | zero =>
    intro st lst n a b hn hrel hinv
    rw [arena.core.lazy_delta_reduction, lazyDeltaReduction_zero]
    lockstep_f
  | succ m ih =>
    intro st lst n a b hn hrel hinv
    rw [arena.core.lazy_delta_reduction, lazyDeltaReduction]
    lockstep_f

/-- `arena::core::lazy_delta_reduction` against `Arena.lazyDeltaReduction`. -/
@[lockstep] theorem lazy_delta_reduction_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth n a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absLazyResA a)
      (arena.core.lazy_delta_reduction pers vis st mode lane fu fe depth n a b) lst
      (lazyDeltaReduction (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absU n)
        (absEIdx a) (absEIdx b)) :=
  lazy_delta_reduction_aux hk hx hctx hf depth _ n a b rfl hrel hinv

theorem lazyDeltaProjReduction_zero (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv)
    (d : Nat) (sn : NIdx) (i : Nat) (a b : EIdx) :
    lazyDeltaProjReduction mode r fe d sn i 0 a b
      = Arena.fail (.internal "fuel exhausted: lazy delta projection loop") := by
  rw [lazyDeltaProjReduction]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem lazy_delta_proj_reduction_aux {f : Nat} (hk : KnotRel f) {pers : arena.store.PersTier}
    (hx : ExprOpsHyp pers) {vis mode lane fu fe lfe} (hctx : CoreCtx vis fe lfe)
    (hf : absU fu = f) (depth : Std.U64) (sn : arena.handle.NIdx) (i : Std.U64) (m : Nat) :
    ∀ {st : arena.monad.AState} {lst : AState} (n : Std.U64) (a b : arena.handle.EIdx),
      absU n = m → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.core.lazy_delta_proj_reduction pers vis st mode lane fu fe depth sn i n a b) lst
        (lazyDeltaProjReduction (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absNIdx sn)
          (absU i) m (absEIdx a) (absEIdx b)) := by
  induction m with
  | zero =>
    intro st lst n a b hn hrel hinv
    rw [arena.core.lazy_delta_proj_reduction, lazyDeltaProjReduction_zero]
    lockstep_f
  | succ m ih =>
    intro st lst n a b hn hrel hinv
    rw [arena.core.lazy_delta_proj_reduction, lazyDeltaProjReduction]
    lockstep_f

/-- `arena::core::lazy_delta_proj_reduction` against
`Arena.lazyDeltaProjReduction`. -/
@[lockstep] theorem lazy_delta_proj_reduction_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth sn i n a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.lazy_delta_proj_reduction pers vis st mode lane fu fe depth sn i n a b) lst
      (lazyDeltaProjReduction (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absNIdx sn)
        (absU i) (absU n) (absEIdx a) (absEIdx b)) :=
  lazy_delta_proj_reduction_aux hk hx hctx hf depth sn i _ n a b rfl hrel hinv

/-- The two step budgets agree: `DEFEQ_LOOP_FUEL = defeqLoopFuel = 100000`. -/
@[lockstep_simp] theorem absU_DEFEQ_LOOP_FUEL :
    absU arena.core.DEFEQ_LOOP_FUEL = defeqLoopFuel := by
  rw [arena.core.DEFEQ_LOOP_FUEL, defeqLoopFuel]; rfl

/-! ## The proj/proj check and the stuck comparison -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
@[lockstep] theorem defeq_proj_pair_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_proj_pair pers vis st mode lane fu fe depth a b) lst
      (defeqProjPair (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx a) (absEIdx b)) := by
  rw [arena.core.defeq_proj_pair, defeqProjPair]
  lockstep_f

/-! `defeq_str_app` is the twin's two mirrored string-literal arms at once
(the `flipped` flag) and `defeq_apps` its spine-wise application arm: both
unfolded in place. -/
attribute [lockstep_inline] arena.core.defeq_str_app arena.core.defeq_apps

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
@[lockstep] theorem defeq_stuck_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_stuck pers vis st mode lane fu fe depth a b) lst
      (defeqStuck (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx a) (absEIdx b)) := by
  have hview := @PF.view_wf_ls
  have hlift := @lift_fueled_level_ls
  rw [arena.core.defeq_stuck, defeqStuck]
  lockstep_f

/-! ## The body

`defeq_after_whnf` / `defeq_after_lazy` are the tail of `defeqBody` (the
port splits it after the cheap head normalization and after the lazy-delta
loop); unfolded in place. -/

attribute [lockstep_inline] arena.core.defeq_after_whnf arena.core.defeq_after_lazy

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- `arena::core::defeq_body` against `Arena.defeqBody`. -/
theorem defeq_body_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth a b lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a)
      (arena.core.defeq_body pers vis st mode lane fu fe depth a b) lst
      (defeqBody (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx a) (absEIdx b)) := by
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
end ConRon.Refine2.Lockstep.CoreLSReg

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.Lockstep.lazy_delta_reduction_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine2.Lockstep.lazy_delta_reduction_ls

/-- info: 'ConRon.Refine2.Lockstep.lazy_delta_proj_reduction_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine2.Lockstep.lazy_delta_proj_reduction_ls

/-- info: 'ConRon.Refine2.Lockstep.defeq_body_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine2.Lockstep.defeq_body_ls
