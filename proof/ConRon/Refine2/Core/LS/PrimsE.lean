/-
# `ConRon.Refine2.Core.LS.PrimsE` — region E's primitive pairs (the inference bodies)

Task #97-P5-Core round 5, region E.  The `@[lockstep]` pairs the inference
bodies (`infer_body`, `infer_body_io`) and their loops (`infer_lams`,
`infer_pis`, `infer_spine`, `infer_spine_io`) step through that no earlier
file provides: the two binder stacks' abstractions, the level-list length and
the `const` projection, the memoised readbacks, the Rust-only value steps on
binder data, the two pins, and the pending intern prims.
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PE

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## Abstractions -/

/-- The λ loop's binder stack (`Vec<(EIdx, BinderMeta)>`, pushed outermost
first) as the twin's `Array (EIdx × BinderMeta)`. -/
def absLamStk (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    Array (EIdx × ConLeche.BinderMeta) :=
  (v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).toArray

/-- The ∀ loop's sort stack (`Vec<(LIdx, PropWhen)>`) as the twin's
`Array (LIdx × PropWhen)`. -/
def absPiStk (v : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)) :
    Array (LIdx × ConLeche.PropWhen) :=
  (v.val.map fun p => (absLIdx p.1, ConRon.Refine.absPropWhen p.2)).toArray

@[lockstep_simp] theorem absLamStk_size
    (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    (absLamStk v).size = v.val.length := by
  simp [absLamStk]

@[lockstep_simp] theorem absPiStk_size
    (v : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)) :
    (absPiStk v).size = v.val.length := by
  simp [absPiStk]

theorem absLamStk_push (v w : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (x)
    (h : w.val = v.val ++ [x]) :
    absLamStk w = (absLamStk v).push (absEIdx x.1, ConRon.Refine.absBinderMeta x.2) := by
  simp [absLamStk, h]

theorem absPiStk_push (v w : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)) (x)
    (h : w.val = v.val ++ [x]) :
    absPiStk w = (absPiStk v).push (absLIdx x.1, ConRon.Refine.absPropWhen x.2) := by
  simp [absPiStk, h]

theorem absEIdxArr_push (v w : alloc.vec.Vec arena.handle.EIdx) (x)
    (h : w.val = v.val ++ [x]) :
    absEIdxArr w = (absEIdxArr v).push (absEIdx x) := by
  simp [absEIdxArr, h]

@[lockstep_simp] theorem vec_len_abs {α : Type} (v : alloc.vec.Vec α) :
    absSz (alloc.vec.Vec.len v) = v.val.length := by
  simp [absSz]

@[lockstep_simp] theorem absEIdxArr_new :
    absEIdxArr (alloc.vec.Vec.new arena.handle.EIdx) = #[] := rfl

@[lockstep_simp] theorem absLamStk_new :
    absLamStk (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) = #[] := rfl

@[lockstep_simp] theorem absPiStk_new :
    absPiStk (alloc.vec.Vec.new (arena.handle.LIdx × kernel.prop_when.PropWhen)) = #[] := rfl

attribute [lockstep_simp] ConRon.Refine.absBinderMeta absConstT


/-! ## The io view of the lane knot

`laneKnotAt … io f` is `laneKnot … f` with (under `io`) its `infer` slot
rebound to `inferIO`; every other slot is the lane knot's own, by iota. -/

@[lockstep_simp] theorem laneKnotAt_whnf (m fe l io f) :
    (laneKnotAt m fe l io f).whnf = (laneKnot m fe l f).whnf := by cases io <;> rfl
@[lockstep_simp] theorem laneKnotAt_whnfCore (m fe l io f) :
    (laneKnotAt m fe l io f).whnfCore = (laneKnot m fe l f).whnfCore := by cases io <;> rfl
@[lockstep_simp] theorem laneKnotAt_defeq (m fe l io f) :
    (laneKnotAt m fe l io f).defeq = (laneKnot m fe l f).defeq := by cases io <;> rfl
@[lockstep_simp] theorem laneKnotAt_inferIO (m fe l io f) :
    (laneKnotAt m fe l io f).inferIO = (laneKnot m fe l f).inferIO := by cases io <;> rfl
@[lockstep_simp] theorem laneKnotAt_annotate (m fe l io f) :
    (laneKnotAt m fe l io f).annotate = (laneKnot m fe l f).annotate := by cases io <;> rfl

/-- `ensureSort` reads its record's `whnf` slot alone. -/
@[lockstep_simp] theorem ensureSort_laneKnotAt (m fe l io f lfe d e) :
    ensureSort (laneKnotAt m fe l io f) lfe d e = ensureSort (laneKnot m fe l f) lfe d e := by
  cases io <;> rfl

/-! ## Rust-only value steps -/

@[lockstep] theorem verified_checks_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.verified_checks m)
      (fun b => b = (ConRon.Refine.absMode m).verifiedChecks) :=
  by
  intro b h
  cases m <;> (simp only [kernel.env.verified_checks, Result.ok.injEq] at h; rw [← h]; rfl)

@[lockstep] theorem io_skip_ls (m : kernel.env.CheckMode) (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.env.io_skip m pw)
      (fun b => b = (ConRon.Refine.absMode m).ioSkip (ConRon.Refine.absPropWhen pw)) :=
  by
  intro b h
  cases m
  · simp only [kernel.env.io_skip, kernel.env.certs, bind_tc_ok, reduceIte] at h
    rw [ConRon.Refine.PropWhen.is_never_refines h]; rfl
  · simp only [kernel.env.io_skip, kernel.env.certs, bind_tc_ok, Bool.false_eq_true, if_false,
      Result.ok.injEq] at h
    rw [← h]; rfl

/-- The twin's `(if c then a else b) >>= g`, pushed into the branches so that
the twin test sits at the head where `lockstep` decides it. -/
theorem twin_ite_bind {α β : Type} {c : Prop} [Decidable c] (a b : AM α) (g : α → AM β) :
    ((if c then a else b) >>= g) = (if c then a >>= g else b >>= g) := by
  split <;> rfl


/-! ## Local tactic moves (reported to the coordinator)

1. **`ok v >>= k` is NOT definitionally `k v`** for Aeneas's `Result` (an
   `ITree`; `bind_tc_ok` is proved by `simp`, not `rfl`).  `lockstep_core`'s
   `coreMove` feeds an `ok` to the continuation with `replaceTargetDefEq`,
   which does not check, and the kernel then rejects the proof ("application
   type mismatch").  `LS.rust_ok_bind` is the propositional step.
2. **An error arm through a pair-returning inner block**
   (`let (st1, cert) ← (match r with … | Err e1 => ok (st2, Err e1)); match
   cert with … | Err e1 => ok (Err e1, st1)`): `errArm` head-normalises only
   and cannot see through the inner `ok … >>= k'`.  `ls_state_bind` is
   `LS.bind` with the error arm closed by `simp`. -/

theorem LS.rust_ok_bind {γ α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {v : γ} {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R (k v) lst x) :
    LS pers R (ok v >>= k) lst x := by
  rw [bind_tc_ok]; exact h

theorem LSP.rust_ok_bind {γ α : Type} {v : γ} {k : γ → Result α} {Q : α → Prop}
    (h : LSP (k v) Q) : LSP (ok v >>= k) Q := by
  rw [bind_tc_ok]; exact h

open Lean Meta Elab Tactic in
/-- Feed an `ok v` to the Rust continuation, propositionally. -/
elab "ls_ok_bind" : tactic => withMainContext do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let ty ← instantiateMVars (← g.getType)
  let some rp := rustPos ty | throwError "ls_ok_bind: not a judgement"
  let m := (ty.getArg! rp).headBeta
  unless m.isAppOfArity ``Bind.bind 6 do throwError "ls_ok_bind: not a bind"
  let f ← headNorm (m.getArg! 4)
  unless f.isAppOfArity ``Result.ok 2 do throwError "ls_ok_bind: not an ok"
  let m' := mkAppN m.getAppFn (m.getAppArgs.set! 4 f)
  let g ← g.replaceTargetDefEq (mkAppN ty.getAppFn (ty.getAppArgs.set! rp m'))
  let gs ← applyRule g (if rp == 4 then ``LS.rust_ok_bind else ``LSP.rust_ok_bind)
  let g' ← pick gs `h
  setGoals ((← normAll [g']) ++ others)

open Lean Meta Elab Tactic in
/-- `LS.bind` with the error arm closed by `simp`. -/
elab "ls_state_bind" : tactic => withMainContext do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let gs ← applyRule g ``LS.bind
  specCore (← pick gs `hf)
  runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
  runClosed (← pick gs `he) (evalT `(tactic| (
    intro e st1 o st' h
    simp at h
    first | exact h.1.symm | exact h.symm | (obtain ⟨rfl, -⟩ := h; rfl))))
  let rest ← cont (← pick gs `hk) [`a, `b, `st1, `lst1, `hR, `hrel, `hinv] (some `hR)
  setGoals ((← normAll rest) ++ others)

/-- `lockstep_core` with the two local moves. -/
macro "lockstep_e" : tactic =>
  `(tactic| repeat' (first | ls_ok_bind | lockstep_core_step | ls_state_bind))

end ConRon.Refine2.Lockstep.PE
