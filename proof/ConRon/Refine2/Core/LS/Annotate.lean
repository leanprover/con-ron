/-
# `ConRon.Refine2.Core.LS.Annotate` — region G: the annotation pass in lockstep

Task #97-P5-Core round 5, region G.  The second mutual block of
`arena::core` (`annotate_pis_leaf` … `knot_annotate`) against
`Arena/Core.lean`'s annotation twins: the two datum computations
(`annotPwPi`, `annotPwLam`), the outward rebuild (`annotateBindersOut`), the
two binder-telescope loops and their leaves, and the body `annotateBody`
(`BodyRel`'s `annotate` field) with its fragments `annotate_binder`,
`annotate_let`, `annotate_proj`, `annotate_proj_at`.
-/
import ConRon.Refine2.Core.LS.PrimsG

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PG

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

/-- Region A2's `pw_written`. -/
@[lockstep] theorem stub_pw_written_ls (pw : kernel.prop_when.PropWhen) :
    LSP (arena.core.pw_written pw)
      (fun b => TwinEq (pwWritten (ConRon.Refine.absPropWhen pw)) b) := by
  sorry

/-- Region A2's `annot_binder_meta`. -/
@[lockstep] theorem stub_annot_binder_meta_ls (pw : Option kernel.prop_when.PropWhen)
    (mb : kernel.expr.BinderMeta) :
    LSP (arena.core.annot_binder_meta pw mb)
      (fun m => TwinEq (annotBinderMeta (ExprOps.absPwOpt pw) (ConRon.Refine.absBinderMeta mb))
        (ConRon.Refine.absBinderMeta m)) := by
  sorry

/-- Region B's `nat_lit_supported`. -/
@[lockstep] theorem stub_nat_lit_supported_ls {pers vis st fe lfe lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.nat_lit_supported pers vis st fe) lst
      (natLitSupported lfe) := by
  sorry

/-- Region B's `str_lit_supported`. -/
@[lockstep] theorem stub_str_lit_supported_ls {pers vis st fe lfe lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.str_lit_supported pers vis st fe) lst
      (strLitSupported lfe) := by
  sorry

/-! ## Local normalisation -/

attribute [local lockstep_simp] absEIdxArr_eq vec_new_val vec_len_abs absStk_size
  List.map_append List.map_cons List.map_nil List.push_toArray
  List.nil_append List.size_toArray List.length_map
  ite_true ite_false Bool.not_true Bool.not_false Nat.add_sub_cancel

/-! ## Local tactic glue: the `ok`-bind feed, propositionally

`lockstep_core`'s `coreMove` feeds `ok v >>= k` to `k v` by
`replaceTargetDefEq`, but Aeneas's `Result` is an `ITree` and `bind_ok` is a
theorem, not a definitional equation: the kernel rejects the proof term.
`lockstep_g_okfeed` does the same move by `bind_tc_ok`, and runs before
`lockstep_core_step`; `lockstep_g_sbind` is `LS.bind` with the error arm
closed by `bind_tc_ok` too (a Rust continuation that re-packs a pair,
`let (st2, node) ← (… ; ok (st3, node1))`). -/

theorem LS.rust_ok_bind {γ α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {v : γ} {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R (k v) lst x) :
    LS pers R (ok v >>= k) lst x := by
  rw [bind_tc_ok]; exact h

theorem LSP.rust_ok_bind {γ α : Type} {v : γ} {k : γ → Result α} {Q : α → Prop}
    (h : LSP (k v) Q) : LSP (ok v >>= k) Q := by
  rw [bind_tc_ok]; exact h

open Lean Meta Elab Tactic in
elab "lockstep_g_okfeed" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some rp := rustPos ty | throwError "lockstep_g_okfeed: not a judgement"
    let m := (ty.getArg! rp).headBeta
    unless m.isAppOfArity ``Bind.bind 6 do throwError "lockstep_g_okfeed: no bind"
    unless (m.getArg! 4).headBeta.isAppOfArity ``Result.ok 2 do
      throwError "lockstep_g_okfeed: not an ok"
    let rule := if rp == 4 then ``LS.rust_ok_bind else ``LSP.rust_ok_bind
    let gs ← applyRule g rule
    let rest ← normAll [← pick gs `h]
    setGoals (rest ++ others)

macro "lockstep_g_errarm" : tactic => `(tactic| (
  intro e st1; unfold ErrArm; intro o st2 h
  simp only [Aeneas.Std.uncurry_apply_pair, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at h
  all_goals first | exact h.1.symm | exact h.symm))

open Lean Meta Elab Tactic in
elab "lockstep_g_sbind" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``LS 7 do throwError "lockstep_g_sbind: not LS"
    let m := (ty.getArg! 4).headBeta
    unless m.isAppOfArity ``Bind.bind 6 do throwError "lockstep_g_sbind: no bind"
    let f := m.getArg! 4
    match ← classify (← inferType f).appArg! with
    | .state => pure ()
    | _ => throwError "lockstep_g_sbind: not a state step"
    let gs ← applyRule g ``LS.bind
    specCore (← pick gs `hf)
    runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
    runClosed (← pick gs `he) (evalT `(tactic| lockstep_g_errarm))
    let rest ← cont (← pick gs `hk) [`a, `b, `st1, `lst1, `hR, `hrel, `hinv] (some `hR)
    setGoals ((← normAll rest) ++ others)

macro "lockstep_g1" : tactic =>
  `(tactic| (first | lockstep_g_okfeed | lockstep_core_step | lockstep_g_sbind))

/-- `lockstep_core` with region G's two moves. -/
macro "lockstep_g" : tactic =>
  `(tactic| repeat' lockstep_g1)

/-! ## The datum computations -/

@[lockstep] theorem annot_pw_pi_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth body lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = ConRon.Refine.absPropWhen a)
      (arena.core.annot_pw_pi pers vis st mode lane fu fe depth body) lst
      (annotPwPi (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx body)) := by
  rw [arena.core.annot_pw_pi, annotPwPi]
  lockstep_core

@[lockstep] theorem annot_pw_lam_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth body lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = ConRon.Refine.absPropWhen a)
      (arena.core.annot_pw_lam pers vis st mode lane fu fe depth body) lst
      (annotPwLam (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx body)) := by
  rw [arena.core.annot_pw_lam, annotPwLam]
  lockstep_core

/-! ## The outward rebuild -/

theorem annotate_binders_out_aux (m : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (is_lam : Bool) (d : Std.U64) (pw : Option kernel.prop_when.PropWhen)
      (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
      (n : Std.Usize) (cur : arena.handle.EIdx),
      ExprOpsHyp pers → n.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.annotate_binders_out pers st is_lam d pw stk n cur) lst
        (annotateBindersOut is_lam (absU d) (ExprOps.absPwOpt pw) (absStk stk) m
          (absEIdx cur)) := by
  induction m with
  | zero =>
    intro pers st lst is_lam d pw stk n cur hx hn hrel hinv
    rw [arena.core.annotate_binders_out.eq_def, annotateBindersOut]
    lockstep_g
  | succ m ih =>
    intro pers st lst is_lam d pw stk n cur hx hn hrel hinv
    have hidx : ∀ i : Std.Usize, i.val = m → LSP (alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice (arena.handle.EIdx × kernel.expr.BinderMeta)) stk i)
        (fun x => TwinEq ((absStk stk)[m]!) (absEIdx x.1, ConRon.Refine.absBinderMeta x.2)) :=
      fun i hi => hi ▸ stk_index_twin stk i
    rw [arena.core.annotate_binders_out.eq_def, annotateBindersOut]
    show LS _ _ _ _ _
    lockstep_g

@[lockstep] theorem annotate_binders_out_ls {pers st is_lam d pw stk n cur lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.annotate_binders_out pers st is_lam d pw stk n cur) lst
      (annotateBindersOut is_lam (absU d) (ExprOps.absPwOpt pw) (absStk stk) (absSz n)
        (absEIdx cur)) :=
  annotate_binders_out_aux _ is_lam d pw stk n cur hx rfl hrel hinv

/-! ## The telescope loops -/

@[lockstep] theorem annotate_pis_leaf_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.annotate_pis_leaf pers vis st mode lane fu fe d t k fvs stk) lst
      (annotatePisLeaf (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d)
        (absEIdx t) (absU k) (absEIdxArr fvs) (absStk stk)) := by
  rw [arena.core.annotate_pis_leaf, annotatePisLeaf]
  lockstep_g

@[lockstep] theorem annotate_lams_leaf_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.annotate_lams_leaf pers vis st mode lane fu fe d t k fvs stk) lst
      (annotateLamsLeaf (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d)
        (absEIdx t) (absU k) (absEIdxArr fvs) (absStk stk)) := by
  rw [arena.core.annotate_lams_leaf, annotateLamsLeaf]
  lockstep_g

section loops
attribute [local lockstep_simp] absStk_eq

theorem annotate_pis_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe lst} (d peel : Std.U64) (t : arena.handle.EIdx)
      (k : Std.U64) (fvs : alloc.vec.Vec arena.handle.EIdx)
      (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)),
      ExprOpsHyp pers → peel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.annotate_pis pers vis st mode lane fu fe d peel t k fvs stk) lst
        (annotatePis (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) n
          (absEIdx t) (absU k) (absEIdxArr fvs) (absStk stk)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe lst d peel t k fvs stk hx hn hrel hinv hctx hf
    rw [arena.core.annotate_pis, annotatePis]
    lockstep_g
  | succ n ih =>
    intro pers vis st mode lane fu fe lfe lst d peel t k fvs stk hx hn hrel hinv hctx hf
    rw [arena.core.annotate_pis, annotatePis]
    lockstep_g


@[lockstep] theorem annotate_pis_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d peel t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.annotate_pis pers vis st mode lane fu fe d peel t k fvs stk) lst
      (annotatePis (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absU peel)
        (absEIdx t) (absU k) (absEIdxArr fvs) (absStk stk)) :=
  annotate_pis_aux hk _ d peel t k fvs stk hx rfl hrel hinv hctx hf

theorem annotate_lams_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe lst} (d peel : Std.U64) (t : arena.handle.EIdx)
      (k : Std.U64) (fvs : alloc.vec.Vec arena.handle.EIdx)
      (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)),
      ExprOpsHyp pers → peel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.annotate_lams pers vis st mode lane fu fe d peel t k fvs stk) lst
        (annotateLams (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) n
          (absEIdx t) (absU k) (absEIdxArr fvs) (absStk stk)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe lst d peel t k fvs stk hx hn hrel hinv hctx hf
    rw [arena.core.annotate_lams, annotateLams]
    lockstep_g
  | succ n ih =>
    intro pers vis st mode lane fu fe lfe lst d peel t k fvs stk hx hn hrel hinv hctx hf
    rw [arena.core.annotate_lams, annotateLams]
    lockstep_g


@[lockstep] theorem annotate_lams_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe d peel t k fvs stk lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.annotate_lams pers vis st mode lane fu fe d peel t k fvs stk) lst
      (annotateLams (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU d) (absU peel)
        (absEIdx t) (absU k) (absEIdxArr fvs) (absStk stk)) :=
  annotate_lams_aux hk _ d peel t k fvs stk hx rfl hrel hinv hctx hf


/-! ## The body -/

attribute [lockstep_inline] arena.core.annotate_binder arena.core.annotate_let
  arena.core.annotate_proj arena.core.annotate_proj_at
attribute [local lockstep_simp] annotateBinder absIProjEntry bne_iff_ne ExprOps.absEIdxList
  vec_len_val'

/-- **`BodyRel.annotate` in lockstep**: `arena::core::annotate_body` against
`Arena.annotateBody`. -/
@[lockstep] theorem annotate_body_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.annotate_body pers vis st mode lane fu fe depth e) lst
      (annotateBody (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx e)) := by
  rw [arena.core.annotate_body, annotateBody]
  lockstep_g

end loops

end ConRon.Refine2.Lockstep
