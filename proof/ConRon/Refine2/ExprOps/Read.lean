/-
# `ConRon.Refine2.ExprOps.Read` — Theorem 2 for `expr_ops`' READ-ONLY slice

DESIGN.md §8.2's Theorem 2 for the functions of
`crates/con-ron-core/src/arena/expr_ops.rs` that take `st : &AState` — a
SHARED reference, so they read the store and never append.

## The statement: lockstep (task #97-T2-LOCKSTEP)

A read-only Rust function answers `Result (Result α CheckError)`; its
`@[lockstep]` form is the judgement `LSR pers R (rust_f …) st lst (twinF …)`
of `Refine2/Tactic/Lockstep.lean` (what a caller's bind rule wants), and its
public form is `AOut₀ A pers o st ((twinF …).run lst)` (`LSR.toAOut₀`).  The
premises are `AStateRel₀` and `AStateInv` — representation facts only.
Every proof is `apply LSR.ofLS` (thread the unchanged state through the
result), `rw [rust_f, twinF]`, `lockstep`; a fuel recursion states the `_aux`
at `fuel.val = n` and runs that line in each case of `induction n`.

## What changed with the lockstep migration

* **No `EResolves` premise and no `StoreWF`.**  They were there because nine
  of these twins read the VIEW where the Rust reads the TAG (task
  #97-T2-AUDIT's D1): on a dangling handle whose tag is not the one tested,
  the Rust answered `Ok` and the twin threw.  The twins now test the tag
  first and read the same typed projection as the Rust (`viewBind`,
  `viewBindI`, `viewFVarTy`), so a dangling handle behaves the same on both
  sides: `is_lam`, `lam_pw`, `forall_pw`, `strip_lams`, `strip_pis`,
  `pi_arity`, `fvar_type_d` (and `pi_result`, which task #97-P5-Core round 4
  had already made tag-first).
* **The memoised DAG walks** (`wscoped_b_go`, `fvar_leaves_go`,
  `leaves_sub_go`) thread their walk-local memo as an argument and a result;
  its relation (`WMemoRel`, `SeenRel`, `LMemoRel`, now in
  `ExprOps/Pure.lean`) is part of the ANSWER relation (`∃ m', WMemoRel a.2 m'
  ∧ b = (a.1, m')`).  Their Rust-only splits (`*_node`, `*_two`, extraction
  rule 5) are unfolded in place before `lockstep`, so the two programs line up
  arm by arm; they have no statement of their own.
* **`fvar_leaves_go`'s accumulator is the twin's list REVERSED** (the Rust
  pushes where the twin conses), and `leaves_sub_go`'s base list is therefore
  stated reversed too; `leafMem` is order blind (`leafMem_reverse`, a
  `lockstep_simp` rule), which is what makes the deviation sound at its one
  reader.
-/
import ConRon.Refine2.Tactic.Prims
import ConRon.Refine2.ExprOps.Pure
import ConRon.Arena.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.ExprOps

open ConRon.Arena
open ConRon.Refine2
open ConRon.Refine2.Lockstep
open ConRon.Refine.HashMap2 (Inv RelOn toFun)

/-! ## The result abstractions this slice needs -/

/-- A `Vec<EIdx>` result as the twin's `List EIdx` (`get_app_args`). -/
def absEIdxList (v : alloc.vec.Vec arena.handle.EIdx) : List EIdx :=
  v.val.map absEIdx

/-- A `Vec<(u64, EIdx)>` leaf list as the twin's `List (Nat × EIdx)`. -/
def absLeaves (v : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) :
    List (Nat × EIdx) :=
  v.val.map fun p => (absU p.1, absEIdx p.2)

/-- A `Vec<(EIdx, BinderMeta)>` telescope as the twin's
`List (EIdx × BinderMeta)` (`strip_lams`, `strip_pis`). -/
def absBinders (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    List (EIdx × ConLeche.BinderMeta) :=
  v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)

/-- `strip_lams`/`strip_pis`' whole answer. -/
def absStrip
    (o : Option ((alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) ×
      arena.handle.EIdx)) :
    Option (List (EIdx × ConLeche.BinderMeta) × EIdx) :=
  o.map fun p => (absBinders p.1, absEIdx p.2)

/-- `lam_pw`/`forall_pw`' answer. -/
def absPwOpt (o : Option kernel.prop_when.PropWhen) : Option ConLeche.PropWhen :=
  o.map ConRon.Refine.absPropWhen

/-- `result_sort`'s answer. -/
def absLIdxOpt (o : Option arena.handle.LIdx) : Option LIdx := o.map absLIdx

attribute [lockstep_simp] absEIdxList absLeaves absLIdxOpt absPwOpt absBinders absStrip

/-! ## "The handle resolves" — **deprecated** (task #97-T2-LOCKSTEP)

No statement of this file takes it any more: the D1 twins now test the tag
first, as the port does, so a dangling handle behaves the same on both sides.
The definition stays for the Core and Checker statements that still name it.

Finding 1's hypothesis.  `EResolves` is task #97s's template rule 4 at the
arena's `view`: an `isSome`, not a named view, so that a side goal is
metavariable-free.  `StoreWF` is what carries it to the children — `EWFAt`'s
`childOK` clause — and is `Arena/WF.lean`'s own predicate, so nothing new is
assumed here that Theorem 1 does not already establish. -/

/-- The handle decodes in the twin's store: the state the Rust's tag-first
dispatch and the twin's view-first dispatch agree on. -/
def EResolves (lst : AState) (h : EIdx) : Prop := (lst.store.view h).isSome = true

/-! ## The three memo-threading outcome shapes of the pre-lockstep statements

**Deprecated** (task #97-T2-LOCKSTEP): this file's walks are stated in the
`LS` judgement now, with the memo relation inside the answer relation (`∃ m',
WMemoRel a.2 m' ∧ b = (a.1, m')`).  `WOut`/`LOut`/`FOut` stay only for the
Inductives and Checker statements that still name them. -/

/-- The outcome of a `(Bool × memo)`-returning walk keyed on `(handle, depth)`. -/
def WOut (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result (Bool × ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
      kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError ((Bool × Std.HashMap (EIdx × Nat) Bool) × AState)) :
    Prop :=
  match o with
  | .Ok r => ∃ m' lst', x = .ok ((r.1, m'), lst') ∧ WMemoRel r.2 m' ∧
      AStateRel pers st' lst' ∧ AStateInv pers st' ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e x

/-- The outcome of a `(Bool × memo)`-returning walk keyed on the handle. -/
def LOut (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result (Bool × ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError ((Bool × Std.HashMap EIdx Bool) × AState)) :
    Prop :=
  match o with
  | .Ok r => ∃ m' lst', x = .ok ((r.1, m'), lst') ∧ LMemoRel r.2 m' ∧
      AStateRel pers st' lst' ∧ AStateInv pers st' ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e x

/-- The outcome of `fvar_leaves_go`'s accumulator-and-`seen` pair.

**Finding 12 (this round): the port's accumulator is the twin's list
REVERSED, and the statement has to say so.**  `fvar_leaves_go` pushes where
the twin conses — the port's own doc comment says "the two lists are each
other's reverse" and explains why (a `Vec` has no cons, and `leaf_mem`, the
only reader, is order blind).  P5-0 stated this group at `absLeaves r.1`,
which is false; it is `(absLeaves r.1).reverse`.  The same correction goes to
`fvar_leaves_fast_refines`, which P5-0 had "closed" against the wrong
statement (vacuously, off the `sorry` below it). -/
def FOut (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result ((alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) ×
      ron.hashmap2.HashMap2 arena.handle.EIdx Bool) kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError
      ((List (Nat × EIdx) × Std.HashMap EIdx Unit) × AState)) : Prop :=
  match o with
  | .Ok r => ∃ s' lst', x = .ok (((absLeaves r.1).reverse, s'), lst') ∧
      SeenRel r.2 s' ∧
      AStateRel pers st' lst' ∧ AStateInv pers st' ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e x


section size_b
attribute [local lockstep_simp] sizeBArmApp sizeBArmBind sizeBArmLet sizeBArmProj

theorem size_b_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absU a) (arena.expr_ops.size_b pers st fuel h) st lst
        (sizeB n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.size_b, sizeB_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.size_b, sizeB_succ]
    lockstep

@[lockstep] theorem size_b_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absU a) (arena.expr_ops.size_b pers st fuel h) st lst
      (sizeB (absU fuel) (absEIdx h)) :=
  size_b_aux _ fuel h rfl hrel hinv

theorem size_b_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.size_b pers st fuel h = ok o) :
    AOut₀ absU pers o st ((sizeB (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (size_b_ls hrel hinv fuel h) hrun

end size_b

section size_f
attribute [local lockstep_simp] sizeFArmFVar sizeFArmApp sizeFArmBind sizeFArmLet sizeFArmProj

theorem size_f_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absU a) (arena.expr_ops.size_f pers st fuel h) st lst
        (sizeF n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.size_f, sizeF_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.size_f, sizeF_succ]
    lockstep

@[lockstep] theorem size_f_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absU a) (arena.expr_ops.size_f pers st fuel h) st lst
      (sizeF (absU fuel) (absEIdx h)) :=
  size_f_aux _ fuel h rfl hrel hinv

theorem size_f_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.size_f pers st fuel h = ok o) :
    AOut₀ absU pers o st ((sizeF (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (size_f_ls hrel hinv fuel h) hrun

end size_f

section has_fvar
attribute [local lockstep_simp] hasFvarArmApp hasFvarArmBind hasFvarArmLet

theorem has_fvar_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = id a) (arena.expr_ops.has_fvar pers st fuel h) st lst
        (hasFvar n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.has_fvar, hasFvar_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.has_fvar, hasFvar_succ]
    lockstep

@[lockstep] theorem has_fvar_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = id a) (arena.expr_ops.has_fvar pers st fuel h) st lst
      (hasFvar (absU fuel) (absEIdx h)) :=
  has_fvar_aux _ fuel h rfl hrel hinv

theorem has_fvar_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.has_fvar pers st fuel h = ok o) :
    AOut₀ id pers o st ((hasFvar (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (has_fvar_ls hrel hinv fuel h) hrun

end has_fvar

section fvar_leaves
attribute [local lockstep_simp] fvarLeavesArmFVar fvarLeavesArmApp fvarLeavesArmBind fvarLeavesArmLet

theorem fvar_leaves_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absLeaves a) (arena.expr_ops.fvar_leaves pers st fuel h) st lst
        (fvarLeaves n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.fvar_leaves, fvarLeaves_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.fvar_leaves, fvarLeaves_succ]
    lockstep

@[lockstep] theorem fvar_leaves_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absLeaves a) (arena.expr_ops.fvar_leaves pers st fuel h) st lst
      (fvarLeaves (absU fuel) (absEIdx h)) :=
  fvar_leaves_aux _ fuel h rfl hrel hinv

theorem fvar_leaves_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_leaves pers st fuel h = ok o) :
    AOut₀ absLeaves pers o st ((fvarLeaves (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (fvar_leaves_ls hrel hinv fuel h) hrun

end fvar_leaves

section wscoped_b
attribute [local lockstep_simp] wscopedBArmApp wscopedBArmBind wscopedBArmLet

theorem wscoped_b_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (d : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = id a) (arena.expr_ops.wscoped_b pers st fuel d h) st lst
        (wscopedB n (absU d) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel d h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.wscoped_b, wscopedB_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel d h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.wscoped_b, wscopedB_succ]
    lockstep

@[lockstep] theorem wscoped_b_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (d : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = id a) (arena.expr_ops.wscoped_b pers st fuel d h) st lst
      (wscopedB (absU fuel) (absU d) (absEIdx h)) :=
  wscoped_b_aux _ fuel d h rfl hrel hinv

theorem wscoped_b_refines {pers st lst} {fuel : Std.U64} {d : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.wscoped_b pers st fuel d h = ok o) :
    AOut₀ id pers o st ((wscopedB (absU fuel) (absU d) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (wscoped_b_ls hrel hinv fuel d h) hrun

end wscoped_b

section loose_bvars_bounded
attribute [local lockstep_simp] looseBArmApp looseBArmBind looseBArmLet

theorem loose_bvars_bounded_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (k : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = id a) (arena.expr_ops.loose_bvars_bounded pers st fuel k h) st lst
        (looseBVarsBounded n (absU k) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel k h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.loose_bvars_bounded, looseBVarsBounded_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel k h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.loose_bvars_bounded, looseBVarsBounded_succ]
    lockstep

@[lockstep] theorem loose_bvars_bounded_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = id a) (arena.expr_ops.loose_bvars_bounded pers st fuel k h) st lst
      (looseBVarsBounded (absU fuel) (absU k) (absEIdx h)) :=
  loose_bvars_bounded_aux _ fuel k h rfl hrel hinv

theorem loose_bvars_bounded_refines {pers st lst} {fuel : Std.U64} {k : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.loose_bvars_bounded pers st fuel k h = ok o) :
    AOut₀ id pers o st ((looseBVarsBounded (absU fuel) (absU k) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (loose_bvars_bounded_ls hrel hinv fuel k h) hrun

end loose_bvars_bounded

section result_sort

theorem result_sort_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absLIdxOpt a) (arena.expr_ops.result_sort pers st fuel h) st lst
        (resultSort n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.result_sort, resultSort]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.result_sort, resultSort]
    lockstep

@[lockstep] theorem result_sort_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absLIdxOpt a) (arena.expr_ops.result_sort pers st fuel h) st lst
      (resultSort (absU fuel) (absEIdx h)) :=
  result_sort_aux _ fuel h rfl hrel hinv

theorem result_sort_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.result_sort pers st fuel h = ok o) :
    AOut₀ absLIdxOpt pers o st ((resultSort (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (result_sort_ls hrel hinv fuel h) hrun

end result_sort

section get_app_fn

theorem get_app_fn_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.get_app_fn pers st fuel h) st lst
        (getAppFn n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.get_app_fn, getAppFn]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.get_app_fn, getAppFn]
    lockstep

@[lockstep] theorem get_app_fn_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.get_app_fn pers st fuel h) st lst
      (getAppFn (absU fuel) (absEIdx h)) :=
  get_app_fn_aux _ fuel h rfl hrel hinv

theorem get_app_fn_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.get_app_fn pers st fuel h = ok o) :
    AOut₀ absEIdx pers o st ((getAppFn (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (get_app_fn_ls hrel hinv fuel h) hrun

end get_app_fn

section pi_result

theorem pi_result_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.pi_result pers st fuel h) st lst
        (piResult n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.pi_result, piResult]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.pi_result, piResult]
    lockstep

@[lockstep] theorem pi_result_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.pi_result pers st fuel h) st lst
      (piResult (absU fuel) (absEIdx h)) :=
  pi_result_aux _ fuel h rfl hrel hinv

theorem pi_result_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.pi_result pers st fuel h = ok o) :
    AOut₀ absEIdx pers o st ((piResult (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (pi_result_ls hrel hinv fuel h) hrun

end pi_result

section pi_arity

theorem pi_arity_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absU a) (arena.expr_ops.pi_arity pers st fuel h) st lst
        (piArity n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.pi_arity, piArity]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.pi_arity, piArity]
    lockstep

@[lockstep] theorem pi_arity_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absU a) (arena.expr_ops.pi_arity pers st fuel h) st lst
      (piArity (absU fuel) (absEIdx h)) :=
  pi_arity_aux _ fuel h rfl hrel hinv

theorem pi_arity_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.pi_arity pers st fuel h = ok o) :
    AOut₀ absU pers o st ((piArity (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (pi_arity_ls hrel hinv fuel h) hrun

end pi_arity


section getAppArgs

theorem get_app_args_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx) (k : Std.Usize),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absEIdxList a) (arena.expr_ops.get_app_args_go pers st fuel h k)
        st lst (getAppArgs n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h k hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.get_app_args_go, getAppArgs]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h k hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.get_app_args_go, getAppArgs]
    lockstep

end getAppArgs

section oneNode

theorem is_lam_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = a) (arena.expr_ops.is_lam pers st h) st lst (isLam (absEIdx h)) := by
  apply LSR.ofLS
  rw [arena.expr_ops.is_lam, isLam]
  lockstep

theorem lam_pw_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absPwOpt a) (arena.expr_ops.lam_pw pers st h) st lst
      (lamPw (absEIdx h)) := by
  apply LSR.ofLS
  rw [arena.expr_ops.lam_pw, lamPw]
  lockstep

theorem forall_pw_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absPwOpt a) (arena.expr_ops.forall_pw pers st h) st lst
      (forallPw (absEIdx h)) := by
  apply LSR.ofLS
  rw [arena.expr_ops.forall_pw, forallPw]
  lockstep

theorem fvar_type_d_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.fvar_type_d pers st h) st lst
      (fvarTypeD (absEIdx h)) := by
  apply LSR.ofLS
  rw [arena.expr_ops.fvar_type_d, fvarTypeD]
  lockstep

theorem lidx_has_param_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LIdx) :
    LSV pers (fun a b => b = a) (arena.expr_ops.lidx_has_param pers st h) st lst
      (LIdx.hasParam (absLIdx h)) := by
  apply LSV.ofLS
  rw [arena.expr_ops.lidx_has_param, LIdx.hasParam]
  lockstep

theorem eidx_has_level_param_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = a) (arena.expr_ops.eidx_has_level_param pers st h) st lst
      (EIdx.hasLevelParam (absEIdx h)) := by
  apply LSV.ofLS
  rw [arena.expr_ops.eidx_has_level_param, EIdx.hasLevelParam]
  lockstep

end oneNode

section strip

theorem strip_lams_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (k : Std.U64) (h : arena.handle.EIdx),
      k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absStrip a) (arena.expr_ops.strip_lams pers st k h) st lst
        (stripLams n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst k h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.strip_lams, stripLams]
    lockstep
  | succ m ih =>
    intro pers st lst k h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.strip_lams, stripLams]
    lockstep

theorem strip_pis_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (k : Std.U64) (h : arena.handle.EIdx),
      k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absStrip a) (arena.expr_ops.strip_pis pers st k h) st lst
        (stripPis n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst k h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.strip_pis, stripPis]
    lockstep
  | succ m ih =>
    intro pers st lst k h hn hrel hinv
    apply LSR.ofLS
    rw [arena.expr_ops.strip_pis, stripPis]
    lockstep

end strip


open Lean Meta Elab Tactic in
elab "dbg_ih" : tactic => do
  let g ← getMainGoal
  g.withContext do
  for d in (← getLCtx) do
    if d.userName.toString == "ih" then
      let t ← instantiateMVars d.type
      forallTelescope t fun xs c => do
        logInfo m!"ih concl head {c.getAppFn} nargs {c.getAppNumArgs}; rust {(ConRon.Refine2.Lockstep.judgementRustArg? c)}"

section wscoped
attribute [local lockstep_simp] wscopedBGoArmApp wscopedBGoArmBind wscopedBGoArmLet



theorem wscoped_b_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool) (lm : Std.HashMap (EIdx × Nat) Bool)
      (fuel d : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → WMemoRel rm lm →
      LSR pers (fun a b => ∃ m', WMemoRel a.2 m' ∧ b = (a.1, m'))
        (arena.expr_ops.wscoped_b_go pers st rm fuel d h) st lst
        (wscopedBGo lm n (absU d) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel d h hn hrel hinv hm
    apply LSR.ofLS
    rw [arena.expr_ops.wscoped_b_go, wscopedBGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst rm lm fuel d h hn hrel hinv hm
    apply LSR.ofLS
    rw [arena.expr_ops.wscoped_b_go, wscopedBGo_succ]
    unfold arena.expr_ops.wscoped_b_node arena.expr_ops.wscoped_b_two
    lockstep


end wscoped

section fvl
attribute [local lockstep_simp] fvarLeavesGoArmApp fvarLeavesGoArmBind fvarLeavesGoArmLet

theorem fvar_leaves_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (racc : alloc.vec.Vec (Std.U64 × arena.handle.EIdx))
      (rs : ron.hashmap2.HashMap2 arena.handle.EIdx Bool) (ls : Std.HashMap EIdx Unit)
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → SeenRel rs ls →
      LSR pers (fun a b => ∃ s', SeenRel a.2 s' ∧ b = ((absLeaves a.1).reverse, s'))
        (arena.expr_ops.fvar_leaves_go pers st racc rs fuel h) st lst
        (fvarLeavesGo (absLeaves racc).reverse ls n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst racc rs ls fuel h hn hrel hinv hs
    apply LSR.ofLS
    rw [arena.expr_ops.fvar_leaves_go, fvarLeavesGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst racc rs ls fuel h hn hrel hinv hs
    apply LSR.ofLS
    rw [arena.expr_ops.fvar_leaves_go, fvarLeavesGo_succ]
    unfold arena.expr_ops.fvar_leaves_node arena.expr_ops.fvar_leaves_two
    lockstep

end fvl

section lsub
attribute [local lockstep_simp] leavesSubArmApp leavesSubArmBind leavesSubArmLet

theorem leaves_sub_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx))
      (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool) (lm : Std.HashMap EIdx Bool)
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → LMemoRel rm lm →
      LSR pers (fun a b => ∃ m', LMemoRel a.2 m' ∧ b = (a.1, m'))
        (arena.expr_ops.leaves_sub_go pers st bl rm fuel h) st lst
        (leavesSubGo (absLeaves bl).reverse lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst bl rm lm fuel h hn hrel hinv hm
    apply LSR.ofLS
    rw [arena.expr_ops.leaves_sub_go, leavesSubGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst bl rm lm fuel h hn hrel hinv hm
    apply LSR.ofLS
    rw [arena.expr_ops.leaves_sub_go, leavesSubGo_succ]
    unfold arena.expr_ops.leaves_sub_node arena.expr_ops.leaves_sub_two
    lockstep

end lsub

section entries

@[lockstep] theorem wscoped_b_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} (hm : WMemoRel rm lm) (fuel d : Std.U64)
    (h : arena.handle.EIdx) :
    LSR pers (fun a b => ∃ m', WMemoRel a.2 m' ∧ b = (a.1, m'))
      (arena.expr_ops.wscoped_b_go pers st rm fuel d h) st lst
      (wscopedBGo lm (absU fuel) (absU d) (absEIdx h)) :=
  wscoped_b_go_aux _ rm lm fuel d h rfl hrel hinv hm

@[lockstep] theorem fvar_leaves_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (racc : alloc.vec.Vec (Std.U64 × arena.handle.EIdx))
    {rs : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {ls : Std.HashMap EIdx Unit}
    (hs : SeenRel rs ls) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => ∃ s', SeenRel a.2 s' ∧ b = ((absLeaves a.1).reverse, s'))
      (arena.expr_ops.fvar_leaves_go pers st racc rs fuel h) st lst
      (fvarLeavesGo (absLeaves racc).reverse ls (absU fuel) (absEIdx h)) :=
  fvar_leaves_go_aux _ racc rs ls fuel h rfl hrel hinv hs

@[lockstep] theorem leaves_sub_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx))
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {lm : Std.HashMap EIdx Bool}
    (hm : LMemoRel rm lm) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => ∃ m', LMemoRel a.2 m' ∧ b = (a.1, m'))
      (arena.expr_ops.leaves_sub_go pers st bl rm fuel h) st lst
      (leavesSubGo (absLeaves bl).reverse lm (absU fuel) (absEIdx h)) :=
  leaves_sub_go_aux _ bl rm lm fuel h rfl hrel hinv hm

@[lockstep] theorem wscoped_b_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel d : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = a) (arena.expr_ops.wscoped_b_fast pers st fuel d h) st lst
      (wscopedBFast (absU fuel) (absU d) (absEIdx h)) := by
  apply LSR.ofLS
  rw [arena.expr_ops.wscoped_b_fast, wscopedBFast]
  lockstep

@[lockstep] theorem fvar_leaves_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = (absLeaves a).reverse)
      (arena.expr_ops.fvar_leaves_fast pers st fuel h) st lst
      (fvarLeavesFast (absU fuel) (absEIdx h)) := by
  apply LSR.ofLS
  rw [arena.expr_ops.fvar_leaves_fast, fvarLeavesFast]
  lockstep

@[lockstep] theorem leaf_guard_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (fab base : arena.handle.EIdx) :
    LSR pers (fun a b => b = a) (arena.expr_ops.leaf_guard pers st fuel fab base) st lst
      (leafGuard (absU fuel) (absEIdx fab) (absEIdx base)) := by
  apply LSR.ofLS
  rw [arena.expr_ops.leaf_guard, leafGuard]
  lockstep

end entries


/-! ## `getAppArgs`, the one-node readers and the telescope strips: the `@[lockstep]` forms -/

@[lockstep] theorem get_app_args_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) (k : Std.Usize) :
    LSR pers (fun a b => b = absEIdxList a) (arena.expr_ops.get_app_args_go pers st fuel h k)
      st lst (getAppArgs (absU fuel) (absEIdx h)) :=
  get_app_args_go_aux _ fuel h k rfl hrel hinv

@[lockstep] theorem get_app_args_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdxList a) (arena.expr_ops.get_app_args pers st fuel h)
      st lst (getAppArgs (absU fuel) (absEIdx h)) := by
  rw [arena.expr_ops.get_app_args]; exact get_app_args_go_ls hrel hinv fuel h 0#usize

@[lockstep] theorem strip_lams_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absStrip a) (arena.expr_ops.strip_lams pers st k h) st lst
      (stripLams (absU k) (absEIdx h)) :=
  strip_lams_aux _ k h rfl hrel hinv

@[lockstep] theorem strip_pis_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absStrip a) (arena.expr_ops.strip_pis pers st k h) st lst
      (stripPis (absU k) (absEIdx h)) :=
  strip_pis_aux _ k h rfl hrel hinv

attribute [lockstep] is_lam_ls lam_pw_ls forall_pw_ls fvar_type_d_ls lidx_has_param_ls
  eidx_has_level_param_ls

@[lockstep] theorem inst_list_cutoff_ls' {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) (k : Std.U64) :
    LSV pers (fun a b => b = a) (arena.expr_ops.inst_list_cutoff pers st h k) st lst
      (instListCutoff (absEIdx h) (absU k)) := by
  apply LSV.ofLS
  rw [arena.expr_ops.inst_list_cutoff, instListCutoff]
  lockstep

/-! ## The public statements (`AOut₀`, read-only: the Rust post-state is its pre-state) -/

theorem get_app_args_go_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {k : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.get_app_args_go pers st fuel h k = ok o) :
    AOut₀ absEIdxList pers o st ((getAppArgs (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (get_app_args_go_ls hrel hinv fuel h k) hrun

theorem get_app_args_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.get_app_args pers st fuel h = ok o) :
    AOut₀ absEIdxList pers o st ((getAppArgs (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (get_app_args_ls hrel hinv fuel h) hrun

theorem strip_lams_refines {pers st lst} {k : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.strip_lams pers st k h = ok o) :
    AOut₀ absStrip pers o st ((stripLams (absU k) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (strip_lams_ls hrel hinv k h) hrun

theorem strip_pis_refines {pers st lst} {k : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.strip_pis pers st k h = ok o) :
    AOut₀ absStrip pers o st ((stripPis (absU k) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (strip_pis_ls hrel hinv k h) hrun

theorem is_lam_refines {pers st lst} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.is_lam pers st h = ok o) :
    AOut₀ id pers o st ((isLam (absEIdx h)).run lst) :=
  LSR.toAOut₀ (is_lam_ls hrel hinv h) hrun

theorem lam_pw_refines {pers st lst} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lam_pw pers st h = ok o) :
    AOut₀ absPwOpt pers o st ((lamPw (absEIdx h)).run lst) :=
  LSR.toAOut₀ (lam_pw_ls hrel hinv h) hrun

theorem forall_pw_refines {pers st lst} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.forall_pw pers st h = ok o) :
    AOut₀ absPwOpt pers o st ((forallPw (absEIdx h)).run lst) :=
  LSR.toAOut₀ (forall_pw_ls hrel hinv h) hrun

theorem fvar_type_d_refines {pers st lst} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_type_d pers st h = ok o) :
    AOut₀ absEIdx pers o st ((fvarTypeD (absEIdx h)).run lst) :=
  LSR.toAOut₀ (fvar_type_d_ls hrel hinv h) hrun

theorem wscoped_b_fast_refines {pers st lst} {fuel d : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.wscoped_b_fast pers st fuel d h = ok o) :
    AOut₀ id pers o st ((wscopedBFast (absU fuel) (absU d) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (wscoped_b_fast_ls hrel hinv fuel d h) hrun

theorem fvar_leaves_fast_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_leaves_fast pers st fuel h = ok o) :
    AOut₀ (fun v => (absLeaves v).reverse) pers o st ((fvarLeavesFast (absU fuel) (absEIdx h)).run lst) :=
  LSR.toAOut₀ (fvar_leaves_fast_ls hrel hinv fuel h) hrun

theorem leaf_guard_refines {pers st lst} {fuel : Std.U64} {fab base : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.leaf_guard pers st fuel fab base = ok o) :
    AOut₀ id pers o st ((leafGuard (absU fuel) (absEIdx fab) (absEIdx base)).run lst) :=
  LSR.toAOut₀ (leaf_guard_ls hrel hinv fuel fab base) hrun

end ConRon.Refine2.ExprOps
