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
Every proof is `apply LSR.of_LS` (thread the unchanged state through the
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

attribute [lockstep_simp] absEIdxList absLeaves absPwOpt absBinders absStrip

section size_b
attribute [local lockstep_simp] sizeBArmApp sizeBArmBind sizeBArmLet sizeBArmProj

end size_b

section size_f
attribute [local lockstep_simp] sizeFArmFVar sizeFArmApp sizeFArmBind sizeFArmLet sizeFArmProj

end size_f

section has_fvar
attribute [local lockstep_simp] hasFvarArmApp hasFvarArmBind hasFvarArmLet

end has_fvar

section fvar_leaves
attribute [local lockstep_simp] fvarLeavesArmFVar fvarLeavesArmApp fvarLeavesArmBind fvarLeavesArmLet

end fvar_leaves

section wscoped_b
attribute [local lockstep_simp] wscopedBArmApp wscopedBArmBind wscopedBArmLet

end wscoped_b

section loose_bvars_bounded
attribute [local lockstep_simp] looseBArmApp looseBArmBind looseBArmLet

end loose_bvars_bounded

section result_sort

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
    apply LSR.of_LS
    rw [arena.expr_ops.get_app_fn, getAppFn]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [arena.expr_ops.get_app_fn, getAppFn]
    lockstep

@[lockstep] theorem get_app_fn_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.get_app_fn pers st fuel h) st lst
      (getAppFn (absU fuel) (absEIdx h)) :=
  get_app_fn_aux _ fuel h rfl hrel hinv

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
    apply LSR.of_LS
    rw [arena.expr_ops.pi_result, piResult]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [arena.expr_ops.pi_result, piResult]
    lockstep

@[lockstep] theorem pi_result_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.pi_result pers st fuel h) st lst
      (piResult (absU fuel) (absEIdx h)) :=
  pi_result_aux _ fuel h rfl hrel hinv

end pi_result

section pi_arity

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
    apply LSR.of_LS
    rw [arena.expr_ops.get_app_args_go, getAppArgs]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h k hn hrel hinv
    apply LSR.of_LS
    rw [arena.expr_ops.get_app_args_go, getAppArgs]
    lockstep

end getAppArgs

section oneNode

theorem lam_pw_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absPwOpt a) (arena.expr_ops.lam_pw pers st h) st lst
      (lamPw (absEIdx h)) := by
  apply LSR.of_LS
  rw [arena.expr_ops.lam_pw, lamPw]
  lockstep

@[lockstep] theorem fvar_type_d_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.fvar_type_d pers st h) st lst
      (fvarTypeD (absEIdx h)) := by
  apply LSR.of_LS
  rw [arena.expr_ops.fvar_type_d, fvarTypeD]
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
    apply LSR.of_LS
    rw [arena.expr_ops.strip_lams, stripLams]
    lockstep
  | succ m ih =>
    intro pers st lst k h hn hrel hinv
    apply LSR.of_LS
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
    apply LSR.of_LS
    rw [arena.expr_ops.strip_pis, stripPis]
    lockstep
  | succ m ih =>
    intro pers st lst k h hn hrel hinv
    apply LSR.of_LS
    rw [arena.expr_ops.strip_pis, stripPis]
    lockstep

end strip


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
    apply LSR.of_LS
    rw [arena.expr_ops.wscoped_b_go, wscopedBGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst rm lm fuel d h hn hrel hinv hm
    apply LSR.of_LS
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
    apply LSR.of_LS
    rw [arena.expr_ops.fvar_leaves_go, fvarLeavesGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst racc rs ls fuel h hn hrel hinv hs
    apply LSR.of_LS
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
    apply LSR.of_LS
    rw [arena.expr_ops.leaves_sub_go, leavesSubGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst bl rm lm fuel h hn hrel hinv hm
    apply LSR.of_LS
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
  apply LSR.of_LS
  rw [arena.expr_ops.wscoped_b_fast, wscopedBFast]
  lockstep

@[lockstep] theorem fvar_leaves_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = (absLeaves a).reverse)
      (arena.expr_ops.fvar_leaves_fast pers st fuel h) st lst
      (fvarLeavesFast (absU fuel) (absEIdx h)) := by
  apply LSR.of_LS
  rw [arena.expr_ops.fvar_leaves_fast, fvarLeavesFast]
  lockstep

@[lockstep] theorem leaf_guard_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (fab base : arena.handle.EIdx) :
    LSR pers (fun a b => b = a) (arena.expr_ops.leaf_guard pers st fuel fab base) st lst
      (leafGuard (absU fuel) (absEIdx fab) (absEIdx base)) := by
  apply LSR.of_LS
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

attribute [lockstep] lam_pw_ls fvar_type_d_ls

@[lockstep] theorem inst_list_cutoff_ls' {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) (k : Std.U64) :
    LSV pers (fun a b => b = a) (arena.expr_ops.inst_list_cutoff pers st h k) st lst
      (instListCutoff (absEIdx h) (absU k)) := by
  apply LSV.ofLS
  rw [arena.expr_ops.inst_list_cutoff, instListCutoff]
  lockstep

end ConRon.Refine2.ExprOps
