/-
# `ConRon.Refine2.ExprOps.Mut` — Theorem 2 for the state-WRITING functions of `arena::expr_ops`

DESIGN.md §8.2's Theorem 2 for every function of
`crates/con-ron-core/src/arena/expr_ops.rs` that takes `pers: &PersTier` and
`st: &mut AState` — the substituting walks, the `internRebuilt` family, the
telescope instantiations, the packed-range recomputations and the level
substitution — against its `proof/ConRon/Arena/ExprOps.lean` twin.

## The statement: lockstep (task #97-T2-LOCKSTEP)

The Rust and the twin do the same operations, in the same order, from states
related by `AStateRel₀` (representation facts only) and `AStateInv` (the
Rust-side representation invariant).  Every function has two lemmas:

* `f_ls` — the judgement `LS pers R (rust_f …) lst (twinF …)` of
  `Refine2/Tactic/Lockstep.lean`, tagged `@[lockstep]` so that a caller's
  `lockstep` steps over the call;
* `f_refines` — the public `Sim₀` statement, `LS.toSim₀` of the first.

There is no premise about the twin's store: no `StoreWF`, no "the handle
resolves", no memo clause, and no `Ext` in the conclusion (task #97-T2-AUDIT
§2 ruled all of them Theorem-1 content).  What premises remain are facts
about the RUST inputs (`NameWF`/`LevelWF` of a level substitution, the
renaming dictionary's `RenameRel`).

## The proofs

Every proof is `rw [rust_f, twinF]; lockstep`, or, for a recursion on fuel or
a cursor, `induction n` with that line in each case (the induction hypothesis
is found in the context).  A twin whose arms are separate definitions names
them `lockstep_simp` locally.  Where a proof is anything else, the lemma says
why.

## What does not line up one-to-one

**The `_from` cursor companions.**  DESIGN §3.4's standing deviation: where
the twin recurses structurally on a `List`, the Rust takes the whole `Vec` and
an index, so `f_from … args i` is the twin `f` applied to `args` from `i` on
(`absEIdxListFrom`, `ExprOps/Pure.lean`).  `mk_app_n_from` has a twin of its
own, `mkAppNFrom`, at the same cursor; `mk_app_n` meets the list twin
`mkAppN` through the twin-only `mkAppNFrom_eq`.

**`instantiate_list*`'s `vs` is an `Array` and `inst_pis*`'s `args` a
`List`**, both `Vec<EIdx>` in the Rust (`absEIdxArr` against `absEIdxList`).

**`rename_consts_*` take a dictionary, not a function** (`RenameRel`).
-/
import ConRon.Refine2.Tactic.Prims
import ConRon.Refine2.ExprOps.Pure
import ConRon.Refine2.ExprOps.Read
import ConRon.Arena.ExprOps
import ConRon.Refine.ExprOpsMeta

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena ConRon.Refine2.Lockstep

/-- **The renaming dictionary against the twin's function** (`rename_consts`'s
one higher-order argument).  Aeneas renders the `NIdxToNIdx` trait method as
`Result`-valued because a trait method may fail; the twin's argument is a
total `NIdx → NIdx`.  Read it forward from `= ok`, as everything in this tier
is: *whatever the dictionary answers, the twin's function answers the
abstraction of it.* -/
def RenameRel {F : Type} (inst : arena.expr_ops.NIdxToNIdx F) (f : F)
    (g : NIdx → NIdx) : Prop :=
  ∀ n r, inst.rename f n = ok r → g (absNIdx n) = absNIdx r

/-- `kernel::expr_ops::sub_nat` is `Nat` subtraction on the abstraction. -/
theorem sub_nat_val {a b r : Std.U64}
    (h : kernel.expr_ops.sub_nat a b = ok r) : absU r = absU a - absU b := by
  rw [kernel.expr_ops.sub_nat] at h
  split at h <;> rename_i hge
  · exact (ConRon.Refine.Nat.usub_val h).2
  · simp only [Result.ok.injEq] at h
    rw [← h]
    show (0 : Nat) = a.val - b.val
    scalar_tac

/-! ## The level substitution's memo steps -/

@[lockstep] theorem subst_l_memo_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} (u : arena.handle.LIdx)
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k)
    (hus : ∀ v ∈ us.val, ConRon.Refine.LevelWF v) :
    LS pers (fun a b => b = absLIdx a) (arena.expr_ops.subst_l_memo_at pers st ks us u) lst
      (substLMemoAt (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us) (absLIdx u)) := by
  rw [arena.expr_ops.subst_l_memo_at, substLMemoAt]
  lockstep

@[lockstep] theorem subst_ls_memo_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} (vs : arena.handle.LsIdx)
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k)
    (hus : ∀ v ∈ us.val, ConRon.Refine.LevelWF v) :
    LS pers (fun a b => b = absLsIdx a) (arena.expr_ops.subst_ls_memo_at pers st ks us vs) lst
      (substLsMemoAt (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us) (absLsIdx vs)) := by
  rw [arena.expr_ops.subst_ls_memo_at, substLsMemoAt]
  lockstep

theorem subst_l_memo_at_refines {pers st lst} {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} {u : arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k) (hus : ∀ v ∈ us.val, ConRon.Refine.LevelWF v)
    (hrun : arena.expr_ops.subst_l_memo_at pers st ks us u = ok o) :
    Sim₀ absLIdx pers lst o
      (substLMemoAt (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us) (absLIdx u)) :=
  LS.toSim₀ (subst_l_memo_at_ls hrel hinv u hks hus) hrun

theorem subst_ls_memo_at_refines {pers st lst} {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} {vs : arena.handle.LsIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k) (hus : ∀ v ∈ us.val, ConRon.Refine.LevelWF v)
    (hrun : arena.expr_ops.subst_ls_memo_at pers st ks us vs = ok o) :
    Sim₀ absLsIdx pers lst o
      (substLsMemoAt (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us) (absLsIdx vs)) :=
  LS.toSim₀ (subst_ls_memo_at_ls hrel hinv vs hks hus) hrun

/-! ## `internRebuilt` and its per-constructor entries -/

section rebuilt
variable {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
  (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
include hrel hinv

@[lockstep] theorem intern_rebuilt_bvar_ls (h : arena.handle.EIdx) (same : Bool) (i : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_bvar pers st h same i) lst
      (internRebuiltBVar (absEIdx h) same (absU i)) := by
  rw [arena.expr_ops.intern_rebuilt_bvar, internRebuiltBVar]; lockstep

@[lockstep] theorem intern_rebuilt_fvar_ls (h : arena.handle.EIdx) (same : Bool) (i : Std.U64)
    (ty : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_fvar pers st h same i ty)
      lst (internRebuiltFVar (absEIdx h) same (absU i) (absEIdx ty)) := by
  rw [arena.expr_ops.intern_rebuilt_fvar, internRebuiltFVar]; lockstep

@[lockstep] theorem intern_rebuilt_sort_ls (h : arena.handle.EIdx) (same : Bool)
    (u : arena.handle.LIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_sort pers st h same u)
      lst (internRebuiltSort (absEIdx h) same (absLIdx u)) := by
  rw [arena.expr_ops.intern_rebuilt_sort, internRebuiltSort]; lockstep

@[lockstep] theorem intern_rebuilt_const_ls (h : arena.handle.EIdx) (same : Bool)
    (n : arena.handle.NIdx) (us : arena.handle.LsIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_const pers st h same n us)
      lst (internRebuiltConst (absEIdx h) same (absNIdx n) (absLsIdx us)) := by
  rw [arena.expr_ops.intern_rebuilt_const, internRebuiltConst]; lockstep

@[lockstep] theorem intern_rebuilt_app_ls (h : arena.handle.EIdx) (same : Bool)
    (f a : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_app pers st h same f a)
      lst (internRebuiltApp (absEIdx h) same (absEIdx f) (absEIdx a)) := by
  rw [arena.expr_ops.intern_rebuilt_app, internRebuiltApp]; lockstep

@[lockstep] theorem intern_rebuilt_lam_ls (h : arena.handle.EIdx) (same : Bool)
    (ty b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_lam pers st h same ty b m)
      lst (internRebuiltLam (absEIdx h) same (absEIdx ty) (absEIdx b)
        (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.expr_ops.intern_rebuilt_lam, internRebuiltLam]; lockstep

@[lockstep] theorem intern_rebuilt_forall_e_ls (h : arena.handle.EIdx) (same : Bool)
    (ty b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) :
    LS pers (fun a b => b = absEIdx a)
      (arena.expr_ops.intern_rebuilt_forall_e pers st h same ty b m)
      lst (internRebuiltForallE (absEIdx h) same (absEIdx ty) (absEIdx b)
        (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.expr_ops.intern_rebuilt_forall_e, internRebuiltForallE]; lockstep

@[lockstep] theorem intern_rebuilt_let_e_ls (h : arena.handle.EIdx) (same : Bool)
    (t v b : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_let_e pers st h same t v b)
      lst (internRebuiltLetE (absEIdx h) same (absEIdx t) (absEIdx v) (absEIdx b)) := by
  rw [arena.expr_ops.intern_rebuilt_let_e, internRebuiltLetE]; lockstep

@[lockstep] theorem intern_rebuilt_lit_ls (h : arena.handle.EIdx) (same : Bool)
    (l : kernel.expr.Literal) (hwf : ConRon.Refine.LiteralWF l) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_lit pers st h same l)
      lst (internRebuiltLit (absEIdx h) same (ConRon.Refine.absLiteral l)) := by
  rw [arena.expr_ops.intern_rebuilt_lit, internRebuiltLit]; lockstep

@[lockstep] theorem intern_rebuilt_proj_ls (h : arena.handle.EIdx) (same : Bool)
    (n : arena.handle.NIdx) (i : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_proj pers st h same n i e)
      lst (internRebuiltProj (absEIdx h) same (absNIdx n) (absU i) (absEIdx e)) := by
  rw [arena.expr_ops.intern_rebuilt_proj, internRebuiltProj]; lockstep

@[lockstep] theorem intern_rebuilt_bind_ls (h : arena.handle.EIdx) (same : Bool)
    (tag : Std.U32) (ty b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) :
    LS pers (fun a b => b = absEIdx a)
      (arena.expr_ops.intern_rebuilt_bind pers st h same tag ty b m)
      lst (internRebuiltBind (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx b)
        (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.expr_ops.intern_rebuilt_bind, internRebuiltBind]; lockstep

@[lockstep] theorem intern_rebuilt_bind_i_ls (h : arena.handle.EIdx) (same : Bool)
    (tag : Std.U32) (ty b : arena.handle.EIdx) (m : arena.handle.BMIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.expr_ops.intern_rebuilt_bind_i pers st h same tag ty b m)
      lst (internRebuiltBindI (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx b)
        (absBMIdx m)) := by
  rw [arena.expr_ops.intern_rebuilt_bind_i, internRebuiltBindI]; lockstep

end rebuilt

/-! ### The public statements -/

theorem intern_rebuilt_bvar_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (i : Std.U64) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_bvar pers st h same i = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltBVar (absEIdx h) same (absU i)) :=
  LS.toSim₀ (intern_rebuilt_bvar_ls hrel hinv h same i) hrun

theorem intern_rebuilt_fvar_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (i : Std.U64) (ty : arena.handle.EIdx) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_fvar pers st h same i ty = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltFVar (absEIdx h) same (absU i) (absEIdx ty)) :=
  LS.toSim₀ (intern_rebuilt_fvar_ls hrel hinv h same i ty) hrun

theorem intern_rebuilt_sort_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (u : arena.handle.LIdx) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_sort pers st h same u = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltSort (absEIdx h) same (absLIdx u)) :=
  LS.toSim₀ (intern_rebuilt_sort_ls hrel hinv h same u) hrun

theorem intern_rebuilt_const_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (n : arena.handle.NIdx) (us : arena.handle.LsIdx) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_const pers st h same n us = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltConst (absEIdx h) same (absNIdx n) (absLsIdx us)) :=
  LS.toSim₀ (intern_rebuilt_const_ls hrel hinv h same n us) hrun

theorem intern_rebuilt_app_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (f a : arena.handle.EIdx) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_app pers st h same f a = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltApp (absEIdx h) same (absEIdx f) (absEIdx a)) :=
  LS.toSim₀ (intern_rebuilt_app_ls hrel hinv h same f a) hrun

theorem intern_rebuilt_lam_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (ty b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_lam pers st h same ty b m = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltLam (absEIdx h) same (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)) :=
  LS.toSim₀ (intern_rebuilt_lam_ls hrel hinv h same ty b m) hrun

theorem intern_rebuilt_forall_e_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (ty b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_forall_e pers st h same ty b m = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltForallE (absEIdx h) same (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)) :=
  LS.toSim₀ (intern_rebuilt_forall_e_ls hrel hinv h same ty b m) hrun

theorem intern_rebuilt_let_e_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (t v b : arena.handle.EIdx) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_let_e pers st h same t v b = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltLetE (absEIdx h) same (absEIdx t) (absEIdx v) (absEIdx b)) :=
  LS.toSim₀ (intern_rebuilt_let_e_ls hrel hinv h same t v b) hrun

theorem intern_rebuilt_proj_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (n : arena.handle.NIdx) (i : Std.U64) (e : arena.handle.EIdx) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_proj pers st h same n i e = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltProj (absEIdx h) same (absNIdx n) (absU i) (absEIdx e)) :=
  LS.toSim₀ (intern_rebuilt_proj_ls hrel hinv h same n i e) hrun

theorem intern_rebuilt_bind_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (tag : Std.U32) (ty b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_bind pers st h same tag ty b m = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltBind (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)) :=
  LS.toSim₀ (intern_rebuilt_bind_ls hrel hinv h same tag ty b m) hrun

theorem intern_rebuilt_bind_i_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool) (tag : Std.U32) (ty b : arena.handle.EIdx) (m : arena.handle.BMIdx) {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_bind_i pers st h same tag ty b m = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltBindI (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx b) (absBMIdx m)) :=
  LS.toSim₀ (intern_rebuilt_bind_i_ls hrel hinv h same tag ty b m) hrun

theorem intern_rebuilt_lit_refines {pers st lst} (h : arena.handle.EIdx) (same : Bool)
    (l : kernel.expr.Literal) {o} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ConRon.Refine.LiteralWF l)
    (hrun : arena.expr_ops.intern_rebuilt_lit pers st h same l = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltLit (absEIdx h) same (ConRon.Refine.absLiteral l)) :=
  LS.toSim₀ (intern_rebuilt_lit_ls hrel hinv h same l hwf) hrun


/-! ## `instLPGo` -/

section instLP
attribute [local lockstep_simp] instLPArmFVar instLPArmApp instLPArmLam instLPArmForallE
  instLPArmLet instLPArmProj

theorem inst_lp_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (ks : alloc.vec.Vec kernel.name.Name) (us : alloc.vec.Vec kernel.level.Level)
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      (∀ k ∈ ks.val, ConRon.Refine.NameWF k) → (∀ v ∈ us.val, ConRon.Refine.LevelWF v) →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_lp_go pers st ks us fuel h) lst
        (instLPGo (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us) n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst ks us fuel h hn hrel hinv hks hus
    rw [arena.expr_ops.inst_lp_go, instLPGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst ks us fuel h hn hrel hinv hks hus
    rw [arena.expr_ops.inst_lp_go, instLPGo_succ]
    lockstep

@[lockstep] theorem inst_lp_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ks : alloc.vec.Vec kernel.name.Name)
    (us : alloc.vec.Vec kernel.level.Level) (fuel : Std.U64) (h : arena.handle.EIdx)
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k) (hus : ∀ v ∈ us.val, ConRon.Refine.LevelWF v) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_lp_go pers st ks us fuel h) lst
      (instLPGo (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us) (absU fuel)
        (absEIdx h)) :=
  inst_lp_go_aux _ ks us fuel h rfl hrel hinv hks hus

theorem inst_lp_go_refines {pers st lst} {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k) (hus : ∀ v ∈ us.val, ConRon.Refine.LevelWF v)
    (hrun : arena.expr_ops.inst_lp_go pers st ks us fuel h = ok o) :
    Sim₀ absEIdx pers lst o
      (instLPGo (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us) (absU fuel)
        (absEIdx h)) :=
  LS.toSim₀ (inst_lp_go_ls hrel hinv ks us fuel h hks hus) hrun

@[lockstep] theorem inst_lp_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (ks : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_lp_fast pers st fuel ks us e) lst
      (instLPFast (absU fuel) (ks.val.map absNIdx) (absLsIdx us) (absEIdx e)) := by
  rw [arena.expr_ops.inst_lp_fast, instLPFast]
  lockstep

/-- **`arena::expr_ops::inst_lp_fast` against `instLPFast`** — `ExprOpsHyp.instLPFast`. -/
theorem inst_lp_fast_refines {pers st lst} {fuel : Std.U64}
    {ks : alloc.vec.Vec arena.handle.NIdx} {us : arena.handle.LsIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lp_fast pers st fuel ks us e = ok o) :
    Sim₀ absEIdx pers lst o (instLPFast (absU fuel) (ks.val.map absNIdx) (absLsIdx us) (absEIdx e)) :=
  LS.toSim₀ (inst_lp_fast_ls hrel hinv fuel ks us e) hrun

end instLP

/-! ## `mkAppN` -/

theorem mk_app_n_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (f : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.mk_app_n_from pers st f args i) lst
        (mkAppNFrom (absEIdx f) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers st lst f args i hn hrel hinv
    rw [arena.expr_ops.mk_app_n_from, mkAppNFrom]
    lockstep
  | succ k ih =>
    intro pers st lst f args i hn hrel hinv
    rw [arena.expr_ops.mk_app_n_from, mkAppNFrom]
    lockstep

@[lockstep] theorem mk_app_n_from_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx)
    (i : Std.Usize) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.mk_app_n_from pers st f args i) lst
      (mkAppNFrom (absEIdx f) (absEIdxArr args) (absSz i)) :=
  mk_app_n_from_aux _ f args i rfl hrel hinv

/-- **Twin-only**: the cursor form over an array is the list form over what
the cursor has not consumed. -/
theorem mkAppNFrom_eq (arr : Array EIdx) :
    ∀ (n i : Nat) (f : EIdx), arr.size - i = n →
      mkAppNFrom f arr i = mkAppN f (arr.toList.drop i) := by
  intro n
  induction n with
  | zero =>
    intro i f hn
    rw [mkAppNFrom, dif_neg (show ¬ (i < arr.size) from by omega),
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_sub_eq_zero hn), mkAppN]
  | succ m ih =>
    intro i f hn
    have hlt : i < arr.size := by omega
    rw [mkAppNFrom, dif_pos hlt]
    rw [show arr.toList.drop i = arr[i] :: arr.toList.drop (i + 1) from by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp]
    rw [mkAppN]
    have : ∀ g : EIdx, mkAppNFrom g arr (i + 1) = mkAppN g (arr.toList.drop (i + 1)) :=
      fun g => ih (i + 1) g (by omega)
    simp only [Arena.internAppE]
    exact bind_congr (fun g => this g)

/-- The list twin `mkAppN` at the argument vector is its cursor twin from `0`. -/
theorem mkAppN_absEIdxList (f : EIdx) (args : alloc.vec.Vec arena.handle.EIdx) :
    mkAppN f (absEIdxList args) = mkAppNFrom f (absEIdxArr args) 0 := by
  rw [mkAppNFrom_eq (absEIdxArr args) _ 0 f rfl]
  simp [absEIdxArr, absEIdxList]

@[lockstep] theorem mk_app_n_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.mk_app_n pers st f args) lst
      (Arena.mkAppN (absEIdx f) (absEIdxList args)) := by
  rw [arena.expr_ops.mk_app_n, mkAppN_absEIdxList]
  exact mk_app_n_from_ls hrel hinv f args 0#usize

/-- **`arena::expr_ops::mk_app_n_from` against `mkAppNFrom`** — `ExprOpsHyp.mkAppNFrom`. -/
theorem mk_app_n_from_refines {pers st lst} {f : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.mk_app_n_from pers st f args i = ok o) :
    Sim₀ absEIdx pers lst o (mkAppNFrom (absEIdx f) (absEIdxArr args) (absSz i)) :=
  LS.toSim₀ (mk_app_n_from_ls hrel hinv f args i) hrun

/-- **`arena::expr_ops::mk_app_n` against `mkAppN`** — `ExprOpsHyp.mkAppN`. -/
theorem mk_app_n_refines {pers st lst} {f : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.mk_app_n pers st f args = ok o) :
    Sim₀ absEIdx pers lst o (Arena.mkAppN (absEIdx f) (absEIdxList args)) :=
  LS.toSim₀ (mk_app_n_ls hrel hinv f args) hrun


/-! ## The substituting walks, the entries and the telescopes

Every walk below is `rw [rust_f, twinF]; lockstep` in each fuel (or cursor,
or count) case.  Their twins that read a node are tag-first since task
#97-T2-LOCKSTEP (`instPis`, `instPisAt`, `instLamsAt`, `instPisAtFGo`,
`instLamsAtFGo`, `instPisAtLift`, `pisToLams`, `replacePiBody`,
`recRulePlain`), and `renameConstsGo` interns unconditionally in every arm, as
the port does. -/

attribute [lockstep_simp] absEIdxList absOptArgsE absNIdxList

section instantiate1_go
attribute [local lockstep_simp] instantiate1ArmBVar instantiate1ArmApp instantiate1ArmBind instantiate1ArmLet instantiate1ArmProj

theorem instantiate1_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (v : arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_go pers st v fuel h d) lst
        (instantiate1Go (absEIdx v) n (absEIdx h) (absU d)) := by
  induction n with
  | zero =>
    intro pers st lst v fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate1_go, instantiate1Go_zero]
    lockstep
  | succ m ih =>
    intro pers st lst v fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate1_go, instantiate1Go_succ]
    lockstep

@[lockstep] theorem instantiate1_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (v : arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_go pers st v fuel h d) lst
      (instantiate1Go (absEIdx v) (absU fuel) (absEIdx h) (absU d)) :=
  instantiate1_go_aux _ v fuel h d rfl hrel hinv

end instantiate1_go

@[lockstep] theorem instantiate1_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e v : arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_fast pers st fuel e v d) lst
      (instantiate1Fast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) := by
  rw [arena.expr_ops.instantiate1_fast, instantiate1Fast]
  lockstep

section instantiate_list
attribute [local lockstep_simp] instListArmApp instListArmBind instListArmLet instListArmProj instListArmBVar

theorem instantiate_list_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (vs : alloc.vec.Vec arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate_list pers st vs fuel h d) lst
        (instantiateList (absEIdxArr vs) n (absEIdx h) (absU d)) := by
  induction n with
  | zero =>
    intro pers st lst vs fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate_list, instantiateList_zero]
    lockstep
  | succ m ih =>
    intro pers st lst vs fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate_list, instantiateList_succ]
    lockstep

@[lockstep] theorem instantiate_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (vs : alloc.vec.Vec arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate_list pers st vs fuel h d) lst
      (instantiateList (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)) :=
  instantiate_list_aux _ vs fuel h d rfl hrel hinv

end instantiate_list

section instantiate_list_go
attribute [local lockstep_simp] instListGoArmApp instListGoArmBind instListGoArmLet instListGoArmProj instListArmBVar

theorem instantiate_list_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (vs : alloc.vec.Vec arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate_list_go pers st vs fuel h d) lst
        (instantiateListGo (absEIdxArr vs) n (absEIdx h) (absU d)) := by
  induction n with
  | zero =>
    intro pers st lst vs fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate_list_go, instantiateListGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst vs fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate_list_go, instantiateListGo_succ]
    lockstep

@[lockstep] theorem instantiate_list_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (vs : alloc.vec.Vec arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate_list_go pers st vs fuel h d) lst
      (instantiateListGo (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)) :=
  instantiate_list_go_aux _ vs fuel h d rfl hrel hinv

end instantiate_list_go

@[lockstep] theorem instantiate_list_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) (vs : alloc.vec.Vec arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate_list_fast pers st fuel e vs d) lst
      (instantiateListFast (absU fuel) (absEIdx e) (absEIdxArr vs) (absU d)) := by
  rw [arena.expr_ops.instantiate_list_fast, instantiateListFast]
  lockstep

section lift_loose_bvars_go
attribute [local lockstep_simp] liftArmApp liftArmLam liftArmForallE liftArmLet liftArmProj

theorem lift_loose_bvars_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (amount : Std.U64) (fuel : Std.U64) (h : arena.handle.EIdx) (c : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.lift_loose_bvars_go pers st amount fuel h c) lst
        (liftLooseBVarsGo (absU amount) n (absEIdx h) (absU c)) := by
  induction n with
  | zero =>
    intro pers st lst amount fuel h c hn hrel hinv
    rw [arena.expr_ops.lift_loose_bvars_go, liftLooseBVarsGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst amount fuel h c hn hrel hinv
    rw [arena.expr_ops.lift_loose_bvars_go, liftLooseBVarsGo_succ]
    lockstep

@[lockstep] theorem lift_loose_bvars_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (amount : Std.U64) (fuel : Std.U64) (h : arena.handle.EIdx) (c : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.lift_loose_bvars_go pers st amount fuel h c) lst
      (liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)) :=
  lift_loose_bvars_go_aux _ amount fuel h c rfl hrel hinv

end lift_loose_bvars_go

@[lockstep] theorem lift_loose_bvars_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel amount c : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.lift_loose_bvars_fast pers st fuel amount c e) lst
      (liftLooseBVarsFast (absU fuel) (absU amount) (absU c) (absEIdx e)) := by
  rw [arena.expr_ops.lift_loose_bvars_fast, liftLooseBVarsFast]
  lockstep

section reset_meta_go
attribute [local lockstep_simp] resetArmFVar resetArmApp resetArmLam resetArmForallE resetArmLet resetArmProj

theorem reset_meta_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.reset_meta_go pers st fuel h) lst
        (resetMetaGo n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    rw [arena.expr_ops.reset_meta_go, resetMetaGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    rw [arena.expr_ops.reset_meta_go, resetMetaGo_succ]
    lockstep

@[lockstep] theorem reset_meta_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.reset_meta_go pers st fuel h) lst
      (resetMetaGo (absU fuel) (absEIdx h)) :=
  reset_meta_go_aux _ fuel h rfl hrel hinv

end reset_meta_go

@[lockstep] theorem reset_meta_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.reset_meta_fast pers st fuel e) lst
      (resetMetaFast (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.reset_meta_fast, resetMetaFast]
  lockstep

section abstract_range
attribute [local lockstep_simp] absRangeArmApp absRangeArmLam absRangeArmForallE absRangeArmLet absRangeArmProj

theorem abstract_range_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx) (d k c : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract_range pers st fuel h d k c) lst
        (abstractRange n (absEIdx h) (absU d) (absU k) (absU c)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h d k c hn hrel hinv
    rw [arena.expr_ops.abstract_range, abstractRange_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h d k c hn hrel hinv
    rw [arena.expr_ops.abstract_range, abstractRange_succ]
    lockstep

@[lockstep] theorem abstract_range_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) (d k c : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract_range pers st fuel h d k c) lst
      (abstractRange (absU fuel) (absEIdx h) (absU d) (absU k) (absU c)) :=
  abstract_range_aux _ fuel h d k c rfl hrel hinv

end abstract_range

section bvar_bound_go
attribute [local lockstep_simp] bvarBoundArmApp bvarBoundArmBind bvarBoundArmLet

theorem bvar_bound_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absU a) (arena.expr_ops.bvar_bound_go pers st fuel h) lst
        (bvarBoundGo n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    rw [arena.expr_ops.bvar_bound_go, bvarBoundGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    rw [arena.expr_ops.bvar_bound_go, bvarBoundGo_succ]
    lockstep

@[lockstep] theorem bvar_bound_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absU a) (arena.expr_ops.bvar_bound_go pers st fuel h) lst
      (bvarBoundGo (absU fuel) (absEIdx h)) :=
  bvar_bound_go_aux _ fuel h rfl hrel hinv

end bvar_bound_go

section fvar_range_go
attribute [local lockstep_simp] fvarRangeArmApp fvarRangeArmBind fvarRangeArmLet

theorem fvar_range_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absU a) (arena.expr_ops.fvar_range_go pers st fuel h) lst
        (fvarRangeGo n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    rw [arena.expr_ops.fvar_range_go, fvarRangeGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    rw [arena.expr_ops.fvar_range_go, fvarRangeGo_succ]
    lockstep

@[lockstep] theorem fvar_range_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absU a) (arena.expr_ops.fvar_range_go pers st fuel h) lst
      (fvarRangeGo (absU fuel) (absEIdx h)) :=
  fvar_range_go_aux _ fuel h rfl hrel hinv

end fvar_range_go

@[lockstep] theorem bvar_bound_memo_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absU a) (arena.expr_ops.bvar_bound_memo pers st fuel e) lst
      (bvarBoundMemo (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.bvar_bound_memo, bvarBoundMemo]
  lockstep

@[lockstep] theorem fvar_range_memo_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absU a) (arena.expr_ops.fvar_range_memo pers st fuel e) lst
      (fvarRangeMemo (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.fvar_range_memo, fvarRangeMemo]
  lockstep

@[lockstep] theorem bvar_b_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absU a) (arena.expr_ops.bvar_b pers st fuel e) lst
      (bvarB (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.bvar_b, bvarB]
  lockstep

@[lockstep] theorem fvar_b_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absU a) (arena.expr_ops.fvar_b pers st fuel e) lst
      (fvarB (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.fvar_b, fvarB]
  lockstep

@[lockstep] theorem has_fvar_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = id a) (arena.expr_ops.has_fvar_fast pers st fuel e) lst
      (hasFvarFast (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.has_fvar_fast, hasFvarFast]
  lockstep

@[lockstep] theorem loose_bvars_bounded_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel k : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = id a) (arena.expr_ops.loose_bvars_bounded_fast pers st fuel k e) lst
      (looseBVarsBoundedFast (absU fuel) (absU k) (absEIdx e)) := by
  rw [arena.expr_ops.loose_bvars_bounded_fast, looseBVarsBoundedFast]
  lockstep

section abstract1_go
attribute [local lockstep_simp] abstract1ArmFVar abstract1ArmApp abstract1ArmBind abstract1ArmLet abstract1ArmProj

theorem abstract1_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (d : Std.U64) (fuel : Std.U64) (h : arena.handle.EIdx) (k : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract1_go pers st d fuel h k) lst
        (abstract1Go (absU d) n (absEIdx h) (absU k)) := by
  induction n with
  | zero =>
    intro pers st lst d fuel h k hn hrel hinv
    rw [arena.expr_ops.abstract1_go, abstract1Go_zero]
    lockstep
  | succ m ih =>
    intro pers st lst d fuel h k hn hrel hinv
    rw [arena.expr_ops.abstract1_go, abstract1Go_succ]
    lockstep

@[lockstep] theorem abstract1_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (d : Std.U64) (fuel : Std.U64) (h : arena.handle.EIdx) (k : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract1_go pers st d fuel h k) lst
      (abstract1Go (absU d) (absU fuel) (absEIdx h) (absU k)) :=
  abstract1_go_aux _ d fuel h k rfl hrel hinv

end abstract1_go

@[lockstep] theorem abstract1_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) (d k : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract1_fast pers st fuel e d k) lst
      (abstract1Fast (absU fuel) (absEIdx e) (absU d) (absU k)) := by
  rw [arena.expr_ops.abstract1_fast, abstract1Fast]
  lockstep

section abstract_range_go
attribute [local lockstep_simp] absRangeArmFVar absRangeGoArmApp absRangeGoArmBind absRangeGoArmLet absRangeGoArmProj

theorem abstract_range_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (d k : Std.U64) (fuel : Std.U64) (h : arena.handle.EIdx) (c : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract_range_go pers st d k fuel h c) lst
        (abstractRangeGo (absU d) (absU k) n (absEIdx h) (absU c)) := by
  induction n with
  | zero =>
    intro pers st lst d k fuel h c hn hrel hinv
    rw [arena.expr_ops.abstract_range_go, abstractRangeGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst d k fuel h c hn hrel hinv
    rw [arena.expr_ops.abstract_range_go, abstractRangeGo_succ]
    lockstep

@[lockstep] theorem abstract_range_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (d k : Std.U64) (fuel : Std.U64) (h : arena.handle.EIdx) (c : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract_range_go pers st d k fuel h c) lst
      (abstractRangeGo (absU d) (absU k) (absU fuel) (absEIdx h) (absU c)) :=
  abstract_range_go_aux _ d k fuel h c rfl hrel hinv

end abstract_range_go

@[lockstep] theorem abstract_range_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) (d k c : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract_range_fast pers st fuel e d k c) lst
      (abstractRangeFast (absU fuel) (absEIdx e) (absU d) (absU k) (absU c)) := by
  rw [arena.expr_ops.abstract_range_fast, abstractRangeFast]
  lockstep

section lower_bvars_go
attribute [local lockstep_simp] lowerArmApp lowerArmLam lowerArmForallE lowerArmLet lowerArmProj

theorem lower_bvars_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (amount : Std.U64) (fuel : Std.U64) (h : arena.handle.EIdx) (c : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.lower_bvars_go pers st amount fuel h c) lst
        (lowerBVarsGo (absU amount) n (absEIdx h) (absU c)) := by
  induction n with
  | zero =>
    intro pers st lst amount fuel h c hn hrel hinv
    rw [arena.expr_ops.lower_bvars_go, lowerBVarsGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst amount fuel h c hn hrel hinv
    rw [arena.expr_ops.lower_bvars_go, lowerBVarsGo_succ]
    lockstep

@[lockstep] theorem lower_bvars_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (amount : Std.U64) (fuel : Std.U64) (h : arena.handle.EIdx) (c : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.lower_bvars_go pers st amount fuel h c) lst
      (lowerBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)) :=
  lower_bvars_go_aux _ amount fuel h c rfl hrel hinv

end lower_bvars_go

@[lockstep] theorem lower_bvars_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel amount c : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.lower_bvars_fast pers st fuel amount c e) lst
      (lowerBVarsFast (absU fuel) (absU amount) (absU c) (absEIdx e)) := by
  rw [arena.expr_ops.lower_bvars_fast, lowerBVarsFast]
  lockstep

section instantiate1_lift_go
attribute [local lockstep_simp] inst1LiftArmApp inst1LiftArmLam inst1LiftArmForallE inst1LiftArmLet inst1LiftArmProj

theorem instantiate1_lift_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (v : arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_lift_go pers st v fuel h d) lst
        (instantiate1LiftGo (absEIdx v) n (absEIdx h) (absU d)) := by
  induction n with
  | zero =>
    intro pers st lst v fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate1_lift_go, instantiate1LiftGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst v fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate1_lift_go, instantiate1LiftGo_succ]
    lockstep

@[lockstep] theorem instantiate1_lift_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (v : arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_lift_go pers st v fuel h d) lst
      (instantiate1LiftGo (absEIdx v) (absU fuel) (absEIdx h) (absU d)) :=
  instantiate1_lift_go_aux _ v fuel h d rfl hrel hinv

end instantiate1_lift_go

@[lockstep] theorem instantiate1_lift_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e v : arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_lift_fast pers st fuel e v d) lst
      (instantiate1LiftFast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) := by
  rw [arena.expr_ops.instantiate1_lift_fast, instantiate1LiftFast]
  lockstep

theorem inst_spine_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (t : Std.U64) (e : arena.handle.EIdx),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_spine_from pers st fuel args i t e) lst
        (instSpine (absU fuel) (absEIdxListFrom args i) (absU t) (absEIdx e)) := by
  induction n with
  | zero =>
    intro pers st lst fuel args i t e hn hrel hinv
    rw [arena.expr_ops.inst_spine_from, listFrom_nil args i (by omega), instSpine]
    lockstep
  | succ k ih =>
    intro pers st lst fuel args i t e hn hrel hinv
    rw [arena.expr_ops.inst_spine_from, listFrom_cons args i (by omega), instSpine]
    lockstep

@[lockstep] theorem inst_spine_from_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (t : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_spine_from pers st fuel args i t e) lst
      (instSpine (absU fuel) (absEIdxListFrom args i) (absU t) (absEIdx e)) :=
  inst_spine_from_aux _ fuel args i t e rfl hrel hinv

@[lockstep] theorem inst_spine_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (t : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_spine pers st fuel args t e) lst
      (instSpine (absU fuel) (absEIdxList args) (absU t) (absEIdx e)) := by
  rw [arena.expr_ops.inst_spine]
  lockstep

theorem bvar_range_aux (N : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (m_i n k : Std.U64),
      n.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxList a) (arena.expr_ops.bvar_range pers st m_i n k) lst
        (bvarRange (absU m_i) N (absU k)) := by
  induction N with
  | zero =>
    intro pers st lst m_i n k hn hrel hinv
    rw [arena.expr_ops.bvar_range, bvarRange]
    lockstep
  | succ m ih =>
    intro pers st lst m_i n k hn hrel hinv
    rw [arena.expr_ops.bvar_range, bvarRange]
    lockstep

@[lockstep] theorem bvar_range_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (m_i n k : Std.U64) :
    LS pers (fun a b => b = absEIdxList a) (arena.expr_ops.bvar_range pers st m_i n k) lst
      (bvarRange (absU m_i) (absU n) (absU k)) :=
  bvar_range_aux _ m_i n k rfl hrel hinv

@[lockstep] theorem rec_rule_plain_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (rec_ty : arena.handle.EIdx) (m_i r_p cn_p : Std.U64) :
    LS pers (fun a b => b = id a) (arena.expr_ops.rec_rule_plain pers st fuel rec_ty m_i r_p cn_p) lst
      (recRulePlain (absU fuel) (absEIdx rec_ty) (absU m_i) (absU r_p) (absU cn_p)) := by
  rw [arena.expr_ops.rec_rule_plain, recRulePlain]
  lockstep

theorem pis_to_lams_aux (N : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (k : Std.U64) (h body : arena.handle.EIdx),
      k.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptE a) (arena.expr_ops.pis_to_lams pers st k h body) lst
        (pisToLams N (absEIdx h) (absEIdx body)) := by
  induction N with
  | zero =>
    intro pers st lst k h body hn hrel hinv
    rw [arena.expr_ops.pis_to_lams, pisToLams]
    lockstep
  | succ m ih =>
    intro pers st lst k h body hn hrel hinv
    rw [arena.expr_ops.pis_to_lams, pisToLams]
    lockstep

@[lockstep] theorem pis_to_lams_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h body : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptE a) (arena.expr_ops.pis_to_lams pers st k h body) lst
      (pisToLams (absU k) (absEIdx h) (absEIdx body)) :=
  pis_to_lams_aux _ k h body rfl hrel hinv

theorem replace_pi_body_aux (N : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (k : Std.U64) (h b : arena.handle.EIdx),
      k.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptE a) (arena.expr_ops.replace_pi_body pers st k h b) lst
        (replacePiBody N (absEIdx h) (absEIdx b)) := by
  induction N with
  | zero =>
    intro pers st lst k h b hn hrel hinv
    rw [arena.expr_ops.replace_pi_body, replacePiBody]
    lockstep
  | succ m ih =>
    intro pers st lst k h b hn hrel hinv
    rw [arena.expr_ops.replace_pi_body, replacePiBody]
    lockstep

@[lockstep] theorem replace_pi_body_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h b : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptE a) (arena.expr_ops.replace_pi_body pers st k h b) lst
      (replacePiBody (absU k) (absEIdx h) (absEIdx b)) :=
  replace_pi_body_aux _ k h b rfl hrel hinv

theorem inst_pis_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (e : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptE a) (arena.expr_ops.inst_pis_from pers st fuel e args i) lst
        (instPis (absU fuel) (absEIdx e) (absEIdxListFrom args i)) := by
  induction n with
  | zero =>
    intro pers st lst fuel e args i hn hrel hinv
    rw [arena.expr_ops.inst_pis_from, listFrom_nil args i (by omega), instPis]
    lockstep
  | succ k ih =>
    intro pers st lst fuel e args i hn hrel hinv
    rw [arena.expr_ops.inst_pis_from, listFrom_cons args i (by omega), instPis]
    lockstep

@[lockstep] theorem inst_pis_from_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    LS pers (fun a b => b = absOptE a) (arena.expr_ops.inst_pis_from pers st fuel e args i) lst
      (instPis (absU fuel) (absEIdx e) (absEIdxListFrom args i)) :=
  inst_pis_from_aux _ fuel e args i rfl hrel hinv

@[lockstep] theorem inst_pis_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absOptE a) (arena.expr_ops.inst_pis pers st fuel e args) lst
      (instPis (absU fuel) (absEIdx e) (absEIdxList args)) := by
  rw [arena.expr_ops.inst_pis]
  lockstep

theorem inst_pis_at_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_pis_at_from pers st fuel args i h) lst
        (instPisAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel args i h hn hrel hinv
    rw [arena.expr_ops.inst_pis_at_from, listFrom_nil args i (by omega), instPisAt]
    lockstep
  | succ k ih =>
    intro pers st lst fuel args i h hn hrel hinv
    rw [arena.expr_ops.inst_pis_at_from, listFrom_cons args i (by omega), instPisAt]
    lockstep

@[lockstep] theorem inst_pis_at_from_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_pis_at_from pers st fuel args i h) lst
      (instPisAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)) :=
  inst_pis_at_from_aux _ fuel args i h rfl hrel hinv

@[lockstep] theorem inst_pis_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_pis_at pers st fuel args h) lst
      (instPisAt (absU fuel) (absEIdxList args) (absEIdx h)) := by
  rw [arena.expr_ops.inst_pis_at]
  lockstep

theorem inst_lams_at_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_lams_at_from pers st fuel args i h) lst
        (instLamsAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel args i h hn hrel hinv
    rw [arena.expr_ops.inst_lams_at_from, listFrom_nil args i (by omega), instLamsAt]
    lockstep
  | succ k ih =>
    intro pers st lst fuel args i h hn hrel hinv
    rw [arena.expr_ops.inst_lams_at_from, listFrom_cons args i (by omega), instLamsAt]
    lockstep

@[lockstep] theorem inst_lams_at_from_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_lams_at_from pers st fuel args i h) lst
      (instLamsAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)) :=
  inst_lams_at_from_aux _ fuel args i h rfl hrel hinv

@[lockstep] theorem inst_lams_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_lams_at pers st fuel args h) lst
      (instLamsAt (absU fuel) (absEIdxList args) (absEIdx h)) := by
  rw [arena.expr_ops.inst_lams_at]
  lockstep

theorem inst_pis_at_f_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (acc args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_pis_at_f_go pers st fuel acc args i h) lst
        (instPisAtFGo (absU fuel) (absEIdxArr acc) (absEIdxListFrom args i) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel acc args i h hn hrel hinv
    rw [arena.expr_ops.inst_pis_at_f_go, listFrom_nil args i (by omega), instPisAtFGo]
    lockstep
  | succ k ih =>
    intro pers st lst fuel acc args i h hn hrel hinv
    rw [arena.expr_ops.inst_pis_at_f_go, listFrom_cons args i (by omega), instPisAtFGo]
    lockstep

@[lockstep] theorem inst_pis_at_f_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (acc args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_pis_at_f_go pers st fuel acc args i h) lst
      (instPisAtFGo (absU fuel) (absEIdxArr acc) (absEIdxListFrom args i) (absEIdx h)) :=
  inst_pis_at_f_go_aux _ fuel acc args i h rfl hrel hinv

@[lockstep] theorem inst_pis_at_f_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_pis_at_f pers st fuel args e) lst
      (instPisAtF (absU fuel) (absEIdxList args) (absEIdx e)) := by
  rw [arena.expr_ops.inst_pis_at_f, instPisAtF]
  lockstep

theorem inst_lams_at_f_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (acc args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_lams_at_f_go pers st fuel acc args i h) lst
        (instLamsAtFGo (absU fuel) (absEIdxArr acc) (absEIdxListFrom args i) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel acc args i h hn hrel hinv
    rw [arena.expr_ops.inst_lams_at_f_go, listFrom_nil args i (by omega), instLamsAtFGo]
    lockstep
  | succ k ih =>
    intro pers st lst fuel acc args i h hn hrel hinv
    rw [arena.expr_ops.inst_lams_at_f_go, listFrom_cons args i (by omega), instLamsAtFGo]
    lockstep

@[lockstep] theorem inst_lams_at_f_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (acc args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_lams_at_f_go pers st fuel acc args i h) lst
      (instLamsAtFGo (absU fuel) (absEIdxArr acc) (absEIdxListFrom args i) (absEIdx h)) :=
  inst_lams_at_f_go_aux _ fuel acc args i h rfl hrel hinv

@[lockstep] theorem inst_lams_at_f_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptArgsE a) (arena.expr_ops.inst_lams_at_f pers st fuel args e) lst
      (instLamsAtF (absU fuel) (absEIdxList args) (absEIdx e)) := by
  rw [arena.expr_ops.inst_lams_at_f, instLamsAtF]
  lockstep

theorem inst_pis_at_lift_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptE a) (arena.expr_ops.inst_pis_at_lift_from pers st fuel args i h) lst
        (instPisAtLift (absU fuel) (absEIdxListFrom args i) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel args i h hn hrel hinv
    rw [arena.expr_ops.inst_pis_at_lift_from, listFrom_nil args i (by omega), instPisAtLift]
    lockstep
  | succ k ih =>
    intro pers st lst fuel args i h hn hrel hinv
    rw [arena.expr_ops.inst_pis_at_lift_from, listFrom_cons args i (by omega), instPisAtLift]
    lockstep

@[lockstep] theorem inst_pis_at_lift_from_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptE a) (arena.expr_ops.inst_pis_at_lift_from pers st fuel args i h) lst
      (instPisAtLift (absU fuel) (absEIdxListFrom args i) (absEIdx h)) :=
  inst_pis_at_lift_from_aux _ fuel args i h rfl hrel hinv

@[lockstep] theorem inst_pis_at_lift_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absOptE a) (arena.expr_ops.inst_pis_at_lift pers st fuel args h) lst
      (instPisAtLift (absU fuel) (absEIdxList args) (absEIdx h)) := by
  rw [arena.expr_ops.inst_pis_at_lift]
  lockstep



/-! ## `renameConsts` — the module's one higher-order argument -/

/-- The renaming dictionary's one method, against the twin's function. -/
@[lockstep] theorem rename_dict_spec {F : Type} (inst : arena.expr_ops.NIdxToNIdx F) (f : F)
    {g : NIdx → NIdx} (hg : RenameRel inst f g) (n : arena.handle.NIdx) :
    LSP (inst.rename f n) (fun r => g (absNIdx n) = absNIdx r) :=
  fun r h => hg n r h

section rename
attribute [local lockstep_simp] renameArmFVar renameArmApp renameArmLam renameArmForallE
  renameArmLet renameArmProj

theorem rename_consts_go_aux {F : Type} (inst : arena.expr_ops.NIdxToNIdx F) (f : F)
    (g : NIdx → NIdx) (hg : RenameRel inst f g) (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.rename_consts_go inst pers st f fuel h)
        lst (renameConstsGo g n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    rw [arena.expr_ops.rename_consts_go, renameConstsGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    rw [arena.expr_ops.rename_consts_go, renameConstsGo_succ]
    lockstep

@[lockstep] theorem rename_consts_go_ls {F : Type} {inst : arena.expr_ops.NIdxToNIdx F}
    {f : F} {g : NIdx → NIdx} (hg : RenameRel inst f g) {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel : Std.U64)
    (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.rename_consts_go inst pers st f fuel h)
      lst (renameConstsGo g (absU fuel) (absEIdx h)) :=
  rename_consts_go_aux inst f g hg _ fuel h rfl hrel hinv

@[lockstep] theorem rename_consts_fast_ls {F : Type} {inst : arena.expr_ops.NIdxToNIdx F}
    {f : F} {g : NIdx → NIdx} (hg : RenameRel inst f g) {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel : Std.U64)
    (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.rename_consts_fast inst pers st fuel f e)
      lst (renameConstsFast (absU fuel) g (absEIdx e)) := by
  rw [arena.expr_ops.rename_consts_fast, renameConstsFast]
  lockstep

end rename


/-! ## The public statements (`Sim₀`) -/

theorem instantiate1_go_refines {pers st lst} {v : arena.handle.EIdx} {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate1_go pers st v fuel h d = ok o) :
    Sim₀ absEIdx pers lst o (instantiate1Go (absEIdx v) (absU fuel) (absEIdx h) (absU d)) :=
  LS.toSim₀ (instantiate1_go_ls hrel hinv v fuel h d) hrun

theorem instantiate1_fast_refines {pers st lst} {fuel : Std.U64} {e v : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate1_fast pers st fuel e v d = ok o) :
    Sim₀ absEIdx pers lst o (instantiate1Fast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) :=
  LS.toSim₀ (instantiate1_fast_ls hrel hinv fuel e v d) hrun

theorem instantiate_list_refines {pers st lst} {vs : alloc.vec.Vec arena.handle.EIdx} {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate_list pers st vs fuel h d = ok o) :
    Sim₀ absEIdx pers lst o (instantiateList (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)) :=
  LS.toSim₀ (instantiate_list_ls hrel hinv vs fuel h d) hrun

theorem instantiate_list_go_refines {pers st lst} {vs : alloc.vec.Vec arena.handle.EIdx} {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate_list_go pers st vs fuel h d = ok o) :
    Sim₀ absEIdx pers lst o (instantiateListGo (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)) :=
  LS.toSim₀ (instantiate_list_go_ls hrel hinv vs fuel h d) hrun

theorem instantiate_list_fast_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {vs : alloc.vec.Vec arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate_list_fast pers st fuel e vs d = ok o) :
    Sim₀ absEIdx pers lst o (instantiateListFast (absU fuel) (absEIdx e) (absEIdxArr vs) (absU d)) :=
  LS.toSim₀ (instantiate_list_fast_ls hrel hinv fuel e vs d) hrun

theorem lift_loose_bvars_go_refines {pers st lst} {amount : Std.U64} {fuel : Std.U64} {h : arena.handle.EIdx} {c : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lift_loose_bvars_go pers st amount fuel h c = ok o) :
    Sim₀ absEIdx pers lst o (liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)) :=
  LS.toSim₀ (lift_loose_bvars_go_ls hrel hinv amount fuel h c) hrun

theorem lift_loose_bvars_fast_refines {pers st lst} {fuel amount c : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lift_loose_bvars_fast pers st fuel amount c e = ok o) :
    Sim₀ absEIdx pers lst o (liftLooseBVarsFast (absU fuel) (absU amount) (absU c) (absEIdx e)) :=
  LS.toSim₀ (lift_loose_bvars_fast_ls hrel hinv fuel amount c e) hrun

theorem reset_meta_go_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.reset_meta_go pers st fuel h = ok o) :
    Sim₀ absEIdx pers lst o (resetMetaGo (absU fuel) (absEIdx h)) :=
  LS.toSim₀ (reset_meta_go_ls hrel hinv fuel h) hrun

theorem reset_meta_fast_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.reset_meta_fast pers st fuel e = ok o) :
    Sim₀ absEIdx pers lst o (resetMetaFast (absU fuel) (absEIdx e)) :=
  LS.toSim₀ (reset_meta_fast_ls hrel hinv fuel e) hrun

theorem abstract_range_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {d k c : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract_range pers st fuel h d k c = ok o) :
    Sim₀ absEIdx pers lst o (abstractRange (absU fuel) (absEIdx h) (absU d) (absU k) (absU c)) :=
  LS.toSim₀ (abstract_range_ls hrel hinv fuel h d k c) hrun

theorem bvar_bound_go_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_bound_go pers st fuel h = ok o) :
    Sim₀ absU pers lst o (bvarBoundGo (absU fuel) (absEIdx h)) :=
  LS.toSim₀ (bvar_bound_go_ls hrel hinv fuel h) hrun

theorem fvar_range_go_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_range_go pers st fuel h = ok o) :
    Sim₀ absU pers lst o (fvarRangeGo (absU fuel) (absEIdx h)) :=
  LS.toSim₀ (fvar_range_go_ls hrel hinv fuel h) hrun

theorem bvar_bound_memo_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_bound_memo pers st fuel e = ok o) :
    Sim₀ absU pers lst o (bvarBoundMemo (absU fuel) (absEIdx e)) :=
  LS.toSim₀ (bvar_bound_memo_ls hrel hinv fuel e) hrun

theorem fvar_range_memo_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_range_memo pers st fuel e = ok o) :
    Sim₀ absU pers lst o (fvarRangeMemo (absU fuel) (absEIdx e)) :=
  LS.toSim₀ (fvar_range_memo_ls hrel hinv fuel e) hrun

theorem bvar_b_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_b pers st fuel e = ok o) :
    Sim₀ absU pers lst o (bvarB (absU fuel) (absEIdx e)) :=
  LS.toSim₀ (bvar_b_ls hrel hinv fuel e) hrun

theorem fvar_b_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_b pers st fuel e = ok o) :
    Sim₀ absU pers lst o (fvarB (absU fuel) (absEIdx e)) :=
  LS.toSim₀ (fvar_b_ls hrel hinv fuel e) hrun

theorem has_fvar_fast_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.has_fvar_fast pers st fuel e = ok o) :
    Sim₀ id pers lst o (hasFvarFast (absU fuel) (absEIdx e)) :=
  LS.toSim₀ (has_fvar_fast_ls hrel hinv fuel e) hrun

theorem loose_bvars_bounded_fast_refines {pers st lst} {fuel k : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.loose_bvars_bounded_fast pers st fuel k e = ok o) :
    Sim₀ id pers lst o (looseBVarsBoundedFast (absU fuel) (absU k) (absEIdx e)) :=
  LS.toSim₀ (loose_bvars_bounded_fast_ls hrel hinv fuel k e) hrun

theorem abstract1_go_refines {pers st lst} {d : Std.U64} {fuel : Std.U64} {h : arena.handle.EIdx} {k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract1_go pers st d fuel h k = ok o) :
    Sim₀ absEIdx pers lst o (abstract1Go (absU d) (absU fuel) (absEIdx h) (absU k)) :=
  LS.toSim₀ (abstract1_go_ls hrel hinv d fuel h k) hrun

theorem abstract1_fast_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {d k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract1_fast pers st fuel e d k = ok o) :
    Sim₀ absEIdx pers lst o (abstract1Fast (absU fuel) (absEIdx e) (absU d) (absU k)) :=
  LS.toSim₀ (abstract1_fast_ls hrel hinv fuel e d k) hrun

theorem abstract_range_go_refines {pers st lst} {d k : Std.U64} {fuel : Std.U64} {h : arena.handle.EIdx} {c : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract_range_go pers st d k fuel h c = ok o) :
    Sim₀ absEIdx pers lst o (abstractRangeGo (absU d) (absU k) (absU fuel) (absEIdx h) (absU c)) :=
  LS.toSim₀ (abstract_range_go_ls hrel hinv d k fuel h c) hrun

theorem abstract_range_fast_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {d k c : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract_range_fast pers st fuel e d k c = ok o) :
    Sim₀ absEIdx pers lst o (abstractRangeFast (absU fuel) (absEIdx e) (absU d) (absU k) (absU c)) :=
  LS.toSim₀ (abstract_range_fast_ls hrel hinv fuel e d k c) hrun

theorem lower_bvars_go_refines {pers st lst} {amount : Std.U64} {fuel : Std.U64} {h : arena.handle.EIdx} {c : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lower_bvars_go pers st amount fuel h c = ok o) :
    Sim₀ absEIdx pers lst o (lowerBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)) :=
  LS.toSim₀ (lower_bvars_go_ls hrel hinv amount fuel h c) hrun

theorem lower_bvars_fast_refines {pers st lst} {fuel amount c : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lower_bvars_fast pers st fuel amount c e = ok o) :
    Sim₀ absEIdx pers lst o (lowerBVarsFast (absU fuel) (absU amount) (absU c) (absEIdx e)) :=
  LS.toSim₀ (lower_bvars_fast_ls hrel hinv fuel amount c e) hrun

theorem instantiate1_lift_go_refines {pers st lst} {v : arena.handle.EIdx} {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate1_lift_go pers st v fuel h d = ok o) :
    Sim₀ absEIdx pers lst o (instantiate1LiftGo (absEIdx v) (absU fuel) (absEIdx h) (absU d)) :=
  LS.toSim₀ (instantiate1_lift_go_ls hrel hinv v fuel h d) hrun

theorem instantiate1_lift_fast_refines {pers st lst} {fuel : Std.U64} {e v : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate1_lift_fast pers st fuel e v d = ok o) :
    Sim₀ absEIdx pers lst o (instantiate1LiftFast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) :=
  LS.toSim₀ (instantiate1_lift_fast_ls hrel hinv fuel e v d) hrun

theorem inst_spine_from_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {t : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_spine_from pers st fuel args i t e = ok o) :
    Sim₀ absEIdx pers lst o (instSpine (absU fuel) (absEIdxListFrom args i) (absU t) (absEIdx e)) :=
  LS.toSim₀ (inst_spine_from_ls hrel hinv fuel args i t e) hrun

theorem inst_spine_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {t : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_spine pers st fuel args t e = ok o) :
    Sim₀ absEIdx pers lst o (instSpine (absU fuel) (absEIdxList args) (absU t) (absEIdx e)) :=
  LS.toSim₀ (inst_spine_ls hrel hinv fuel args t e) hrun

theorem bvar_range_refines {pers st lst} {m_i n k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_range pers st m_i n k = ok o) :
    Sim₀ absEIdxList pers lst o (bvarRange (absU m_i) (absU n) (absU k)) :=
  LS.toSim₀ (bvar_range_ls hrel hinv m_i n k) hrun

theorem rec_rule_plain_refines {pers st lst} {fuel : Std.U64} {rec_ty : arena.handle.EIdx} {m_i r_p cn_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.rec_rule_plain pers st fuel rec_ty m_i r_p cn_p = ok o) :
    Sim₀ id pers lst o (recRulePlain (absU fuel) (absEIdx rec_ty) (absU m_i) (absU r_p) (absU cn_p)) :=
  LS.toSim₀ (rec_rule_plain_ls hrel hinv fuel rec_ty m_i r_p cn_p) hrun

theorem pis_to_lams_refines {pers st lst} {k : Std.U64} {h body : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.pis_to_lams pers st k h body = ok o) :
    Sim₀ absOptE pers lst o (pisToLams (absU k) (absEIdx h) (absEIdx body)) :=
  LS.toSim₀ (pis_to_lams_ls hrel hinv k h body) hrun

theorem replace_pi_body_refines {pers st lst} {k : Std.U64} {h b : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.replace_pi_body pers st k h b = ok o) :
    Sim₀ absOptE pers lst o (replacePiBody (absU k) (absEIdx h) (absEIdx b)) :=
  LS.toSim₀ (replace_pi_body_ls hrel hinv k h b) hrun

theorem inst_pis_from_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_from pers st fuel e args i = ok o) :
    Sim₀ absOptE pers lst o (instPis (absU fuel) (absEIdx e) (absEIdxListFrom args i)) :=
  LS.toSim₀ (inst_pis_from_ls hrel hinv fuel e args i) hrun

theorem inst_pis_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {args : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis pers st fuel e args = ok o) :
    Sim₀ absOptE pers lst o (instPis (absU fuel) (absEIdx e) (absEIdxList args)) :=
  LS.toSim₀ (inst_pis_ls hrel hinv fuel e args) hrun

theorem inst_pis_at_from_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_from pers st fuel args i h = ok o) :
    Sim₀ absOptArgsE pers lst o (instPisAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)) :=
  LS.toSim₀ (inst_pis_at_from_ls hrel hinv fuel args i h) hrun

theorem inst_pis_at_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at pers st fuel args h = ok o) :
    Sim₀ absOptArgsE pers lst o (instPisAt (absU fuel) (absEIdxList args) (absEIdx h)) :=
  LS.toSim₀ (inst_pis_at_ls hrel hinv fuel args h) hrun

theorem inst_lams_at_from_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lams_at_from pers st fuel args i h = ok o) :
    Sim₀ absOptArgsE pers lst o (instLamsAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)) :=
  LS.toSim₀ (inst_lams_at_from_ls hrel hinv fuel args i h) hrun

theorem inst_lams_at_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lams_at pers st fuel args h = ok o) :
    Sim₀ absOptArgsE pers lst o (instLamsAt (absU fuel) (absEIdxList args) (absEIdx h)) :=
  LS.toSim₀ (inst_lams_at_ls hrel hinv fuel args h) hrun

theorem inst_pis_at_f_go_refines {pers st lst} {fuel : Std.U64} {acc args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_f_go pers st fuel acc args i h = ok o) :
    Sim₀ absOptArgsE pers lst o (instPisAtFGo (absU fuel) (absEIdxArr acc) (absEIdxListFrom args i) (absEIdx h)) :=
  LS.toSim₀ (inst_pis_at_f_go_ls hrel hinv fuel acc args i h) hrun

theorem inst_pis_at_f_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_f pers st fuel args e = ok o) :
    Sim₀ absOptArgsE pers lst o (instPisAtF (absU fuel) (absEIdxList args) (absEIdx e)) :=
  LS.toSim₀ (inst_pis_at_f_ls hrel hinv fuel args e) hrun

theorem inst_lams_at_f_go_refines {pers st lst} {fuel : Std.U64} {acc args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lams_at_f_go pers st fuel acc args i h = ok o) :
    Sim₀ absOptArgsE pers lst o (instLamsAtFGo (absU fuel) (absEIdxArr acc) (absEIdxListFrom args i) (absEIdx h)) :=
  LS.toSim₀ (inst_lams_at_f_go_ls hrel hinv fuel acc args i h) hrun

theorem inst_lams_at_f_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lams_at_f pers st fuel args e = ok o) :
    Sim₀ absOptArgsE pers lst o (instLamsAtF (absU fuel) (absEIdxList args) (absEIdx e)) :=
  LS.toSim₀ (inst_lams_at_f_ls hrel hinv fuel args e) hrun

theorem inst_pis_at_lift_from_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_lift_from pers st fuel args i h = ok o) :
    Sim₀ absOptE pers lst o (instPisAtLift (absU fuel) (absEIdxListFrom args i) (absEIdx h)) :=
  LS.toSim₀ (inst_pis_at_lift_from_ls hrel hinv fuel args i h) hrun

theorem inst_pis_at_lift_refines {pers st lst} {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_lift pers st fuel args h = ok o) :
    Sim₀ absOptE pers lst o (instPisAtLift (absU fuel) (absEIdxList args) (absEIdx h)) :=
  LS.toSim₀ (inst_pis_at_lift_ls hrel hinv fuel args h) hrun

theorem rename_consts_go_refines {pers st lst} {F : Type} {inst : arena.expr_ops.NIdxToNIdx F} {f : F} {g : NIdx → NIdx} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hg : RenameRel inst f g)
    (hrun : arena.expr_ops.rename_consts_go inst pers st f fuel h = ok o) :
    Sim₀ absEIdx pers lst o (renameConstsGo g (absU fuel) (absEIdx h)) :=
  LS.toSim₀ (rename_consts_go_ls hg hrel hinv fuel h) hrun

theorem rename_consts_fast_refines {pers st lst} {F : Type} {inst : arena.expr_ops.NIdxToNIdx F} {f : F} {g : NIdx → NIdx} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hg : RenameRel inst f g)
    (hrun : arena.expr_ops.rename_consts_fast inst pers st fuel f e = ok o) :
    Sim₀ absEIdx pers lst o (renameConstsFast (absU fuel) g (absEIdx e)) :=
  LS.toSim₀ (rename_consts_fast_ls hg hrel hinv fuel e) hrun


end ConRon.Refine2
