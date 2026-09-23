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

end ConRon.Refine2
