/-
# The inductive routes' shared foundation (task #57, `CORE_PLAN.md` step 7)

`crates/con-ron-core/src/kernel/inductives/` — the two install routes for an
inductive block (task #25) — is refined against
`ConLeche/Kernel/Inductives/*.lean` and the cached drivers of
`ConLeche/Cached/CheckerC.lean` in the eight sibling files `Ind*.lean`.  This
file is what all eight import: the abstraction functions and
well-formedness predicates of the routes' **record types**, and the
**operation lemmas** that turn the knot (task #53/#55) into the fields of
con-leche's `sharedOpsC` that every stage calls.

## The records

`sum_parts::InductiveShape`, `native_parts::{RecFieldKind, NativeParts}`,
`struct_parts::StructParts` and `native_install::NativePass` abstract by a
*function* except the last, which stores an `FEnv` — so `NativePassRel` is a
relation, `FEnv`'s (`Refine/FEnv.lean`).  **These belong in `Refine/Abs.lean`
and are to be unified into it** when the tier is merged; they live here so
that task #57 lands without touching a file three other tasks are editing.

Two spellings deviate from con-leche and the abstraction is where they meet:
Lean's `NativeParts extends InductiveShape` is the port's field `shape`
(task #25's deviation 3), so `absNativeParts` builds `⟨absInductiveShape
p.shape, …⟩`; and every count is a `U64` (§3.3), read by `.val`.

## The operations

§3.1's knot ruling dissolves con-leche's `CheckerOps` record into direct
wrapper calls (task #25's deviation 2): `ops.whnf env d e` is
`core_c::whnf(mode, core_k::check_fuel(), st, fe, d, &e)`, and
`sharedOpsC mode fe`'s fields are `coreKnotI mode fe checkFuel` — the *same*
knot, at the *same* fuel.  So the lemmas below are the fields of
`Core.Wrappers mode checkFuelU` restated at the form the stages read, plus
`ensureSortI`, which is `whnf` and a `.sort` match
(`Cached/CoreC.lean:1115-1119`).  Every lemma of the eight files takes
`hk : Core.KnotSpec mode checkFuelU` — task #55 is proving its arms
concurrently — and reaches the operations only through these.

`checkFuelU` is the port's `core_k::check_fuel()` as a value: Aeneas gives
the zero-argument function the type `Result U64`, so the hypothesis cannot
literally read `core_k.check_fuel`; `check_fuel_eq` is the identity that
closes the gap, and `checkFuelU_val` is `= ConLeche.checkFuel`.

## The full outcome (task #67, DESIGN.md §3's ruling of 2026-09-13)

Each operation lemma comes in **two** halves, because `Core.Wrappers` is now
stated over the Rust computation's whole outcome: `ops_*` is the accept
direction (the pre-#67 statement, `Wrappers.*.ok`) and `ops_*_err` says that
where the port's wrapper threw a mirrored error, con-leche's `sharedOpsC`
slot throws at the same *kind* (`Refine/Abs.lean`'s `ErrSim`; messages are
never compared).  The eight `Ind*.lean` files reach a failing operation only
through the `_err` companions.
-/
import ConRon.Refine.Scalars
import ConRon.RefineOld.Core.Statements
import ConRon.RefineOld.StateC
import ConLeche.Cached.CheckerC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.IndAbs

/-! ## `core_k::check_fuel()` as a value -/

/-- `core_k::check_fuel()`'s value (`core_k.rs:2692`), the fuel at which
`sharedOpsC` ties the knot (`checkFuel = 100000`,
`ConLeche/Kernel/Core.lean:2904`). -/
def checkFuelU : Std.U64 := 100000#u64

/-- Aeneas models the zero-argument `check_fuel()` as a `Result`; this is the
identity that lets a stage's `let i ← core_k.check_fuel` be rewritten to the
value the knot hypothesis is stated at. -/
@[simp] theorem check_fuel_eq : kernel.core_k.check_fuel = ok checkFuelU := by
  simp [kernel.core_k.check_fuel, checkFuelU]

/-- The fuel agrees with con-leche's. -/
@[simp] theorem checkFuelU_val : checkFuelU.val = ConLeche.checkFuel := by
  simp [checkFuelU, ConLeche.checkFuel]

/-! ## The record abstractions (**to be unified into `Refine/Abs.lean`**) -/

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:60-76` — `RecFieldKind`. -/
def absRecFieldKind :
    inductives.native_parts.RecFieldKind → ConLeche.RecFieldKind
  | .Ordinary => .ordinary
  | .Recursive => .recursive
  | .Reflexive => .reflexive
  | .Negative => .negative
  | .Unsupported => .unsupported

/-- One constructor's field kinds. -/
def absRecFieldKinds
    (ks : alloc.vec.Vec inductives.native_parts.RecFieldKind) :
    List ConLeche.RecFieldKind :=
  ks.val.map absRecFieldKind

/-- `NativeParts.kinds`: per constructor, per field. -/
def absKindss
    (kss : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)) :
    List (List ConLeche.RecFieldKind) :=
  kss.val.map absRecFieldKinds

/-- A constructor list `Vec<(ConstantVal, u64)>` as `List (ConstantVal × Nat)`
(`InductiveShape.ctors`, `NativePass.ctorsA`). -/
def absCtors (cs : alloc.vec.Vec (env.ConstantVal × Std.U64)) :
    List (ConLeche.ConstantVal × Nat) :=
  cs.val.map (fun c => (absConstantVal c.1, c.2.val))

/-- A `Vec<Vec<Level>>` as `List (List Level)` (`NativePass.sortss`). -/
def absLevelss (uss : alloc.vec.Vec (alloc.vec.Vec level.Level)) :
    List (List ConLeche.Level) :=
  uss.val.map absLevels

/-- `ConLeche/Kernel/Inductives/SumParts.lean:78-101` — `InductiveShape`. -/
def absInductiveShape (p : inductives.sum_parts.InductiveShape) :
    ConLeche.InductiveShape where
  cvT := absConstantVal p.cv_t
  ctors := absCtors p.ctors
  nP := p.n_p.val
  nIdx := p.n_idx.val
  cvR := absConstantVal p.cv_r
  elim := absName p.elim
  resSort := absLevel p.res_sort
  rhss := absExprs p.rhss
  large := p.large
  isProp := p.is_prop

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:177-192` — `NativeParts`.
Lean's `extends InductiveShape` is the port's field `shape` (task #25's
deviation 3), so the abstraction is where the two spellings meet. -/
def absNativeParts (p : inductives.native_parts.NativeParts) :
    ConLeche.NativeParts where
  toInductiveShape := absInductiveShape p.shape
  kinds := absKindss p.kinds
  recPinned := p.rec_pinned

/-- `ConLeche/Kernel/Inductives/StructParts.lean:214-241` — `StructParts`. -/
def absStructParts (p : inductives.struct_parts.StructParts) :
    ConLeche.StructParts where
  cvT := absConstantVal p.cv_t
  cvC := absConstantVal p.cv_c
  nP := p.n_p.val
  nF := p.n_f.val
  cvR := absConstantVal p.cv_r
  elim := absName p.elim
  resSort := absLevel p.res_sort
  rhs := absExpr p.rhs
  large := p.large
  isProp := p.is_prop

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:527-537` — `NativePass`.
A **relation**, not a function: the record's `env₁` is an `FEnv`, which
`Refine/FEnv.lean` abstracts relationally. -/
def NativePassRel (q : inductives.native_install.NativePass)
    (lq : ConLeche.NativePass ConLeche.FEnv) : Prop :=
  FEnvRel q.env1 lq.env₁
  ∧ absConstantVal q.cv_ta = lq.cvTa
  ∧ absNativeParts q.p = lq.p
  ∧ absCtors q.ctors_a = lq.ctorsA
  ∧ absLevelss q.sortss = lq.sortss

/-! ## The records' well-formedness (**to be unified into `Refine/Abs.lean`**)

Hereditary, in the task-#5/#17 style: every stored `Expr`/`Level`/`Name` is
WF, which is what the pointer fast paths and `abs`'s injectivity need. -/

/-- Every stored constant and expression of a shape is WF. -/
def InductiveShapeWF (p : inductives.sum_parts.InductiveShape) : Prop :=
  ConstantValWF p.cv_t ∧ (∀ c ∈ p.ctors.val, ConstantValWF c.1)
  ∧ ConstantValWF p.cv_r ∧ NameWF p.elim ∧ LevelWF p.res_sort
  ∧ ExprsWF p.rhss

/-- `NativePartsWF`: the shape's, plus nothing — the kinds are tags. -/
def NativePartsWF (p : inductives.native_parts.NativeParts) : Prop :=
  InductiveShapeWF p.shape

/-- `StructPartsWF`. -/
def StructPartsWF (p : inductives.struct_parts.StructParts) : Prop :=
  ConstantValWF p.cv_t ∧ ConstantValWF p.cv_c ∧ ConstantValWF p.cv_r
  ∧ NameWF p.elim ∧ LevelWF p.res_sort ∧ ExprWF p.rhs

/-- `NativePassWF`. -/
def NativePassWF (q : inductives.native_install.NativePass) : Prop :=
  FEnvWF q.env1 ∧ ConstantValWF q.cv_ta ∧ NativePartsWF q.p
  ∧ (∀ c ∈ q.ctors_a.val, ConstantValWF c.1)
  ∧ (∀ us ∈ q.sortss.val, LevelsWF us)

/-! ## The operations

`sharedOpsC mode fe`'s fields, as the port spells them.  Each is one field of
`Core.Wrappers mode checkFuelU` — `Refines{E,B}` unfolded at the `sharedOpsC`
spelling, with the ignored `Env` argument dropped — except `ensureSort`,
which is `whnf` plus con-leche's `.sort` match. -/

/-- `ExprWF` inverted at a `.Sort` node: only `ExprWF.sort` can have built
one, and `Expr.sort_inv` says which level it stored.  **To be unified into
`Refine/Expr.lean`** beside the other `*_inv`s; `ensure_sort_i`'s node read is
its first consumer. -/
theorem sort_node_wf {d : Std.U64} {u : level.Level}
    (h : ExprWF (.mk (.mk d (.«Sort» u)))) : LevelWF u := by
  cases h with
  | bvar hb => obtain ⟨_, he, -, -, -⟩ := Expr.bvar_inv hb; simp at he
  | fvar _ hb => obtain ⟨_, he, -, -, -⟩ := Expr.fvar_inv hb; simp at he
  | «sort» hu hb =>
    obtain ⟨_, _, -, he, -, -, -⟩ := Expr.sort_inv hb
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at he
    obtain ⟨-, he⟩ := he; cases he; exact hu
  | mk_const _ _ hb =>
    obtain ⟨_, _, -, he, -, -, -⟩ := Expr.mk_const_inv hb; simp at he
  | app _ _ hb => obtain ⟨_, he, -, -, -⟩ := Expr.app_inv hb; simp at he
  | lam _ _ _ hb => obtain ⟨_, he, -, -, -⟩ := Expr.lam_inv hb; simp at he
  | forall_e _ _ _ hb => obtain ⟨_, he, -, -, -⟩ := Expr.forall_e_inv hb; simp at he
  | let_e _ _ _ hb => obtain ⟨_, he, -, -, -⟩ := Expr.let_e_inv hb; simp at he
  | lit _ hb => obtain ⟨_, he, -, -, -⟩ := Expr.lit_inv hb; simp at he
  | proj _ _ hb => obtain ⟨_, he, -, -, -⟩ := Expr.proj_inv hb; simp at he

/-- **`throw` in `CheckCM`**: the monad-plumbing `simp` set the `ensureSort`
proofs use does not carry the `MonadExcept` instance, so `simp` would
otherwise leave con-leche's `throw` arm un-run
(`Refine/Core/Arms/Shared.lean` re-declares the same lemma;
`attribute [local simp]` does not travel across files). -/
private theorem checkCM_throw_apply {b : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM b) lst = .error le := rfl

attribute [local simp] checkCM_throw_apply

/-- The port's `Err` value at `ensure_sort_i`'s one mirrored `throw` arm:
`core_types::invalid` is the `Invalid` constructor (task #67). -/
private theorem invalid_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v :=
  (Result.ok_injective (by rw [core_types.invalid] at h; exact h)).symm

section Ops

variable {mode : env.CheckMode} (hw : Core.Wrappers mode checkFuelU)

include hw

/-- `ops.whnf` (`sharedOpsC`'s `whnf`). -/
theorem ops_whnf {st fe d e r st'} (hst : StateWF st) (hfe : FEnvWF fe)
    (he : ExprWF e)
    (h : cached.core_c.whnf mode checkFuelU st fe d e = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).whnf
            (absEnv fe.env) d.val (absExpr e)).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r :=
  hw.whnf.ok st fe d e r st' hst hfe he h

/-- `ops.whnf`'s failure half (task #67): the wrapper threw, and con-leche's
`whnf` slot throws at the same kind. -/
theorem ops_whnf_err {st fe d e ce st'} (hst : StateWF st) (hfe : FEnvWF fe)
    (he : ExprWF e)
    (h : cached.core_c.whnf mode checkFuelU st fe d e = ok (.Err ce, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ErrSim ce (((ConLeche.Cached.sharedOpsC (absMode mode) lfe).whnf
        (absEnv fe.env) d.val (absExpr e)).run lst) :=
  fun lst lfe hrel hfrel =>
    hw.whnf.err st fe d e ce st' hst hfe he h lst lfe hrel hfrel

/-- `ops.inferType`. -/
theorem ops_infer {st fe d e r st'} (hst : StateWF st) (hfe : FEnvWF fe)
    (he : ExprWF e)
    (h : cached.core_c.infer mode checkFuelU st fe d e = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).inferType
            (absEnv fe.env) d.val (absExpr e)).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r :=
  hw.infer.ok st fe d e r st' hst hfe he h

/-- `ops.inferType`'s failure half. -/
theorem ops_infer_err {st fe d e ce st'} (hst : StateWF st) (hfe : FEnvWF fe)
    (he : ExprWF e)
    (h : cached.core_c.infer mode checkFuelU st fe d e = ok (.Err ce, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ErrSim ce (((ConLeche.Cached.sharedOpsC (absMode mode) lfe).inferType
        (absEnv fe.env) d.val (absExpr e)).run lst) :=
  fun lst lfe hrel hfrel =>
    hw.infer.err st fe d e ce st' hst hfe he h lst lfe hrel hfrel

/-- `ops.annotate`. -/
theorem ops_annotate {st fe d e r st'} (hst : StateWF st) (hfe : FEnvWF fe)
    (he : ExprWF e)
    (h : cached.core_c.annotate mode checkFuelU st fe d e = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).annotate
            (absEnv fe.env) d.val (absExpr e)).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r :=
  hw.annotate.ok st fe d e r st' hst hfe he h

/-- `ops.annotate`'s failure half. -/
theorem ops_annotate_err {st fe d e ce st'} (hst : StateWF st) (hfe : FEnvWF fe)
    (he : ExprWF e)
    (h : cached.core_c.annotate mode checkFuelU st fe d e = ok (.Err ce, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ErrSim ce (((ConLeche.Cached.sharedOpsC (absMode mode) lfe).annotate
        (absEnv fe.env) d.val (absExpr e)).run lst) :=
  fun lst lfe hrel hfrel =>
    hw.annotate.err st fe d e ce st' hst hfe he h lst lfe hrel hfrel

/-- `ops.isDefEq`. -/
theorem ops_defeq {st fe d a b r st'} (hst : StateWF st) (hfe : FEnvWF fe)
    (ha : ExprWF a) (hb : ExprWF b)
    (h : cached.core_c.defeq mode checkFuelU st fe d a b = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).isDefEq
            (absEnv fe.env) d.val (absExpr a) (absExpr b)).run lst
          = .ok (r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' :=
  hw.defeq.ok st fe d a b r st' hst hfe ha hb h

/-- `ops.isDefEq`'s failure half. -/
theorem ops_defeq_err {st fe d a b ce st'} (hst : StateWF st) (hfe : FEnvWF fe)
    (ha : ExprWF a) (hb : ExprWF b)
    (h : cached.core_c.defeq mode checkFuelU st fe d a b = ok (.Err ce, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ErrSim ce (((ConLeche.Cached.sharedOpsC (absMode mode) lfe).isDefEq
        (absEnv fe.env) d.val (absExpr a) (absExpr b)).run lst) :=
  fun lst lfe hrel hfrel =>
    hw.defeq.err st fe d a b ce st' hst hfe ha hb h lst lfe hrel hfrel

/-- `ops.ensureSort`: `whnf` and con-leche's `.sort` match
(`ensureSortI`, `Cached/CoreC.lean:1115-1119`).  The Rust reads the whnf'd
node's kind and `level::dup`s the sort's level; the match's nine other arms
throw `.invalid`, so on success the node *is* a `.Sort` — and `ExprWF` of the
whnf result, which `ops_whnf` hands back, is what says its level is WF. -/
theorem ops_ensure_sort {st fe d e u st'} (hst : StateWF st) (hfe : FEnvWF fe)
    (he : ExprWF e)
    (h : cached.core_c.ensure_sort_i mode checkFuelU st fe d e
        = ok (.Ok u, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).ensureSort
            (absEnv fe.env) d.val (absExpr e)).run lst
          = .ok (absLevel u, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ LevelWF u := by
  intro lst lfe hrel hfer
  rw [cached.core_c.ensure_sort_i.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨r, st1⟩ := p
  cases r with
  | Err err => simp at h
  | Ok w =>
    obtain ⟨lst', hrun, hrel', hwf', hwfe⟩ :=
      ops_whnf hw hst hfe he hp lst lfe hrel hfer
    obtain ⟨⟨dd, k⟩⟩ := w
    try dsimp only at h
    cases k with
    | «Sort» u0 =>
      simp [ron.node.ExprView.ofKind] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lst', ?_, hrel', hwf', sort_node_wf hwfe⟩
      have hrun' :
          (ConLeche.Cached.coreKnotI (absMode mode) lfe ConLeche.checkFuel).whnf
              d.val (absExpr e) lst
            = Except.ok (ConLeche.Expr.sort (absLevel u0), lst') := by
        simpa [ConLeche.Cached.sharedOpsC, ConLeche.Cached.opE, StateT.run]
          using hrun
      simp [ConLeche.Cached.sharedOpsC, ConLeche.Cached.opS,
        ConLeche.Cached.ensureSortI, StateT.run, Bind.bind, StateT.bind,
        Except.bind, Pure.pure, StateT.pure, Except.pure, hrun']
    | Bvar i2 => simp [ron.node.ExprView.ofKind] at h
    | Fvar idx ty => simp [ron.node.ExprView.ofKind] at h
    | Const n us => simp [ron.node.ExprView.ofKind] at h
    | App f a => simp [ron.node.ExprView.ofKind] at h
    | Lam ty bo m => simp [ron.node.ExprView.ofKind] at h
    | ForallE ty bo m => simp [ron.node.ExprView.ofKind] at h
    | LetE ty v bo => simp [ron.node.ExprView.ofKind] at h
    | Lit l => simp [ron.node.ExprView.ofKind] at h
    | Proj s i2 x => simp [ron.node.ExprView.ofKind] at h

/-- `ops.ensureSort`'s failure half (task #67), with **two** mirrored arms:
`whnf` threw, and con-leche's bind fails at the very same step
(`ErrSim.bindCM`); or the reduced type was not a `Sort`, and both sides throw
`invalid` — the port at `ensure_sort_i.M`'s code points, con-leche at
`"expected a sort"` (`Cached/CoreC.lean:1118`).  Messages are never
compared. -/
theorem ops_ensure_sort_err {st fe d e ce st'} (hst : StateWF st)
    (hfe : FEnvWF fe) (he : ExprWF e)
    (h : cached.core_c.ensure_sort_i mode checkFuelU st fe d e
        = ok (.Err ce, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ErrSim ce (((ConLeche.Cached.sharedOpsC (absMode mode) lfe).ensureSort
        (absEnv fe.env) d.val (absExpr e)).run lst) := by
  intro lst lfe hrel hfer
  rw [cached.core_c.ensure_sort_i.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨r, st1⟩ := p
  cases r with
  | Err err =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [ConLeche.Cached.sharedOpsC, ConLeche.Cached.opS,
      ConLeche.Cached.ensureSortI]
    exact ErrSim.bindCM
      (hw.whnf.err st fe d e err st1 hst hfe he hp lst lfe hrel hfer)
  | Ok w =>
    obtain ⟨lst', hrun, hrel', hwf', hwfe⟩ :=
      ops_whnf hw hst hfe he hp lst lfe hrel hfer
    obtain ⟨⟨dd, k⟩⟩ := w
    have hrun' :
        (ConLeche.Cached.coreKnotI (absMode mode) lfe ConLeche.checkFuel).whnf
            d.val (absExpr e) lst
          = Except.ok (absExprKind k, lst') := by
      simpa [ConLeche.Cached.sharedOpsC, ConLeche.Cached.opE, StateT.run]
        using hrun
    try dsimp only at h
    cases k
    case «Sort» u0 => simp [ron.node.ExprView.ofKind] at h
    all_goals
      simp [ron.node.ExprView.ofKind] at h
      obtain ⟨v, -, hce, rfl⟩ := h
      rw [invalid_err hce]
      refine ErrSim.invalid (s := "expected a sort") ?_
      simp only [absExprKind] at hrun'
      simp [ConLeche.Cached.sharedOpsC, ConLeche.Cached.opS,
        ConLeche.Cached.ensureSortI, StateT.run, Bind.bind, StateT.bind,
        Except.bind, hrun']

end Ops

end ConRon.Refine.IndAbs
