/-
# The io-grade inference body (task #55, `CORE_PLAN.md` step 6)

`cached::core_c::infer_body_io_i` (`core_c.rs:3588`) is con-leche's
**`inferBodyIOI`** (`ConLeche/Cached/CoreC.lean:1399-1448`): `inferBodyI` with
exactly three clauses changed — the application spine walk is the gated
`inferSpineIOI` (the ONE io-graded check), and the `∀`/`λ` clauses are the
*chained* pure io clauses, deliberately not the task-#72 telescope loops.
Every other node view dispatches to `inferBodyI` itself, on the record the
knot hands this body — the `ioView`.

**Task #61.**  `infer_body_i` used to carry that choice as an `io : Bool`
(task #18's deviation 4), and the `io = true` instance was *false*: the Rust's
`.app`/`.forallE`/`.lam` clauses called the full-grade wrappers there.  Those
three views are overridden right here, so the flag only ever mattered at
`.proj` — the one delegated view whose clause makes a recursive call, and at
`ioView` that call is the io slot.  `infer_body_io_i` therefore spells the
`.proj` clause itself (`infer_proj_i … true`, `InferIODeps.inferProj`), and
`infer_body_i` is flagless; at the six remaining views `inferBodyI`'s clause
makes no recursive call at all, so the record is irrelevant there and the six
`inferBodyI_leaf_*` `rfl`s below say so.

So this file owns four Rust functions:

| Rust | con-leche |
|---|---|
| `infer_body_io_i` (`:3588`) | `inferBodyIOI` (`CoreC.lean:1399`) |
| `infer_forall_io_i` (`:3622`) | its `.forallE` clause |
| `infer_lam_io_i` (`:3684`) | its `.lam` clause |
| `infer_lam_cod_io_i` (`:3723`) | that clause's codomain validation |

The last three have no *named* con-leche twin — con-leche writes them inline
in `inferBodyIOI`'s `match`.  Following `Refine/StateC.lean`'s convention for
inline subterms (`eqvStep`, `nodeL`), the three blocks are **named** below and
tied back to `inferBodyIOI` by `inferBodyIOI_forallE` (a `rfl`-identity) and
`inferBodyIOI_lam` (two monad laws — Lean's `do` elaborator inlines a clause's
continuation into each arm of a gate, where the Rust returns the gate as its
own `CheckM<()>`), so nothing is assumed: the named block *is* the clause.

The `.M`-suffixed `Array Std.U32` constants (`infer_forall_io_i.M`,
`.M_COD`, `infer_lam_cod_io_i.M_CHAIN`, `.M_LEAF`) are error-message code
points.  At the **full outcome** (task #67, DESIGN.md §3's ruling of
2026-09-13) each of the four arms they build is *mirrored* by a `throw`
beside it in `inferBodyIOI`, at the same kind and at the same step:

| Rust | con-leche |
|---|---|
| `:3688` `not_implemented(M_COD)` | `:1424` `throw (.notImplemented "sort-annotation mismatch (forall-cod)")` |
| `:3699` `invalid(M)` | `:1427` `throw (.invalid "expected a sort")` |
| `:3776` `not_implemented(M_CHAIN)` | `:1438` `throw (.notImplemented "sort-annotation mismatch (lam-cod-chain)")` |
| `:3789` `not_implemented(M_LEAF)` | `:1444` `throw (.notImplemented "sort-annotation mismatch (lam-cod-leaf)")` |

so the constants still carry no theorem — the messages themselves are never
compared (DESIGN.md §3.1), only the kinds.  Every other failure of the four
functions is a sub-computation's, carried across by `ErrSim.trans` through
con-leche's own bind.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKGuards
import ConRon.Refine.ExprOpsCSubst
import ConRon.Refine.ExprOpsCAbs
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.PropWhen
import ConRon.Refine.Level
import ConRon.Refine.Env

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! ## The three inline blocks of `inferBodyIOI`

Each is the cited clause verbatim, with `r` the record the knot hands the
body (`(knot …).ioView`, so `r.infer` is the io slot).  The two
`inferBodyIOI_*` identities below are what ties them back. -/

/-- `ConLeche/Cached/CoreC.lean:1434-1445` — the io `λ` clause's
codomain-sort validation, the block `inferBodyIOI` runs under
`mode.verifiedChecks`: **the chain rule** at an outer binder (datum equality
with the neighbour's own `lamPw`, no inference), the leaf computation at the
innermost binder. -/
def inferLamCodIOI (r : ConLeche.Cached.CoreFnsI) (depth : Nat)
    (body : ConLeche.Expr) (mb : ConLeche.BinderMeta) (bt : ConLeche.Expr) :
    ConLeche.Cached.CheckCM Unit := do
  match body.lamPw with
  | some pwI =>
    unless mb.pw == pwI do
      throw (.notImplemented "sort-annotation mismatch (lam-cod-chain)")
  | none =>
    let btt ← r.infer (depth + 1) bt
    let vb ← ConLeche.Cached.ensureSortI r (depth + 1) btt
    unless ConLeche.Level.zeronessOf vb == mb.pw do
      throw (.notImplemented "sort-annotation mismatch (lam-cod-leaf)")

/-- `ConLeche/Cached/CoreC.lean:1428-1447` — the io `λ` clause, chained and
with **no domain-sort run** (con-leche's task #168 stage 2). -/
def inferLamIOI (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (depth : Nat) (ty body : ConLeche.Expr) (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.CheckCM ConLeche.Expr := do
  let fv ← pure (ConLeche.Expr.fvar depth ty)
  let ob ← ConLeche.Cached.inst1M body fv
  let bt ← r.infer (depth + 1) ob
  if mode.verifiedChecks then
    inferLamCodIOI r depth body mb bt
  let bAbs ← ConLeche.Cached.abstract1M bt depth
  pure (ConLeche.Expr.forallE ty bAbs mb)

/-- `ConLeche/Cached/CoreC.lean:1407-1426` — the io `∀` clause, chained. -/
def inferForallIOI (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (depth : Nat) (ty body : ConLeche.Expr) (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.CheckCM ConLeche.Expr := do
  let tty ← r.infer depth ty
  let wtty ← r.whnf depth tty
  match wtty with
  | .sort u => do
    let fv ← pure (ConLeche.Expr.fvar depth ty)
    let ob ← ConLeche.Cached.inst1M body fv
    let bt ← r.infer (depth + 1) ob
    let v ← ConLeche.Cached.ensureSortI r (depth + 1) bt
    if mode.verifiedChecks then
      unless ConLeche.Level.zeronessOf v == mb.pw do
        throw (.notImplemented "sort-annotation mismatch (forall-cod)")
    let iu ← pure (ConLeche.Level.imax u v)
    pure (ConLeche.Expr.sort iu)
  | _ => throw (.invalid "expected a sort")

/-- The `.forallE` clause of `inferBodyIOI` *is* `inferForallIOI`. -/
theorem inferBodyIOI_forallE (mode : ConLeche.CheckMode)
    (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv) (depth : Nat)
    (ty body : ConLeche.Expr) (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.inferBodyIOI mode r fe depth (.forallE ty body mb)
      = inferForallIOI mode r depth ty body mb := rfl

/-! ### Monad plumbing

Lean's `do` elaborator inlines a clause's continuation (here the
`abstract1M`/rebuild join point) into each arm of a gate, where the Rust
returns the gate as its own `CheckM<()>`: `gate_bind` and `check_bind` are the
whole of that difference.  `run_bind` is the one step every proof below takes
on the con-leche side — `Arms/Shape.lean` declares `Refine/StateC.lean`'s
`CheckCM = StateT CState (Except CheckError)` plumbing `local`, so it does not
export, and this is the only form of it these proofs need. -/

/-- `(if c then G) >>= k` is the gate with `k` inlined into both arms. -/
private theorem gate_bind {α : Type} (c : Bool)
    (G : ConLeche.Cached.CheckCM PUnit) (k : ConLeche.Cached.CheckCM α) :
    ((if c = true then G else pure PUnit.unit) >>= fun _ => k)
      = if c = true then (G >>= fun _ => k) else k := by
  cases c <;> simp

/-- One step of a con-leche run: a `.run` that succeeded lets the bind through
to its continuation at the resulting state. -/
private theorem run_bind {α β : Type} (x : ConLeche.Cached.CheckCM α)
    (f : α → ConLeche.Cached.CheckCM β) {s s' : ConLeche.Cached.CState} {a : α}
    (h : x.run s = .ok (a, s')) : (x >>= f).run s = (f a).run s' := by
  simp only [StateT.run] at h ⊢
  simp [StateT.bind, Bind.bind, Except.bind, h]

/-- One step of a con-leche run that **threw**: the bind hands the error
straight on.  `run_bind`'s failure-half twin, the move every error arm below
makes through `ErrSim.trans` (task #67). -/
private theorem run_bind_err {α β : Type} (x : ConLeche.Cached.CheckCM α)
    (f : α → ConLeche.Cached.CheckCM β) {s : ConLeche.Cached.CState}
    {le : ConLeche.CheckError} (h : x.run s = .error le) :
    (x >>= f).run s = .error le := by
  simp only [StateT.run] at h ⊢
  simp [StateT.bind, Bind.bind, Except.bind, h]

/-- `throw` in `CheckCM`, applied to a state: the state is dropped and the
`Except` is the error.  The last step of every mirrored `throw` arm below
(task #67); `throw_bind_apply` is the same with the clause's continuation
still inlined behind it. -/
@[local simp] private theorem throw_apply {α : Type} (e : ConLeche.CheckError)
    (s : ConLeche.Cached.CState) :
    (throw e : ConLeche.Cached.CheckCM α) s = Except.error e := rfl

@[local simp] private theorem throw_bind_apply {α β : Type}
    (e : ConLeche.CheckError) (f : α → ConLeche.Cached.CheckCM β)
    (s : ConLeche.Cached.CState) :
    ((throw e : ConLeche.Cached.CheckCM α) >>= f) s = Except.error e := rfl

/-- `(unless b do throw err) >>= k` is the check with `k` inlined into both
arms. -/
private theorem check_bind {α : Type} (b : Bool) (err : ConLeche.CheckError)
    (k : ConLeche.Cached.CheckCM α) :
    ((if b = true then (pure PUnit.unit : ConLeche.Cached.CheckCM PUnit)
        else throw err) >>= fun _ => k)
      = if b = true then k
        else ((throw err : ConLeche.Cached.CheckCM PUnit) >>= fun _ => k) := by
  cases b <;> simp

/-- The `.lam` clause of `inferBodyIOI` *is* `inferLamIOI` — the two
identities above, at the codomain gate and at each of its two checks. -/
theorem inferBodyIOI_lam (mode : ConLeche.CheckMode)
    (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv) (depth : Nat)
    (ty body : ConLeche.Expr) (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.inferBodyIOI mode r fe depth (.lam ty body mb)
      = inferLamIOI mode r depth ty body mb := by
  simp only [ConLeche.Cached.inferBodyIOI, inferLamIOI, inferLamCodIOI]
  cases body.lamPw with
  | none => simp only [bind_assoc, check_bind, pure_bind]
  | some pwI => simp only [check_bind, pure_bind]

/-! ## The foreign callees -/

/-- The three helpers of *other* arms files that the io body calls, each
field the exact statement that helper's own `<fn>_refines` has.

* `inferBody` — `Arms/Infer.lean`'s `infer_body_i_refines` at the `io : Bool`
  flag (`knotV mode lfe fuel.val io` is Shape.lean's name for the record the
  flag selects);
* `inferSpineIO` — `Arms/InferSpineIO.lean`'s `infer_spine_io_i_refines`, the
  index-loop shape (the `acc` accumulator, the argument suffix
  `(absExprs args).drop i.val`);
* `ensureSort` — `Arms/Shared.lean`'s `ensure_sort_i_refines`. -/
structure InferIODeps (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  /-- `Arms/Infer.lean`'s `infer_body_i_refines` (`core_c.rs:3336`,
  `CoreC.lean:1293-1389 inferBodyI`).  Task #61: `infer_body_i` carries no
  grade flag any more, so this is `inferBodyI` at the knot itself; the views
  it is used for here make **no** recursive call, so the record is
  irrelevant at each of them (`inferBodyI_leaf` below). -/
  inferBody : ∀ (d : Std.U64) (e : expr.Expr), ExprWF e →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val (absExpr e))
  /-- `Arms/Infer.lean`'s `infer_proj_i_refines` at `io = true`
  (`core_c.rs:3581`, `CoreC.lean:1353-1381`).  Task #61: the `.proj` view is
  the one view `inferBodyIOI`'s fall-through reaches that *does* make a
  recursive call, and at `ioView` that call is the io slot, so
  `infer_body_io_i` spells the clause itself rather than handing it to
  `infer_body_i`. -/
  inferProj : ∀ (d : Std.U64) (sn : name.Name) (i : Std.U64) (pe : expr.Expr),
      NameWF sn → ExprWF pe →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_proj_i mode fuel st fe d sn i pe true)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode)
        (knot mode lfe fuel.val).ioView lfe d.val
        (.proj (absName sn) i.val (absExpr pe)))
  inferSpineIO : ∀ (d : Std.U64) (t : expr.Expr)
      (acc args : alloc.vec.Vec expr.Expr) (i : Std.Usize),
      ExprWF t → ExprsWF acc → ExprsWF args →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_spine_io_i mode fuel st fe d t acc args i)
      (fun lfe => ConLeche.Cached.inferSpineIOI (absMode mode)
        (knot mode lfe fuel.val).ioView lfe d.val (absExpr t)
        (absExprs acc).toArray ((absExprs args).drop i.val))
  ensureSort : ∀ (d : Std.U64) (e : expr.Expr), ExprWF e →
    Sim absLevel LevelWF
      (fun st fe => cached.core_c.ensure_sort_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.ensureSortI (knot mode lfe fuel.val) d.val
        (absExpr e))

/-! ## The views the fall-through delegates

`inferBodyIOI`'s `_` arm is `inferBodyI` on the record it was handed — the
knot's `ioView`.  At every view it reaches **except `.proj`**, `inferBodyI`'s
clause makes no recursive call at all, so the clause does not mention the
record and the io view and the knot itself give the same action.  These six
`rfl`s are what lets `InferIODeps.inferBody` be stated at the knot (task #61);
`.proj` is `InferIODeps.inferProj`. -/

private theorem inferBodyI_leaf_bvar (lmode : ConLeche.CheckMode)
    (r r' : ConLeche.Cached.CoreFnsI) (lfe : ConLeche.FEnv) (d i : Nat) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.bvar i)
      = ConLeche.Cached.inferBodyI lmode r' lfe d (.bvar i) := rfl

private theorem inferBodyI_leaf_fvar (lmode : ConLeche.CheckMode)
    (r r' : ConLeche.Cached.CoreFnsI) (lfe : ConLeche.FEnv) (d idx : Nat)
    (ty : ConLeche.Expr) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.fvar idx ty)
      = ConLeche.Cached.inferBodyI lmode r' lfe d (.fvar idx ty) := rfl

private theorem inferBodyI_leaf_sort (lmode : ConLeche.CheckMode)
    (r r' : ConLeche.Cached.CoreFnsI) (lfe : ConLeche.FEnv) (d : Nat)
    (u : ConLeche.Level) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.sort u)
      = ConLeche.Cached.inferBodyI lmode r' lfe d (.sort u) := rfl

private theorem inferBodyI_leaf_const (lmode : ConLeche.CheckMode)
    (r r' : ConLeche.Cached.CoreFnsI) (lfe : ConLeche.FEnv) (d : Nat)
    (n : ConLeche.Name) (us : List ConLeche.Level) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.const n us)
      = ConLeche.Cached.inferBodyI lmode r' lfe d (.const n us) := rfl

private theorem inferBodyI_leaf_lit (lmode : ConLeche.CheckMode)
    (r r' : ConLeche.Cached.CoreFnsI) (lfe : ConLeche.FEnv) (d : Nat)
    (l : ConLeche.Literal) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.lit l)
      = ConLeche.Cached.inferBodyI lmode r' lfe d (.lit l) := by
  cases l <;> rfl

private theorem inferBodyI_leaf_letE (lmode : ConLeche.CheckMode)
    (r r' : ConLeche.Cached.CoreFnsI) (lfe : ConLeche.FEnv) (d : Nat)
    (ty v b : ConLeche.Expr) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.letE ty v b)
      = ConLeche.Cached.inferBodyI lmode r' lfe d (.letE ty v b) := rfl

/-- The io view's `infer` slot is the io slot (the whole of the view). -/
private theorem ioView_infer (r : ConLeche.Cached.CoreFnsI) :
    r.ioView.infer = r.inferIO := rfl

/-- The io view's `whnf` slot is the record's. -/
private theorem ioView_whnf (r : ConLeche.Cached.CoreFnsI) :
    r.ioView.whnf = r.whnf := rfl

/-- `ensureSortI` reads the record only through its `whnf` slot, which the io
view does not change, so the `Arms/Shared.lean` statement is the io-lane one. -/
private theorem ensureSortI_ioView (r : ConLeche.Cached.CoreFnsI) (depth : Nat)
    (e : ConLeche.Expr) :
    ConLeche.Cached.ensureSortI r.ioView depth e
      = ConLeche.Cached.ensureSortI r depth e := rfl

/-- `expr_ops::lam_pw` answers `some` only at a `Lam` node, whose annotation is
well formed when the node is.  (A `Refine/ExprOpsMeta.lean` fact; kept local
until the arms are merged.) -/
private theorem lam_pw_wf {t : expr.Expr} (ht : ExprWF t)
    {pw : prop_when.PropWhen} (h : expr_ops.lam_pw t = ok (some pw)) :
    PropWhenWF pw := by
  cases ht with
  | @lam ty bo m e hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [expr_ops.lam_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨pw1, hpw1, ho⟩ := h
    rw [PropWhen.dup_eq hpw1] at ho
    have hp : pw = m.pw := by simpa using (Result.ok_injective ho).symm
    rw [hp]; exact hm
  | @bvar i e h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp [expr_ops.lam_pw] at h
  | @fvar idx ty e _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp [expr_ops.lam_pw] at h
  | @sort u e _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp [expr_ops.lam_pw] at h
  | @mk_const n us e _ _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp [expr_ops.lam_pw] at h
  | @app f a e _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp [expr_ops.lam_pw] at h
  | @forall_e ty bo m e _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; simp [expr_ops.lam_pw] at h
  | @let_e ty v bo e _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp [expr_ops.lam_pw] at h
  | @lit l e _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp [expr_ops.lam_pw] at h
  | @proj s i x e _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp [expr_ops.lam_pw] at h

/-! ## The monad plumbing

`CheckCM = StateT CState (Except CheckError)`: `Refine/StateC.lean`'s set,
which `Arms/Shape.lean` declares `local` and so does not export.  `Bind.bind`
is deliberately **not** in it — unfolding it would also unfold the Aeneas
`Result` bind and stop `bind_eq_ok_iff` from firing on the Rust side — so the
`simp` calls that finish a con-leche run name it themselves. -/

attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet StateT.bind Pure.pure StateT.pure Except.bind Except.pure

/-! ## The full outcome (task #67)

Three one-liners the error halves below share.  `invalid_err` and
`not_implemented_err` read the port's `Err` value off the smart constructor
that built it — `core_types::invalid`/`not_implemented` *are* the
constructors — so that `ErrSim.invalid`/`.notImplemented` can be applied at
the con-leche `throw` beside it.  `Sim.applyO` is `Sim` used at the *whole*
outcome, the form a clause that hands its callee's outcome straight back
wants: the caller's obligation is literally the callee's. -/

private theorem invalid_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v :=
  (Result.ok_injective (by rw [core_types.invalid] at h; exact h)).symm

private theorem not_implemented_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.not_implemented v = ok ce) :
    ce = .NotImplemented v :=
  (Result.ok_injective (by rw [core_types.not_implemented] at h; exact h)).symm

private theorem Sim.applyO {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : Sim A WF f g) {st fe o st' lst lfe} (hwf : StateWF st) (hfe : FEnvWF fe)
    (hok : f st fe = Aeneas.Std.Result.ok (o, st')) (hrel : StateRel st lst)
    (hfrel : FEnvRel fe lfe) : Out A WF o st' ((g lfe).run lst) :=
  h fe lfe hfe hfrel st o st' hwf hok lst hrel

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:1434-1445` — **`infer_lam_cod_io_i` refines
`inferBodyIOI`'s λ-codomain validation** (`core_c.rs:3723`): `expr_ops::lam_pw`
of the body picks the chain rule (`prop_when::beq` against the neighbour's
datum) or the leaf computation (`infer_io` then `ensure_sort_i` then the same
`beq`).  Unit-valued: on success there is nothing to abstract.

At the **full outcome** (task #67) it has four failures and every one is
mirrored: on the leaf route `infer_io` or `ensure_sort_i` threw, and
con-leche's own bind carries that error; on either route the `beq` guard
disagreed, and both sides `throw` at `notImplemented` — `M_CHAIN` against
`CoreC.lean:1438`, `M_LEAF` against `:1444`. -/
theorem infer_lam_cod_io_i_refines (hw : Wrappers mode fuel)
    (hd : InferIODeps mode fuel) (d : Std.U64) {body bt : expr.Expr}
    {mb : expr.BinderMeta} (hbody : ExprWF body) (hbt : ExprWF bt)
    (hmb : BinderMetaWF mb) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.infer_lam_cod_io_i mode fuel st fe d body mb bt)
      (fun lfe => inferLamCodIOI (knot mode lfe fuel.val).ioView d.val
        (absExpr body) (absBinderMeta mb) (absExpr bt)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.infer_lam_cod_io_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨op, ho, hok⟩ := hok
  have habs := ExprOps.lam_pw_refines ho
  cases op with
  | some pwI =>
    -- the chain rule: datum equality with the inner λ's own annotation
    simp only [Option.map_some] at habs
    simp only [arc_deref_eq, bind_tc_ok, bind_eq_ok_iff] at hok
    obtain ⟨b, hb, hok⟩ := hok
    have hbeq := PropWhen.beq_shape (PropWhen.wf_shape hmb)
      (PropWhen.wf_shape (lam_pw_wf hbody ho)) hb
    cases b with
    | true =>
      have hp := Result.ok_injective hok
      obtain rfl : o = .Ok () := (congrArg Prod.fst hp).symm
      obtain rfl : st' = st := (congrArg Prod.snd hp).symm
      refine ⟨lst, ?_, hrel, hwf, trivial⟩
      simp [inferLamCodIOI, ← habs, absBinderMeta, of_decide_eq_true hbeq.symm]
    | false =>
      -- the mirrored `throw`: `core_c.rs:3776` against `CoreC.lean:1438`
      obtain ⟨sl, -, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨cp, -, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
      have hp := Result.ok_injective hok
      obtain rfl : o = .Err ce := (congrArg Prod.fst hp).symm
      obtain rfl : st' = st := (congrArg Prod.snd hp).symm
      rw [not_implemented_err hce]
      refine Out.err (ErrSim.notImplemented
        (s := "sort-annotation mismatch (lam-cod-chain)") ?_)
      simp [inferLamCodIOI, ← habs, absBinderMeta, of_decide_eq_false hbeq.symm]
  | none =>
    -- the leaf: infer the body type's own type, then its sort
    simp only [Option.map_none] at habs
    simp only [bind_eq_ok_iff] at hok
    obtain ⟨i, hi, hok⟩ := hok
    obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
    have hiv : i.val = d.val + 1 := HashMap.uscalar_add_eq hi
    cases r0 with
    | Err err =>
      -- `infer_io` threw; con-leche's bind carries it
      obtain rfl : o = .Err err := (congrArg Prod.fst (Result.ok_injective hok)).symm
      have hIO := (hw.inferIOSim i hbt).apply_err hwf hfe h1 hrel hfrel
      rw [hiv] at hIO
      refine Out.err ?_
      simp only [inferLamCodIOI, ← habs, ioView_infer]
      exact ErrSim.bindCM hIO
    | Ok btt =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, hbttWF⟩ :=
        (hw.inferIOSim i hbt).apply hwf hfe h1 hrel hfrel
      obtain ⟨⟨r1, st2⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
      cases r1 with
      | Err err =>
        -- `ensure_sort_i` threw; likewise
        obtain rfl : o = .Err err := (congrArg Prod.fst (Result.ok_injective hok)).symm
        have hES := (hd.ensureSort i btt hbttWF).apply_err hwf1 hfe h2 hrel1 hfrel
        have hrun1' := hrun1
        rw [hiv] at hrun1' hES
        refine Out.err ?_
        simp only [inferLamCodIOI, ← habs, ioView_infer, ensureSortI_ioView]
        rw [run_bind _ _ hrun1']
        exact ErrSim.bindCM hES
      | Ok vb =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, hvbWF⟩ :=
          (hd.ensureSort i btt hbttWF).apply hwf1 hfe h2 hrel1 hfrel
        simp only [arc_deref_eq, bind_tc_ok] at hok
        obtain ⟨pw, hpw, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨hpwabs, hpwWF⟩ := ExprOps.zeroness_of_refines hvbWF pw hpw
        have hbeq := PropWhen.beq_shape (PropWhen.wf_shape hpwWF)
          (PropWhen.wf_shape hmb) hb
        simp only [hiv, StateT.run] at hrun1 hrun2
        cases b with
        | true =>
          have hp := Result.ok_injective hok
          obtain rfl : o = .Ok () := (congrArg Prod.fst hp).symm
          obtain rfl : st' = st2 := (congrArg Prod.snd hp).symm
          refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
          simp [inferLamCodIOI, ← habs, absBinderMeta, ioView_infer,
            ensureSortI_ioView, Bind.bind, hrun1, hrun2, ← hpwabs,
            of_decide_eq_true hbeq.symm]
        | false =>
          -- the mirrored `throw`: `core_c.rs:3789` against `CoreC.lean:1444`
          obtain ⟨sl, -, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨cp, -, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
          have hp := Result.ok_injective hok
          obtain rfl : o = .Err ce := (congrArg Prod.fst hp).symm
          obtain rfl : st' = st2 := (congrArg Prod.snd hp).symm
          rw [not_implemented_err hce]
          refine Out.err (ErrSim.notImplemented
            (s := "sort-annotation mismatch (lam-cod-leaf)") ?_)
          simp [inferLamCodIOI, ← habs, absBinderMeta, ioView_infer,
            ensureSortI_ioView, Bind.bind, hrun1, hrun2, ← hpwabs,
            of_decide_eq_false hbeq.symm]

/-- `ConLeche/Cached/CoreC.lean:1428-1447` — **`infer_lam_io_i` refines
`inferBodyIOI`'s `.lam` clause** (`core_c.rs:3684`).

It throws nothing of its own: at the full outcome (task #67) either
`infer_io` on the opened body threw, or the codomain validation did — and the
latter runs only at the verified modes, on both sides, which is what makes
the `b = false` case of the gate absurd rather than a deviation. -/
theorem infer_lam_io_i_refines (hw : Wrappers mode fuel)
    (hd : InferIODeps mode fuel) (d : Std.U64) {ty body : expr.Expr}
    {mb : expr.BinderMeta} (hty : ExprWF ty) (hbody : ExprWF body)
    (hmb : BinderMetaWF mb) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_lam_io_i mode fuel st fe d ty body mb)
      (fun lfe => inferLamIOI (absMode mode) (knot mode lfe fuel.val).ioView
        d.val (absExpr ty) (absExpr body) (absBinderMeta mb)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.infer_lam_io_i at hok
  obtain ⟨tyc, hdup, hok⟩ := bind_eq_ok_iff.mp hok
  rw [Expr.dup_eq hdup] at hok
  obtain ⟨fv, hfv, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨ob, hob, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
  have hiv : i.val = d.val + 1 := HashMap.uscalar_add_eq hi
  have hfvWF : ExprWF fv := ExprWF.fvar hty hfv
  rw [StateC.inst1_m_eq] at hob
  obtain ⟨hobabs, hobWF⟩ := ExprOpsC.instantiate1_refines hbody hfvWF hob
  rw [Expr.fvar_refines hfv] at hobabs
  cases r0 with
  | Err err =>
    -- `infer_io` on the opened body threw; con-leche's bind carries it
    obtain rfl : o = .Err err :=
      (congrArg Prod.fst (Result.ok_injective hok)).symm
    have hIO := (hw.inferIOSim i hobWF).apply_err hwf hfe h1 hrel hfrel
    rw [hiv] at hIO
    refine Out.err ?_
    simp only [show ((0#u64 : Std.U64)).val = 0 from rfl] at hobabs
    simp only [inferLamIOI, ConLeche.Cached.inst1M, ioView_infer, pure_bind,
      ← hobabs]
    exact ErrSim.bindCM hIO
  | Ok bt =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hbtWF⟩ :=
      (hw.inferIOSim i hobWF).apply hwf hfe h1 hrel hfrel
    obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
    have hbv := Env.verified_checks_refines hb
    obtain ⟨⟨st2, chk⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
    cases chk with
    | Err err =>
      -- the codomain validation threw — a gate only the verified modes run,
      -- so `b` is `true` and con-leche runs the same block
      obtain rfl : o = .Err err :=
        (congrArg Prod.fst (Result.ok_injective hok)).symm
      cases b with
      | false => simp at h2
      | true =>
        obtain ⟨⟨chk1, st3⟩, h3, h2⟩ := bind_eq_ok_iff.mp h2
        obtain rfl : chk1 = .Err err := congrArg Prod.snd (Result.ok_injective h2)
        have hcod := (infer_lam_cod_io_i_refines hw hd d hbody hbtWF hmb).apply_err
          hwf1 hfe h3 hrel1 hfrel
        have hrun1' := hrun1
        rw [hiv] at hrun1'
        refine Out.err ?_
        simp only [show ((0#u64 : Std.U64)).val = 0 from rfl] at hobabs
        simp only [inferLamIOI, ConLeche.Cached.inst1M,
          ConLeche.Cached.abstract1M, ioView_infer, pure_bind, ← hobabs]
        rw [run_bind _ _ hrun1', ← hbv]
        exact ErrSim.bindCM hcod
    | Ok u =>
      -- the codomain gate: run it at the verified modes, skip it otherwise
      have key : ∃ lst2, StateRel st2 lst2 ∧ StateWF st2 ∧
          (if (absMode mode).verifiedChecks = true then
              inferLamCodIOI (knot mode lfe fuel.val).ioView d.val (absExpr body)
                (absBinderMeta mb) (absExpr bt)
            else pure ()).run lst1 = Except.ok ((), lst2) := by
        cases b with
        | false =>
          have hst : st2 = st1 := (congrArg Prod.fst (Result.ok_injective h2)).symm
          subst hst
          exact ⟨lst1, hrel1, hwf1, by simp [← hbv]⟩
        | true =>
          obtain ⟨⟨chk1, st3⟩, h3, h2⟩ := bind_eq_ok_iff.mp h2
          have hst : st2 = st3 := (congrArg Prod.fst (Result.ok_injective h2)).symm
          have hchk : chk1 = .Ok u := (congrArg Prod.snd (Result.ok_injective h2))
          subst hst; subst hchk
          obtain ⟨lst2, hrun, hrel2, hwf2, -⟩ :=
            (infer_lam_cod_io_i_refines hw hd d hbody hbtWF hmb).apply hwf1 hfe h3
              hrel1 hfrel
          refine ⟨lst2, hrel2, hwf2, ?_⟩
          simp only [StateT.run] at hrun
          simpa [← hbv] using hrun
      obtain ⟨lst2, hrel2, hwf2, hgate⟩ := key
      obtain ⟨e1, he1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨bm, hbm, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨e2, he2, hok⟩ := bind_eq_ok_iff.mp hok
      have hpair := Result.ok_injective hok
      obtain rfl : o = .Ok e2 := (congrArg Prod.fst hpair).symm
      have hst' : st' = st2 := (congrArg Prod.snd hpair).symm
      subst hst'
      rw [StateC.abstract1_m_eq] at he1
      obtain ⟨he1abs, he1WF⟩ := ExprOpsC.abstract1_refines hbtWF he1
      rw [Expr.binder_meta_dup_eq hbm] at he2
      have hrabs : absExpr e2
          = .forallE (absExpr ty) (absExpr e1) (absBinderMeta mb) :=
        Expr.forall_e_refines he2
      refine ⟨lst2, ?_, hrel2, hwf2, Expr.forall_e_wf hty he1WF hmb he2⟩
      simp only [hiv] at hrun1
      simp only [show ((0#u64 : Std.U64)).val = 0 from rfl] at hobabs he1abs
      simp only [inferLamIOI, ConLeche.Cached.inst1M, ConLeche.Cached.abstract1M,
        ioView_infer, pure_bind, ← hobabs]
      rw [run_bind _ _ hrun1, ← gate_bind, run_bind _ _ hgate]
      simp [StateT.run, StateT.pure, ← he1abs, hrabs]

/-- `ConLeche/Cached/CoreC.lean:1407-1426` — **`infer_forall_io_i` refines
`inferBodyIOI`'s `.forallE` clause** (`core_c.rs:3622`).

Six failures at the full outcome (task #67), all mirrored: the four
sub-computations (`infer_io`, `whnf`, `infer_io`, `ensure_sort_i`) throw
through con-leche's own binds; a reduced domain type that is not a `Sort` is
`invalid` on both sides (the `M` arm); and a codomain annotation mismatch is
`notImplemented` on both (the `M_COD` arm, at the verified modes only). -/
theorem infer_forall_io_i_refines (hw : Wrappers mode fuel)
    (hd : InferIODeps mode fuel) (d : Std.U64) {ty body : expr.Expr}
    {mb : expr.BinderMeta} (hty : ExprWF ty) (hbody : ExprWF body)
    (hmb : BinderMetaWF mb) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_forall_io_i mode fuel st fe d ty body mb)
      (fun lfe => inferForallIOI (absMode mode) (knot mode lfe fuel.val).ioView
        d.val (absExpr ty) (absExpr body) (absBinderMeta mb)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.infer_forall_io_i at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
  cases r0 with
  | Err err =>
    -- `infer_io` on the domain threw; con-leche's bind carries it
    obtain rfl : o = .Err err :=
      (congrArg Prod.fst (Result.ok_injective hok)).symm
    refine Out.err ?_
    simp only [inferForallIOI, ioView_infer, ioView_whnf]
    exact ErrSim.bindCM ((hw.inferIOSim d hty).apply_err hwf hfe h1 hrel hfrel)
  | Ok tty =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, httyWF⟩ :=
      (hw.inferIOSim d hty).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
    cases r1 with
    | Err err =>
      -- `whnf` of the domain's type threw
      obtain rfl : o = .Err err :=
        (congrArg Prod.fst (Result.ok_injective hok)).symm
      refine Out.err ?_
      simp only [inferForallIOI, ioView_infer, ioView_whnf]
      rw [run_bind _ _ hrun1]
      exact ErrSim.bindCM ((hw.whnfSim d httyWF).apply_err hwf1 hfe h2 hrel1 hfrel)
    | Ok wtty =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwttyWF⟩ :=
        (hw.whnfSim d httyWF).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨⟨dw, kd⟩⟩ := wtty
      simp only [arc_deref_eq, bind_tc_ok] at hok
      cases kd with
      | «Sort» u =>
        have huWF : LevelWF u := CoreK.wf_sort_inv hwttyWF rfl
        obtain ⟨u1, hu1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [level_dup_eq, Result.ok.injEq] at hu1
        rw [← hu1] at hok
        obtain ⟨tyc, hdup, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hdup] at hok
        obtain ⟨fv, hfv, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ob, hob, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨⟨r2, st3⟩, h3, hok⟩ := bind_eq_ok_iff.mp hok
        have hiv : i.val = d.val + 1 := HashMap.uscalar_add_eq hi
        have hfvWF : ExprWF fv := ExprWF.fvar hty hfv
        rw [StateC.inst1_m_eq] at hob
        obtain ⟨hobabs, hobWF⟩ := ExprOpsC.instantiate1_refines hbody hfvWF hob
        rw [Expr.fvar_refines hfv] at hobabs
        cases r2 with
        | Err err =>
          -- `infer_io` on the opened body threw
          obtain rfl : o = .Err err :=
            (congrArg Prod.fst (Result.ok_injective hok)).symm
          have hIO := (hw.inferIOSim i hobWF).apply_err hwf2 hfe h3 hrel2 hfrel
          rw [hiv] at hIO
          refine Out.err ?_
          simp only [show ((0#u64 : Std.U64)).val = 0 from rfl] at hobabs
          simp only [inferForallIOI, ConLeche.Cached.inst1M, ioView_infer,
            ioView_whnf, pure_bind, ← hobabs]
          rw [run_bind _ _ hrun1, run_bind _ _ hrun2]
          simp only [absExpr_mk, absExprKind]
          exact ErrSim.bindCM hIO
        | Ok bt =>
          obtain ⟨lst3, hrun3, hrel3, hwf3, hbtWF⟩ :=
            (hw.inferIOSim i hobWF).apply hwf2 hfe h3 hrel2 hfrel
          obtain ⟨⟨r3, st4⟩, h4, hok⟩ := bind_eq_ok_iff.mp hok
          cases r3 with
          | Err err =>
            -- `ensure_sort_i` on the codomain's type threw
            obtain rfl : o = .Err err :=
              (congrArg Prod.fst (Result.ok_injective hok)).symm
            have hES := (hd.ensureSort i bt hbtWF).apply_err hwf3 hfe h4 hrel3 hfrel
            have hrun3' := hrun3
            rw [hiv] at hrun3' hES
            refine Out.err ?_
            simp only [show ((0#u64 : Std.U64)).val = 0 from rfl] at hobabs
            simp only [inferForallIOI, ConLeche.Cached.inst1M, ioView_infer,
              ioView_whnf, pure_bind, ← hobabs]
            rw [run_bind _ _ hrun1, run_bind _ _ hrun2]
            simp only [absExpr_mk, absExprKind]
            rw [run_bind _ _ hrun3', ensureSortI_ioView]
            exact ErrSim.bindCM hES
          | Ok v =>
            obtain ⟨lst4, hrun4, hrel4, hwf4, hvWF⟩ :=
              (hd.ensureSort i bt hbtWF).apply hwf3 hfe h4 hrel3 hfrel
            obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
            have hbv := Env.verified_checks_refines hb
            -- the shared leaf: `.sort (.imax u v)`, whichever way the gate went
            have hK : ∀ stx : cached.state_c.CState,
                (do let l ← kernel.level.imax u v
                    let e1 ← kernel.expr.sort l
                    ok ((core.result.Result.Ok e1 :
                      core.result.Result expr.Expr core_types.CheckError), stx))
                  = ok (o, st') →
                ∃ rr, o = .Ok rr
                  ∧ absExpr rr = .sort (.imax (absLevel u) (absLevel v))
                  ∧ ExprWF rr ∧ st' = stx := by
              intro stx h
              obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
              have hp := Result.ok_injective h
              refine ⟨e1, (congrArg Prod.fst hp).symm, ?_, ?_,
                (congrArg Prod.snd hp).symm⟩
              · rw [Expr.sort_refines he1, Level.imax_refines hl]
              · exact Expr.sort_wf (LevelWF.imax huWF hvWF hl) he1
            simp only [hiv] at hrun3 hrun4
            simp only [show ((0#u64 : Std.U64)).val = 0 from rfl] at hobabs
            cases b with
            | false =>
              -- the unverified modes skip the codomain check, on both sides
              obtain ⟨rr, rfl, hrabs, hrWF, rfl⟩ := hK st4 hok
              refine Out.ok (lst' := lst4) ?_ hrel4 hwf4 hrWF
              simp only [inferForallIOI, ConLeche.Cached.inst1M, ioView_infer,
                ioView_whnf, pure_bind, ← hobabs]
              rw [run_bind _ _ hrun1, run_bind _ _ hrun2]
              simp only [absExpr_mk, absExprKind]
              rw [run_bind _ _ hrun3, ensureSortI_ioView, run_bind _ _ hrun4]
              simp [StateT.run, StateT.pure, hrabs, ← hbv]
            | true =>
              obtain ⟨pw, hpw, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨hpwabs, hpwWF⟩ := ExprOps.zeroness_of_refines hvWF pw hpw
              have hbeq := PropWhen.beq_shape (PropWhen.wf_shape hpwWF)
                (PropWhen.wf_shape hmb) hb1
              cases b1 with
              | true =>
                obtain ⟨rr, rfl, hrabs, hrWF, rfl⟩ := hK st4 hok
                refine Out.ok (lst' := lst4) ?_ hrel4 hwf4 hrWF
                simp only [inferForallIOI, ConLeche.Cached.inst1M, ioView_infer,
                  ioView_whnf, pure_bind, ← hobabs]
                rw [run_bind _ _ hrun1, run_bind _ _ hrun2]
                simp only [absExpr_mk, absExprKind]
                rw [run_bind _ _ hrun3, ensureSortI_ioView, run_bind _ _ hrun4]
                simp [StateT.run, StateT.pure, hrabs, ← hbv, ← hpwabs,
                  of_decide_eq_true hbeq.symm]
              | false =>
                -- the mirrored `throw`: `core_c.rs:3688` against
                -- `CoreC.lean:1424`
                obtain ⟨sl, -, hok⟩ := bind_eq_ok_iff.mp hok
                obtain ⟨cp, -, hok⟩ := bind_eq_ok_iff.mp hok
                obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
                have hp := Result.ok_injective hok
                obtain rfl : o = .Err ce := (congrArg Prod.fst hp).symm
                obtain rfl : st' = st4 := (congrArg Prod.snd hp).symm
                rw [not_implemented_err hce]
                refine Out.err (ErrSim.notImplemented
                  (s := "sort-annotation mismatch (forall-cod)") ?_)
                simp only [inferForallIOI, ConLeche.Cached.inst1M, ioView_infer,
                  ioView_whnf, pure_bind, ← hobabs]
                rw [run_bind _ _ hrun1, run_bind _ _ hrun2]
                simp only [absExpr_mk, absExprKind]
                rw [run_bind _ _ hrun3, ensureSortI_ioView, run_bind _ _ hrun4]
                simp [StateT.run, ← hbv, ← hpwabs,
                  of_decide_eq_false hbeq.symm]
      | _ =>
        -- the reduced domain type was not a `Sort`: the mirrored `throw` at
        -- `core_c.rs:3699` against `CoreC.lean:1427`
        obtain ⟨sl, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨cp, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
        have hp := Result.ok_injective hok
        obtain rfl : o = .Err ce := (congrArg Prod.fst hp).symm
        obtain rfl : st' = st2 := (congrArg Prod.snd hp).symm
        rw [invalid_err hce]
        refine Out.err (ErrSim.invalid (s := "expected a sort") ?_)
        simp only [inferForallIOI, ioView_infer, ioView_whnf]
        rw [run_bind _ _ hrun1, run_bind _ _ hrun2]
        simp [absExpr_mk, absExprKind, StateT.run]

/-- `ConLeche/Cached/CoreC.lean:1399` — **`infer_body_io_i` refines
`inferBodyIOI`** (`core_c.rs:3588`), the `infer_io` body: the three io clauses
above, and every other node view handed to `inferBodyI` at the io view (the
Rust `infer_body_i … true`).

Every failure here is a callee's, so the proof never names an error of its
own: the six delegated views and `.proj` hand their callee's *whole* outcome
back unchanged (`Sim.applyO`), `.lam` and `.forallE` hand back their clause's,
and `.app` is `infer_io`'s or `inferSpineIOI`'s. -/
theorem infer_body_io_i_refines (hw : Wrappers mode fuel)
    (hd : InferIODeps mode fuel) (d : Std.U64) {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_body_io_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.inferBodyIOI (absMode mode)
        (knot mode lfe fuel.val).ioView lfe d.val (absExpr e)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.infer_body_io_i at hok
  cases he with
  | @bvar i e0 h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.bvar_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    have h := (hd.inferBody d _ (ExprWF.bvar h1)).applyO hwf hfe hok hrel hfrel
    simpa [ConLeche.Cached.inferBodyIOI,
      inferBodyI_leaf_bvar _ (knot mode lfe fuel.val) (knot mode lfe fuel.val).ioView] using h
  | @fvar idx tyf e0 htyf h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.fvar_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    have h := (hd.inferBody d _ (ExprWF.fvar htyf h1)).applyO hwf hfe hok hrel hfrel
    simpa [ConLeche.Cached.inferBodyIOI,
      inferBodyI_leaf_fvar _ (knot mode lfe fuel.val) (knot mode lfe fuel.val).ioView] using h
  | @sort u e0 hu h1 =>
    obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    have h := (hd.inferBody d _ (ExprWF.sort hu h1)).applyO hwf hfe hok hrel hfrel
    simpa [ConLeche.Cached.inferBodyIOI,
      inferBodyI_leaf_sort _ (knot mode lfe fuel.val) (knot mode lfe fuel.val).ioView] using h
  | @mk_const n us e0 hn hus h1 =>
    obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    have h := (hd.inferBody d _ (ExprWF.mk_const hn hus h1)).applyO hwf hfe hok
      hrel hfrel
    simpa [ConLeche.Cached.inferBodyIOI,
      inferBodyI_leaf_const _ (knot mode lfe fuel.val) (knot mode lfe fuel.val).ioView] using h
  | @let_e tyl vl bl e0 htyl hvl hbl h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.let_e_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    have h := (hd.inferBody d _ (ExprWF.let_e htyl hvl hbl h1)).applyO hwf hfe hok
      hrel hfrel
    simpa [ConLeche.Cached.inferBodyIOI,
      inferBodyI_leaf_letE _ (knot mode lfe fuel.val) (knot mode lfe fuel.val).ioView] using h
  | @lit l e0 hl h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.lit_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    have h := (hd.inferBody d _ (ExprWF.lit hl h1)).applyO hwf hfe hok hrel hfrel
    simpa [ConLeche.Cached.inferBodyIOI,
      inferBodyI_leaf_lit _ (knot mode lfe fuel.val) (knot mode lfe fuel.val).ioView] using h
  | @proj sn idx x e0 hsn hx h1 =>
    -- task #61: the one delegated view with a recursive call, and at `ioView`
    -- that call is the io slot, so the Rust spells the clause here
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.proj_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    have h := (hd.inferProj d sn idx x hsn hx).applyO hwf hfe hok hrel hfrel
    simpa [ConLeche.Cached.inferBodyIOI] using h
  | @lam tyl bo m e0 htyl hbo hm h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    have h := (infer_lam_io_i_refines hw hd d htyl hbo hm).applyO hwf hfe hok hrel hfrel
    simpa [inferBodyIOI_lam] using h
  | @forall_e tyf bo m e0 htyf hbo hm h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    have h := (infer_forall_io_i_refines hw hd d htyf hbo hm).applyO hwf hfe hok hrel hfrel
    simpa [inferBodyIOI_forallE] using h
  | @app f a e0 hf ha h1 =>
    -- the one io-graded clause: the spine walk is `inferSpineIOI`
    have heWF := ExprWF.app hf ha h1
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [arc_deref_eq, bind_tc_ok] at hok
    obtain ⟨hh, hhok, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨args, hargs, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨⟨r0, st1⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨hhabs, hhWF⟩ := ExprOps.get_app_fn_refines heWF hhok
    obtain ⟨hargsabs, hargsWF⟩ := ExprOps.get_app_args_refines heWF hargs
    simp only [absExpr_mk, absExprKind] at hhabs hargsabs
    cases r0 with
    | Err err =>
      -- `infer_io` on the head threw; con-leche's bind carries it
      obtain rfl : o = .Err err :=
        (congrArg Prod.fst (Result.ok_injective hok)).symm
      refine Out.err ?_
      simp only [ConLeche.Cached.inferBodyIOI, absExpr_mk, absExprKind,
        ConLeche.Cached.ExprC.getAppFn_spec, ConLeche.Cached.ExprC.getAppArgs_spec,
        ioView_infer, pure_bind, ← hhabs, ← hargsabs]
      exact ErrSim.bindCM ((hw.inferIOSim d hhWF).apply_err hwf hfe h2 hrel hfrel)
    | Ok tf =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, htfWF⟩ :=
        (hw.inferIOSim d hhWF).apply hwf hfe h2 hrel hfrel
      have hsp := hd.inferSpineIO d tf (alloc.vec.Vec.new expr.Expr) args 0#usize
        htfWF ExprOps.exprsWF_new hargsWF
      cases o with
      | Ok r =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, hrWF⟩ :=
          hsp.apply hwf1 hfe hok hrel1 hfrel
        refine Out.ok (lst' := lst2) ?_ hrel2 hwf2 hrWF
        simp only [ConLeche.Cached.inferBodyIOI, absExpr_mk, absExprKind,
          ConLeche.Cached.ExprC.getAppFn_spec, ConLeche.Cached.ExprC.getAppArgs_spec,
          ioView_infer, pure_bind, ← hhabs, ← hargsabs]
        rw [run_bind _ _ hrun1]
        simpa [absExprs, alloc.vec.Vec.new] using hrun2
      | Err ce =>
        -- the spine walk threw; likewise
        refine Out.err (ErrSim.trans (hsp.apply_err hwf1 hfe hok hrel1 hfrel) ?_)
        intro le hle
        simp only [ConLeche.Cached.inferBodyIOI, absExpr_mk, absExprKind,
          ConLeche.Cached.ExprC.getAppFn_spec, ConLeche.Cached.ExprC.getAppArgs_spec,
          ioView_infer, pure_bind, ← hhabs, ← hargsabs]
        rw [run_bind _ _ hrun1]
        simpa [absExprs, alloc.vec.Vec.new] using hle

end

end ConRon.Refine.Core
