/-
# `infer_spine_i`, the application-inference spine loop (task #55, one arm)

`crates/con-ron-core/src/cached/core_c.rs:2667`'s `infer_spine_i` against
con-leche's `inferSpineI` (`ConLeche/Cached/CoreC.lean:1018-1042`): walk the
raw Π-telescope against the argument list with *deferred* substitution.

Three things carry the correspondence.

* **The argument list.**  con-leche recurses on `List Expr`; the Rust walks
  `args : Vec Expr` by an index `i : Usize`.  The remaining arguments are
  `(absExprs args).drop i.val`, and the induction is a strong induction on
  `args.val.length - i.val` — `i` only ever grows by one, and only while
  `i < args.len()`.
* **The accumulator.**  con-leche's deferred-substitution list is an
  `Array Expr` pushed at the end (`acc.push a`); the Rust's is a `Vec Expr`
  pushed at the end too, so the two agree *elementwise*:
  `(absExprs acc).toArray` is con-leche's `acc`.  The reversal the two share
  is the one *inside* the consumer: `instListRevM e acc` is
  `Expr.instantiateList e acc.toList.reverse`, which is exactly what
  `cached::state_c::inst_list_rev_m` = `expr_ops_c::instantiate_rev` refines
  to (`Refine/ExprOpsCSubst.lean`).  So no orientation flip is needed at the
  boundary — what is reversed is the *consumption* of the accumulator, not
  the accumulator; the Rust `Vec` and the con-leche `Array` both hold the
  arguments in application order.
* **The three knot calls** — `r.infer`, `r.defeq`, `r.whnf` — come from
  `Wrappers mode fuel` (`Arms/Shape.lean`).

The arm is stated at the **full outcome** (task #67, DESIGN.md §3's ruling of
2026-09-13): the accept direction as before, and on a failure con-leche's own
`throw` at the same kind.  All of `infer_spine_i`'s ten `Err` exits are
mirrored — seven carry a sub-call's error (`r.infer`, `r.defeq`, `r.whnf`) and
three are its own `throw`s: `core_c.rs:2714` and `:2740` against
`CoreC.lean:1031` and `:1040`, and `core_c.rs:2755` against `CoreC.lean:1042`.

The two `.M`-suffixed `Array Std.U32` constants (`infer_spine_i.M_FN`,
`.M_MISMATCH`) are those messages' code points, and still carry no theorem:
messages are never compared (DESIGN.md §3.1), so the failure half only has to
name the string con-leche throws.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKSupport
import ConRon.Refine.ExprOpsCSubst

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! Shape.lean's monad plumbing is declared `local`, so it is re-activated
here. -/
attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-- The local `Bind.bind` unfolding above hides `Refine/Abs.lean`'s
`bind_eq_ok_iff` from `simp`; this is the same fact at the unfolded head. -/
@[local simp] theorem std_bind_eq_ok_iff {α β : Type} {e : Result α}
    {f : α → Result β} {v : β} :
    (Aeneas.Std.bind e f = ok v) ↔ ∃ y, e = ok y ∧ f y = ok v := bind_eq_ok_iff

/-- `throw` in `CheckCM = StateT CState (Except CheckError)` discards the
state, which is what a mirrored `throw` arm needs (task #67).  The plumbing
set above unfolds `StateT.run`, so this is stated at the applied form. -/
@[local simp] theorem checkCM_throw_apply {α : Type} (e : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw e : ConLeche.Cached.CheckCM α) lst = .error e := rfl

/-! ## `inst_list_rev_m`, the deferred substitution

`cached::state_c::inst_list_rev_m e acc 0` *is* `expr_ops_c::instantiate_rev`
(`Refine/StateC.lean`'s `inst_list_rev_m_eq`), which refines
`Expr.instantiateRev`, which is con-leche's `instListRevM`'s whole body;
`instantiateRev_spec` is the reversal. -/

private theorem instListRevM_run {e r : expr.Expr} {acc : alloc.vec.Vec expr.Expr}
    (he : ExprWF e) (hacc : ExprsWF acc)
    (h : cached.state_c.inst_list_rev_m e acc 0#u64 = ok r) :
    ∀ lst, (ConLeche.Cached.instListRevM (absExpr e) (absExprs acc).toArray).run lst
        = .ok (absExpr r, lst) := by
  intro lst
  rw [ConRon.Refine.StateC.inst_list_rev_m_eq] at h
  obtain ⟨hr, -⟩ := ConRon.Refine.ExprOpsC.instantiate_rev_refines he hacc h
  simp [ConLeche.Cached.instListRevM, ConLeche.Expr.instantiateRev_spec, hr]

private theorem instListRevM_wf {e r : expr.Expr} {acc : alloc.vec.Vec expr.Expr}
    (he : ExprWF e) (hacc : ExprsWF acc)
    (h : cached.state_c.inst_list_rev_m e acc 0#u64 = ok r) : ExprWF r := by
  rw [ConRon.Refine.StateC.inst_list_rev_m_eq] at h
  exact (ConRon.Refine.ExprOpsC.instantiate_rev_refines he hacc h).2

/-! ## The two `inferSpineI` clauses as `run` equations

`inferSpineI.eq_2` is the syntactic ∀ step, `inferSpineI.eq_3` the
substitute-and-normalize step (its side condition is exactly "the head is not
a `.forallE`").  Each is stated here as the one-step `run` equation the arm
needs: given the sub-calls' runs, the whole call is the recursive call at the
state the certificate left behind. -/

/-- The syntactic telescope step (`CoreC.lean:1023-1032`): the argument's
certificate against the *domain* substituted under the deferred list, then
the walk continues into the codomain with the argument pushed. -/
private theorem inferSpineI_pi_run {fns : ConLeche.Cached.CoreFnsI}
    {lfe : ConLeche.FEnv} {depth : Nat} {dom body dom' ta : ConLeche.Expr}
    {mt : ConLeche.BinderMeta} {accArr : _root_.Array ConLeche.Expr}
    {a : ConLeche.Expr} {rest : List ConLeche.Expr}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (h1 : (ConLeche.Cached.instListRevM dom accArr).run lst = .ok (dom', lst))
    (h2 : (fns.infer depth a).run lst = .ok (ta, lst1))
    (h3 : (fns.defeq depth ta dom').run lst1 = .ok (true, lst2)) :
    (ConLeche.Cached.inferSpineI fns lfe depth (.forallE dom body mt) accArr
        (a :: rest)).run lst
      = (ConLeche.Cached.inferSpineI fns lfe depth body (accArr.push a) rest).run lst2 := by
  rw [ConLeche.Cached.inferSpineI.eq_2]
  simp only [StateT.run] at h1 h2 h3 ⊢
  simp [h1, h2, h3]

/-- The non-syntactic telescope step (`CoreC.lean:1033-1042`): substitute the
deferred list into the head, normalize, and require a `.forallE`; the walk
continues with a *fresh* one-element accumulator. -/
private theorem inferSpineI_nonpi_run {fns : ConLeche.Cached.CoreFnsI}
    {lfe : ConLeche.FEnv} {depth : Nat} {lty ty' w dom body ta : ConLeche.Expr}
    {mt : ConLeche.BinderMeta} {accArr : _root_.Array ConLeche.Expr}
    {a : ConLeche.Expr} {rest : List ConLeche.Expr}
    {lst lst1 lst2 lst3 : ConLeche.Cached.CState}
    (hnp : ∀ dom body m, lty = ConLeche.Expr.forallE dom body m → False)
    (h1 : (ConLeche.Cached.instListRevM lty accArr).run lst = .ok (ty', lst))
    (h2 : (fns.whnf depth ty').run lst = .ok (w, lst1))
    (hwf : w = ConLeche.Expr.forallE dom body mt)
    (h3 : (fns.infer depth a).run lst1 = .ok (ta, lst2))
    (h4 : (fns.defeq depth ta dom).run lst2 = .ok (true, lst3)) :
    (ConLeche.Cached.inferSpineI fns lfe depth lty accArr (a :: rest)).run lst
      = (ConLeche.Cached.inferSpineI fns lfe depth body #[a] rest).run lst3 := by
  rw [ConLeche.Cached.inferSpineI.eq_3 _ _ _ _ _ _ _ hnp]
  subst hwf
  simp only [StateT.run] at h1 h2 h3 h4 ⊢
  simp [h1, h2, h3, h4]

/-! ### The same two clauses at a `throw`

Task #67 (DESIGN.md §3's ruling of 2026-09-13) states the arm over the **full**
outcome, so every point at which the Rust returns an `Err` is a point at which
con-leche's `do` block ends `.error`.  These are those equations: three per
clause carrying a sub-call's own error (`r.infer`, `r.defeq`, `r.whnf`), and
two for the explicit `throw`s — `core_c.rs:2714` and `:2740` against
`CoreC.lean:1031` and `:1040` (`"application type mismatch"`), and
`core_c.rs:2755` against `CoreC.lean:1042` (`"function expected"`).  All three
`throw`s are mirrored; messages are never compared, so the two `.M`-suffixed
code-point constants still carry no theorem of their own. -/

section ErrRun

variable {fns : ConLeche.Cached.CoreFnsI} {lfe : ConLeche.FEnv} {depth : Nat}
  {lty ty' dom body dom' w ta : ConLeche.Expr} {mt : ConLeche.BinderMeta}
  {accArr : _root_.Array ConLeche.Expr} {a : ConLeche.Expr}
  {rest : List ConLeche.Expr} {lst lst1 lst2 lst3 : ConLeche.Cached.CState}
  {le : ConLeche.CheckError}

/-- Syntactic step, the argument's inference throwing (`CoreC.lean:1029`). -/
private theorem inferSpineI_pi_run_infer_err
    (h1 : (ConLeche.Cached.instListRevM dom accArr).run lst = .ok (dom', lst))
    (h2 : (fns.infer depth a).run lst = .error le) :
    (ConLeche.Cached.inferSpineI fns lfe depth (.forallE dom body mt) accArr
        (a :: rest)).run lst = .error le := by
  rw [ConLeche.Cached.inferSpineI.eq_2]
  simp only [StateT.run] at h1 h2 ⊢
  simp [h1, h2]

/-- Syntactic step, the domain comparison throwing (`CoreC.lean:1030`). -/
private theorem inferSpineI_pi_run_defeq_err
    (h1 : (ConLeche.Cached.instListRevM dom accArr).run lst = .ok (dom', lst))
    (h2 : (fns.infer depth a).run lst = .ok (ta, lst1))
    (h3 : (fns.defeq depth ta dom').run lst1 = .error le) :
    (ConLeche.Cached.inferSpineI fns lfe depth (.forallE dom body mt) accArr
        (a :: rest)).run lst = .error le := by
  rw [ConLeche.Cached.inferSpineI.eq_2]
  simp only [StateT.run] at h1 h2 h3 ⊢
  simp [h1, h2, h3]

/-- Syntactic step, the comparison *failing* — the mirrored `throw`
(`core_c.rs:2714` ← `CoreC.lean:1031`). -/
private theorem inferSpineI_pi_run_mismatch
    (h1 : (ConLeche.Cached.instListRevM dom accArr).run lst = .ok (dom', lst))
    (h2 : (fns.infer depth a).run lst = .ok (ta, lst1))
    (h3 : (fns.defeq depth ta dom').run lst1 = .ok (false, lst2)) :
    (ConLeche.Cached.inferSpineI fns lfe depth (.forallE dom body mt) accArr
        (a :: rest)).run lst = .error (.invalid "application type mismatch") := by
  rw [ConLeche.Cached.inferSpineI.eq_2]
  simp only [StateT.run] at h1 h2 h3 ⊢
  simp [h1, h2, h3]

/-- The whnf step, the normalization throwing (`CoreC.lean:1035`). -/
private theorem inferSpineI_nonpi_run_whnf_err
    (hnp : ∀ dom body m, lty = ConLeche.Expr.forallE dom body m → False)
    (h1 : (ConLeche.Cached.instListRevM lty accArr).run lst = .ok (ty', lst))
    (h2 : (fns.whnf depth ty').run lst = .error le) :
    (ConLeche.Cached.inferSpineI fns lfe depth lty accArr (a :: rest)).run lst
      = .error le := by
  rw [ConLeche.Cached.inferSpineI.eq_3 _ _ _ _ _ _ _ hnp]
  simp only [StateT.run] at h1 h2 ⊢
  simp [h1, h2]

/-- The whnf step, the normal form *not* a Π — the mirrored `throw`
(`core_c.rs:2755` ← `CoreC.lean:1042`). -/
private theorem inferSpineI_nonpi_run_fn
    (hnp : ∀ dom body m, lty = ConLeche.Expr.forallE dom body m → False)
    (h1 : (ConLeche.Cached.instListRevM lty accArr).run lst = .ok (ty', lst))
    (h2 : (fns.whnf depth ty').run lst = .ok (w, lst1))
    (hnw : ∀ dom body m, w = ConLeche.Expr.forallE dom body m → False) :
    (ConLeche.Cached.inferSpineI fns lfe depth lty accArr (a :: rest)).run lst
      = .error (.invalid "function expected") := by
  rw [ConLeche.Cached.inferSpineI.eq_3 _ _ _ _ _ _ _ hnp]
  simp only [StateT.run] at h1 h2 ⊢
  cases w
  case forallE dm bd m => exact absurd rfl (hnw dm bd m)
  all_goals simp [h1, h2]

/-- The whnf step, the argument's inference throwing (`CoreC.lean:1038`). -/
private theorem inferSpineI_nonpi_run_infer_err
    (hnp : ∀ dom body m, lty = ConLeche.Expr.forallE dom body m → False)
    (h1 : (ConLeche.Cached.instListRevM lty accArr).run lst = .ok (ty', lst))
    (h2 : (fns.whnf depth ty').run lst = .ok (w, lst1))
    (hwf : w = ConLeche.Expr.forallE dom body mt)
    (h3 : (fns.infer depth a).run lst1 = .error le) :
    (ConLeche.Cached.inferSpineI fns lfe depth lty accArr (a :: rest)).run lst
      = .error le := by
  rw [ConLeche.Cached.inferSpineI.eq_3 _ _ _ _ _ _ _ hnp]
  subst hwf
  simp only [StateT.run] at h1 h2 h3 ⊢
  simp [h1, h2, h3]

/-- The whnf step, the domain comparison throwing (`CoreC.lean:1039`). -/
private theorem inferSpineI_nonpi_run_defeq_err
    (hnp : ∀ dom body m, lty = ConLeche.Expr.forallE dom body m → False)
    (h1 : (ConLeche.Cached.instListRevM lty accArr).run lst = .ok (ty', lst))
    (h2 : (fns.whnf depth ty').run lst = .ok (w, lst1))
    (hwf : w = ConLeche.Expr.forallE dom body mt)
    (h3 : (fns.infer depth a).run lst1 = .ok (ta, lst2))
    (h4 : (fns.defeq depth ta dom).run lst2 = .error le) :
    (ConLeche.Cached.inferSpineI fns lfe depth lty accArr (a :: rest)).run lst
      = .error le := by
  rw [ConLeche.Cached.inferSpineI.eq_3 _ _ _ _ _ _ _ hnp]
  subst hwf
  simp only [StateT.run] at h1 h2 h3 h4 ⊢
  simp [h1, h2, h3, h4]

/-- The whnf step, the comparison *failing* — the mirrored `throw`
(`core_c.rs:2740` ← `CoreC.lean:1040`). -/
private theorem inferSpineI_nonpi_run_mismatch
    (hnp : ∀ dom body m, lty = ConLeche.Expr.forallE dom body m → False)
    (h1 : (ConLeche.Cached.instListRevM lty accArr).run lst = .ok (ty', lst))
    (h2 : (fns.whnf depth ty').run lst = .ok (w, lst1))
    (hwf : w = ConLeche.Expr.forallE dom body mt)
    (h3 : (fns.infer depth a).run lst1 = .ok (ta, lst2))
    (h4 : (fns.defeq depth ta dom).run lst2 = .ok (false, lst3)) :
    (ConLeche.Cached.inferSpineI fns lfe depth lty accArr (a :: rest)).run lst
      = .error (.invalid "application type mismatch") := by
  rw [ConLeche.Cached.inferSpineI.eq_3 _ _ _ _ _ _ _ hnp]
  subst hwf
  simp only [StateT.run] at h1 h2 h3 h4 ⊢
  simp [h1, h2, h3, h4]

end ErrRun

/-- A node whose kind is not a `.ForallE` does not abstract to a `.forallE`:
`inferSpineI.eq_3`'s side condition, read off the node. -/
private theorem absExpr_ne_forallE {e : expr.Expr}
    (h : ∀ dm bd mt, e._0.kind ≠ expr.ExprKind.ForallE dm bd mt) :
    ∀ dm bd mt, absExpr e = ConLeche.Expr.forallE dm bd mt → False := by
  rw [CoreK.absExpr_kind]
  cases e with
  | mk nd =>
    cases nd with
    | mk dw k =>
      cases k
      case ForallE dm bd mt => exact absurd rfl (h dm bd mt)
      all_goals (intro dm bd mt hc; simp at hc)

/-- The `.Err` arms of every `match` on a `core::result::Result`, in the
**accept** half: there the hypothesis is `.Ok res`, which they contradict
outright.  (The failure half meets the same arms from the other side, where
they are the whole of the work.) -/
private theorem err_absurd {α : Type} {ce : core_types.CheckError}
    {st1 st' : cached.state_c.CState} {res : α}
    (h : (ok (core.result.Result.Err ce, st1) :
        Result ((core.result.Result α core_types.CheckError) × cached.state_c.CState))
      = ok (.Ok res, st')) : False := by
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  exact absurd h.1 (by simp)

/-- The same arms in the **failure** half, where they are the whole of the
work: the port hands its callee's error straight back, so the arm's error
*is* the outcome's.  Stated as a lemma for the same reason `err_absurd` is —
`cases` leaves the generated `match` unreduced, and applying a lemma to it
unfolds it. -/
private theorem err_eq {α : Type} {ce e : core_types.CheckError}
    {st1 st' : cached.state_c.CState}
    (h : (ok (core.result.Result.Err e, st1) :
        Result ((core.result.Result α core_types.CheckError) × cached.state_c.CState))
      = ok (.Err ce, st')) : e = ce := by
  simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at h
  exact h.1

/-- The port's `Err` value at a mirrored `throw` arm: `core_types::invalid` is
the `Invalid` constructor, so an `Err` built from it is `Err (.Invalid v)`
(task #67).  `absErrKind` then sends it to `ErrKind.invalid`, which is what
`ErrSim.invalid` asks for. -/
private theorem invalid_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v :=
  (Result.ok_injective (by rw [core_types.invalid] at h; exact h)).symm

/-- With an argument still to spend, the abstracted remainder is a cons — the
shape `inferSpineI`'s two step clauses match on.  The accept direction reads
it off `ExprOps.vec_index_expr`; the two failure arms that throw *before* the
Rust indexes `args[i]` (`core_c.rs:2750`'s `whnf` and `:2755`'s
"function expected") need it from the bound alone. -/
private theorem absExprs_drop_cons {args : alloc.vec.Vec expr.Expr}
    {i : Std.Usize} (hlt : i.val < args.val.length) :
    ∃ a rest, (absExprs args).drop i.val = a :: rest := by
  have hlen : (absExprs args).length = args.val.length := by simp [absExprs]
  refine List.exists_cons_of_ne_nil ?_
  intro hd
  have h0 := congrArg List.length hd
  rw [List.length_drop, hlen, List.length_nil] at h0
  omega

/-! ## The loop

`spine_aux` is the induction: strong induction on the number of remaining
arguments, `N = args.val.length - i.val`.  Its three clauses are
`inferSpineI`'s three: the spent-arguments base case, the syntactic ∀ step,
and the whnf step. -/

/-- The inductive hypothesis in the shape the two step clauses use it: the
walk at the *next* index, on any codomain and any fresh accumulator. -/
private def SpineIH (mode : env.CheckMode) (fuel : Std.U64) (d : Std.U64)
    (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) : Prop :=
  ∀ (ty' : expr.Expr) (acc' : alloc.vec.Vec expr.Expr) (i' : Std.Usize),
    i'.val = i.val + 1 → ExprWF ty' → ExprsWF acc' →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_spine_i mode fuel st fe d ty' acc' args i')
      (fun lfe => ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
        (absExpr ty') (absExprs acc').toArray ((absExprs args).drop i'.val))

section

variable {mode : env.CheckMode} {fuel : Std.U64}

/-- **Clause 2, the syntactic ∀ step** (`CoreC.lean:1023-1032`).  `ty`'s node
is a `.ForallE`, so nothing is normalized: the argument is inferred, its type
compared against the domain substituted under the deferred list, and the walk
continues into the codomain with the argument appended to the accumulator. -/
private theorem spine_pi (hw : Wrappers mode fuel) (d : Std.U64)
    {ty : expr.Expr} {acc args : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    {dm bd : expr.Expr} {mt : expr.BinderMeta}
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {res : expr.Expr}
    {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    (ihn : SpineIH mode fuel d args i)
    (hk : ty._0.kind = expr.ExprKind.ForallE dm bd mt)
    (hlt : i.val < args.val.length)
    (hty : ExprWF ty) (hacc : ExprsWF acc) (hargs : ExprsWF args)
    (hwf : StateWF st) (hfe : FEnvWF fe)
    (hok : cached.core_c.infer_spine_i mode fuel st fe d ty acc args i
      = ok (.Ok res, st'))
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe) :
    ∃ lst', (ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
        (absExpr ty) (absExprs acc).toArray ((absExprs args).drop i.val)).run lst
        = .ok (absExpr res, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF res := by
  -- the node's children, and `absExpr ty` read off the node
  obtain ⟨hdm, hbd, -⟩ : ExprWF dm ∧ ExprWF bd ∧ BinderMetaWF mt := by
    have := CoreK.ExprWF.children hty; rw [hk] at this; exact this
  have habs : absExpr ty = .forallE (absExpr dm) (absExpr bd) (absBinderMeta mt) := by
    rw [CoreK.absExpr_kind, hk]; simp
  -- the Rust side, forward from `ok`
  unfold cached.core_c.infer_spine_i at hok
  simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, hk] at hok
  rw [if_neg (show ¬ (i ≥ alloc.vec.Vec.len args) by
    have := alloc.vec.Vec.len_val args; scalar_tac)] at hok
  obtain ⟨bd1, hbd1, hok⟩ := bind_eq_ok_iff.mp hok
  rw [Expr.dup_eq hbd1] at hok
  obtain ⟨dom2, hdom2, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨a, hidx, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨-, haWF, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
  obtain ⟨⟨r1, st1⟩, hinf, hok⟩ := bind_eq_ok_iff.mp hok
  cases r1 with
  | Err e => exact (err_absurd hok).elim
  | Ok ta =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htaWF⟩ :=
      Sim.apply (hw.inferSim d haWF) hwf hfe hinf hrel hfrel
    obtain ⟨⟨r2, st2⟩, hdeq, hok⟩ := bind_eq_ok_iff.mp hok
    cases r2 with
    | Err e => exact (err_absurd hok).elim
    | Ok b =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
        Sim.apply (hw.defeqSim d htaWF (instListRevM_wf hdm hacc hdom2))
          hwf1 hfe hdeq hrel1 hfrel
      cases b with
      | false =>
        obtain ⟨s0, -, hok1⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨v0, -, hok2⟩ := bind_eq_ok_iff.mp hok1
        obtain ⟨ce0, -, hok3⟩ := bind_eq_ok_iff.mp hok2
        exact (err_absurd hok3).elim
      | true =>
        obtain ⟨a1, ha1, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq ha1] at hok
        obtain ⟨acc1, hpush, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hacc1 : ExprsWF acc1 := ExprOps.exprsWF_push hacc haWF hpush
        have haccArr : (absExprs acc1).toArray
            = (absExprs acc).toArray.push (absExpr a) := by
          rw [ExprOps.absExprs_push hpush]; simp
        obtain ⟨lst3, hrun3, hrel3, hwf3, hresWF⟩ :=
          Sim.apply (ihn bd acc1 i2 hi2v hbd hacc1) hwf2 hfe hok hrel2 hfrel
        refine ⟨lst3, ?_, hrel3, hwf3, hresWF⟩
        simp only [habs, hdrop]
        rw [inferSpineI_pi_run (instListRevM_run hdm hacc hdom2 lst) hrun1 hrun2]
        rw [hi2v] at hrun3
        rw [← haccArr]
        exact hrun3

/-- **Clause 3, the whnf step** (`CoreC.lean:1033-1042`).  `ty`'s node is not
a `.ForallE`, so the deferred list is substituted into it and the result
normalized; the certificate then runs against the *whnf'd* domain and the walk
continues with a fresh one-element accumulator. -/
private theorem spine_nonpi (hw : Wrappers mode fuel) (d : Std.U64)
    {ty : expr.Expr} {acc args : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {res : expr.Expr}
    {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    (ihn : SpineIH mode fuel d args i)
    (hnp : ∀ dm bd mt, ty._0.kind ≠ expr.ExprKind.ForallE dm bd mt)
    (hlt : i.val < args.val.length)
    (hty : ExprWF ty) (hacc : ExprsWF acc) (hargs : ExprsWF args)
    (hwf : StateWF st) (hfe : FEnvWF fe)
    (hok : cached.core_c.infer_spine_i mode fuel st fe d ty acc args i
      = ok (.Ok res, st'))
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe) :
    ∃ lst', (ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
        (absExpr ty) (absExprs acc).toArray ((absExprs args).drop i.val)).run lst
        = .ok (absExpr res, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF res := by
  -- `eq_3`'s side condition
  have hnpa : ∀ dm bd mt, absExpr ty = ConLeche.Expr.forallE dm bd mt → False :=
    absExpr_ne_forallE hnp
  unfold cached.core_c.infer_spine_i at hok
  simp only [expr_view_eq, arc_deref_eq, bind_tc_ok] at hok
  rw [if_neg (show ¬ (i ≥ alloc.vec.Vec.len args) by
    have := alloc.vec.Vec.len_val args; scalar_tac)] at hok
  split at hok
  -- the `.ForallE` arm contradicts `hnp`
  case h_7 dm bd mt heq => of_kind_inv heq; exact absurd heq (hnp _ _ _)
  -- the nine other arms are one and the same proof
  all_goals
    clear hnp
    obtain ⟨ty2, hty2, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨⟨r0, st1⟩, hwhn, hok⟩ := bind_eq_ok_iff.mp hok
    cases r0 with
    | Err e => exact (err_absurd hok).elim
    | Ok w =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, hwWF⟩ :=
        Sim.apply (hw.whnfSim d (instListRevM_wf hty hacc hty2)) hwf hfe hwhn hrel hfrel
      obtain ⟨⟨wdw, wk⟩⟩ := w
      cases wk
      case' ForallE dm bd mt =>
        obtain ⟨hdm, hbd, -⟩ : ExprWF dm ∧ ExprWF bd ∧ BinderMetaWF mt :=
          CoreK.ExprWF.children hwWF
        have habsw : absExpr (expr.Expr.mk (expr.ExprNode.mk wdw
              (expr.ExprKind.ForallE dm bd mt)))
            = .forallE (absExpr dm) (absExpr bd) (absBinderMeta mt) := by simp
        obtain ⟨dm1, hdm1, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hdm1] at hok
        obtain ⟨bd1, hbd1, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hbd1] at hok
        obtain ⟨a, hidx, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨-, haWF, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
        obtain ⟨⟨r1, st2⟩, hinf, hok⟩ := bind_eq_ok_iff.mp hok
        cases r1 with
        | Err e => exact (err_absurd hok).elim
        | Ok ta =>
          obtain ⟨lst2, hrun2, hrel2, hwf2, htaWF⟩ :=
            Sim.apply (hw.inferSim d haWF) hwf1 hfe hinf hrel1 hfrel
          obtain ⟨⟨r2, st3⟩, hdeq, hok⟩ := bind_eq_ok_iff.mp hok
          cases r2 with
          | Err e => exact (err_absurd hok).elim
          | Ok b =>
            obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
              Sim.apply (hw.defeqSim d htaWF hdm) hwf2 hfe hdeq hrel2 hfrel
            cases b with
            | false =>
              obtain ⟨s0, -, hok1⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨v0, -, hok2⟩ := bind_eq_ok_iff.mp hok1
              obtain ⟨ce0, -, hok3⟩ := bind_eq_ok_iff.mp hok2
              exact (err_absurd hok3).elim
            | true =>
              obtain ⟨acc2, hacc2, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨habs2, hacc2WF⟩ := CoreK.expr_singleton_refines haWF hacc2
              obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
              have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
              obtain ⟨lst4, hrun4, hrel4, hwf4, hresWF⟩ :=
                Sim.apply (ihn bd acc2 i2 hi2v hbd hacc2WF) hwf3 hfe hok hrel3 hfrel
              refine ⟨lst4, ?_, hrel4, hwf4, hresWF⟩
              simp only [hdrop]
              rw [inferSpineI_nonpi_run hnpa (instListRevM_run hty hacc hty2 lst)
                hrun1 habsw hrun2 hrun3]
              rw [hi2v, habs2] at hrun4
              simpa using hrun4
      all_goals
        obtain ⟨s0, -, hok1⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨v0, -, hok2⟩ := bind_eq_ok_iff.mp hok1
        obtain ⟨ce0, -, hok3⟩ := bind_eq_ok_iff.mp hok2
        exact (err_absurd hok3).elim

/-- **Clause 2's failure half** (task #67).  Four of the Rust's `Err` exits
live here and all four are mirrored: `r.infer` threw, `r.defeq` threw, the
comparison came back `false` and both sides throw `invalid`
(`core_c.rs:2714` ← `CoreC.lean:1031`), or the walk at the next index threw
and the inductive hypothesis carries it. -/
private theorem spine_pi_err (hw : Wrappers mode fuel) (d : Std.U64)
    {ty : expr.Expr} {acc args : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    {dm bd : expr.Expr} {mt : expr.BinderMeta}
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {ce : core_types.CheckError}
    {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    (ihn : SpineIH mode fuel d args i)
    (hk : ty._0.kind = expr.ExprKind.ForallE dm bd mt)
    (hlt : i.val < args.val.length)
    (hty : ExprWF ty) (hacc : ExprsWF acc) (hargs : ExprsWF args)
    (hwf : StateWF st) (hfe : FEnvWF fe)
    (hok : cached.core_c.infer_spine_i mode fuel st fe d ty acc args i
      = ok (.Err ce, st'))
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe) :
    ErrSim ce ((ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
      (absExpr ty) (absExprs acc).toArray ((absExprs args).drop i.val)).run lst) := by
  obtain ⟨hdm, hbd, -⟩ : ExprWF dm ∧ ExprWF bd ∧ BinderMetaWF mt := by
    have := CoreK.ExprWF.children hty; rw [hk] at this; exact this
  have habs : absExpr ty = .forallE (absExpr dm) (absExpr bd) (absBinderMeta mt) := by
    rw [CoreK.absExpr_kind, hk]; simp
  unfold cached.core_c.infer_spine_i at hok
  simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, hk] at hok
  rw [if_neg (show ¬ (i ≥ alloc.vec.Vec.len args) by
    have := alloc.vec.Vec.len_val args; scalar_tac)] at hok
  obtain ⟨bd1, hbd1, hok⟩ := bind_eq_ok_iff.mp hok
  rw [Expr.dup_eq hbd1] at hok
  obtain ⟨dom2, hdom2, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨a, hidx, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨-, haWF, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
  obtain ⟨⟨r1, st1⟩, hinf, hok⟩ := bind_eq_ok_iff.mp hok
  simp only [habs, hdrop]
  cases r1 with
  | Err e =>
    obtain rfl := err_eq (α := expr.Expr) hok
    refine ErrSim.trans
      (Sim.apply_err (hw.inferSim d haWF) hwf hfe hinf hrel hfrel) ?_
    intro le hle
    exact inferSpineI_pi_run_infer_err (instListRevM_run hdm hacc hdom2 lst) hle
  | Ok ta =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htaWF⟩ :=
      Sim.apply (hw.inferSim d haWF) hwf hfe hinf hrel hfrel
    obtain ⟨⟨r2, st2⟩, hdeq, hok⟩ := bind_eq_ok_iff.mp hok
    have hdsim := hw.defeqSim d htaWF (instListRevM_wf hdm hacc hdom2)
    cases r2 with
    | Err e =>
      obtain rfl := err_eq (α := expr.Expr) hok
      refine ErrSim.trans (Sim.apply_err hdsim hwf1 hfe hdeq hrel1 hfrel) ?_
      intro le hle
      exact inferSpineI_pi_run_defeq_err (instListRevM_run hdm hacc hdom2 lst) hrun1 hle
    | Ok b =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ := Sim.apply hdsim hwf1 hfe hdeq hrel1 hfrel
      cases b with
      | false =>
        obtain ⟨s0, -, hok1⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨v0, -, hok2⟩ := bind_eq_ok_iff.mp hok1
        obtain ⟨ce0, hce0, hok3⟩ := bind_eq_ok_iff.mp hok2
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at hok3
        obtain ⟨rfl, -⟩ := hok3
        rw [invalid_err hce0]
        exact ErrSim.invalid
          (inferSpineI_pi_run_mismatch (instListRevM_run hdm hacc hdom2 lst) hrun1 hrun2)
      | true =>
        obtain ⟨a1, ha1, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq ha1] at hok
        obtain ⟨acc1, hpush, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hacc1 : ExprsWF acc1 := ExprOps.exprsWF_push hacc haWF hpush
        have haccArr : (absExprs acc1).toArray
            = (absExprs acc).toArray.push (absExpr a) := by
          rw [ExprOps.absExprs_push hpush]; simp
        refine ErrSim.trans
          (Sim.apply_err (ihn bd acc1 i2 hi2v hbd hacc1) hwf2 hfe hok hrel2 hfrel) ?_
        intro le hle
        rw [inferSpineI_pi_run (instListRevM_run hdm hacc hdom2 lst) hrun1 hrun2]
        rw [hi2v] at hle
        rw [← haccArr]
        exact hle

/-- **Clause 3's failure half** (task #67).  Six `Err` exits, all mirrored:
`r.whnf` threw, the normal form was not a Π and both sides throw `invalid`
(`core_c.rs:2755` ← `CoreC.lean:1042`), `r.infer` threw, `r.defeq` threw, the
comparison came back `false` (`core_c.rs:2740` ← `CoreC.lean:1040`), or the
walk at the next index threw. -/
private theorem spine_nonpi_err (hw : Wrappers mode fuel) (d : Std.U64)
    {ty : expr.Expr} {acc args : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {ce : core_types.CheckError}
    {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    (ihn : SpineIH mode fuel d args i)
    (hnp : ∀ dm bd mt, ty._0.kind ≠ expr.ExprKind.ForallE dm bd mt)
    (hlt : i.val < args.val.length)
    (hty : ExprWF ty) (hacc : ExprsWF acc) (hargs : ExprsWF args)
    (hwf : StateWF st) (hfe : FEnvWF fe)
    (hok : cached.core_c.infer_spine_i mode fuel st fe d ty acc args i
      = ok (.Err ce, st'))
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe) :
    ErrSim ce ((ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
      (absExpr ty) (absExprs acc).toArray ((absExprs args).drop i.val)).run lst) := by
  have hnpa : ∀ dm bd mt, absExpr ty = ConLeche.Expr.forallE dm bd mt → False :=
    absExpr_ne_forallE hnp
  obtain ⟨a0, rest0, hcons⟩ := absExprs_drop_cons hlt
  unfold cached.core_c.infer_spine_i at hok
  simp only [expr_view_eq, arc_deref_eq, bind_tc_ok] at hok
  rw [if_neg (show ¬ (i ≥ alloc.vec.Vec.len args) by
    have := alloc.vec.Vec.len_val args; scalar_tac)] at hok
  split at hok
  -- the `.ForallE` arm contradicts `hnp`
  case h_7 dm bd mt heq => of_kind_inv heq; exact absurd heq (hnp _ _ _)
  -- the nine other arms are one and the same proof
  all_goals
    clear hnp
    obtain ⟨ty2, hty2, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨⟨r0, st1⟩, hwhn, hok⟩ := bind_eq_ok_iff.mp hok
    have hwsim := hw.whnfSim d (instListRevM_wf hty hacc hty2)
    cases r0 with
    | Err e =>
      obtain rfl := err_eq (α := expr.Expr) hok
      refine ErrSim.trans (Sim.apply_err hwsim hwf hfe hwhn hrel hfrel) ?_
      intro le hle
      rw [hcons]
      exact inferSpineI_nonpi_run_whnf_err hnpa (instListRevM_run hty hacc hty2 lst) hle
    | Ok w =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, hwWF⟩ := Sim.apply hwsim hwf hfe hwhn hrel hfrel
      obtain ⟨⟨wdw, wk⟩⟩ := w
      cases wk
      case' ForallE dm bd mt =>
        obtain ⟨hdm, hbd, -⟩ : ExprWF dm ∧ ExprWF bd ∧ BinderMetaWF mt :=
          CoreK.ExprWF.children hwWF
        have habsw : absExpr (expr.Expr.mk (expr.ExprNode.mk wdw
              (expr.ExprKind.ForallE dm bd mt)))
            = .forallE (absExpr dm) (absExpr bd) (absBinderMeta mt) := by simp
        obtain ⟨dm1, hdm1, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hdm1] at hok
        obtain ⟨bd1, hbd1, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hbd1] at hok
        obtain ⟨a, hidx, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨-, haWF, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
        obtain ⟨⟨r1, st2⟩, hinf, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [hdrop]
        cases r1 with
        | Err e =>
          obtain rfl := err_eq (α := expr.Expr) hok
          refine ErrSim.trans
            (Sim.apply_err (hw.inferSim d haWF) hwf1 hfe hinf hrel1 hfrel) ?_
          intro le hle
          exact inferSpineI_nonpi_run_infer_err hnpa
            (instListRevM_run hty hacc hty2 lst) hrun1 habsw hle
        | Ok ta =>
          obtain ⟨lst2, hrun2, hrel2, hwf2, htaWF⟩ :=
            Sim.apply (hw.inferSim d haWF) hwf1 hfe hinf hrel1 hfrel
          obtain ⟨⟨r2, st3⟩, hdeq, hok⟩ := bind_eq_ok_iff.mp hok
          have hdsim := hw.defeqSim d htaWF hdm
          cases r2 with
          | Err e =>
            obtain rfl := err_eq (α := expr.Expr) hok
            refine ErrSim.trans (Sim.apply_err hdsim hwf2 hfe hdeq hrel2 hfrel) ?_
            intro le hle
            exact inferSpineI_nonpi_run_defeq_err hnpa
              (instListRevM_run hty hacc hty2 lst) hrun1 habsw hrun2 hle
          | Ok b =>
            obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
              Sim.apply hdsim hwf2 hfe hdeq hrel2 hfrel
            cases b with
            | false =>
              obtain ⟨s0, -, hok1⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨v0, -, hok2⟩ := bind_eq_ok_iff.mp hok1
              obtain ⟨ce0, hce0, hok3⟩ := bind_eq_ok_iff.mp hok2
              simp only [Result.ok.injEq, Prod.mk.injEq,
                core.result.Result.Err.injEq] at hok3
              obtain ⟨rfl, -⟩ := hok3
              rw [invalid_err hce0]
              exact ErrSim.invalid (inferSpineI_nonpi_run_mismatch hnpa
                (instListRevM_run hty hacc hty2 lst) hrun1 habsw hrun2 hrun3)
            | true =>
              obtain ⟨acc2, hacc2, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨habs2, hacc2WF⟩ := CoreK.expr_singleton_refines haWF hacc2
              obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
              have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
              refine ErrSim.trans
                (Sim.apply_err (ihn bd acc2 i2 hi2v hbd hacc2WF) hwf3 hfe hok hrel3 hfrel) ?_
              intro le hle
              rw [inferSpineI_nonpi_run hnpa (instListRevM_run hty hacc hty2 lst)
                hrun1 habsw hrun2 hrun3]
              rw [hi2v, habs2] at hle
              simpa using hle
      all_goals
        obtain ⟨s0, -, hok1⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨v0, -, hok2⟩ := bind_eq_ok_iff.mp hok1
        obtain ⟨ce0, hce0, hok3⟩ := bind_eq_ok_iff.mp hok2
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at hok3
        obtain ⟨rfl, -⟩ := hok3
        rw [invalid_err hce0, hcons]
        exact ErrSim.invalid (inferSpineI_nonpi_run_fn hnpa
          (instListRevM_run hty hacc hty2 lst) hrun1 (by intro dm bd m hc; simp at hc))

/-- The whole walk, by strong induction on the number of arguments left.
`SimS.mk'` puts the two halves side by side: the accept direction is the
pre-task-#67 proof word for word, and the failure direction repeats its three
clauses against `spine_pi_err` / `spine_nonpi_err`.  **Clause 1 cannot throw**
— the Rust returns `Ok(inst_list_rev_m …)` — so that arm is absurd where the
accept direction had the work. -/
private theorem spine_aux (hw : Wrappers mode fuel) (d : Std.U64) (N : Nat) :
    ∀ (ty : expr.Expr) (acc args : alloc.vec.Vec expr.Expr) (i : Std.Usize),
      args.val.length - i.val = N → ExprWF ty → ExprsWF acc → ExprsWF args →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.infer_spine_i mode fuel st fe d ty acc args i)
        (fun lfe => ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
          (absExpr ty) (absExprs acc).toArray ((absExprs args).drop i.val)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ty acc args i hN hty hacc hargs fe lfe hfe hfrel
    refine SimS.mk' ?_ ?_
    · intro st res st' hwf hok lst hrel
      by_cases hge : i ≥ alloc.vec.Vec.len args
      · -- **Clause 1**: the arguments are spent; `instListRevM ty acc` is the answer.
        have hdrop : (absExprs args).drop i.val = [] := by
          refine List.drop_eq_nil_of_le ?_
          have hlen : (absExprs args).length = args.val.length := by simp [absExprs]
          rw [hlen]
          have := alloc.vec.Vec.len_val args
          scalar_tac
        unfold cached.core_c.infer_spine_i at hok
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok] at hok
        rw [if_pos hge] at hok
        obtain ⟨e, he, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst, ?_, hrel, hwf, instListRevM_wf hty hacc he⟩
        simp only [hdrop]
        rw [ConLeche.Cached.inferSpineI.eq_1]
        exact instListRevM_run hty hacc he lst
      · have hlt : i.val < args.val.length := by
          have := alloc.vec.Vec.len_val args; scalar_tac
        have ihn : SpineIH mode fuel d args i := by
          intro ty' acc' i' hi' hty' hacc'
          exact ih (args.val.length - i'.val) (by omega) ty' acc' args i' rfl hty' hacc' hargs
        by_cases hpi : ∃ dm bd mt, ty._0.kind = expr.ExprKind.ForallE dm bd mt
        · obtain ⟨dm, bd, mt, hk⟩ := hpi
          exact spine_pi hw d ihn hk hlt hty hacc hargs hwf hfe hok hrel hfrel
        · refine spine_nonpi hw d ihn ?_ hlt hty hacc hargs hwf hfe hok hrel hfrel
          intro dm bd mt hc
          exact hpi ⟨dm, bd, mt, hc⟩
    · intro st ce st' hwf hok lst hrel
      by_cases hge : i ≥ alloc.vec.Vec.len args
      · -- **Clause 1** has no `Err` exit at all.
        unfold cached.core_c.infer_spine_i at hok
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok] at hok
        rw [if_pos hge] at hok
        obtain ⟨e, -, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        exact absurd hok.1 (by simp)
      · have hlt : i.val < args.val.length := by
          have := alloc.vec.Vec.len_val args; scalar_tac
        have ihn : SpineIH mode fuel d args i := by
          intro ty' acc' i' hi' hty' hacc'
          exact ih (args.val.length - i'.val) (by omega) ty' acc' args i' rfl hty' hacc' hargs
        by_cases hpi : ∃ dm bd mt, ty._0.kind = expr.ExprKind.ForallE dm bd mt
        · obtain ⟨dm, bd, mt, hk⟩ := hpi
          exact spine_pi_err hw d ihn hk hlt hty hacc hargs hwf hfe hok hrel hfrel
        · refine spine_nonpi_err hw d ihn ?_ hlt hty hacc hargs hwf hfe hok hrel hfrel
          intro dm bd mt hc
          exact hpi ⟨dm, bd, mt, hc⟩

end

/-- `ConLeche/Cached/CoreC.lean:1018` — **`infer_spine_i` refines
`inferSpineI`** (`core_c.rs:2667`): the walk of the raw Π-telescope against
`args[i..]`, with `acc` the deferred-substitution list (con-leche's
elementwise: both are pushed at the end and consumed reversed) and
`r.infer`/`r.defeq`/`r.whnf` the knot's — at the full outcome (task #67), so
a throwing walk is con-leche's own throw at the same kind. -/
theorem infer_spine_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {ty : expr.Expr}
    {acc args : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    (hty : ExprWF ty) (hacc : ExprsWF acc) (hargs : ExprsWF args) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_spine_i mode fuel st fe d ty acc args i)
      (fun lfe => ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
        (absExpr ty) (absExprs acc).toArray ((absExprs args).drop i.val)) :=
  spine_aux hw d _ ty acc args i rfl hty hacc hargs

/-- info: 'ConRon.Refine.Core.infer_spine_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms infer_spine_i_refines

end ConRon.Refine.Core
