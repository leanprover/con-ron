/-
# The `annotate` arm of the knot (task #55, `CORE_PLAN.md` step 6)

The eighteen helpers of `crates/con-ron-core/src/cached/core_c.rs` that make up
the annotation pass — `annotate_body_i` (`core_c.rs:4704`) and its arms —
against con-leche's `annotateBodyI` (`ConLeche/Cached/CoreC.lean:1779`) and the
block of binder-telescope loops above it (`:1637-1777`).

The pass is the ζ-reducing, `PropWhen`-threading rebuild: it computes every
binder's codomain-sort annotation bottom-up by real inference on the opened
(already annotated) body, and returns the ζ reduct of a `let`.  It reads no
mode function at all, which is why con-leche gives it **one** named core for
both modes (`annotateBodyI` takes no `mode`); `mode` is in the Rust only to
reach the wrappers.

Three groups:

* the **pure node constructions** (`annot_node_i`, `annot_pw_dup_i`,
  `annot_pw_thread_i`, `annotate_binders_out_i`) — `SimP`, the rebuild fold
  and its three one-liners, over `Refine/PropWhen.lean`, `Refine/Abs.lean`,
  `Refine/CoreKGuards.lean`'s `annot_binder_meta` and
  `Refine/ExprOpsC*.lean`'s cached substitutions;
* the **telescope loops** (`annot_pw_pi_i`, `annotate_pis_pw_i`,
  `annotate_pis_leaf_i`, `annotate_pis_i` and their four λ twins) — `Sim`,
  where the Rust's `Vec<Expr>` accumulator is con-leche's `Array ExprC`
  (`absExprArr`) and the Rust's `Vec<AnnotBinderEntry>` pushed innermost-last
  is con-leche's `List AnnotBinderEntry` consed innermost-first (`absStk`, the
  reversal);
* the **body's own arms** (`annotate_forall_i`, `annotate_lam_loop_i`,
  `annotate_lam_chain_i`, `annotate_let_i`, `annotate_proj_i`) — Rust-only
  splits of `annotateBodyI`'s `match`, so each is stated against
  `annotateBodyI` *at the node the arm was reached on*, which is exactly what
  the caller (`annotate_body_i`) needs and what the arm's own proof unfolds.
  The two λ arms carry the `bvarBoundM e = 0` test the Rust reads before it
  branches — a hypothesis the caller discharges from `bvar_bound_m_refines`.

Every lemma is stated over the **full outcome** (task #67, DESIGN.md §3's
ruling of 2026-09-13): exact result on success *and* con-leche's own throw, at
the same kind, on a failure.  The pass has no `Native` site — its six
`CheckError` constructions are all mirrored, the three of `annotate_body_i`
(`core_c.rs:4760` ← `Cached/CoreC.lean:1786`, `:4769` ← `:1791`, `:4776` ←
`:1794`), `annotate_let_i`'s (`:4955` ← `:1844`), `annotate_proj_i`'s
(`:5003` ← `:1867`) and, through `core_k::annotate_proj_entry`,
`Refine/CoreKInfer.lean`'s four.  The `.M`-suffixed `Array Std.U32` constants
of the block are those messages' code points; messages are never compared, so
they still carry no theorem.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKGuards
import ConRon.Refine.CoreKInfer
import ConRon.Refine.CoreKPinned
import ConRon.Refine.CoreKSupport
import ConRon.Refine.PropRead
import ConRon.Refine.ExprOpsCAbs
import ConRon.Refine.ExprOpsCSubst
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.ExprOpsSpine

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! `attribute [local simp]` does not travel across files, so `Shape.lean`'s
monad-plumbing set (`CheckCM = StateT CState (Except CheckError)`) is
re-declared here verbatim. -/
attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-! ## The mirrored `throw` arms (task #67)

The full-outcome convention (DESIGN.md §3's ruling of 2026-09-13): every
lemma of this file claims con-leche's outcome for *every* Rust outcome, and
the annotation pass's `CheckError` sites are all mirrored -- three in
`annotate_body_i` (`core_c.rs:4760` <- `Cached/CoreC.lean:1786`, `:4769` <-
`:1791`, `:4776` <- `:1794`), one in `annotate_let_i` (`:4955` <- `:1844`),
one in `annotate_proj_i` (`:5003` <- `:1867`) and `core_k::annotate_proj_entry`'s
four, which `Refine/CoreKInfer.lean`'s `annotate_proj_entry_err` owns.

Three small helpers do the shared bookkeeping.  `invalid_inv` /
`not_implemented_inv` invert the port's error constructor (the coordinator
hoists these into `Abs.lean` at the end of the campaign), and `throw_apply`
is the *applied* form of a con-leche `throw`: the plumbing `simp` set above
has `StateT.run` but no `MonadExcept` instance, so an explicit-`throw` arm
ends there. -/

/-- `core_types::invalid v = ok ce -> ce = .Invalid v`. -/
private theorem invalid_inv {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v := by
  rw [core_types.invalid] at h; exact (Result.ok_injective h).symm

/-- `core_types::not_implemented v = ok ce -> ce = .NotImplemented v`. -/
private theorem not_implemented_inv {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.not_implemented v = ok ce) :
    ce = .NotImplemented v := by
  rw [core_types.not_implemented] at h; exact (Result.ok_injective h).symm

/-- `throw` in `CheckCM`, at the *applied* form (`StateT.run` is already in the
plumbing set and fires first, so the lemma must be stated here, not on
`(throw le).run lst`). -/
@[local simp] private theorem throw_apply {β : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM β) lst = .error le := rfl

/-! ## The two accumulators

`annotate_pis_i`/`annotate_lams_i` carry the opened free variables in a
`Vec<Expr>` where con-leche carries an `Array ExprC`, and the rebuild stack in
a `Vec<AnnotBinderEntry>` **pushed innermost-last** where con-leche conses a
`List AnnotBinderEntry` **innermost-first**.  The first correspondence is
`List.toArray`, the second is `List.reverse`; `absStkTake` is the partial form
`annotate_binders_out_i`'s downward index `p` needs. -/

/-- The Rust free-variable accumulator as con-leche's `Array ExprC`. -/
def absExprArr (vs : alloc.vec.Vec expr.Expr) : Array ConLeche.Expr :=
  (absExprs vs).toArray

/-- The first `p` entries of the Rust rebuild stack as the `List` the Lean fold
consumes: the Rust walks `stk[p-1], …, stk[0]`, the Lean walks its list from
the head, so the list is the reversal. -/
def absStkTake (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) (p : Nat) :
    List ConLeche.Cached.AnnotBinderEntry :=
  ((stk.val.take p).map (fun q => (absExpr q.1, absBinderMeta q.2))).reverse

/-- The whole rebuild stack. -/
def absStk (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) :
    List ConLeche.Cached.AnnotBinderEntry :=
  absStkTake stk stk.val.length

/-- Every entry of the rebuild stack is well formed. -/
def StkWF (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) : Prop :=
  ∀ q ∈ stk.val, ExprWF q.1 ∧ BinderMetaWF q.2

/-- The node constructor con-leche passes as `mk`, as the Rust's `is_forall`
flag selects it (`annot_node_i`, the module note's point 6). -/
def mkNode (is_forall : Bool) :
    ConLeche.Expr → ConLeche.Expr → ConLeche.BinderMeta → ConLeche.Expr :=
  fun ty b mb => if is_forall then .forallE ty b mb else .lam ty b mb

@[simp] theorem mkNode_true :
    mkNode true = fun ty b mb => ConLeche.Expr.forallE ty b mb := rfl

@[simp] theorem mkNode_false :
    mkNode false = fun ty b mb => ConLeche.Expr.lam ty b mb := rfl

@[simp] theorem absStkTake_zero (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) :
    absStkTake stk 0 = [] := by simp [absStkTake]

/-- The fold's step on the list side: taking one more entry conses the entry at
index `p` onto the front. -/
theorem absStkTake_succ {stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {p : Nat}
    {ty0 : expr.Expr} {mb0 : expr.BinderMeta} (hp : p < stk.val.length)
    (hq : stk.val[p]? = some (ty0, mb0)) :
    absStkTake stk (p + 1)
      = (absExpr ty0, absBinderMeta mb0) :: absStkTake stk p := by
  have hget : stk.val[p] = (ty0, mb0) := by
    rw [List.getElem?_eq_getElem hp] at hq; exact Option.some.inj hq
  have h1 : stk.val.take (p + 1) = stk.val.take p ++ [(ty0, mb0)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hp, hget]; rfl
  simp only [absStkTake, h1, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]

/-- `absStk` at a vector the caller has just pushed onto: the Rust's push at
the end is the Lean's cons at the head. -/
theorem absStk_push {stk stk' : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {x : expr.Expr} {m : expr.BinderMeta}
    (h : alloc.vec.Vec.push stk (x, m) = ok stk') :
    absStk stk' = (absExpr x, absBinderMeta m) :: absStk stk := by
  have hv := vec_push_val h
  simp only [absStk, absStkTake, hv]
  simp

/-- `absExprArr` at a vector the caller has just pushed onto. -/
theorem absExprArr_push {vs vs' : alloc.vec.Vec expr.Expr} {x : expr.Expr}
    (h : alloc.vec.Vec.push vs x = ok vs') :
    absExprArr vs' = (absExprArr vs).push (absExpr x) := by
  have hv := vec_push_val h
  simp only [absExprArr, absExprs, hv]
  simp

/-- `StkWF` is preserved by the push. -/
theorem StkWF_push {stk stk' : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {x : expr.Expr} {m : expr.BinderMeta} (hstk : StkWF stk) (hx : ExprWF x)
    (hm : BinderMetaWF m) (h : alloc.vec.Vec.push stk (x, m) = ok stk') :
    StkWF stk' := by
  intro r hr
  rw [vec_push_val h] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hstk r hr
  · rw [List.mem_singleton.mp hr]; exact ⟨hx, hm⟩

/-- `ExprsWF` is preserved by the push. -/
theorem ExprsWF_push {vs vs' : alloc.vec.Vec expr.Expr} {x : expr.Expr}
    (hvs : ExprsWF vs) (hx : ExprWF x) (h : alloc.vec.Vec.push vs x = ok vs') :
    ExprsWF vs' := by
  intro r hr
  rw [vec_push_val h] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hvs r hr
  · rw [List.mem_singleton.mp hr]; exact hx

/-- One `do`-bind of a `CheckCM` action whose run is known: the shape every arm
composes in.  Rewriting with this (rather than unfolding `StateT.bind`) keeps
an `if` in the bound action from being distributed over the continuation. -/
theorem bind_run {α β : Type} {m : ConLeche.Cached.CheckCM α}
    {f : α → ConLeche.Cached.CheckCM β} {s s' : ConLeche.Cached.CState} {a : α}
    (h : m.run s = .ok (a, s')) :
    (do let x ← m; f x).run s = (f a).run s' := by
  simp only [StateT.run, Bind.bind, StateT.bind] at h ⊢
  rw [h]
  rfl

/-- Associativity of the `CheckCM` bind, in the direction that puts the Rust's
fused `infer_io_whnf_i` back together on the Lean side. -/
theorem bind_assoc' {α β γ : Type} (m : ConLeche.Cached.CheckCM α)
    (f : α → ConLeche.Cached.CheckCM β) (g : β → ConLeche.Cached.CheckCM γ) :
    (do let x ← m; let y ← f x; g y) = (do let y ← (do let x ← m; f x); g y) := by
  funext s
  simp only [Bind.bind, StateT.bind]
  cases m s <;> rfl

/-- The `do`-elaborator turns `let x ← if c then A else B; k x` into a join
point — `if c then (do let x ← A; k x) else (do let x ← B; k x)` — so the two
routes of the single-binder write are put back under one bind here. -/
theorem ite_bind_jp {α β : Type} (C : Prop) [Decidable C]
    (A B : ConLeche.Cached.CheckCM α) (k : α → ConLeche.Cached.CheckCM β) :
    (if C then (do let x ← A; k x) else (do let x ← B; k x))
      = (do let x ← (if C then A else B); k x) := by
  by_cases h : C <;> simp only [if_pos, h, ite_false]

/-! ## The foreign callees

Two helpers of the block live in `Arms/Shared.lean` (they are called from
otherwise disjoint clusters).  Per the task brief they are *declared* here, one
field each, at exactly the statement their own `<fn>_refines` has; the
coordinator discharges the structure at the end. -/

/-- `ensure_sort_i` and `infer_io_whnf_i` (`Arms/Shared.lean`). -/
structure AnnotateDeps (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  /-- `ConLeche/Cached/CoreC.lean:1115` — `ensure_sort_i` refines `ensureSortI`
  (`core_c.rs:2604`). -/
  ensureSort : ∀ (d : Std.U64) {e : expr.Expr}, ExprWF e →
    Sim absLevel LevelWF
      (fun st fe => cached.core_c.ensure_sort_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.ensureSortI (knot mode lfe fuel.val) d.val
        (absExpr e))
  /-- `ConLeche/Cached/CoreC.lean:557-558` — `infer_io_whnf_i` refines
  `majorToCtorI`'s opening two lines (`core_c.rs:1445`). -/
  inferIOWhnf : ∀ (d : Std.U64) {e : expr.Expr}, ExprWF e →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_io_whnf_i mode fuel st fe d e)
      (fun lfe => do
        let t ← (knot mode lfe fuel.val).inferIO d.val (absExpr e)
        (knot mode lfe fuel.val).whnf d.val t)

/-! ## The rebuild fold and its three one-liners -/

/-- `ConLeche/Cached/CoreC.lean:1649-1676` — **`annot_node_i` refines
`annotateBindersOutI`'s `mk` argument** (`core_c.rs:4390`): the node constructor
the Lean passes as a function, as the `is_forall` flag (the module note's
point 6), and as its own function because written inline Aeneas could not match
the two arms' contexts (task #23). -/
theorem annot_node_i_refines (is_forall : Bool) {ty body : expr.Expr}
    {mb : expr.BinderMeta} (hty : ExprWF ty) (hbody : ExprWF body)
    (hmb : BinderMetaWF mb) :
    SimP absExpr ExprWF (cached.core_c.annot_node_i is_forall ty body mb)
      (mkNode is_forall (absExpr ty) (absExpr body) (absBinderMeta mb)) := by
  intro r h
  rw [cached.core_c.annot_node_i] at h
  cases is_forall with
  | true =>
    simp only [if_true] at h
    exact ⟨by rw [Expr.forall_e_refines h]; simp, Expr.forall_e_wf hty hbody hmb h⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    exact ⟨by rw [Expr.lam_refines h]; simp, Expr.lam_wf hty hbody hmb h⟩

/-- `ConLeche/Cached/CoreC.lean:1649-1676` — **`annot_pw_dup_i` refines
`Option.map PropWhen.dup`** (`core_c.rs:4415`): the threaded datum is read twice
per entry and `PropWhen` is not `Copy`, so the port copies it; the copy is the
identity in the model (`Refine/PropWhen.lean`'s `dup_eq`). -/
theorem annot_pw_dup_i_refines {pw : Option prop_when.PropWhen}
    (hpw : ∀ q, pw = some q → PropWhenWF q) :
    SimP (Option.map absPropWhen) (fun o => ∀ q, o = some q → PropWhenWF q)
      (cached.core_c.annot_pw_dup_i pw) (pw.map absPropWhen) := by
  intro r h
  rw [cached.core_c.annot_pw_dup_i.eq_def] at h
  cases pw with
  | none =>
    simp only [Result.ok.injEq] at h
    subst h
    exact ⟨rfl, by simp⟩
  | some p =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨q, hq, hr⟩ := h
    rw [PropWhen.dup_eq hq] at hr
    refine ⟨by rw [← hr], ?_⟩
    intro q' hq'
    rw [← hr, Option.some.injEq] at hq'
    rw [← hq']
    exact hpw p rfl

/-- `ConLeche/Cached/CoreC.lean:1649-1676` — **`annot_pw_thread_i` refines
`pw?.map fun _ => mb.pw`** (`core_c.rs:4404`): the datum *just written*, threaded
outward.  The Rust hands it the already-computed `annot_binder_meta` result, so
the Lean side reads `mb`'s datum, which is what
`(annotBinderMetaI pw? mb).pw` is at the call site. -/
theorem annot_pw_thread_i_refines {pw : Option prop_when.PropWhen}
    {mb : expr.BinderMeta} (hmb : BinderMetaWF mb) :
    SimP (Option.map absPropWhen) (fun o => ∀ q, o = some q → PropWhenWF q)
      (cached.core_c.annot_pw_thread_i pw mb)
      ((pw.map absPropWhen).map (fun _ => (absBinderMeta mb).pw)) := by
  intro r h
  rw [cached.core_c.annot_pw_thread_i.eq_def] at h
  cases pw with
  | none =>
    simp only [Result.ok.injEq] at h
    subst h
    exact ⟨rfl, by simp⟩
  | some p =>
    simp only [arc_deref_eq, bind_tc_ok, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨q, hq, hr⟩ := h
    rw [PropWhen.dup_eq hq] at hr
    refine ⟨by rw [← hr]; rfl, ?_⟩
    intro q' hq'
    rw [← hr, Option.some.injEq] at hq'
    rw [← hq']
    exact hmb
/-! ### The Lean fold, in `pure`-normal form

`annotateBindersOutI`'s two clauses, with `abstractRangeM` and the inner `pure`
discharged — the shape the Rust's step composes against.  `annotBinderMetaI`
(`CoreC.lean:1643`) is `Core.lean:2682`'s `annotBinderMeta` verbatim, which is
what `Refine/CoreKGuards.lean` refines. -/

theorem annotBinderMetaI_eq (pw? : Option ConLeche.PropWhen) (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.annotBinderMetaI pw? mb = ConLeche.annotBinderMeta pw? mb := rfl

theorem annotateBindersOutI_nil
    (mk : ConLeche.Expr → ConLeche.Expr → ConLeche.BinderMeta → ConLeche.Expr)
    (d : Nat) (pw? : Option ConLeche.PropWhen) (j : Nat) (cur : ConLeche.Expr) :
    ConLeche.Cached.annotateBindersOutI mk d pw? [] j cur = pure cur := rfl

theorem annotateBindersOutI_cons
    (mk : ConLeche.Expr → ConLeche.Expr → ConLeche.BinderMeta → ConLeche.Expr)
    (d : Nat) (pw? : Option ConLeche.PropWhen) (ty' : ConLeche.Expr)
    (mb : ConLeche.BinderMeta) (rest : List ConLeche.Cached.AnnotBinderEntry)
    (j : Nat) (cur : ConLeche.Expr) :
    ConLeche.Cached.annotateBindersOutI mk d pw? ((ty', mb) :: rest) j cur
      = ConLeche.Cached.annotateBindersOutI mk d
          (pw?.map fun _ => (ConLeche.annotBinderMeta pw? mb).pw) rest (j - 1)
          (mk (ConLeche.Cached.ExprC.abstractRange ty' d j) cur
            (ConLeche.annotBinderMeta pw? mb)) := rfl

/-- `ConLeche/Cached/CoreC.lean:1649-1676` — **`annotate_binders_out_i` refines
`annotateBindersOutI`** (`core_c.rs:4353`): the rebuild fold of the annotation
telescope loops, one binder node per stack entry with one `abstractRangeM` per
domain, and the datum *just written* threaded outward.

The `List` stack is a `Vec` walked downwards by `p` (`absStkTake`, the partial
reversal), the `mk` node constructor is the `is_forall` flag (`annot_node_i`),
and `pw?.map (fun _ => …)` is `annot_pw_thread_i`.  The Rust's extra
`p > stk.len()` guard is unreachable from either caller (both pass
`stk.len()`), which is why `p.val ≤ stk.val.length` is a hypothesis: at a
larger `p` the Rust returns `cur` while the Lean fold would still have entries
left.

The Lean twin is a `CheckCM` action that touches no state, so the value
abstraction is `fun r => pure (absExpr r)` and the shape is `SimP`. -/
theorem annotate_binders_out_i_refines (is_forall : Bool) (d : Std.U64) :
    ∀ (P : Nat) (pw : Option prop_when.PropWhen)
      (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) (p : Std.Usize) (j : Std.U64)
      (cur : expr.Expr), p.val = P → p.val ≤ stk.val.length →
      (∀ q, pw = some q → PropWhenWF q) → StkWF stk → ExprWF cur →
      SimP (fun x => (pure (absExpr x) : ConLeche.Cached.CheckCM ConLeche.Expr)) ExprWF
        (cached.core_c.annotate_binders_out_i is_forall d pw stk p j cur)
        (ConLeche.Cached.annotateBindersOutI (mkNode is_forall) d.val
          (pw.map absPropWhen) (absStkTake stk p.val) j.val (absExpr cur)) := by
  intro P
  induction P with
  | zero =>
    intro pw stk p j cur hp _ _ _ hcur r h
    unfold cached.core_c.annotate_binders_out_i at h
    rw [if_pos (show p = 0#usize by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [hp, absStkTake_zero, annotateBindersOutI_nil]
    exact ⟨rfl, hcur⟩
  | succ P ih =>
    intro pw stk p j cur hp hlen hpw hstk hcur r h
    have hPlt : P < stk.val.length := by omega
    have hlenv : (alloc.vec.Vec.len stk).val = stk.val.length := alloc.vec.Vec.len_val stk
    unfold cached.core_c.annotate_binders_out_i at h
    rw [if_neg (show ¬ p = 0#usize by scalar_tac),
      if_neg (show ¬ p > alloc.vec.Vec.len stk by scalar_tac)] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i1, hi1, h⟩ := h
    have hi1v : i1.val = P := by
      have h1 := HashMap.uscalar_sub_eq hi1
      have h2 : (1#usize : Std.Usize).val = 1 := by scalar_tac
      omega
    obtain ⟨ent, hent, h⟩ := h
    obtain ⟨ty0, mb0⟩ := ent
    have hg : stk.val[P]? = some (ty0, mb0) := by
      rw [← hi1v]; exact ExprOps.vec_index_getElem? hent
    have hty0WF : ExprWF ty0 := (hstk (ty0, mb0) (List.mem_of_getElem? hg)).1
    have hmb0WF : BinderMetaWF mb0 := (hstk (ty0, mb0) (List.mem_of_getElem? hg)).2
    -- the pattern-`let` Aeneas emits for the tuple entry: only the *unifier*
    -- sees through it (task #16's hard spot 1), so it goes by ascription
    have h : (do
        let ty_abs ← cached.state_c.abstract_range_m ty0 d j
        let o ← cached.core_c.annot_pw_dup_i pw
        let mb ← core_k.annot_binder_meta o mb0
        let next ← cached.core_c.annot_pw_thread_i pw mb
        let node ← cached.core_c.annot_node_i is_forall ty_abs cur mb
        let i2 ← expr_ops.sub_nat j 1#u64
        cached.core_c.annotate_binders_out_i is_forall d next stk i1 i2 node)
          = ok r := h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨tyAbs, htyAbs, h⟩ := h
    obtain ⟨habsTy, hwfTy⟩ := ExprOpsC.abstract_range_refines hty0WF
      (by rw [StateC.abstract_range_m_eq] at htyAbs; exact htyAbs)
    rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac] at habsTy
    obtain ⟨o, ho, h⟩ := h
    obtain ⟨habsO, hwfO⟩ := annot_pw_dup_i_refines hpw o ho
    obtain ⟨mb, hmb, h⟩ := h
    obtain ⟨habsMb, hwfMb⟩ := CoreK.annot_binder_meta_refines hwfO hmb0WF hmb
    obtain ⟨next, hnext, h⟩ := h
    obtain ⟨habsNext, hwfNext⟩ := annot_pw_thread_i_refines hwfMb next hnext
    obtain ⟨node, hnode, h⟩ := h
    obtain ⟨habsNode, hwfNode⟩ :=
      annot_node_i_refines is_forall hwfTy hcur hwfMb node hnode
    obtain ⟨i2, hi2, h⟩ := h
    have hi2v : i2.val = j.val - 1 := ExprOps.sub_nat_val hi2
    obtain ⟨habsR, hwfR⟩ := ih next stk i1 i2 node hi1v (by omega)
      (fun q hq => hwfNext q hq) hstk hwfNode r h
    refine ⟨?_, hwfR⟩
    rw [habsO] at habsMb
    rw [habsMb] at habsNext habsNode
    rw [hp, absStkTake_succ hPlt hg, annotateBindersOutI_cons, ← habsTy, ← habsNode]
    rw [habsR, hi1v, hi2v, habsNext]

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-! ## The two telescope data

`annotPwPiI`/`annotPwLamI` compute the datum a whole binder chain shares
(`zeronessOf (imax u v) = zeronessOf v` for ∀, the `(lam-cod-chain)` rule for
λ).  Both open with the head-symbol reader (con-leche's task #168 stage 2),
which `Refine/PropRead.lean` refines, and fall back on inference.

`uncurry_apply_pair` is the peel of the `let (r, st) ← …` Aeneas emits for
every state-threading call: the pattern-`let` is `Function.uncurry` at a pair,
which neither `dsimp` nor `split` reduces (task #16's hard spot 1). -/

/-- `ConLeche/Cached/CoreC.lean:1682` — **`annot_pw_pi_i` refines `annotPwPiI`**
(`core_c.rs:4429`): the ∀ telescope's datum, the leaf codomain sort's
zero-ness, the head-symbol reader first. -/
theorem annot_pw_pi_i_refines (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (d : Std.U64) {body2 : expr.Expr} (hb : ExprWF body2) :
    Sim absPropWhen PropWhenWF
      (fun st fe => cached.core_c.annot_pw_pi_i mode fuel st fe d body2)
      (fun lfe => ConLeche.Cached.annotPwPiI (knot mode lfe fuel.val) lfe d.val
        (absExpr body2)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  rw [cached.core_c.annot_pw_pi_i.eq_def] at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨o, ho, hok⟩ := hok
  obtain ⟨habsO, hwfO⟩ := PropRead.type_sort_pw_refines (FindAgree.of_rel hfrel hfe)
    (FindWF.of_wf hfe) hb ho
  rw [ConLeche.Cached.annotPwPiI.eq_def, ← habsO]
  cases o with
  | some p =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hr, hst⟩ := hok
    subst hr
    subst hst
    exact ⟨lst, by simp, hrel, hwf, hwfO p rfl⟩
  | none =>
    simp only [bind_eq_ok_iff] at hok
    obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
    cases r0 with
    | Err err =>
      simp only [uncurry_apply_pair] at hok
      simp at hok
      obtain ⟨hr, -⟩ := hok
      subst hr
      exact Out.err (ErrSim.bindCM ((hw.inferIOSim d hb).apply_err hwf hfe h1 hrel hfrel))
    | Ok bt =>
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
      obtain ⟨lst1, hrun1, hrel1, hwf1, hbtWF⟩ :=
        (hw.inferIOSim d hb).apply hwf hfe h1 hrel hfrel
      obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
      cases r1 with
      | Err err =>
        simp only [uncurry_apply_pair] at hok
        simp at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        simp only [Option.map_none]
        rw [bind_run hrun1]
        exact Out.err (ErrSim.bindCM ((hd.ensureSort d hbtWF).apply_err hwf1 hfe h2 hrel1 hfrel))
      | Ok v =>
        simp only [uncurry_apply_pair, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨lst2, hrun2, hrel2, hwf2, hvWF⟩ :=
          (hd.ensureSort d hbtWF).apply hwf1 hfe h2 hrel1 hfrel
        obtain ⟨pw, hpw, hr, hst⟩ := hok
        obtain ⟨habsPw, hwfPw⟩ := ExprOps.zeroness_of_refines hvWF pw hpw
        subst hst
        subst hr
        refine ⟨lst2, ?_, hrel2, hwf2, hwfPw⟩
        simp only [StateT.run] at hrun1 hrun2
        simp [hrun1, hrun2, habsPw]

/-- `ConLeche/Cached/CoreC.lean:1736` — **`annot_pw_lam_i` refines
`annotPwLamI`** (`core_c.rs:4566`): the λ chain's datum, the zero-ness of the
sort of the innermost body's TYPE, the reader first. -/
theorem annot_pw_lam_i_refines (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (d : Std.U64) {body2 : expr.Expr} (hb : ExprWF body2) :
    Sim absPropWhen PropWhenWF
      (fun st fe => cached.core_c.annot_pw_lam_i mode fuel st fe d body2)
      (fun lfe => ConLeche.Cached.annotPwLamI (knot mode lfe fuel.val) lfe d.val
        (absExpr body2)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  rw [cached.core_c.annot_pw_lam_i.eq_def] at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨o, ho, hok⟩ := hok
  obtain ⟨habsO, hwfO⟩ := PropRead.proof_pw_refines (FindAgree.of_rel hfrel hfe)
    (FindWF.of_wf hfe) hb ho
  rw [ConLeche.Cached.annotPwLamI.eq_def, ← habsO]
  cases o with
  | some p =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hr, hst⟩ := hok
    subst hr
    subst hst
    exact ⟨lst, by simp, hrel, hwf, hwfO p rfl⟩
  | none =>
    simp only [bind_eq_ok_iff] at hok
    obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
    cases r0 with
    | Err err =>
      simp only [uncurry_apply_pair] at hok
      simp at hok
      obtain ⟨hr, -⟩ := hok
      subst hr
      exact Out.err (ErrSim.bindCM ((hw.inferIOSim d hb).apply_err hwf hfe h1 hrel hfrel))
    | Ok bt =>
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
      obtain ⟨lst1, hrun1, hrel1, hwf1, hbtWF⟩ :=
        (hw.inferIOSim d hb).apply hwf hfe h1 hrel hfrel
      obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
      cases r1 with
      | Err err =>
        simp only [uncurry_apply_pair] at hok
        simp at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        simp only [Option.map_none]
        rw [bind_run hrun1]
        exact Out.err (ErrSim.bindCM ((hw.inferIOSim d hbtWF).apply_err hwf1 hfe h2 hrel1 hfrel))
      | Ok btt =>
        simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
        obtain ⟨lst2, hrun2, hrel2, hwf2, hbttWF⟩ :=
          (hw.inferIOSim d hbtWF).apply hwf1 hfe h2 hrel1 hfrel
        obtain ⟨⟨r2, st3⟩, h3, hok⟩ := hok
        cases r2 with
        | Err err =>
          simp only [uncurry_apply_pair] at hok
          simp at hok
          obtain ⟨hr, -⟩ := hok
          subst hr
          simp only [Option.map_none]
          rw [bind_run hrun1, bind_run hrun2]
          exact Out.err
            (ErrSim.bindCM ((hd.ensureSort d hbttWF).apply_err hwf2 hfe h3 hrel2 hfrel))
        | Ok vb =>
          simp only [uncurry_apply_pair, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨lst3, hrun3, hrel3, hwf3, hvbWF⟩ :=
            (hd.ensureSort d hbttWF).apply hwf2 hfe h3 hrel2 hfrel
          obtain ⟨pw, hpw, hr, hst⟩ := hok
          obtain ⟨habsPw, hwfPw⟩ := ExprOps.zeroness_of_refines hvbWF pw hpw
          subst hst
          subst hr
          refine ⟨lst3, ?_, hrel3, hwf3, hwfPw⟩
          simp only [StateT.run] at hrun1 hrun2 hrun3
          simp [hrun1, hrun2, hrun3, habsPw]

/-- `ConLeche/Cached/CoreC.lean:1699` — **`annotate_pis_pw_i` refines
`annotatePisPwI`** (`core_c.rs:4457`): the ∀ telescope loop's write, ungated
since con-leche's ruling of 2026-09-06 — writing the datum is part of the real
checker's algorithm, only *validating* it is certification-only work. -/
theorem annotate_pis_pw_i_refines (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (d k : Std.U64) {leaf2 : expr.Expr} (hl : ExprWF leaf2) :
    Sim (Option.map absPropWhen) (fun o => ∀ q, o = some q → PropWhenWF q)
      (fun st fe => cached.core_c.annotate_pis_pw_i mode fuel st fe d k leaf2)
      (fun lfe => ConLeche.Cached.annotatePisPwI (knot mode lfe fuel.val) lfe d.val
        k.val (absExpr leaf2)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  rw [cached.core_c.annotate_pis_pw_i.eq_def] at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨i, hi, hok⟩ := hok
  have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp only [uncurry_apply_pair] at hok
    simp at hok
    obtain ⟨hr, -⟩ := hok
    subst hr
    rw [ConLeche.Cached.annotatePisPwI, ← hiv]
    exact Out.err
      (ErrSim.bindCM ((annot_pw_pi_i_refines hw hd i hl).apply_err hwf hfe h1 hrel hfrel))
  | Ok p =>
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨lst1, hrun1, hrel1, hwf1, hpWF⟩ :=
      (annot_pw_pi_i_refines hw hd i hl).apply hwf hfe h1 hrel hfrel
    obtain ⟨hr, hst⟩ := hok
    subst hst
    subst hr
    refine ⟨lst1, ?_, hrel1, hwf1, ?_⟩
    · rw [ConLeche.Cached.annotatePisPwI, ← hiv]
      simp only [StateT.run] at hrun1
      simp [hrun1]
    · intro q hq; rw [Option.some.injEq] at hq; rw [← hq]; exact hpWF

/-- `ConLeche/Cached/CoreC.lean:1748` — **`annotate_lams_pw_i` refines
`annotateLamsPwI`** (`core_c.rs:4591`), the λ twin, ungated with it. -/
theorem annotate_lams_pw_i_refines (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (d k : Std.U64) {leaf2 : expr.Expr} (hl : ExprWF leaf2) :
    Sim (Option.map absPropWhen) (fun o => ∀ q, o = some q → PropWhenWF q)
      (fun st fe => cached.core_c.annotate_lams_pw_i mode fuel st fe d k leaf2)
      (fun lfe => ConLeche.Cached.annotateLamsPwI (knot mode lfe fuel.val) lfe d.val
        k.val (absExpr leaf2)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  rw [cached.core_c.annotate_lams_pw_i.eq_def] at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨i, hi, hok⟩ := hok
  have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp only [uncurry_apply_pair] at hok
    simp at hok
    obtain ⟨hr, -⟩ := hok
    subst hr
    rw [ConLeche.Cached.annotateLamsPwI, ← hiv]
    exact Out.err
      (ErrSim.bindCM ((annot_pw_lam_i_refines hw hd i hl).apply_err hwf hfe h1 hrel hfrel))
  | Ok p =>
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨lst1, hrun1, hrel1, hwf1, hpWF⟩ :=
      (annot_pw_lam_i_refines hw hd i hl).apply hwf hfe h1 hrel hfrel
    obtain ⟨hr, hst⟩ := hok
    subst hst
    subst hr
    refine ⟨lst1, ?_, hrel1, hwf1, ?_⟩
    · rw [ConLeche.Cached.annotateLamsPwI, ← hiv]
      simp only [StateT.run] at hrun1
      simp [hrun1]
    · intro q hq; rw [Option.some.injEq] at hq; rw [← hq]; exact hpWF

/-! ## The two leaf phases

`annotatePisLeafI`/`annotateLamsLeafI`: bulk-open the residual body against the
accumulated free variables, annotate it once, compute the telescope's datum,
and rebuild outward with one `abstractRange` over the leaf and one per
domain. -/

/-- `instListRevM` at the port's `Vec` accumulator: `instantiateRev_spec` reads
the cited definition as `Expr.instantiateList` on the reversed list, which is
what `Refine/ExprOpsCSubst.lean` refines `expr_ops_c::instantiate_rev` to. -/
theorem instantiateRev_absExprArr (e : ConLeche.Expr) (vs : alloc.vec.Vec expr.Expr)
    (d : Nat) :
    ConLeche.Cached.ExprC.instantiateRev e (absExprArr vs) d
      = ConLeche.Expr.instantiateList e (absExprs vs).reverse d := by
  rw [ConLeche.Cached.ExprC.instantiateRev_spec]
  simp [absExprArr]

theorem annotatePisLeafI_eq (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv)
    (d : Nat) (t : ConLeche.Expr) (k : Nat) (fvs : Array ConLeche.Expr)
    (stk : List ConLeche.Cached.AnnotBinderEntry) :
    ConLeche.Cached.annotatePisLeafI r fe d t k fvs stk = (do
      let leaf' ← r.annotate (d + k) (ConLeche.Cached.ExprC.instantiateRev t fvs 0)
      let pw? ← ConLeche.Cached.annotatePisPwI r fe d k leaf'
      ConLeche.Cached.annotateBindersOutI (mkNode true) d pw? stk (k - 1)
        (ConLeche.Cached.ExprC.abstractRange leaf' d k)) := rfl

theorem annotateLamsLeafI_eq (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv)
    (d : Nat) (t : ConLeche.Expr) (k : Nat) (fvs : Array ConLeche.Expr)
    (stk : List ConLeche.Cached.AnnotBinderEntry) :
    ConLeche.Cached.annotateLamsLeafI r fe d t k fvs stk = (do
      let leaf' ← r.annotate (d + k) (ConLeche.Cached.ExprC.instantiateRev t fvs 0)
      let pw? ← ConLeche.Cached.annotateLamsPwI r fe d k leaf'
      ConLeche.Cached.annotateBindersOutI (mkNode false) d pw? stk (k - 1)
        (ConLeche.Cached.ExprC.abstractRange leaf' d k)) := rfl

/-- `ConLeche/Cached/CoreC.lean:1706` — **`annotate_pis_leaf_i` refines
`annotatePisLeafI`** (`core_c.rs:4475`). -/
theorem annotate_pis_leaf_i_refines (hw : Wrappers mode fuel)
    (hd : AnnotateDeps mode fuel) (d : Std.U64) {t : expr.Expr} (ht : ExprWF t)
    (k : Std.U64) {fvs : alloc.vec.Vec expr.Expr} (hfvs : ExprsWF fvs)
    {stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} (hstk : StkWF stk) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.annotate_pis_leaf_i mode fuel st fe d t k fvs stk)
      (fun lfe => ConLeche.Cached.annotatePisLeafI (knot mode lfe fuel.val) lfe d.val
        (absExpr t) k.val (absExprArr fvs) (absStk stk)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  unfold cached.core_c.annotate_pis_leaf_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨tO, hto, hok⟩ := hok
  obtain ⟨habsTo, hwfTo⟩ := ExprOpsC.instantiate_rev_refines ht hfvs
    (by rw [StateC.inst_list_rev_m_eq] at hto; exact hto)
  rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac] at habsTo
  obtain ⟨i, hi, hok⟩ := hok
  have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp only [uncurry_apply_pair] at hok
    simp at hok
    obtain ⟨hr, -⟩ := hok
    subst hr
    rw [annotatePisLeafI_eq, instantiateRev_absExprArr, ← habsTo, ← hiv]
    exact Out.err (ErrSim.bindCM ((hw.annotateSim i hwfTo).apply_err hwf hfe h1 hrel hfrel))
  | Ok leaf2 =>
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
    obtain ⟨lst1, hrun1, hrel1, hwf1, hleafWF⟩ :=
      (hw.annotateSim i hwfTo).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
    cases r1 with
    | Err err =>
      simp only [uncurry_apply_pair] at hok
      simp at hok
      obtain ⟨hr, -⟩ := hok
      subst hr
      rw [annotatePisLeafI_eq, instantiateRev_absExprArr, ← habsTo, ← hiv,
        bind_run hrun1]
      exact Out.err (ErrSim.bindCM
        ((annotate_pis_pw_i_refines hw hd d k hleafWF).apply_err hwf1 hfe h2 hrel1 hfrel))
    | Ok pw =>
      simp only [uncurry_apply_pair, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨lst2, hrun2, hrel2, hwf2, hpwWF⟩ :=
        (annotate_pis_pw_i_refines hw hd d k hleafWF).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨cur, hcur, i2, hi2, e, he, hr, hst⟩ := hok
      obtain ⟨habsCur, hwfCur⟩ := ExprOpsC.abstract_range_refines hleafWF
        (by rw [StateC.abstract_range_m_eq] at hcur; exact hcur)
      rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac] at habsCur
      have hi2v : i2.val = k.val - 1 := ExprOps.sub_nat_val hi2
      have hlenv : (alloc.vec.Vec.len stk).val = stk.val.length :=
        alloc.vec.Vec.len_val stk
      obtain ⟨habsE, hwfE⟩ :=
        annotate_binders_out_i_refines true d stk.val.length pw stk
          (alloc.vec.Vec.len stk) i2 cur hlenv (by omega) hpwWF hstk hwfCur e he
      subst hst
      subst hr
      refine ⟨lst2, ?_, hrel2, hwf2, hwfE⟩
      simp only [StateT.run] at hrun1 hrun2 ⊢
      rw [annotatePisLeafI_eq, instantiateRev_absExprArr, ← habsTo]
      simp only [Bind.bind, StateT.bind, Except.bind, ← hiv, hrun1, hrun2]
      rw [hlenv, hi2v, ← absStk] at habsE
      rw [← habsCur, ← habsE]
      rfl

/-- `ConLeche/Cached/CoreC.lean:1755` — **`annotate_lams_leaf_i` refines
`annotateLamsLeafI`** (`core_c.rs:4609`), the λ twin. -/
theorem annotate_lams_leaf_i_refines (hw : Wrappers mode fuel)
    (hd : AnnotateDeps mode fuel) (d : Std.U64) {t : expr.Expr} (ht : ExprWF t)
    (k : Std.U64) {fvs : alloc.vec.Vec expr.Expr} (hfvs : ExprsWF fvs)
    {stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} (hstk : StkWF stk) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.annotate_lams_leaf_i mode fuel st fe d t k fvs stk)
      (fun lfe => ConLeche.Cached.annotateLamsLeafI (knot mode lfe fuel.val) lfe d.val
        (absExpr t) k.val (absExprArr fvs) (absStk stk)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  unfold cached.core_c.annotate_lams_leaf_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨tO, hto, hok⟩ := hok
  obtain ⟨habsTo, hwfTo⟩ := ExprOpsC.instantiate_rev_refines ht hfvs
    (by rw [StateC.inst_list_rev_m_eq] at hto; exact hto)
  rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac] at habsTo
  obtain ⟨i, hi, hok⟩ := hok
  have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp only [uncurry_apply_pair] at hok
    simp at hok
    obtain ⟨hr, -⟩ := hok
    subst hr
    rw [annotateLamsLeafI_eq, instantiateRev_absExprArr, ← habsTo, ← hiv]
    exact Out.err (ErrSim.bindCM ((hw.annotateSim i hwfTo).apply_err hwf hfe h1 hrel hfrel))
  | Ok leaf2 =>
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
    obtain ⟨lst1, hrun1, hrel1, hwf1, hleafWF⟩ :=
      (hw.annotateSim i hwfTo).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
    cases r1 with
    | Err err =>
      simp only [uncurry_apply_pair] at hok
      simp at hok
      obtain ⟨hr, -⟩ := hok
      subst hr
      rw [annotateLamsLeafI_eq, instantiateRev_absExprArr, ← habsTo, ← hiv,
        bind_run hrun1]
      exact Out.err (ErrSim.bindCM
        ((annotate_lams_pw_i_refines hw hd d k hleafWF).apply_err hwf1 hfe h2 hrel1 hfrel))
    | Ok pw =>
      simp only [uncurry_apply_pair, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨lst2, hrun2, hrel2, hwf2, hpwWF⟩ :=
        (annotate_lams_pw_i_refines hw hd d k hleafWF).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨cur, hcur, i2, hi2, e, he, hr, hst⟩ := hok
      obtain ⟨habsCur, hwfCur⟩ := ExprOpsC.abstract_range_refines hleafWF
        (by rw [StateC.abstract_range_m_eq] at hcur; exact hcur)
      rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac] at habsCur
      have hi2v : i2.val = k.val - 1 := ExprOps.sub_nat_val hi2
      have hlenv : (alloc.vec.Vec.len stk).val = stk.val.length :=
        alloc.vec.Vec.len_val stk
      obtain ⟨habsE, hwfE⟩ :=
        annotate_binders_out_i_refines false d stk.val.length pw stk
          (alloc.vec.Vec.len stk) i2 cur hlenv (by omega) hpwWF hstk hwfCur e he
      subst hst
      subst hr
      refine ⟨lst2, ?_, hrel2, hwf2, hwfE⟩
      simp only [StateT.run] at hrun1 hrun2 ⊢
      rw [annotateLamsLeafI_eq, instantiateRev_absExprArr, ← habsTo]
      simp only [Bind.bind, StateT.bind, Except.bind, ← hiv, hrun1, hrun2]
      rw [hlenv, hi2v, ← absStk] at habsE
      rw [← habsCur, ← habsE]
      rfl

/-! ## The two peel loops

`annotatePisI`/`annotateLamsI` peel the raw binder chain, annotating each
opened domain on the way in.  The `peel` budget is a `U64` in the port and a
`Nat` in con-leche, and it is *semantically transparent*: on exhaustion the
leaf phase hands the residual chain back to the knot.  The induction is on
`peel.val`. -/

theorem annotatePisI_zero (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv)
    (d : Nat) (t : ConLeche.Expr) (k : Nat) (fvs : Array ConLeche.Expr)
    (stk : List ConLeche.Cached.AnnotBinderEntry) :
    ConLeche.Cached.annotatePisI r fe d 0 t k fvs stk
      = ConLeche.Cached.annotatePisLeafI r fe d t k fvs stk := rfl

theorem annotatePisI_succ_leaf (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv)
    (d n : Nat) (t : ConLeche.Expr) (k : Nat) (fvs : Array ConLeche.Expr)
    (stk : List ConLeche.Cached.AnnotBinderEntry)
    (h : ∀ ty body mb, t ≠ ConLeche.Expr.forallE ty body mb) :
    ConLeche.Cached.annotatePisI r fe d (n + 1) t k fvs stk
      = ConLeche.Cached.annotatePisLeafI r fe d t k fvs stk := by
  cases t with
  | forallE ty body mb => exact absurd rfl (h ty body mb)
  | _ => rfl

theorem annotatePisI_succ_forallE (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv)
    (d n : Nat) (ty body : ConLeche.Expr) (mb : ConLeche.BinderMeta) (k : Nat)
    (fvs : Array ConLeche.Expr) (stk : List ConLeche.Cached.AnnotBinderEntry) :
    ConLeche.Cached.annotatePisI r fe d (n + 1) (.forallE ty body mb) k fvs stk = (do
      let ty' ← r.annotate (d + k) (ConLeche.Cached.ExprC.instantiateRev ty fvs 0)
      ConLeche.Cached.annotatePisI r fe d n body (k + 1)
        (fvs.push (ConLeche.Expr.fvar (d + k) ty')) ((ty', mb) :: stk)) := rfl

theorem annotateLamsI_zero (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv)
    (d : Nat) (t : ConLeche.Expr) (k : Nat) (fvs : Array ConLeche.Expr)
    (stk : List ConLeche.Cached.AnnotBinderEntry) :
    ConLeche.Cached.annotateLamsI r fe d 0 t k fvs stk
      = ConLeche.Cached.annotateLamsLeafI r fe d t k fvs stk := rfl

theorem annotateLamsI_succ_leaf (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv)
    (d n : Nat) (t : ConLeche.Expr) (k : Nat) (fvs : Array ConLeche.Expr)
    (stk : List ConLeche.Cached.AnnotBinderEntry)
    (h : ∀ ty body mb, t ≠ ConLeche.Expr.lam ty body mb) :
    ConLeche.Cached.annotateLamsI r fe d (n + 1) t k fvs stk
      = ConLeche.Cached.annotateLamsLeafI r fe d t k fvs stk := by
  cases t with
  | lam ty body mb => exact absurd rfl (h ty body mb)
  | _ => rfl

theorem annotateLamsI_succ_lam (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv)
    (d n : Nat) (ty body : ConLeche.Expr) (mb : ConLeche.BinderMeta) (k : Nat)
    (fvs : Array ConLeche.Expr) (stk : List ConLeche.Cached.AnnotBinderEntry) :
    ConLeche.Cached.annotateLamsI r fe d (n + 1) (.lam ty body mb) k fvs stk = (do
      let ty' ← r.annotate (d + k) (ConLeche.Cached.ExprC.instantiateRev ty fvs 0)
      ConLeche.Cached.annotateLamsI r fe d n body (k + 1)
        (fvs.push (ConLeche.Expr.fvar (d + k) ty')) ((ty', mb) :: stk)) := rfl

/-- `ConLeche/Cached/CoreC.lean:1719` — **`annotate_pis_i` refines
`annotatePisI`** (`core_c.rs:4513`): the ∀-telescope annotation loop.  `k ≥ 1`
counts the opened binders (the caller peels the first inline), `fvs` their free
variables; the induction is on the peel budget. -/
theorem annotate_pis_i_refines (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (d : Std.U64) :
    ∀ (N : Nat) (peel : Std.U64) (t : expr.Expr) (k : Std.U64)
      (fvs : alloc.vec.Vec expr.Expr)
      (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)),
      peel.val = N → ExprWF t → ExprsWF fvs → StkWF stk →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.annotate_pis_i mode fuel st fe d peel t k fvs stk)
        (fun lfe => ConLeche.Cached.annotatePisI (knot mode lfe fuel.val) lfe d.val
          peel.val (absExpr t) k.val (absExprArr fvs) (absStk stk)) := by
  intro N
  induction N with
  | zero =>
    intro peel t k fvs stk hpeel ht hfvs hstk fe lfe hfe hfrel st r st' hwf hok lst hrel
    dsimp only at hok ⊢
    unfold cached.core_c.annotate_pis_i at hok
    rw [if_pos (show peel = 0#u64 by scalar_tac)] at hok
    rw [hpeel, annotatePisI_zero]
    exact annotate_pis_leaf_i_refines hw hd d ht k hfvs hstk fe lfe hfe hfrel st r st'
      hwf hok lst hrel
  | succ N ih =>
    intro peel t k fvs stk hpeel ht hfvs hstk fe lfe hfe hfrel st r st' hwf hok lst hrel
    dsimp only at hok ⊢
    unfold cached.core_c.annotate_pis_i at hok
    rw [if_neg (show ¬ peel = 0#u64 by scalar_tac)] at hok
    rw [hpeel]
    have leafCase : ∀ (t0 : expr.Expr), ExprWF t0 →
        (∀ ty body mb, absExpr t0 ≠ ConLeche.Expr.forallE ty body mb) →
        cached.core_c.annotate_pis_leaf_i mode fuel st fe d t0 k fvs stk = ok (r, st') →
        Out absExpr ExprWF r st'
          ((ConLeche.Cached.annotatePisI (knot mode lfe fuel.val) lfe d.val
            (N + 1) (absExpr t0) k.val (absExprArr fvs) (absStk stk)).run lst) := by
      intro t0 ht0 hne hok0
      rw [annotatePisI_succ_leaf _ _ _ _ _ _ _ _ hne]
      exact annotate_pis_leaf_i_refines hw hd d ht0 k hfvs hstk fe lfe hfe hfrel st r st'
        hwf hok0 lst hrel
    cases ht with
    | @forall_e ty body mb e hty hbody hmb h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.forall_e_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, 
        bind_eq_ok_iff, absExpr_mk, absExprKind] at hok ⊢
      obtain ⟨body1, hbody1, hok⟩ := hok
      rw [Expr.dup_eq hbody1] at hok
      obtain ⟨mb1, hmb1, hok⟩ := hok
      rw [Expr.binder_meta_dup_eq hmb1] at hok
      obtain ⟨tyo, htyo, hok⟩ := hok
      obtain ⟨habsTyo, hwfTyo⟩ := ExprOpsC.instantiate_rev_refines hty hfvs
        (by rw [StateC.inst_list_rev_m_eq] at htyo; exact htyo)
      rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac] at habsTyo
      obtain ⟨i, hi, hok⟩ := hok
      have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
      obtain ⟨⟨r0, st1⟩, h2, hok⟩ := hok
      cases r0 with
      | Err err =>
        simp only [uncurry_apply_pair] at hok
        simp at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [annotatePisI_succ_forallE, instantiateRev_absExprArr, ← habsTyo, ← hiv]
        exact Out.err
          (ErrSim.bindCM ((hw.annotateSim i hwfTyo).apply_err hwf hfe h2 hrel hfrel))
      | Ok ty2 =>
        simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
        obtain ⟨lst1, hrun1, hrel1, hwf1, hty2WF⟩ :=
          (hw.annotateSim i hwfTyo).apply hwf hfe h2 hrel hfrel
        obtain ⟨e1, he1, hok⟩ := hok
        rw [Expr.dup_eq he1] at hok
        obtain ⟨fv, hfv, hok⟩ := hok
        obtain ⟨fvs1, hfvs1, hok⟩ := hok
        obtain ⟨stk1, hstk1, hok⟩ := hok
        obtain ⟨i1, hi1, hok⟩ := hok
        obtain ⟨i2, hi2, hok⟩ := hok
        have hi1v : i1.val = N := by
          have hs := HashMap.uscalar_sub_eq hi1
          have h1' : (1#u64 : Std.U64).val = 1 := by scalar_tac
          omega
        have hi2v : i2.val = k.val + 1 := HashMap.uscalar_add_eq hi2
        have hout := ih i1 body i2 fvs1 stk1 hi1v hbody
            (ExprsWF_push hfvs (Expr.fvar_wf hty2WF hfv) hfvs1)
            (StkWF_push hstk hty2WF hmb hstk1) fe lfe hfe hfrel st1 r st' hwf1 hok lst1 hrel1
        simp only [StateT.run] at hrun1 hout ⊢
        rw [absExprArr_push hfvs1, Expr.fvar_refines hfv, absStk_push hstk1, hi1v,
          hi2v] at hout
        rw [annotatePisI_succ_forallE, instantiateRev_absExprArr, ← habsTyo, ← hiv]
        simp only [Bind.bind, StateT.bind, Except.bind, hrun1]
        exact hout
    | @bvar i e h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.bvar_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.bvar h1) (by simp) hok
    | @fvar idx ty e hty h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.fvar_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.fvar hty h1) (by simp) hok
    | @sort u e hu h1 =>
      obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.sort hu h1) (by simp) hok
    | @mk_const n us e hn hus h1 =>
      obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.mk_const hn hus h1) (by simp) hok
    | @app f a e hf ha h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.app_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.app hf ha h1) (by simp) hok
    | @lam ty bo m e hty hbo hm h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.lam_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.lam hty hbo hm h1) (by simp) hok
    | @let_e ty v bo e hty hv hbo h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.let_e_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.let_e hty hv hbo h1) (by simp) hok
    | @lit l e hl h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.lit_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.lit hl h1) (by simp) hok
    | @proj sn idx x e hsn hx h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.proj_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.proj hsn hx h1) (by simp) hok

/-- `ConLeche/Cached/CoreC.lean:1766` — **`annotate_lams_i` refines
`annotateLamsI`** (`core_c.rs:4644`), the λ twin of `annotate_pis_i`. -/
theorem annotate_lams_i_refines (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (d : Std.U64) :
    ∀ (N : Nat) (peel : Std.U64) (t : expr.Expr) (k : Std.U64)
      (fvs : alloc.vec.Vec expr.Expr)
      (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)),
      peel.val = N → ExprWF t → ExprsWF fvs → StkWF stk →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.annotate_lams_i mode fuel st fe d peel t k fvs stk)
        (fun lfe => ConLeche.Cached.annotateLamsI (knot mode lfe fuel.val) lfe d.val
          peel.val (absExpr t) k.val (absExprArr fvs) (absStk stk)) := by
  intro N
  induction N with
  | zero =>
    intro peel t k fvs stk hpeel ht hfvs hstk fe lfe hfe hfrel st r st' hwf hok lst hrel
    dsimp only at hok ⊢
    unfold cached.core_c.annotate_lams_i at hok
    rw [if_pos (show peel = 0#u64 by scalar_tac)] at hok
    rw [hpeel, annotateLamsI_zero]
    exact annotate_lams_leaf_i_refines hw hd d ht k hfvs hstk fe lfe hfe hfrel st r st'
      hwf hok lst hrel
  | succ N ih =>
    intro peel t k fvs stk hpeel ht hfvs hstk fe lfe hfe hfrel st r st' hwf hok lst hrel
    dsimp only at hok ⊢
    unfold cached.core_c.annotate_lams_i at hok
    rw [if_neg (show ¬ peel = 0#u64 by scalar_tac)] at hok
    rw [hpeel]
    have leafCase : ∀ (t0 : expr.Expr), ExprWF t0 →
        (∀ ty body mb, absExpr t0 ≠ ConLeche.Expr.lam ty body mb) →
        cached.core_c.annotate_lams_leaf_i mode fuel st fe d t0 k fvs stk = ok (r, st') →
        Out absExpr ExprWF r st'
          ((ConLeche.Cached.annotateLamsI (knot mode lfe fuel.val) lfe d.val
            (N + 1) (absExpr t0) k.val (absExprArr fvs) (absStk stk)).run lst) := by
      intro t0 ht0 hne hok0
      rw [annotateLamsI_succ_leaf _ _ _ _ _ _ _ _ hne]
      exact annotate_lams_leaf_i_refines hw hd d ht0 k hfvs hstk fe lfe hfe hfrel st r st'
        hwf hok0 lst hrel
    cases ht with
    | @lam ty body mb e hty hbody hmb h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.lam_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, 
        bind_eq_ok_iff, absExpr_mk, absExprKind] at hok ⊢
      obtain ⟨body1, hbody1, hok⟩ := hok
      rw [Expr.dup_eq hbody1] at hok
      obtain ⟨mb1, hmb1, hok⟩ := hok
      rw [Expr.binder_meta_dup_eq hmb1] at hok
      obtain ⟨tyo, htyo, hok⟩ := hok
      obtain ⟨habsTyo, hwfTyo⟩ := ExprOpsC.instantiate_rev_refines hty hfvs
        (by rw [StateC.inst_list_rev_m_eq] at htyo; exact htyo)
      rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac] at habsTyo
      obtain ⟨i, hi, hok⟩ := hok
      have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
      obtain ⟨⟨r0, st1⟩, h2, hok⟩ := hok
      cases r0 with
      | Err err =>
        simp only [uncurry_apply_pair] at hok
        simp at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [annotateLamsI_succ_lam, instantiateRev_absExprArr, ← habsTyo, ← hiv]
        exact Out.err
          (ErrSim.bindCM ((hw.annotateSim i hwfTyo).apply_err hwf hfe h2 hrel hfrel))
      | Ok ty2 =>
        simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
        obtain ⟨lst1, hrun1, hrel1, hwf1, hty2WF⟩ :=
          (hw.annotateSim i hwfTyo).apply hwf hfe h2 hrel hfrel
        obtain ⟨e1, he1, hok⟩ := hok
        rw [Expr.dup_eq he1] at hok
        obtain ⟨fv, hfv, hok⟩ := hok
        obtain ⟨fvs1, hfvs1, hok⟩ := hok
        obtain ⟨stk1, hstk1, hok⟩ := hok
        obtain ⟨i1, hi1, hok⟩ := hok
        obtain ⟨i2, hi2, hok⟩ := hok
        have hi1v : i1.val = N := by
          have hs := HashMap.uscalar_sub_eq hi1
          have h1' : (1#u64 : Std.U64).val = 1 := by scalar_tac
          omega
        have hi2v : i2.val = k.val + 1 := HashMap.uscalar_add_eq hi2
        have hout := ih i1 body i2 fvs1 stk1 hi1v hbody
            (ExprsWF_push hfvs (Expr.fvar_wf hty2WF hfv) hfvs1)
            (StkWF_push hstk hty2WF hmb hstk1) fe lfe hfe hfrel st1 r st' hwf1 hok lst1 hrel1
        simp only [StateT.run] at hrun1 hout ⊢
        rw [absExprArr_push hfvs1, Expr.fvar_refines hfv, absStk_push hstk1, hi1v,
          hi2v] at hout
        rw [annotateLamsI_succ_lam, instantiateRev_absExprArr, ← habsTyo, ← hiv]
        simp only [Bind.bind, StateT.bind, Except.bind, hrun1]
        exact hout
    | @bvar i e h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.bvar_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.bvar h1) (by simp) hok
    | @fvar idx ty e hty h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.fvar_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.fvar hty h1) (by simp) hok
    | @sort u e hu h1 =>
      obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.sort hu h1) (by simp) hok
    | @mk_const n us e hn hus h1 =>
      obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.mk_const hn hus h1) (by simp) hok
    | @app f a e hf ha h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.app_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.app hf ha h1) (by simp) hok
    | @forall_e ty bo m e hty hbo hm h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.forall_e_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.forall_e hty hbo hm h1) (by simp) hok
    | @let_e ty v bo e hty hv hbo h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.let_e_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.let_e hty hv hbo h1) (by simp) hok
    | @lit l e hl h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.lit_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.lit hl h1) (by simp) hok
    | @proj sn idx x e hsn hx h1 =>
      obtain ⟨dd, rfl, -, -, -⟩ := Expr.proj_inv h1
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
      exact leafCase _ (ExprWF.proj hsn hx h1) (by simp) hok

/-! ## `annotateBodyI`'s arms, one clause each

The Rust splits `annotateBodyI`'s `match` into five named functions
(`annotate_forall_i`, `annotate_lam_loop_i`, `annotate_lam_chain_i`,
`annotate_let_i`, `annotate_proj_i`), so each of those is stated against
`annotateBodyI` *at the node the arm was reached on*.  These are the clauses,
transcribed and closed by `rfl`. -/

section Clauses
variable (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv) (depth : Nat)

theorem annotateBodyI_bvar (i : Nat) :
    ConLeche.Cached.annotateBodyI r fe depth (.bvar i) = pure (.bvar i) := rfl

theorem annotateBodyI_fvar (idx : Nat) (ty : ConLeche.Expr) :
    ConLeche.Cached.annotateBodyI r fe depth (.fvar idx ty)
      = (if idx < depth then pure (.fvar idx ty)
         else throw (.invalid "free variable out of scope")) := rfl

theorem annotateBodyI_sort (u : ConLeche.Level) :
    ConLeche.Cached.annotateBodyI r fe depth (.sort u) = pure (.sort u) := rfl

theorem annotateBodyI_const (n : ConLeche.Name) (us : List ConLeche.Level) :
    ConLeche.Cached.annotateBodyI r fe depth (.const n us) = pure (.const n us) := rfl

theorem annotateBodyI_natLit (n : Nat) :
    ConLeche.Cached.annotateBodyI r fe depth (.lit (.natVal n))
      = (if ConLeche.natLitSupportedF fe then pure (.lit (.natVal n))
         else throw (.invalid "Nat literal without the Nat basis declarations")) := rfl

theorem annotateBodyI_strLit (str : String) :
    ConLeche.Cached.annotateBodyI r fe depth (.lit (.strVal str))
      = (if ConLeche.strLitSupportedF fe then pure (.lit (.strVal str))
         else throw (.notImplemented
           "string literals before the String support declarations")) := rfl

theorem annotateBodyI_app (f a : ConLeche.Expr) :
    ConLeche.Cached.annotateBodyI r fe depth (.app f a) = (do
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      pure (ConLeche.Expr.app f' a')) := rfl

theorem annotateBodyI_forallE (ty body : ConLeche.Expr) (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.annotateBodyI r fe depth (.forallE ty body mb) = (do
      let ty' ← r.annotate depth ty
      ConLeche.Cached.annotatePisI r fe depth ConLeche.Cached.peelFuel body 1
        #[ConLeche.Expr.fvar depth ty'] [(ty', mb)]) := rfl

theorem annotateBodyI_lam (ty body : ConLeche.Expr) (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.annotateBodyI r fe depth (.lam ty body mb) = (do
      let bb ← ConLeche.Cached.bvarBoundM (ConLeche.Expr.lam ty body mb)
      if bb = 0 then (do
            let ty' ← r.annotate depth ty
            ConLeche.Cached.annotateLamsI r fe depth ConLeche.Cached.peelFuel body 1
              #[ConLeche.Expr.fvar depth ty'] [(ty', mb)])
          else (do
            let ty' ← r.annotate depth ty
            let body' ← r.annotate (depth + 1)
              (ConLeche.Cached.ExprC.instantiate1 body (ConLeche.Expr.fvar depth ty') 0)
            let pw ← if !ConLeche.pwWritten mb.pw then
                ConLeche.Cached.annotPwLamI r fe (depth + 1) body'
              else pure mb.pw
            pure (ConLeche.Expr.lam ty'
              (ConLeche.Cached.ExprC.abstract1 body' depth) ⟨pw⟩))) := rfl

theorem annotateBodyI_letE (ty v b : ConLeche.Expr) :
    ConLeche.Cached.annotateBodyI r fe depth (.letE ty v b) = (do
      let ty' ← r.annotate depth ty
      let tty ← r.infer depth ty'
      let _ ← ConLeche.Cached.ensureSortI r depth tty
      let v' ← r.annotate depth v
      let tv ← r.infer depth v'
      unless ← r.defeq depth tv ty' do
        throw (.invalid "let value type mismatch")
      r.annotate depth (ConLeche.Cached.ExprC.instantiate1 b v 0)) := rfl

theorem annotateBodyI_proj (sn : ConLeche.Name) (i : Nat) (pe : ConLeche.Expr) :
    ConLeche.Cached.annotateBodyI r fe depth (.proj sn i pe) = (do
      let e' ← r.annotate depth pe
      let tpe ← r.inferIO depth e'
      let te ← r.whnf depth tpe
      match ConLeche.Cached.ExprC.getAppFn te with
      | .const T _ => do
        match fe.findProj? T i with
        | some entry => do
          unless T = sn do
            throw (.invalid "invalid projection: the node names another structure")
          unless (ConLeche.Cached.ExprC.getAppArgs te).length = entry.numParams do
            throw (.invalid "projection parameter mismatch")
          pure (ConLeche.Expr.proj T i e')
        | none =>
          throw (if (fe.findProj? T 0).isSome then
              ConLeche.CheckError.invalid "projection index out of range"
            else .notImplemented "projection on a non-structure-like type")
      | _ => throw (.notImplemented "projection on a non-structure type")) := rfl

/-- `bvarBoundM` is an `O(1)` field read (`pure e.bvarB`), so the `do`-bind
that guards the two λ routes *is* the `if` on the bound.  Stated over abstract
branches: at the concrete ones the kernel would have to normalise `peelFuel`
(16777216) through the structural recursion of `annotateLamsI`. -/
theorem bvarBoundM_split {α : Type} (e : ConLeche.Expr)
    (A B : ConLeche.Cached.CheckCM α) :
    (do let bb ← ConLeche.Cached.bvarBoundM e; if bb = 0 then A else B)
      = (if e.bvarB = 0 then A else B) := rfl

/-- The `.lam` clause with the `bvarBoundM` read discharged: the `O(1)` cached
bound decides which λ route the pass takes (the λ-loop is chain-identical only
on bvar-closed nodes). -/
theorem annotateBodyI_lam_split (ty body : ConLeche.Expr) (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.annotateBodyI r fe depth (.lam ty body mb)
      = (if (ConLeche.Expr.lam ty body mb).bvarB = 0 then (do
            let ty' ← r.annotate depth ty
            ConLeche.Cached.annotateLamsI r fe depth ConLeche.Cached.peelFuel body 1
              #[ConLeche.Expr.fvar depth ty'] [(ty', mb)])
          else (do
            let ty' ← r.annotate depth ty
            let body' ← r.annotate (depth + 1)
              (ConLeche.Cached.ExprC.instantiate1 body (ConLeche.Expr.fvar depth ty') 0)
            let pw ← if !ConLeche.pwWritten mb.pw then
                ConLeche.Cached.annotPwLamI r fe (depth + 1) body'
              else pure mb.pw
            pure (ConLeche.Expr.lam ty'
              (ConLeche.Cached.ExprC.abstract1 body' depth) ⟨pw⟩))) := by
  rw [annotateBodyI_lam, bvarBoundM_split]

end Clauses

/-! ## The empty accumulators (the ∀/λ clauses start the telescope at one) -/

@[simp] theorem absExprArr_new : absExprArr (alloc.vec.Vec.new expr.Expr) = #[] := by
  simp [absExprArr, absExprs, alloc.vec.Vec.new]

@[simp] theorem absStk_new :
    absStk (alloc.vec.Vec.new (expr.Expr × expr.BinderMeta)) = [] := by
  simp [absStk, absStkTake, alloc.vec.Vec.new]

theorem exprsWF_new : ExprsWF (alloc.vec.Vec.new expr.Expr) := by
  intro x hx; simp [alloc.vec.Vec.new] at hx

theorem stkWF_new : StkWF (alloc.vec.Vec.new (expr.Expr × expr.BinderMeta)) := by
  intro x hx; simp [alloc.vec.Vec.new] at hx

/-! ## `annotateBodyI`'s five Rust-only arms -/

/-- `ConLeche/Cached/CoreC.lean:1779-1867` — **`annotate_forall_i` refines the
`.forallE` clause of `annotateBodyI`** (`core_c.rs:4778`): annotate the first
domain inline, then peel the whole chain with `annotate_pis_i`. -/
theorem annotate_forall_i_refines (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (depth : Std.U64) {ty body : expr.Expr} {mb : expr.BinderMeta}
    (hty : ExprWF ty) (hbody : ExprWF body) (hmb : BinderMetaWF mb) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.annotate_forall_i mode fuel st fe depth ty body mb)
      (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe depth.val
        (.forallE (absExpr ty) (absExpr body) (absBinderMeta mb))) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  unfold cached.core_c.annotate_forall_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp only [uncurry_apply_pair] at hok
    simp at hok
    obtain ⟨hr, -⟩ := hok
    subst hr
    rw [annotateBodyI_forallE]
    exact Out.err
      (ErrSim.bindCM ((hw.annotateSim depth hty).apply_err hwf hfe h1 hrel hfrel))
  | Ok ty2 =>
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
    obtain ⟨lst1, hrun1, hrel1, hwf1, hty2WF⟩ :=
      (hw.annotateSim depth hty).apply hwf hfe h1 hrel hfrel
    obtain ⟨e1, he1, hok⟩ := hok
    rw [Expr.dup_eq he1] at hok
    obtain ⟨fv, hfv, hok⟩ := hok
    obtain ⟨fvs, hfvs, hok⟩ := hok
    obtain ⟨bm, hbm, hok⟩ := hok
    rw [Expr.binder_meta_dup_eq hbm] at hok
    obtain ⟨stk, hstk, hok⟩ := hok
    obtain ⟨i, hi, hok⟩ := hok
    have hiv : i.val = ConLeche.Cached.peelFuel := StateC.peel_fuel_refines hi
    have hout := annotate_pis_i_refines hw hd depth i.val i body 1#u64 fvs stk rfl hbody
        (ExprsWF_push exprsWF_new (Expr.fvar_wf hty2WF hfv) hfvs)
        (StkWF_push stkWF_new hty2WF hmb hstk) fe lfe hfe hfrel st1 r st' hwf1 hok lst1 hrel1
    simp only [StateT.run] at hrun1 hout ⊢
    rw [absExprArr_push hfvs, Expr.fvar_refines hfv, absStk_push hstk, hiv,
      show (1#u64 : Std.U64).val = 1 from by scalar_tac, absExprArr_new,
      absStk_new] at hout
    rw [annotateBodyI_forallE]
    simp only [Bind.bind, StateT.bind, Except.bind, hrun1]
    exact hout

/-- `ConLeche/Cached/CoreC.lean:1779-1867` — **`annotate_lam_loop_i` refines the
bvar-closed branch of `annotateBodyI`'s `.lam` clause** (`core_c.rs:4817`).  The
`bvarBoundM e = 0` test is the Rust's own `state_c::bvar_bound_m` read, which
the caller (`annotate_body_i`) discharges. -/
theorem annotate_lam_loop_i_refines (hw : Wrappers mode fuel)
    (hd : AnnotateDeps mode fuel) (depth : Std.U64) {ty body : expr.Expr}
    {mb : expr.BinderMeta} (hty : ExprWF ty) (hbody : ExprWF body)
    (hmb : BinderMetaWF mb)
    (hbb : (ConLeche.Expr.lam (absExpr ty) (absExpr body) (absBinderMeta mb)).bvarB
      = 0) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.annotate_lam_loop_i mode fuel st fe depth ty body mb)
      (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe depth.val
        (.lam (absExpr ty) (absExpr body) (absBinderMeta mb))) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  unfold cached.core_c.annotate_lam_loop_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp only [uncurry_apply_pair] at hok
    simp at hok
    obtain ⟨hr, -⟩ := hok
    subst hr
    rw [annotateBodyI_lam_split, if_pos hbb]
    exact Out.err
      (ErrSim.bindCM ((hw.annotateSim depth hty).apply_err hwf hfe h1 hrel hfrel))
  | Ok ty2 =>
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
    obtain ⟨lst1, hrun1, hrel1, hwf1, hty2WF⟩ :=
      (hw.annotateSim depth hty).apply hwf hfe h1 hrel hfrel
    obtain ⟨e1, he1, hok⟩ := hok
    rw [Expr.dup_eq he1] at hok
    obtain ⟨fv, hfv, hok⟩ := hok
    obtain ⟨fvs, hfvs, hok⟩ := hok
    obtain ⟨bm, hbm, hok⟩ := hok
    rw [Expr.binder_meta_dup_eq hbm] at hok
    obtain ⟨stk, hstk, hok⟩ := hok
    obtain ⟨i, hi, hok⟩ := hok
    have hiv : i.val = ConLeche.Cached.peelFuel := StateC.peel_fuel_refines hi
    have hout := annotate_lams_i_refines hw hd depth i.val i body 1#u64 fvs stk rfl hbody
        (ExprsWF_push exprsWF_new (Expr.fvar_wf hty2WF hfv) hfvs)
        (StkWF_push stkWF_new hty2WF hmb hstk) fe lfe hfe hfrel st1 r st' hwf1 hok lst1 hrel1
    simp only [StateT.run] at hrun1 hout ⊢
    rw [absExprArr_push hfvs, Expr.fvar_refines hfv, absStk_push hstk, hiv,
      show (1#u64 : Std.U64).val = 1 from by scalar_tac, absExprArr_new,
      absStk_new] at hout
    rw [annotateBodyI_lam_split, if_pos hbb]
    simp only [Bind.bind, StateT.bind, Except.bind, hrun1]
    exact hout

/-- `ConLeche/Cached/CoreC.lean:1779-1867` — **`annotate_lam_chain_i` refines the
open branch of `annotateBodyI`'s `.lam` clause** (`core_c.rs:4858`): annotate the
domain, annotate the body opened at a variable of the *annotated* domain, and
write the datum unless the input carries a real one (con-leche's task #161 P5,
the λ-loop's rule at a chain of length one). -/
theorem annotate_lam_chain_i_refines (hw : Wrappers mode fuel)
    (hd : AnnotateDeps mode fuel) (depth : Std.U64) {ty body : expr.Expr}
    {mb : expr.BinderMeta} (hty : ExprWF ty) (hbody : ExprWF body)
    (hmb : BinderMetaWF mb)
    (hbb : (ConLeche.Expr.lam (absExpr ty) (absExpr body) (absBinderMeta mb)).bvarB
      ≠ 0) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.annotate_lam_chain_i mode fuel st fe depth ty body mb)
      (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe depth.val
        (.lam (absExpr ty) (absExpr body) (absBinderMeta mb))) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  unfold cached.core_c.annotate_lam_chain_i at hok
  simp only [bind_eq_ok_iff, arc_deref_eq, bind_tc_ok] at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp only [uncurry_apply_pair] at hok
    simp at hok
    obtain ⟨hr, -⟩ := hok
    subst hr
    rw [annotateBodyI_lam_split, if_neg hbb]
    exact Out.err
      (ErrSim.bindCM ((hw.annotateSim depth hty).apply_err hwf hfe h1 hrel hfrel))
  | Ok ty2 =>
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
    obtain ⟨lst1, hrun1, hrel1, hwf1, hty2WF⟩ :=
      (hw.annotateSim depth hty).apply hwf hfe h1 hrel hfrel
    obtain ⟨e1, he1, hok⟩ := hok
    rw [Expr.dup_eq he1] at hok
    obtain ⟨fv, hfv, hok⟩ := hok
    obtain ⟨ob, hob, hok⟩ := hok
    obtain ⟨habsOb, hwfOb⟩ := ExprOpsC.instantiate1_refines hbody
      (Expr.fvar_wf hty2WF hfv) (by rw [StateC.inst1_m_eq] at hob; exact hob)
    rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac, Expr.fvar_refines hfv]
      at habsOb
    obtain ⟨i, hi, hok⟩ := hok
    have hiv : i.val = depth.val + 1 := HashMap.uscalar_add_eq hi
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
    cases r1 with
    | Err err =>
      simp only [uncurry_apply_pair] at hok
      simp at hok
      obtain ⟨hr, -⟩ := hok
      subst hr
      rw [annotateBodyI_lam_split, if_neg hbb, bind_run hrun1, ← habsOb, ← hiv]
      exact Out.err
        (ErrSim.bindCM ((hw.annotateSim i hwfOb).apply_err hwf1 hfe h2 hrel1 hfrel))
    | Ok body2 =>
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
      obtain ⟨lst2, hrun2, hrel2, hwf2, hbody2WF⟩ :=
        (hw.annotateSim i hwfOb).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨bAbs, hbAbs, hok⟩ := hok
      obtain ⟨habsBAbs, hwfBAbs⟩ := ExprOpsC.abstract1_refines hbody2WF
        (by rw [StateC.abstract1_m_eq] at hbAbs; exact hbAbs)
      rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac] at habsBAbs
      obtain ⟨bw, hbw, hok⟩ := hok
      have hbwv : bw = ConLeche.pwWritten (absPropWhen mb.pw) :=
        CoreK.pw_written_refines hbw
      obtain ⟨⟨st3, pw1⟩, hbranch, hok⟩ := hok
      -- the two routes of the single-binder write, in `Sim` form
      have hbranchSim : ∀ p, pw1 = .Ok p →
          ∃ lst3, (if !ConLeche.pwWritten (absBinderMeta mb).pw then
                ConLeche.Cached.annotPwLamI (knot mode lfe fuel.val) lfe i.val
                  (absExpr body2)
              else pure (absBinderMeta mb).pw).run lst2 = .ok (absPropWhen p, lst3)
            ∧ StateRel st3 lst3 ∧ StateWF st3 ∧ PropWhenWF p := by
        intro p hp
        subst hp
        cases bw with
        | true =>
          rw [if_pos rfl] at hbranch
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq] at hbranch
          obtain ⟨q, hq, hst3, hp⟩ := hbranch
          rw [PropWhen.dup_eq hq] at hp
          refine ⟨lst2, ?_, ?_, ?_, ?_⟩
          · rw [if_neg (by simp [absBinderMeta, ← hbwv])]
            simp [← hp]
          · rw [← hst3]; exact hrel2
          · rw [← hst3]; exact hwf2
          · rw [← hp]; exact hmb
        | false =>
          rw [if_neg (by simp)] at hbranch
          simp only [bind_eq_ok_iff] at hbranch
          obtain ⟨⟨r2, st4⟩, h3, hbranch⟩ := hbranch
          simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at hbranch
          obtain ⟨hst3, hp⟩ := hbranch
          rw [hp] at h3
          obtain ⟨lst3, hrun3, hrel3, hwf3, hpWF⟩ :=
            (annot_pw_lam_i_refines hw hd i hbody2WF).apply hwf2 hfe h3 hrel2 hfrel
          refine ⟨lst3, ?_, by rw [← hst3]; exact hrel3, by rw [← hst3]; exact hwf3,
            hpWF⟩
          rw [if_pos (by simp [absBinderMeta, ← hbwv])]
          exact hrun3
      -- and the same two routes on a throw: the `pw_written` route cannot
      -- throw, the `annot_pw_lam_i` one throws what its callee threw
      have hbranchErr : ∀ e0, pw1 = .Err e0 →
          ErrSim e0 ((if !ConLeche.pwWritten (absBinderMeta mb).pw then
                ConLeche.Cached.annotPwLamI (knot mode lfe fuel.val) lfe i.val
                  (absExpr body2)
              else pure (absBinderMeta mb).pw).run lst2) := by
        intro e0 hp
        subst hp
        cases bw with
        | true =>
          rw [if_pos rfl] at hbranch
          simp only [bind_eq_ok_iff] at hbranch
          obtain ⟨q, -, hbranch⟩ := hbranch
          simp at hbranch
        | false =>
          rw [if_neg (by simp)] at hbranch
          simp only [bind_eq_ok_iff] at hbranch
          obtain ⟨⟨r2, st4⟩, h3, hbranch⟩ := hbranch
          simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at hbranch
          obtain ⟨-, hp⟩ := hbranch
          rw [hp] at h3
          rw [if_pos (by simp [absBinderMeta, ← hbwv])]
          exact (annot_pw_lam_i_refines hw hd i hbody2WF).apply_err hwf2 hfe h3 hrel2 hfrel
      cases pw1 with
      | Err err =>
        simp only [uncurry_apply_pair] at hok
        simp at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [annotateBodyI_lam_split, if_neg hbb, bind_run hrun1, ← habsOb, ← hiv,
          bind_run hrun2, ite_bind_jp]
        exact Out.err (ErrSim.bindCM (hbranchErr err rfl))
      | Ok p =>
        simp only [uncurry_apply_pair, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
          ExprOps.binder_meta_eq] at hok
        obtain ⟨lst3, hrun3, hrel3, hwf3, hpWF⟩ := hbranchSim p rfl
        obtain ⟨bm2, hbm2, e2, he2, hr, hst⟩ := hok
        subst hst
        subst hr
        refine ⟨lst3, ?_, hrel3, hwf3,
          Expr.lam_wf hty2WF hwfBAbs (by rw [← hbm2]; exact hpWF) he2⟩
        rw [annotateBodyI_lam_split, if_neg hbb, bind_run hrun1, ← habsOb, ← hiv,
          bind_run hrun2, ite_bind_jp, bind_run hrun3]
        rw [Expr.lam_refines he2, habsBAbs, ← hbm2]
        rfl

/-- `ConLeche/Cached/CoreC.lean:1779-1867` — **`annotate_let_i` refines the
`.letE` clause of `annotateBodyI`** (`core_c.rs:4900`): the official `infer_let`
triple runs HERE, on the annotated annotation and the annotated value, before
the ζ reduct is taken (con-leche's task #217); the reduct substitutes the
**raw** value, not the annotated one — the Lean's own spelling. -/
theorem annotate_let_i_refines (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (depth : Std.U64) {ty v b : expr.Expr} (hty : ExprWF ty) (hv : ExprWF v)
    (hb : ExprWF b) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.annotate_let_i mode fuel st fe depth ty v b)
      (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe depth.val
        (.letE (absExpr ty) (absExpr v) (absExpr b))) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  unfold cached.core_c.annotate_let_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp only [uncurry_apply_pair] at hok
    simp at hok
    obtain ⟨hr, -⟩ := hok
    subst hr
    rw [annotateBodyI_letE]
    exact Out.err
      (ErrSim.bindCM ((hw.annotateSim depth hty).apply_err hwf hfe h1 hrel hfrel))
  | Ok ty2 =>
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
    obtain ⟨lst1, hrun1, hrel1, hwf1, hty2WF⟩ :=
      (hw.annotateSim depth hty).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
    cases r1 with
    | Err err =>
      simp only [uncurry_apply_pair] at hok
      simp at hok
      obtain ⟨hr, -⟩ := hok
      subst hr
      rw [annotateBodyI_letE, bind_run hrun1]
      exact Out.err
        (ErrSim.bindCM ((hw.inferSim depth hty2WF).apply_err hwf1 hfe h2 hrel1 hfrel))
    | Ok tty =>
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
      obtain ⟨lst2, hrun2, hrel2, hwf2, httyWF⟩ :=
        (hw.inferSim depth hty2WF).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨⟨r2, st3⟩, h3, hok⟩ := hok
      cases r2 with
      | Err err =>
        simp only [uncurry_apply_pair] at hok
        simp at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [annotateBodyI_letE, bind_run hrun1, bind_run hrun2]
        exact Out.err
          (ErrSim.bindCM ((hd.ensureSort depth httyWF).apply_err hwf2 hfe h3 hrel2 hfrel))
      | Ok srt =>
        simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
        obtain ⟨lst3, hrun3, hrel3, hwf3, hsrtWF⟩ :=
          (hd.ensureSort depth httyWF).apply hwf2 hfe h3 hrel2 hfrel
        obtain ⟨⟨r3, st4⟩, h4, hok⟩ := hok
        cases r3 with
        | Err err =>
          simp only [uncurry_apply_pair] at hok
          simp at hok
          obtain ⟨hr, -⟩ := hok
          subst hr
          rw [annotateBodyI_letE, bind_run hrun1, bind_run hrun2, bind_run hrun3]
          exact Out.err
            (ErrSim.bindCM ((hw.annotateSim depth hv).apply_err hwf3 hfe h4 hrel3 hfrel))
        | Ok v2 =>
          simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
          obtain ⟨lst4, hrun4, hrel4, hwf4, hv2WF⟩ :=
            (hw.annotateSim depth hv).apply hwf3 hfe h4 hrel3 hfrel
          obtain ⟨⟨r4, st5⟩, h5, hok⟩ := hok
          cases r4 with
          | Err err =>
            simp only [uncurry_apply_pair] at hok
            simp at hok
            obtain ⟨hr, -⟩ := hok
            subst hr
            rw [annotateBodyI_letE, bind_run hrun1, bind_run hrun2, bind_run hrun3,
              bind_run hrun4]
            exact Out.err
              (ErrSim.bindCM ((hw.inferSim depth hv2WF).apply_err hwf4 hfe h5 hrel4 hfrel))
          | Ok tv =>
            simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
            obtain ⟨lst5, hrun5, hrel5, hwf5, htvWF⟩ :=
              (hw.inferSim depth hv2WF).apply hwf4 hfe h5 hrel4 hfrel
            obtain ⟨⟨r5, st6⟩, h6, hok⟩ := hok
            cases r5 with
            | Err err =>
              simp only [uncurry_apply_pair] at hok
              simp at hok
              obtain ⟨hr, -⟩ := hok
              subst hr
              rw [annotateBodyI_letE, bind_run hrun1, bind_run hrun2, bind_run hrun3,
                bind_run hrun4, bind_run hrun5]
              exact Out.err
                (ErrSim.bindCM
                  ((hw.defeqSim depth htvWF hty2WF).apply_err hwf5 hfe h6 hrel5 hfrel))
            | Ok eq =>
              obtain ⟨lst6, hrun6, hrel6, hwf6, -⟩ :=
                (hw.defeqSim depth htvWF hty2WF).apply hwf5 hfe h6 hrel5 hfrel
              cases eq with
              | false =>
                -- `core_c.rs:4955` <- `Cached/CoreC.lean:1844`: the `unless`
                -- guard agrees, so both sides throw `invalid` here
                obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
                obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
                obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
                simp only [Result.ok.injEq, Prod.mk.injEq] at hok
                obtain ⟨hr, -⟩ := hok
                subst hr
                rw [invalid_inv hce1]
                rw [annotateBodyI_letE, bind_run hrun1, bind_run hrun2, bind_run hrun3,
                  bind_run hrun4, bind_run hrun5, bind_run hrun6]
                exact Out.err
                  (ErrSim.invalid (s := "let value type mismatch") (by simp))
              | true =>
                simp only [uncurry_apply_pair, bind_eq_ok_iff, if_true] at hok
                obtain ⟨red, hred, hok⟩ := hok
                obtain ⟨habsRed, hwfRed⟩ := ExprOpsC.instantiate1_refines hb hv
                  (by rw [StateC.inst1_m_eq] at hred; exact hred)
                rw [show (0#u64 : Std.U64).val = 0 from by scalar_tac] at habsRed
                have hout := hw.annotateSim depth hwfRed fe lfe hfe hfrel st6 r st' hwf6
                  hok lst6 hrel6
                simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4 hrun5 hrun6 hout ⊢
                rw [annotateBodyI_letE]
                simp only [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
                  Except.pure, hrun1, hrun2, hrun3, hrun4, hrun5, hrun6, ← habsRed,
                  id_eq, if_true]
                exact hout

/-- `CoreKInfer.lean`'s transcription of the `.proj` arm below its recursive
calls, as the `CheckCM` action `annotateBodyI` writes inline: on success the
node names the subject type's head, the parameter count matches, and the value
is the normalized `.proj T i e'`.  The state is untouched. -/
theorem annotateProjEntryL_run {lfe : ConLeche.FEnv} {sn T : ConLeche.Name} {i : Nat}
    {e2 X : ConLeche.Expr} {targs : List ConLeche.Expr}
    (h : CoreK.annotateProjEntryL lfe sn T i e2 targs = .ok X)
    (lst : ConLeche.Cached.CState) :
    ((match lfe.findProj? T i with
      | some entry => do
        unless T = sn do
          throw (.invalid "invalid projection: the node names another structure")
        unless targs.length = entry.numParams do
          throw (.invalid "projection parameter mismatch")
        pure (ConLeche.Expr.proj T i e2)
      | none =>
        throw (if (lfe.findProj? T 0).isSome then
            ConLeche.CheckError.invalid "projection index out of range"
          else .notImplemented "projection on a non-structure-like type")) :
      ConLeche.Cached.CheckCM ConLeche.Expr).run lst = .ok (X, lst) := by
  rw [CoreK.annotateProjEntryL] at h
  cases hfp : lfe.findProj? T i with
  | none => simp only [hfp] at h; simp at h
  | some entry =>
    simp only [hfp] at h
    simp only []
    by_cases hT : T = sn
    · rw [if_pos hT] at h
      by_cases hn : targs.length = entry.numParams
      · rw [if_pos hn] at h
        simp only [Except.ok.injEq] at h
        simp [hT, hn, ← h]
      · rw [if_neg hn] at h; simp at h
    · rw [if_neg hT] at h; simp at h

/-- The same clause **on a throw** (task #67): whatever
`CoreK.annotateProjEntryL` throws, the `CheckCM` action `annotateBodyI` writes
inline throws too — the state is untouched on both sides. -/
theorem annotateProjEntryL_run_err {lfe : ConLeche.FEnv} {sn T : ConLeche.Name} {i : Nat}
    {e2 : ConLeche.Expr} {targs : List ConLeche.Expr} {le : ConLeche.CheckError}
    (h : CoreK.annotateProjEntryL lfe sn T i e2 targs = .error le)
    (lst : ConLeche.Cached.CState) :
    ((match lfe.findProj? T i with
      | some entry => do
        unless T = sn do
          throw (.invalid "invalid projection: the node names another structure")
        unless targs.length = entry.numParams do
          throw (.invalid "projection parameter mismatch")
        pure (ConLeche.Expr.proj T i e2)
      | none =>
        throw (if (lfe.findProj? T 0).isSome then
            ConLeche.CheckError.invalid "projection index out of range"
          else .notImplemented "projection on a non-structure-like type")) :
      ConLeche.Cached.CheckCM ConLeche.Expr).run lst = .error le := by
  rw [CoreK.annotateProjEntryL] at h
  cases hfp : lfe.findProj? T i with
  | none =>
    simp only [hfp] at h
    simp only [Except.error.injEq] at h
    simp only []
    simp [← h]
  | some entry =>
    simp only [hfp] at h
    simp only []
    by_cases hT : T = sn
    · rw [if_pos hT] at h
      by_cases hn : targs.length = entry.numParams
      · rw [if_pos hn] at h; simp at h
      · rw [if_neg hn] at h
        simp only [Except.error.injEq] at h
        simp [hT, hn, ← h]
    · rw [if_neg hT] at h
      simp only [Except.error.injEq] at h
      simp [hT, ← h]

/-- `ConLeche/Cached/CoreC.lean:1779-1867` — **`annotate_proj_i` refines the
`.proj` clause of `annotateBodyI`** (`core_c.rs:4950`): run the projection rule,
the one place it is checked.  A table entry types the node directly and the
display name is normalized to the type's head, but the node's OWN structure
name is official's `infer_proj` premise and is checked here (con-leche's
task #271). -/
theorem annotate_proj_i_refines (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (depth : Std.U64) {sn : name.Name} (hsn : NameWF sn) (i : Std.U64)
    {pe : expr.Expr} (hpe : ExprWF pe) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.annotate_proj_i mode fuel st fe depth sn i pe)
      (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe depth.val
        (.proj (absName sn) i.val (absExpr pe))) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  unfold cached.core_c.annotate_proj_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp only [uncurry_apply_pair] at hok
    simp at hok
    obtain ⟨hr, -⟩ := hok
    subst hr
    rw [annotateBodyI_proj]
    exact Out.err
      (ErrSim.bindCM ((hw.annotateSim depth hpe).apply_err hwf hfe h1 hrel hfrel))
  | Ok e2 =>
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
    obtain ⟨lst1, hrun1, hrel1, hwf1, he2WF⟩ :=
      (hw.annotateSim depth hpe).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
    cases r1 with
    | Err err =>
      simp only [uncurry_apply_pair] at hok
      simp at hok
      obtain ⟨hr, -⟩ := hok
      subst hr
      rw [annotateBodyI_proj, bind_run hrun1, bind_assoc']
      exact Out.err
        (ErrSim.bindCM ((hd.inferIOWhnf depth he2WF).apply_err hwf1 hfe h2 hrel1 hfrel))
    | Ok te =>
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
      obtain ⟨lst2, hrun2, hrel2, hwf2, hteWF⟩ :=
        (hd.inferIOWhnf depth he2WF).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨f, hf, hok⟩ := hok
      obtain ⟨en, hen, hok⟩ := hok
      rw [← Result.ok_injective hen] at hok
      obtain ⟨habsF, hfWF⟩ := ExprOps.get_app_fn_refines hteWF hf
      rw [annotateBodyI_proj, bind_run hrun1, bind_assoc', bind_run hrun2,
        ConLeche.Cached.ExprC.getAppFn_spec, ← habsF]
      cases hfWF with
      | @mk_const n us e hn hus h3 =>
        obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h3
        simp only [ExprOps.node_kind, bind_eq_ok_iff] at hok
        obtain ⟨targs, htargs, hok⟩ := hok
        obtain ⟨habsTargs, htargsWF⟩ := ExprOps.get_app_args_refines hteWF htargs
        obtain ⟨r2, hr2, hok⟩ := hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, hst⟩ := hok
        rw [hr] at hr2
        subst hst
        simp only [absExpr_mk, absExprKind]
        rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← habsTargs]
        cases r with
        | Ok x =>
          obtain ⟨hentry, hrWF⟩ := CoreK.annotate_proj_entry_refines
            (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe) hsn hn he2WF hr2
          exact Out.ok (lst' := lst2) (annotateProjEntryL_run hentry lst2) hrel2 hwf2 hrWF
        | Err ce =>
          -- `core_k::annotate_proj_entry`'s four mirrored throws
          refine Out.err (ErrSim.trans (CoreK.annotate_proj_entry_err
            (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe) hsn hn hr2) ?_)
          intro le hle
          exact annotateProjEntryL_run_err hle lst2
      | @bvar j e h3 =>
        obtain ⟨dd, rfl, -, -, -⟩ := Expr.bvar_inv h3
        simp only [ExprOps.node_kind] at hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        exact Out.err (ErrSim.notImplemented
          (s := "projection on a non-structure type")
          (by simp [absExpr_mk, absExprKind]))
      | @fvar idx ty e hty h3 =>
        obtain ⟨dd, rfl, -, -, -⟩ := Expr.fvar_inv h3
        simp only [ExprOps.node_kind] at hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        exact Out.err (ErrSim.notImplemented
          (s := "projection on a non-structure type")
          (by simp [absExpr_mk, absExprKind]))
      | @sort u e hu h3 =>
        obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.sort_inv h3
        simp only [ExprOps.node_kind] at hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        exact Out.err (ErrSim.notImplemented
          (s := "projection on a non-structure type")
          (by simp [absExpr_mk, absExprKind]))
      | @app g a e hg ha h3 =>
        obtain ⟨dd, rfl, -, -, -⟩ := Expr.app_inv h3
        simp only [ExprOps.node_kind] at hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        exact Out.err (ErrSim.notImplemented
          (s := "projection on a non-structure type")
          (by simp [absExpr_mk, absExprKind]))
      | @lam ty bo m e hty hbo hm h3 =>
        obtain ⟨dd, rfl, -, -, -⟩ := Expr.lam_inv h3
        simp only [ExprOps.node_kind] at hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        exact Out.err (ErrSim.notImplemented
          (s := "projection on a non-structure type")
          (by simp [absExpr_mk, absExprKind]))
      | @forall_e ty bo m e hty hbo hm h3 =>
        obtain ⟨dd, rfl, -, -, -⟩ := Expr.forall_e_inv h3
        simp only [ExprOps.node_kind] at hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        exact Out.err (ErrSim.notImplemented
          (s := "projection on a non-structure type")
          (by simp [absExpr_mk, absExprKind]))
      | @let_e ty v bo e hty hv hbo h3 =>
        obtain ⟨dd, rfl, -, -, -⟩ := Expr.let_e_inv h3
        simp only [ExprOps.node_kind] at hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        exact Out.err (ErrSim.notImplemented
          (s := "projection on a non-structure type")
          (by simp [absExpr_mk, absExprKind]))
      | @lit l e hl h3 =>
        obtain ⟨dd, rfl, -, -, -⟩ := Expr.lit_inv h3
        simp only [ExprOps.node_kind] at hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        exact Out.err (ErrSim.notImplemented
          (s := "projection on a non-structure type")
          (by simp [absExpr_mk, absExprKind]))
      | @proj s2 idx x e hs2 hx h3 =>
        obtain ⟨dd, rfl, -, -, -⟩ := Expr.proj_inv h3
        simp only [ExprOps.node_kind] at hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        exact Out.err (ErrSim.notImplemented
          (s := "projection on a non-structure type")
          (by simp [absExpr_mk, absExprKind]))

end

/-! ## The body

`annotate_body_i` is `annotateBodyI`'s `match`, with the five Rust-only arms
above under their own names and the six structural clauses inline.  This is the
lemma `Arms/Arms.lean` feeds to `RefinesE.ofSim` for `Bodies.annotate`. -/

/-- `ConLeche/Cached/CoreC.lean:1779-1867` — **`annotate_body_i` refines
`annotateBodyI`** (`core_c.rs:4704`): the annotation pass's body, the
`PropWhen`-threading, ζ-reducing rebuild.  con-leche gives the pass **one**
named core for both modes, so `annotateBodyI` takes no `mode`; the Rust's
`mode` is there only to reach the wrappers. -/
theorem annotate_body_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (hd : AnnotateDeps mode fuel)
    (d : Std.U64) {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.annotate_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.annotateBodyI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only at hok ⊢
  unfold cached.core_c.annotate_body_i at hok
  cases he with
  | @bvar i e h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.bvar_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff,
      Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨e1, he1, hr, hst⟩ := hok
    rw [Expr.dup_eq he1] at hr
    subst hst
    subst hr
    refine ⟨lst, ?_, hrel, hwf, ExprWF.bvar h1⟩
    simp only [absExpr_mk, absExprKind]
    rw [annotateBodyI_bvar]
    simp
  | @sort u e hu h1 =>
    obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff,
      Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨e1, he1, hr, hst⟩ := hok
    rw [Expr.dup_eq he1] at hr
    subst hst
    subst hr
    refine ⟨lst, ?_, hrel, hwf, ExprWF.sort hu h1⟩
    simp only [absExpr_mk, absExprKind]
    rw [annotateBodyI_sort]
    simp
  | @mk_const n us e hn hus h1 =>
    obtain ⟨dd, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff,
      Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨e1, he1, hr, hst⟩ := hok
    rw [Expr.dup_eq he1] at hr
    subst hst
    subst hr
    refine ⟨lst, ?_, hrel, hwf, ExprWF.mk_const hn hus h1⟩
    simp only [absExpr_mk, absExprKind]
    rw [annotateBodyI_const]
    simp
  | @fvar idx ty e hty h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.fvar_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
    split at hok
    · rename_i hlt
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨e1, he1, hr, hst⟩ := hok
      rw [Expr.dup_eq he1] at hr
      subst hst
      subst hr
      refine ⟨lst, ?_, hrel, hwf, ExprWF.fvar hty h1⟩
      simp only [absExpr_mk, absExprKind]
      rw [annotateBodyI_fvar, if_pos (show idx.val < d.val by scalar_tac)]
      simp
    · -- `core_c.rs:4760` <- `Cached/CoreC.lean:1786`: the scope test agrees
      rename_i hnlt
      obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨hr, -⟩ := hok
      subst hr
      rw [invalid_inv hce1]
      simp only [absExpr_mk, absExprKind]
      rw [annotateBodyI_fvar, if_neg (show ¬ idx.val < d.val by scalar_tac)]
      exact Out.err (ErrSim.invalid (s := "free variable out of scope") (by simp))
  | @app f a e hf ha h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, 
      bind_eq_ok_iff] at hok
    obtain ⟨⟨r0, st1⟩, h2, hok⟩ := hok
    cases r0 with
    | Err err =>
      simp only [uncurry_apply_pair] at hok
      simp at hok
      obtain ⟨hr, -⟩ := hok
      subst hr
      simp only [absExpr_mk, absExprKind]
      rw [annotateBodyI_app]
      exact Out.err (ErrSim.bindCM ((hw.annotateSim d hf).apply_err hwf hfe h2 hrel hfrel))
    | Ok f2 =>
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at hok
      obtain ⟨lst1, hrun1, hrel1, hwf1, hf2WF⟩ :=
        (hw.annotateSim d hf).apply hwf hfe h2 hrel hfrel
      obtain ⟨⟨r1, st2⟩, h3, hok⟩ := hok
      cases r1 with
      | Err err =>
        simp only [uncurry_apply_pair] at hok
        simp at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        simp only [absExpr_mk, absExprKind]
        rw [annotateBodyI_app, bind_run hrun1]
        exact Out.err
          (ErrSim.bindCM ((hw.annotateSim d ha).apply_err hwf1 hfe h3 hrel1 hfrel))
      | Ok a2 =>
        simp only [uncurry_apply_pair, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨lst2, hrun2, hrel2, hwf2, ha2WF⟩ :=
          (hw.annotateSim d ha).apply hwf1 hfe h3 hrel1 hfrel
        obtain ⟨e1, he1, hr, hst⟩ := hok
        subst hst
        subst hr
        refine ⟨lst2, ?_, hrel2, hwf2, Expr.app_wf hf2WF ha2WF he1⟩
        simp only [absExpr_mk, absExprKind]
        rw [annotateBodyI_app, bind_run hrun1, bind_run hrun2, Expr.app_refines he1]
        rfl
  | @forall_e ty bo m e hty hbo hm h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
    simp only [absExpr_mk, absExprKind]
    exact annotate_forall_i_refines hw hd d hty hbo hm fe lfe hfe hfrel st r st'
      hwf hok lst hrel
  | @let_e ty v bo e hty hv hbo h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.let_e_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
    simp only [absExpr_mk, absExprKind]
    exact annotate_let_i_refines hw hd d hty hv hbo fe lfe hfe hfrel st r st'
      hwf hok lst hrel
  | @proj sn idx x e hsn hx h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.proj_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
    simp only [absExpr_mk, absExprKind]
    exact annotate_proj_i_refines hw hd d hsn idx hx fe lfe hfe hfrel st r st'
      hwf hok lst hrel
  | @lam ty bo m e hty hbo hm h1 =>
    have heWF : ExprWF e := ExprWF.lam hty hbo hm h1
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at hok
    obtain ⟨bb, hbbm, hok⟩ := hok
    have hbbv := StateC.bvar_bound_m_refines heWF hbbm
    simp only [absExpr_mk, absExprKind] at hbbv
    simp only [absExpr_mk, absExprKind]
    split at hok
    · rename_i h0
      refine annotate_lam_loop_i_refines hw hd d hty hbo hm ?_ fe lfe hfe hfrel st r st'
        hwf hok lst hrel
      rw [← hbbv, h0]
      scalar_tac
    · rename_i h0
      refine annotate_lam_chain_i_refines hw hd d hty hbo hm ?_ fe lfe hfe hfrel st r st'
        hwf hok lst hrel
      rw [← hbbv]
      intro hc
      exact h0 (by scalar_tac)
  | @lit l e hl h1 =>
    obtain ⟨dd, rfl, -, -, -⟩ := Expr.lit_inv h1
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
    cases l with
    | NatVal n =>
      simp only [bind_eq_ok_iff] at hok
      obtain ⟨b, hb, hok⟩ := hok
      have hbv : b = ConLeche.natLitSupportedF lfe :=
        CoreK.nat_lit_supported_refines CoreK.pinnedBasisNames
          (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe) hb
      split at hok
      · rename_i htrue
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨e1, he1, hr, hst⟩ := hok
        rw [Expr.dup_eq he1] at hr
        subst hst
        subst hr
        refine ⟨lst, ?_, hrel, hwf, ExprWF.lit hl h1⟩
        simp only [absExpr_mk, absExprKind, absLiteral]
        rw [annotateBodyI_natLit, if_pos (by rw [← hbv]; exact htrue)]
        simp
      · -- `core_c.rs:4769` <- `Cached/CoreC.lean:1791`
        rename_i hfalse
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [invalid_inv hce1]
        simp only [absExpr_mk, absExprKind, absLiteral]
        rw [annotateBodyI_natLit, if_neg (by rw [← hbv]; exact hfalse)]
        exact Out.err (ErrSim.invalid
          (s := "Nat literal without the Nat basis declarations") (by simp))
    | StrVal str =>
      simp only [bind_eq_ok_iff] at hok
      obtain ⟨b, hb, hok⟩ := hok
      have hbv : b = ConLeche.strLitSupportedF lfe :=
        CoreK.str_lit_supported_refines CoreK.pinnedBasisNames
          (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe) hb
      split at hok
      · rename_i htrue
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨e1, he1, hr, hst⟩ := hok
        rw [Expr.dup_eq he1] at hr
        subst hst
        subst hr
        refine ⟨lst, ?_, hrel, hwf, ExprWF.lit hl h1⟩
        simp only [absExpr_mk, absExprKind, absLiteral]
        rw [annotateBodyI_strLit, if_pos (by rw [← hbv]; exact htrue)]
        simp
      · -- `core_c.rs:4776` <- `Cached/CoreC.lean:1794`
        rename_i hfalse
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨ce1, hce1, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hr, -⟩ := hok
        subst hr
        rw [not_implemented_inv hce1]
        simp only [absExpr_mk, absExprKind, absLiteral]
        rw [annotateBodyI_strLit, if_neg (by rw [← hbv]; exact hfalse)]
        exact Out.err (ErrSim.notImplemented
          (s := "string literals before the String support declarations") (by simp))


end ConRon.Refine.Core
