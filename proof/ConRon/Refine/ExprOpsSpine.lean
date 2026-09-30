/-
The spine-and-telescope part of task #21: the refinement of the
`getAppFn`/`getAppArgs`/`mkAppN` spine family, the `stripLams`/`stripPis`
telescope family, the `instPis`/`instPisAt`/`instLamsAt`/`instSpine`
instantiation cascade, `recRulePlain` and the small shape readers
(`piResult`, `piArity`, `resultSort`, `fvarTypeD`) of
`crates/con-ron-core/src/kernel/expr_ops.rs`, on the generated model
`ConRon.Generated.kernel.expr_ops.*`.

Statements are against the *logical* definitions of
`ConLeche/Kernel/ExprOps.lean`, exact-result-on-success (DESIGN.md §3.5): the
abstraction equation first, well-formedness second.  `Option`-returning
functions get an `Option.map`-shaped equation (so that the `none` case is a
real claim too) plus a separate well-formedness clause for the `some` case,
which is the shape the callers of `stripPis`/`instPisAt` will want.

Three things shaped the proofs:

* **The port accumulates where Lean conses** (task #13's deviation 3), so
  every `*_go`/`*_from` lemma is stated with the accumulator *prefixed* to
  con-leche's answer (`absExprs out ++ …`), and the wrapper at `out = []` is
  the corollary.  Same for the index recursions, whose lemma is at
  `(absExprs args).drop i.val`.
* **Not `fixpoint_induct`**: a `partial_fixpoint` has one, but it wants an
  admissible motive and Lean derives no `partial_correctness` over `Result`, so
  each walk unfolds `eq_def` and is an induction either on the `ExprWF` derivation (`get_app_fn`, `pi_result`,
  `get_app_args_go`, `pi_arity`, `result_sort`) or on a `Nat` measure --
  `args.length - i` for the index recursions, `k` for the telescope ones.
* **`recRulePlain`'s list comparison** is a `==` on `List Expr`, i.e.
  `List.beq` over con-leche's `Expr.beq`; `rec_rule_args_eq` decides the same
  list equality one index at a time, so its lemma is stated as
  `decide (… = …)` on the `List Expr` and `beq_iff_eq` closes the gap.

Merged at task #47 with the one-pass telescope group (task #21's
`ExprOpsFast.lean`), whose module note is the section comment halfway down; its
four `*_local` duplicates are gone -- the sequential `inst_pis_at`/`inst_lams_at`
lemmas of this file are what the `*F` wrappers' fall-back arm uses.
-/
import ConRon.Refine.ExprOpsSubst

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-! ## The spine readers -/

/-! ## The telescope strippers

`stripLams`/`stripPis` return a *binder list*, `Vec<(Expr, BinderMeta)>` in the
port and `List (Expr × BinderMeta)` in con-leche, so this section needs its own
abstraction and well-formedness (`absBinders`, `BindersWF`).  The recursion is
on the binder count, so the proofs are a strong induction on `k.val` with a
plain `cases` on the `ExprWF` derivation inside -- which is what keeps the
`k = 0` arm from being repeated ten times. -/

/-- A `Vec<(Expr, BinderMeta)>` as con-leche's `List (Expr × BinderMeta)`. -/
def absBinders (bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) :
    List (ConLeche.Expr × ConLeche.BinderMeta) :=
  bs.val.map fun p => (absExpr p.1, absBinderMeta p.2)

@[simp] theorem absBinders_new :
    absBinders (alloc.vec.Vec.new (expr.Expr × expr.BinderMeta)) = [] := rfl

/-! ## The instantiation cascade

`instPis`/`instPisAt`/`instLamsAt`/`instSpine` fold `Expr.instantiate1` over the
argument list, so each of these proofs is an induction on `args.length - i`
whose step is `instantiate1_refines` (the foundation's headline lemma).  The
con-leche side matches on the *list*, which `vec_index_expr` supplies:
`(absExprs args).drop i = absExpr args[i] :: (absExprs args).drop (i+1)`. -/

/-! ## `recRulePlain`

con-leche compares two *lists*: `dom.getAppArgs.take cnP` against
`(List.range cnP).map (fun k => .bvar (mI - 1 - k))`.  The port walks the index
instead (task #13's deviation 6), so `rec_rule_args_eq`'s lemma is the
*pointwise* reading of that equality, and `take_eq_range_map_iff` is the bridge
between the two at `k = 0`. -/

/-! ## Rebuilding a telescope

`pisToLams` and `replacePiBody` build on the way *out* of the recursion, so
there is no accumulator here (task #13's deviation 5); the induction is on the
binder count with a `cases` on the `ExprWF` derivation inside.  `pisToLams`
emits the parse placeholder `⟨.never⟩` as the binder datum, which is
`prop_when::never` on the port side (`PropWhen.never_refines`). -/

/-!Task #21, the one-pass telescope part: `inst_pis_at_f_go`/`inst_pis_at_f` and
`inst_lams_at_f_go`/`inst_lams_at_f` (con-leche's `instPisAtFGo`
`ExprOps.lean:1183`, `instPisAtF` `:1191`, `instLamsAtFGo` `:1197`,
`instLamsAtF` `:1205`).

The `*F` walks peel the *raw* binders while the pending substitutions
accumulate in `acc` (innermost first), and give each domain and the residual a
single `instantiateList` pass instead of one `instantiate1` pass per argument;
when the raw telescope is shorter than the argument list the `Go` walk reports
`none` and the wrapper falls back to the sequential `instPisAt`/`instLamsAt`,
which is what makes the wrappers' equation unconditional.

Two shapes, both forced by the port's deviations (task #13, deviation 3):

* the port walks `args` by an **index** and accumulates the domains into `out`
  on the way *in*, where con-leche consumes a list and conses on the way out.
  So the `Go` lemma is stated at `(absExprs args).drop i` with `absExprs out`
  *prepended* to con-leche's answer: `r.map … = (instPisAtFGo acc (drop i args)
  e).map (fun p => (absExprs out ++ p.1, p.2))`.  An `Option`-valued result is
  compared under `Option.map` of the abstraction, with the well-formedness of a
  `some`'s two components as the second conjunct (`∀ p, r = some p → …`).
* the recursion descends into an expression that is *not* a subterm of `e`
  (`instantiate1 body args[i]` for the sequential walks), so the induction is
  a strong induction on `args.length - i` with `cases he` inside it, not an
  induction on the `ExprWF` derivation: nine of the ten constructors return
  `none`, and the tenth supplies the children's well-formedness.

`inst_pis_at_from`/`inst_lams_at_from` (and their `i = 0` wrappers) belong to
another worker's group but are the wrappers' fall-back arm, so the four
`*_local` lemmas below prove exactly what that arm needs; they are duplicates
to be reconciled at merge.
-/

/-! ## `Vec<Expr>` plumbing -/

/-! ## The one-pass walks -/

end ConRon.Refine.ExprOps
